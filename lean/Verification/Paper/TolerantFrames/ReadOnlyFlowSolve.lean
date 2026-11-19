import Verification.Paper.TolerantFrames.ReadOnlyFitsDecide

/-! # Read-only handles: proposing the flow of a component's codes

The draft "Read-only handles" (`docs/drafts/readonly-handles.md`, "Deciding
the flow"). The proposal `FFlow.check` decides is computed here from the
lowered graphs of `C`'s codes: nothing here is trusted, and nothing is
proved of it; a proposal it gives is accepted only where `FFlow.check`
holds of it.

- **Signatures** (`fnRound`): a slot names a signature where every edge
  into its node carries a slot naming it, from the entry's named slots and
  the closure's own slot. A signature is an index into a table of `C`'s
  codes' signatures and their entries' seeds, compared as a number; a
  target's row has the width of the edge's mapping, or the source's.
- **Sites** (`solveLoop`): one variable per slot a node keeps apart
  (`neededWidths`), one for the slots past them and one for its value; an
  edge copies each variable of its source into the one of its target that
  reads it. A node's sets are its expression's least set (`gen`, `syn` at
  the current proposal, its stores, what reaches outside code and the
  slots of a callee's entry added as requirements; a known call's value
  its callee's return set; a closure's set its code's token). `O` is held
  where outside code supplies values: the entry slots of each closure's
  code whose token reaches `O` (`OpenAt`), a handler's thrown value;
  outside storage at every slot of the unit's entry, and at each slot
  naming a module function's signature its code's token. `O` is grown
  until closed and its storage holds all of it. A worklist runs the
  copies and the nodes until nothing changes or the fuel ends.

Codes and nodes are arrays, read by index. -/
namespace Verification.TolerantFrames.ReadOnly
open Verification ControlFlow

variable {P : Package} [DecidableEq P.Site]

/-- **A code of `C` to propose for**: its graph, the layout of its entry,
the signatures its entry names, the sites its frames allocate at, and
whether it is entered as a closure, its own slot holding it (a unit's
program is entered at its request's inputs). -/
structure SolveCode (P : Package) where
  code : Code
  ar : Nat
  rest : Bool
  ncaps : Nat
  start : Nat
  seeds : List (Option FnSig)
  alloc : Alloc P
  closure : Bool := true
  /-- The site standing for the code's closures. -/
  tok : Option P.Site := none

def SolveCode.sig (c : SolveCode P) : FnSig := ⟨c.code, c.ar, c.start, c.rest, c.ncaps⟩

/-- The sites of `T` not in `S`, each once, last first. -/
def freshOf (S T : Sites P) : Sites P := T.foldl (fun acc x => if x ∈ S || x ∈ acc then acc else x :: acc) []

/-- The union of two sets, each site once. -/
def union (S T : Sites P) : Sites P := S ++ (freshOf S T).reverse

/-- A slot's signature in the rounds: an index into the table of
signatures, compared as a number. -/
abbrev FnIx := Option Nat

/-- **The state of the proposal**: `O`, the heap of sites, the sets of the
variables (each node's slots kept apart, the set past them, its value),
where each node's variables start and how many slots it keeps apart, and
what changed since it was last read. -/
structure SolveState (P : Package) where
  O : Sites P
  heap : List (Option P.Site × Sites P × Sites P)
  vars : Array (Sites P)
  offs : Array (Array Nat)
  needs : Array (Array Nat)
  changedVars : List Nat := []
  /-- Each code's returning nodes' value variables. -/
  rets : Array (List Nat) := #[]
  /-- Each code's token. -/
  toks : Array (Option P.Site) := #[]
  /-- The sites each variable gained since it was last copied. -/
  delta : Array (Sites P) := #[]
  grewO : Bool := false
  grewHeap : Bool := false

namespace SolveState
variable (st : SolveState P)

/-- The heap of sites as a finite flow with no codes: what reads of the
contents need. -/
def heapFlow : FFlow P := ⟨st.O, st.heap, []⟩

/-- Add sites to `O`. -/
def toO (S : Sites P) : SolveState P :=
  let O' := union st.O S
  if O'.length = st.O.length then st else { st with O := O', grewO := true }

/-- Add sites to the contents and bindings of a site's storage. -/
def store (s : Option P.Site) (S : Sites P) : SolveState P :=
  match look s st.heap with
  | none => if S.isEmpty then st else { st with heap := (s, S, S) :: st.heap, grewHeap := true }
  | some (c, b) =>
    let c' := union c S
    let b' := union b S
    if c'.length = c.length ∧ b'.length = b.length then st
    else
      let heap := st.heap.map fun e => if e.1 = s then (s, c', b') else e
      { st with heap := heap, grewHeap := true }

/-- Grow variable `v` by `S`. -/
def grow (v : Nat) (S : Sites P) : SolveState P :=
  let old := st.vars.getD v []
  let new := freshOf old S
  if new.isEmpty then st
  else
    -- (the array taken out of the state before it is set, so that the
    -- update is in place where the state is not shared)
    let vars := st.vars
    let delta := st.delta
    let st := { st with vars := #[], delta := #[] }
    let added := new.reverse
    let delta := delta.modify v (fun d => d ++ added)
    { st with vars := vars.set! v (old ++ added), delta := delta, changedVars := v :: st.changedVars }

/-- The variable of slot `i` of node `l` of code `ci`: the slot's, or the
one past the slots kept apart. -/
def slotVar (ci l i : Nat) : Option Nat :=
  ((st.offs[ci]?).bind (·[l]?)).map fun o => o + min i ((st.needs.getD ci #[]).getD l 0)

/-- The return set of code `ci`: its returning nodes' values. -/
def retOf (ci : Nat) : Sites P :=
  (st.rets.getD ci []).foldl (fun acc v => union acc (st.vars.getD v [])) []

/-- Grow the slot `i` of node `l` of code `ci` by `S`. -/
def slot (ci l i : Nat) (S : Sites P) : SolveState P :=
  match st.slotVar ci l i with
  | some v => st.grow v S
  | none => st

end SolveState

section gen
variable (table : Array (FnSig × Option Nat)) (τ : Nat → Sites P) (φ : Nat → FnIx) (a : Alloc P)

/-- **A term's sets, proposed** (`syn` at the current proposal): its stores
added to the heap of sites, what reaches outside code added to `O`, the
slots of a callee's entry grown. `table` gives each signature and the
index of its code among `C`'s. -/
partial def gen (d : Nat) (Γ : Nat → Option (Sites P)) (e : Tm) : StateM (SolveState P) (Sites P) := do
  match e with
  | .var i => return if i < d then (Γ i).getD [] else τ (i - d)
  | .invoke f r args =>
    let Sf ← gen d Γ f
    let Sr ← gen d Γ r
    let Ls ← args.mapM (gen d Γ)
    let viaC : Option (Nat × FnSig) := match f with
      | .var j => if d ≤ j ∧ args.all partB then
          (φ (j - d)).bind fun t => (table[t]?).bind fun (σ, ci) => ci.map (·, σ)
        else none
      | _ => none
    match viaC with
    | some (ci, σ) =>
      modify fun st => st.slot ci σ.s (capSlot σ.ar σ.rest σ.ncaps) (τ (j' f d))
      modify fun st => st.slot ci σ.s (recvSlot σ.rest) Sr
      for i in List.range σ.ar do
        modify fun st => st.slot ci σ.s (paramSlot σ.rest i) (Ls.getD i [])
      if σ.rest then
        modify fun st => st.slot ci σ.s 0 [a.arr]
        modify fun st => st.store a.arr (Ls.drop σ.ar).flatten
      return (← get).retOf ci
    | none =>
      modify fun st => st.toO (Sf ++ Sr ++ Ls.flatten ++ [a.arr])
      return (← get).O
  | .construct f args =>
    let Sf ← gen d Γ f
    let Ls ← args.mapM (gen d Γ)
    modify fun st => st.toO (Sf ++ Ls.flatten ++ [a.arr])
    return (← get).O
  | .letE x b =>
    let Sx ← gen d Γ x
    gen (d + 1) (consSites Sx Γ) b
  | .spread x => let Sx ← gen d Γ x; return contentsOf (← get).heapFlow Sx
  | .makeAt .absent _ inits =>
    for x in inits do
      let S ← gen d Γ x
      modify fun st => st.store a.obj S
    return [a.obj]
  | .makeAt (.bound t r pre) _ inits =>
    for x in inits do
      let S ← gen d Γ x
      modify fun st => st.store a.obj S
    return a.obj :: ((partsSites τ d Γ (t :: r :: pre)).getD [])
  | .makeAt (.graph ar E K s caps _ rest comp) _ inits =>
    for x in inits do
      let S ← gen d Γ x
      modify fun st => st.store a.obj S
    if P.ofC comp then
      match (table.find? fun e => e.2.isSome && e.1.code == (E, K)).bind (·.2) with
      | some ci =>
        for i in List.range caps.length do
          match caps[i]? with
          | some u => modify fun st => st.slot ci s (capSlot ar rest i) ((partSites τ d Γ u).getD [])
          | none => pure ()
        return [a.obj, (← get).toks.getD ci none]
      | none => return [a.obj]
    else return a.obj :: ((partsSites τ d Γ caps).getD [])
  | .readAt _ x | .indexAt x _ =>
    let Sx ← gen d Γ x
    match e with
    | .indexAt _ k => let _ ← gen d Γ k
    | _ => pure ()
    let F := (← get).heapFlow
    let Q := grow F (Sx.length + (F.heap.map fun e => e.2.1.length).sum + 1) Sx
    return contentsOf F Q
  | .writeAt _ x y =>
    let Sx ← gen d Γ x
    let Sy ← gen d Γ y
    for s in Sx do
      modify fun st => st.store s Sy
    return []
  | .test _ x | .lenOf x => let _ ← gen d Γ x; return []
  | .ite c x y =>
    let _ ← gen d Γ c
    return union (← gen d Γ x) (← gen d Γ y)
  | .arith _ x y => let _ ← gen d Γ x; let _ ← gen d Γ y; return []
  | .arrLit inits =>
    for x in inits do
      let S ← gen d Γ x
      modify fun st => st.store a.arr S
    return [a.arr]
  | .elemAt x i =>
    let Sx ← gen d Γ x
    let _ ← gen d Γ i
    return contentsOf (← get).heapFlow Sx
  | .setElem x i v =>
    let Sx ← gen d Γ x
    let _ ← gen d Γ i
    let Sv ← gen d Γ v
    for s in a.arr :: Sx do
      modify fun st => st.store s Sv
    return a.arr :: Sx
  | .throw x =>
    let Sx ← gen d Γ x
    modify fun st => st.toO Sx
    return []
  | .merge _ x y =>
    let Sx ← gen d Γ x
    let Sy ← gen d Γ y
    let F := (← get).heapFlow
    let Q := grow F ((Sx ++ Sy).length + (F.heap.map fun e => e.2.1.length).sum + 1) (Sx ++ Sy)
    for s in Q do
      modify fun st => st.store a.obj (F.contents s)
    return [a.obj]
  | .makeKey k x =>
    let _ ← gen d Γ k
    let Sx ← gen d Γ x
    modify fun st => st.store a.obj Sx
    return [a.obj]
  | _ => return []
where
  /-- The slot a callee variable reads. -/
  j' (f : Tm) (d : Nat) : Nat := match f with
    | .var j => j - d
    | _ => 0

end gen

/-! ## Signatures -/

/-- The targets of a node's edges, with whether each pushes a value. -/
def edgesOf : Continuation × Option Target → List (Target × Bool)
  | (k, x) =>
    (match k with
      | .ret => []
      | .bind y => [(y, true)]
      | .effect y => [(y, false)]
      | .branch y n => [(y, false), (n, false)]
      | .branchBind y n => [(y, true), (n, true)]
      | .tagBind _ y n => [(y, true), (n, true)]) ++
    (match x with
      | none => []
      | some y => [(y, true)])

/-- Whether an edge pushes no value of the node: a `branchBind`'s Boolean,
or the exception a handler edge pushes. -/
def pushesNoVal (k : Continuation) (x : Option Target) (y : Target) : Bool :=
  (match k with | .branchBind .. => true | _ => false) || (match x with | some y' => y' == y | none => false)

/-- The value signature of a node: a slot variable's signature. -/
def vfnIx (fn : Array FnIx) : Tm → FnIx
  | .var j => fn.getD j none
  | _ => none

/-- The signatures carried along an edge: the target's slot `i` reads the
source's slot `mapIdx m i`; the target's width is the mapping's, or the
source's where none is given. -/
def carryIx (src : Nat → FnIx) (m : Option (List Nat)) (srcW : Nat) : Array FnIx :=
  let w := match m with
    | none => srcW
    | some slots => slots.length
  (List.range w).toArray.map fun i => src (mapIdx m i)

/-- Two signature rows meet: a slot keeps a signature both name. -/
def meetIx (x y : Array FnIx) : Array FnIx :=
  (List.range (min x.size y.size)).toArray.map fun i =>
    let a := x.getD i none
    if a == y.getD i none then a else none

/-- **The signatures carried from a node**: its row carried along each
edge and met at each target; the targets whose rows changed. `none` is a
node no edge reached yet. -/
def fnStep (exprs : Array Tm) (conts : Array (Continuation × Option Target))
    (fns : Array (Option (Array FnIx))) (l : Nat) : Array (Option (Array FnIx)) × List Nat := Id.run do
  let mut acc := fns
  let mut changed : List Nat := []
  let some fn := acc.getD l none | return (acc, [])
  let some e := exprs[l]? | return (acc, [])
  let some (k, x) := conts[l]? | return (acc, [])
  let vf := vfnIx fn e
  for (y, push) in edgesOf (k, x) do
    let noVal := pushesNoVal k x y
    let src : Nat → FnIx := fun i =>
      if push then (match i with | 0 => if noVal then none else vf | i + 1 => fn.getD i none)
      else fn.getD i none
    let car := carryIx src y.mapping (fn.size + if push then 1 else 0)
    let new := match acc.getD y.label none with
      | none => car
      | some old => meetIx old car
    if y.label < acc.size && acc.getD y.label none != some new then
      acc := acc.set! y.label (some new)
      changed := y.label :: changed
  return (acc, changed)

/-- The signatures of a code's nodes: the entry's row seeded, each node
whose row changed carried again, until none is left or the fuel ends (a
row only shrinks once set, so the fuel is not reached on a code's own
rows). -/
def fnsOf (exprs : Array Tm) (conts : Array (Continuation × Option Target)) (start : Nat)
    (seed : Array FnIx) : Array (Array FnIx) :=
  let init : Array (Option (Array FnIx)) :=
    (List.range exprs.size).toArray.map fun l => if l = start then some seed else none
  let rec loop : Nat → List Nat → Array (Option (Array FnIx)) → Array (Option (Array FnIx))
    | 0, _, acc => acc
    | _ + 1, [], acc => acc
    | r + 1, l :: work, acc => let (acc', ch) := fnStep exprs conts acc l; loop r (ch ++ work) acc'
  let maxW := (seed.size + 1 + exprs.foldl (fun m _ => m) 0) + (conts.foldl (fun m (k, _) =>
    max m ((edgesOf (k, none)).foldl (fun m (y, _) => max m (mlen y.mapping)) 0)) 0)
  (loop ((exprs.size + 1) * (maxW + exprs.size + 2) * 4) [start] init).map (·.getD #[])

/-! ## Sites -/

/-- The largest variable a term names, a bound on the slots it reads. -/
partial def maxVar : Tm → Nat
  | .var i => i + 1
  | .invoke f r args => max (maxVar f) (max (maxVar r) ((args.map maxVar).foldl max 0))
  | .construct f args => max (maxVar f) ((args.map maxVar).foldl max 0)
  | .makeAt (.bound t r pre) _ inits => ((t :: r :: pre ++ inits).map maxVar).foldl max 0
  | .makeAt (.graph _ _ _ _ caps _ _ _) _ inits => ((caps ++ inits).map maxVar).foldl max 0
  | .makeAt _ _ inits | .arrLit inits => (inits.map maxVar).foldl max 0
  | .letE a b | .indexAt a b | .writeAt _ a b | .arith _ a b | .elemAt a b | .merge _ a b | .makeKey a b =>
    max (maxVar a) (maxVar b)
  | .ite a b c | .setElem a b c => max (maxVar a) (max (maxVar b) (maxVar c))
  | .readAt _ a | .test _ a | .lenOf a | .spread a | .throw a => maxVar a
  | _ => 0

/-- **The width of each node's slots worth keeping apart**: the slots its
expression reads, those its edges' mappings read, and those a target's
width needs through an edge (one fewer through an edge pushing a value);
the entry's at the entry. Past it a node's slots are only carried, and the
set past the width holds them all. -/
def neededWidths (exprs : Array Tm) (conts : Array (Continuation × Option Target)) (start entry : Nat) :
    Array Nat := Id.run do
  let n := exprs.size
  let mut need : Array Nat := exprs.mapIdx fun l e => if l = start then max (maxVar e) entry else maxVar e
  for _ in [0:n + 2] do
    let mut changed := false
    for r in [0:n] do
      let l := n - 1 - r
      let some (k, x) := conts[l]? | continue
      let mut w := need.getD l 0
      for (y, push) in edgesOf (k, x) do
        let c := match y.mapping with
          | some slots => slots.foldl (fun m i => max m (i + 1)) 1
          | none => if push then need.getD y.label 0 - 1 else need.getD y.label 0
        w := max w c
      if w != need.getD l 0 then
        need := need.set! l w
        changed := true
    if !changed then break
  return need

/-- Whether a term reads the heap of sites (a read's contents), so changes
with it. -/
partial def readsHeap : Tm → Bool
  | .readAt .. | .indexAt .. | .elemAt .. | .spread _ | .merge .. => true
  | .invoke f r args => readsHeap f || readsHeap r || args.any readsHeap
  | .construct f args => readsHeap f || args.any readsHeap
  | .makeAt _ _ inits | .arrLit inits => inits.any readsHeap
  | .letE a b | .writeAt _ a b | .arith _ a b | .makeKey a b => readsHeap a || readsHeap b
  | .ite a b c | .setElem a b c => readsHeap a || readsHeap b || readsHeap c
  | .test _ a | .lenOf a | .throw a => readsHeap a
  | _ => false

/-- Whether a term's set reads `O` or a callee's return set: a call's
value. -/
partial def readsO : Tm → Bool
  | .invoke .. | .construct .. => true
  | .makeAt _ _ inits | .arrLit inits => inits.any readsO
  | .letE a b | .indexAt a b | .arith _ a b | .elemAt a b | .makeKey a b | .writeAt _ a b | .merge _ a b =>
    readsO a || readsO b
  | .ite a b c | .setElem a b c => readsO a || readsO b || readsO c
  | .readAt _ a | .test _ a | .lenOf a | .spread a | .throw a => readsO a
  | _ => false

/-- **`O` closed**: grown by its contents, its storage holding all of it,
and every variable outside code fills holding it: a handler's thrown value
(`oVars`), the entry slots of each closure's code whose token lies in `O`
(`entryVars`). -/
def closeO (oVars : List Nat) (entryVars : List (Option P.Site × List Nat)) (st : SolveState P) :
    SolveState P := Id.run do
  let mut st := st.toO (contentsOf st.heapFlow st.O)
  for s in st.O do
    st := st.store s st.O
  for v in oVars do
    st := st.grow v st.O
  for (t, vs) in entryVars do
    if t ∈ st.O then
      for v in vs do
        st := st.grow v st.O
  return st

/-- **The table of signatures**: each code's own at its index, then the
seeds no code of `C` gives, each with the index of its code among `C`'s. -/
def sigTable (cs : Array (SolveCode P)) : Array (FnSig × Option Nat) :=
  let own : Array (FnSig × Option Nat) := cs.mapIdx fun i c => (c.sig, some i)
  cs.foldl (fun acc c => c.seeds.foldl (fun acc sd => match sd with
    | some σ => if acc.any (·.1 == σ) then acc else acc.push (σ, none)
    | none => acc) acc) own

/-- **The start of the rounds**: the codes as arrays, the table of
signatures, each node's signatures, the variables' layout, the copies of
the edges, each variable's node, and the nodes reading the heap of sites
or `O`. -/
structure SolveStart (P : Package) where
  cs : Array (SolveCode P)
  codes : Array (Array Tm × Array (Continuation × Option Target))
  table : Array (FnSig × Option Nat)
  fns : Array (Array (Array FnIx))
  /-- The variables each variable is copied into. -/
  succ : Array (List Nat)
  /-- The node whose expression reads each variable, if any. -/
  readerOf : Array (Option (Nat × Nat))
  heapReaders : List (Nat × Nat)
  oReaders : List (Nat × Nat)
  /-- The variables outside code fills: the value a handler binds. -/
  oVars : List Nat
  /-- The entry slots of each closure's code, with its token. -/
  entryVars : List (Option P.Site × List Nat)
  st : SolveState P

/-- The copies of a node's edges: each variable of the target read from
one of the node's, from its value where the edge pushes it, nothing where
it pushes a test's Boolean or a thrown value (of `O`, `handlerVars`). -/
def edgeCopies (offs needs : Array Nat) (l : Nat) (k : Continuation) (x : Option Target) : List (Nat × Nat) :=
  let off := offs.getD l 0
  let need := needs.getD l 0
  let srcVar (i : Nat) : Nat := off + min i need
  let valVar := off + need + 1
  (edgesOf (k, x)).flatMap fun (y, push) =>
    let noVal := pushesNoVal k x y
    let toff := offs.getD y.label 0
    let tneed := needs.getD y.label 0
    let src (j : Nat) : Option Nat :=
      let i := mapIdx y.mapping j
      if push then (if i = 0 then (if noVal then none else some valVar) else some (srcVar (i - 1)))
      else some (srcVar i)
    -- Past the target's width its slots read what the variable past them
    -- holds; constant past the source's width and the mapping's.
    let R := max tneed (max (need + 2) (mlen y.mapping))
    ((List.range tneed).filterMap fun j => (src j).map (·, toff + j)) ++
      ((List.range (R + 1 - tneed)).filterMap fun j => (src (tneed + j)).map (·, toff + tneed))

/-- The variables of a handler's target that read the thrown value it
binds. -/
def handlerVars (offs needs : Array Nat) (l : Nat) (x : Option Target) : List Nat :=
  match x with
  | none => []
  | some y =>
    let toff := offs.getD y.label 0
    let tneed := needs.getD y.label 0
    let need := needs.getD l 0
    let R := max tneed (max (need + 2) (mlen y.mapping))
    ((List.range tneed).filter fun j => mapIdx y.mapping j = 0).map (toff + ·) ++
      (if (List.range (R + 1 - tneed)).any fun j => mapIdx y.mapping (tneed + j) = 0 then [toff + tneed] else [])

def solveStart (cs : List (SolveCode P)) : SolveStart P := Id.run do
  let csA := cs.toArray
  let codes := csA.map fun c => (c.code.1.toArray, c.code.2.toArray)
  let table := sigTable csA
  let ix (σ? : Option FnSig) : FnIx := σ?.bind fun σ => table.findIdx? (·.1 == σ)
  let fns : Array (Array (Array FnIx)) := csA.mapIdx fun ci c =>
    let (exprs, conts) := codes.getD ci (#[], #[])
    let self := capSlot c.ar c.rest c.ncaps
    let seed : Array FnIx := (List.range (max c.seeds.length (if c.closure then self + 1 else 0))).toArray.map fun i =>
      if c.closure && i = self then some ci else ix (c.seeds.getD i none)
    fnsOf exprs conts c.start seed
  let needs : Array (Array Nat) := csA.mapIdx fun ci c =>
    let (exprs, conts) := codes.getD ci (#[], #[])
    neededWidths exprs conts c.start (max c.seeds.length (capSlot c.ar c.rest c.ncaps + 1))
  -- Each node's variables: its slots kept apart, the one past them, its value.
  let mut offs : Array (Array Nat) := #[]
  let mut n := 0
  for row in needs do
    let mut o : Array Nat := #[]
    for w in row do
      o := o.push n
      n := n + w + 2
    offs := offs.push o
  let mut succ : Array (List Nat) := Array.replicate n []
  let mut readerOf : Array (Option (Nat × Nat)) := Array.replicate n none
  let mut oVars : List Nat := []
  let mut entryVars : List (Option P.Site × List Nat) := []
  let mut tokVars : List (Nat × Option P.Site) := []
  let mut noneVars : List Nat := []
  let mut rets : Array (List Nat) := #[]
  for (c, ci) in csA.toList.zipIdx do
    let (_, conts) := codes.getD ci (#[], #[])
    let o := offs.getD ci #[]
    let nd := needs.getD ci #[]
    -- The entry's slots: every slot outside code fills at a closure's
    -- entry holds `O`; every slot of the unit's entry outside storage.
    let so := o.getD c.start 0
    let sn := nd.getD c.start 0
    if c.closure then
      entryVars := (c.tok, (List.range (capSlot c.ar c.rest c.ncaps + 1)).map fun i => so + min i sn) :: entryVars
    else
      for i in List.range (sn + 1) do
        noneVars := (so + i) :: noneVars
    -- A slot naming a code's signature at the entry holds its token.
    for (sd, i) in c.seeds.zipIdx do
      match sd.bind (fun σ => (table.find? (·.1 == σ)).bind (·.2)) with
      | some cj => tokVars := (so + min i sn, (csA[cj]?).bind (·.tok)) :: tokVars
      | none => pure ()
    let mut rs : List Nat := []
    for l in [0:conts.size] do
      for v in [o.getD l 0 : o.getD l 0 + nd.getD l 0 + 1] do
        readerOf := readerOf.set! v (some (ci, l))
      let some (k, x) := conts[l]? | continue
      if (match k with | .ret => true | _ => false) then rs := (o.getD l 0 + nd.getD l 0 + 1) :: rs
      oVars := handlerVars o nd l x ++ oVars
      for (v, w) in edgeCopies o nd l k x do
        succ := succ.modify v (w :: ·)
    rets := rets.push rs
  let readers (p : Tm → Bool) : List (Nat × Nat) :=
    (codes.toList.zipIdx.flatMap fun ((exprs, _), ci) =>
      (exprs.toList.zipIdx.filter fun (e, _) => p e).map fun (_, l) => (ci, l))
  let st0 : SolveState P :=
    { O := [none], heap := [], vars := Array.replicate n [], delta := Array.replicate n [], offs := offs,
      needs := needs, rets := rets, toks := csA.map (·.tok) }
  let st0 := (noneVars ++ oVars).foldl (fun st v => st.grow v [none]) st0
  let st0 := tokVars.foldl (fun st (v, t) => st.grow v [t]) st0
  return ⟨csA, codes, table, fns, succ, readerOf, readers readsHeap, readers readsO, oVars, entryVars, st0⟩

/-- **A node's sets**: its expression's least set at its slots (`gen`), its
value grown by it; a returned value given to `O`, its callers run again
(through `grewO`). -/
def siteNode (s : SolveStart P) (st : SolveState P) (ci l : Nat) : SolveState P := Id.run do
  let some c := s.cs[ci]? | return st
  let some (exprs, conts) := s.codes[ci]? | return st
  let some e := exprs[l]? | return st
  let some (k, _) := conts[l]? | return st
  let off := (st.offs.getD ci #[]).getD l 0
  let need := (st.needs.getD ci #[]).getD l 0
  -- (the node's slots read once, so that the state's array is not shared
  -- while the node's term grows it)
  let slots : Array (Sites P) := (Array.range (need + 1)).map fun i => st.vars.getD (off + i) []
  let τ : Nat → Sites P := fun i => slots.getD (min i need) []
  let fn := (s.fns.getD ci #[]).getD l #[]
  let (S, st') := (gen s.table τ (fun i => fn.getD i none) c.alloc 0 (fun _ => none) e).run st
  let before := (st'.vars.getD (off + need + 1) []).length
  let mut st := st'.grow (off + need + 1) S
  if (match k with | .ret => true | _ => false) then
    st := st.toO (st.vars.getD (off + need + 1) [])
    if (st.vars.getD (off + need + 1) []).length != before then st := { st with grewO := true }
  return st

/-- **The sites, by a worklist**: each changed variable copied into those
that read it, each node whose slots changed run again (`siteNode`); when
neither is left, `O` closed (`closeO`), and every node reading the heap of
sites or `O` run again where either grew; until nothing is left or the
fuel ends, with the number of copies and of nodes run. -/
def solveLoop (s : SolveStart P) (fuel : Nat) (st0 : SolveState P) : SolveState P × Nat × Nat := Id.run do
  let n := s.succ.size
  let mut inQ : Array Bool := Array.replicate n false
  let mut vfront : List Nat := []
  let mut vback : List Nat := []
  let mut nodeQ : Array (Array Bool) := s.codes.map fun (exprs, _) => Array.replicate exprs.size true
  let mut nfront : List (Nat × Nat) := s.codes.toList.zipIdx.flatMap fun ((exprs, _), ci) =>
    (List.range exprs.size).map (ci, ·)
  let mut nback : List (Nat × Nat) := []
  let mut st := st0
  let mut copies := 0
  let mut runs := 0
  let mut grewO := false
  let mut grewHeap := false
  for _ in [0:fuel] do
    -- The variables changed: queued, their reader nodes marked.
    for v in st.changedVars do
      if !inQ.getD v true then
        inQ := inQ.set! v true
        vback := v :: vback
      if let some (c, m) := s.readerOf.getD v none then
        if !((nodeQ.getD c #[]).getD m true) then
          nodeQ := nodeQ.modify c (·.set! m true)
          nback := (c, m) :: nback
    grewO := grewO || st.grewO
    grewHeap := grewHeap || st.grewHeap
    st := { st with changedVars := [], grewO := false, grewHeap := false }
    if vfront.isEmpty then
      vfront := vback.reverse
      vback := []
    match vfront with
    | v :: rest =>
      vfront := rest
      inQ := inQ.set! v false
      copies := copies + 1
      -- (only what the variable gained since it was last copied: its
      -- readers hold the rest)
      let S := st.delta.getD v []
      let delta := st.delta
      st := { st with delta := #[] }
      st := { st with delta := delta.set! v [] }
      for w in s.succ.getD v [] do
        st := st.grow w S
    | [] =>
      if nfront.isEmpty then
        nfront := nback.reverse
        nback := []
      match nfront with
      | (ci, l) :: rest =>
        nfront := rest
        nodeQ := nodeQ.modify ci (·.set! l false)
        runs := runs + 1
        st := siteNode s st ci l
      | [] =>
        st := closeO s.oVars s.entryVars st
        grewO := grewO || st.grewO
        grewHeap := grewHeap || st.grewHeap
        let more := (if grewO then s.oReaders else []) ++ (if grewHeap then s.heapReaders else [])
        grewO := false
        grewHeap := false
        st := { st with grewO := false, grewHeap := false }
        if more.isEmpty && st.changedVars.isEmpty then break
        for (c, m) in more do
          if !((nodeQ.getD c #[]).getD m true) then
            nodeQ := nodeQ.modify c (·.set! m true)
            nback := (c, m) :: nback
  return (st, copies, runs)

/-- The finite flow of the result. -/
def SolveStart.flow (s : SolveStart P) (st : SolveState P) : FFlow P :=
  let sigs := s.table.map (·.1)
  let O := st.O
  { O := O
    heap := st.heap
    codes := s.cs.toList.zipIdx.map fun (c, ci) =>
      let offs := st.offs.getD ci #[]
      let needs := st.needs.getD ci #[]
      let fns := s.fns.getD ci #[]
      let exprs := ((s.codes[ci]?).map (·.1)).getD #[]
      (c.code, ⟨exprs.mapIdx (fun l e =>
          let off := offs.getD l 0
          let need := needs.getD l 0
          let fn := fns.getD l #[]
          ⟨(List.range need).toArray.map (fun i => st.vars.getD (off + i) []),
            st.vars.getD (off + need) [], st.vars.getD (off + need + 1) [], fn, vfnIx fn e⟩),
        ⟨#[], [], [], #[], none⟩, c.alloc, sigs, st.retOf ci, c.tok⟩) }

/-- **The proposed flow** of `C`'s codes: the signatures, then the sites
until nothing changes or the fuel ends. -/
def solveFlow (cs : List (SolveCode P)) (fuel : Nat) : FFlow P :=
  let s := solveStart cs
  s.flow (solveLoop s fuel s.st).1

end Verification.TolerantFrames.ReadOnly
