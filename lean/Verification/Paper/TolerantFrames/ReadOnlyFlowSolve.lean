import Verification.Paper.TolerantFrames.ReadOnlyFitsDecide
import Std.Data.HashSet

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
- **Sites** (`solveLoop`): each node has slots up to its needed width,
  a default slot and a value. A slot determined by a single incoming
  copy uses its source's variable (`copyClasses`). The worklist carries
  bitset differences along the remaining inclusions. A node's sets are its expression's least set (`gen`, `syn` at
  the current proposal, its stores, what reaches outside code and the
  slots of a callee's entry added as requirements; a known call's value
  its callee's return set; a closure's set its code's token). `O` is held
  where outside code supplies values: the slots a caller of unknown
  callee fills at the entry of each closure's code whose token reaches `O`
  (`OpenAt`), a handler's thrown value; what outside code may supply
  (outside storage and the tokens `O` holds, `Supplied`) at every slot of
  the unit's entry and at the captures' slots of each code whose token
  reaches `O`; at each slot naming a module function's signature its
  code's token, where a closure of the code naming it is held (the unit's
  entry, outside code, a held closure's captures: `closeO`). Each set is what a rule requires of it. `O` is grown
  until closed and its storage holds all of it. A worklist runs the
  copies and the nodes until nothing changes or the fuel ends.
- **Contexts** (`solveStart`, `mergeFlow`): each node holding a known call (a callee slot
  naming a signature of a code of `C`, `knownCallees`) is a call site with
  its own context, and each callee is proposed for once per call site
  naming it, beside its entry context `entryCx`; the node's `FNode.cx`
  names the context its calls enter. Only the entry context is open to
  outside code; a closure's captures are grown at every copy of its code
  (a closure is made once and entered at every context). The proposed
  flow merges the contexts of a code whose entry sets are equal, a call
  site's context the class of its callees' classes (`mergeFlow`); the
  proposal is that merged flow (`SolveStart.propose`, `solveFlow`).

Codes and nodes are arrays, read by index. -/
namespace Verification.TolerantFrames.ReadOnly
open Verification ControlFlow

deriving instance Hashable for Tag, Target, Continuation

variable {P : Package} [DecidableEq P.Site] [Hashable P.Site]

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
  /-- The context this copy of the code is proposed at. -/
  cx : Nat := entryCx
  /-- The sites a frame of a node's continuation and handler allocates
  at. -/
  allocAt : NodeKey → Alloc P := fun _ => alloc
  /-- Whether an execution may start at a call of the code's closure (an
  entry of `C`): every slot of its first node then holds what outside code
  may supply, at its entry context (`EntryShape`). -/
  entry : Bool := false

def SolveCode.sig (c : SolveCode P) : FnSig := ⟨c.code, c.ar, c.start, c.rest, c.ncaps⟩

/-- A slot's signature in the rounds: an index into the table of
signatures, compared as a number. -/
abbrev FnIx := Option Nat

/-- **The state of the proposal**: `O`, the heap of sites, the sets of the
inclusion variables, the mapping from each node's slots and value to
those variables, and the sites each variable gained since its last copy. -/
structure SolveState (P : Package) [DecidableEq P.Site] [Hashable P.Site] where
  outside : Nat
  /-- Each bit numbers one site. Bits are assigned on first use. -/
  bits : Std.HashMap (Option P.Site) Nat := {}
  sites : Array (Option P.Site) := #[]
  /-- Explicit stores. Outside sites additionally contain the outside set. -/
  stores : Std.HashMap Nat Nat := {}
  vars : Array Nat
  /-- Slot occurrence to inclusion variable. -/
  classes : Array Nat
  offs : Array (Array Nat)
  needs : Array (Array Nat)
  changedVars : List Nat := []
  /-- Each code's returning nodes' value variables. -/
  rets : Array (List Nat) := #[]
  /-- Each code's token. -/
  toks : Array (Option P.Site) := #[]
  /-- The sites each variable gained since it was last copied. -/
  delta : Array Nat := #[]
  grewO : Bool := false
  grewHeap : Bool := false

namespace SolveState
variable (st : SolveState P)

/-- Give a site a bit on first use. -/
def siteBit (s : Option P.Site) : StateM (SolveState P) Nat := do
  let st ← get
  if let some b := st.bits[s]? then return b
  let b := 1 <<< st.sites.size
  set { st with bits := st.bits.insert s b, sites := st.sites.push s }
  return b

/-- Fold over the set bits, from the highest down. -/
@[specialize] def foldBits {α : Type} (mask : Nat) (init : α) (f : α → Nat → α) : α := Id.run do
  let mut left := mask
  let mut acc := init
  while left != 0 do
    let b := 1 <<< left.log2
    acc := f acc b
    left := left ^^^ b
  return acc

def view (mask : Nat) : Sites P :=
  foldBits mask [] fun acc b => st.sites[b.log2]! :: acc

def toOutside (mask : Nat) : SolveState P :=
  let next := st.outside ||| mask
  if next == st.outside then st else { st with outside := next, grewO := true, grewHeap := true }

def toO (sites : Sites P) : SolveState P :=
  sites.foldl (fun acc s =>
    let (bit, next) := (siteBit s).run acc
    next.toOutside bit) st

/-- A write to any outside site adds its value to the common outside set.
Only local receivers need individual heap entries. -/
def storeMask (targets value : Nat) : SolveState P :=
  if value == 0 then st else
  let external := targets &&& st.outside
  let localTargets := targets ^^^ external
  let st := if external == 0 then st else st.toOutside value
  foldBits localTargets st fun acc bit =>
    let old := acc.stores.getD bit 0
    let next := old ||| value
    if old == next then acc else { acc with stores := acc.stores.insert bit next, grewHeap := true }

/-- All sites in the outside set have exactly that set as their contents
at the fixed point. Their earlier explicit stores are absorbed by closeO. -/
def readMask (mask : Nat) : Nat :=
  let external := mask &&& st.outside
  foldBits (mask ^^^ external) (if external == 0 then 0 else st.outside)
    fun acc b => acc ||| st.stores.getD b 0

/-- The contents reachable by at least one heap edge. -/
def reachableContents (mask : Nat) : Nat := Id.run do
  let mut frontier := st.readMask mask
  let mut seen := frontier
  while frontier != 0 do
    let next := st.readMask frontier
    frontier := (next ||| seen) ^^^ seen
    seen := seen ||| next
  return seen

def varMask (v : Nat) : Nat := st.vars.getD (st.classes.getD v 0) 0

def growMask (v mask : Nat) : SolveState P := Id.run do
  let old := st.vars.getD v 0
  let next := old ||| mask
  if old == next then return st
  let vars := st.vars
  let delta := st.delta
  let st := { st with vars := #[], delta := #[] }
  return { st with
    vars := vars.set! v next, delta := delta.modify v (· ||| (next ^^^ old)),
    changedVars := v :: st.changedVars }

def grow (v mask : Nat) : SolveState P := st.growMask (st.classes.getD v 0) mask

/-- The variable of slot `i` of node `l` of code `ci`: the slot's, or the
one past the slots kept apart. -/
def slotVar (ci l i : Nat) : Option Nat :=
  ((st.offs[ci]?).bind (·[l]?)).map fun o => o + min i ((st.needs.getD ci #[]).getD l 0)

/-- The return set of code `ci`: its returning nodes' values. -/
def retOf (ci : Nat) : Nat :=
  (st.rets.getD ci []).foldl (fun acc v => acc ||| st.varMask v) 0

/-- Grow the slot `i` of node `l` of code `ci` by `S`. -/
def slot (ci l i : Nat) (S : Nat) : SolveState P :=
  match st.slotVar ci l i with
  | some v => st.grow v S
  | none => st

end SolveState

section gen
variable (table : Array (FnSig × Option Nat)) (τ : Nat → Nat) (φ : Nat → FnIx) (a : Alloc P)
  (inst : Nat → Option Nat) (allCx : Nat → List Nat)

/-- **A term's sets, proposed** (`syn` at the current proposal): its stores
added to the heap of sites, what reaches outside code added to `O`, the
slots of a callee's entry grown. `table` gives each signature and the
index of its code among `C`'s; `inst` the copy of a callee code the node's
context enters, `allCx` every copy of a code. -/
partial def gen (d : Nat) (Γ : Nat → Nat) (e : Tm) : StateM (SolveState P) Nat := do
  match e with
  | .var i => return if i < d then Γ i else τ (i - d)
  | .invoke f r args =>
    let Sf ← gen d Γ f
    let Sr ← gen d Γ r
    let Ls ← args.mapM (gen d Γ)
    let viaC : Option (Nat × FnSig) := match f with
      | .var j => if d ≤ j ∧ args.all partB then
          (φ (j - d)).bind fun t => (table[t]?).bind fun (σ, ci) => (ci.bind inst).map (·, σ)
        else none
      | _ => none
    match viaC with
    | some (ci, σ) =>
      modify fun st => st.slot ci σ.s (capSlot σ.ar σ.rest σ.ncaps) (τ (j' f d))
      modify fun st => st.slot ci σ.s (recvSlot σ.rest) Sr
      for i in List.range σ.ar do
        modify fun st => st.slot ci σ.s (paramSlot σ.rest i) (Ls.getD i 0)
      if σ.rest then
        let arr ← SolveState.siteBit a.arr
        modify fun st => st.slot ci σ.s 0 arr
        modify fun st => st.storeMask arr ((Ls.drop σ.ar).foldl (· ||| ·) 0)
      return (← get).retOf ci
    | none =>
      let arr ← SolveState.siteBit a.arr
      modify fun st => st.toOutside (Ls.foldl (· ||| ·) (Sf ||| Sr ||| arr))
      return (← get).outside
  | .construct f args =>
    let arr ← SolveState.siteBit a.arr
    let Sf ← gen d Γ f
    let Ls ← args.mapM (gen d Γ)
    modify fun st => st.toOutside (Ls.foldl (· ||| ·) (Sf ||| arr))
    return (← get).outside
  | .letE x b =>
    let Sx ← gen d Γ x
    gen (d + 1) (fun i => match i with | 0 => Sx | i + 1 => Γ i) b
  | .spread x => let Sx ← gen d Γ x; return (← get).readMask Sx
  | .makeAt .absent _ inits =>
    let obj ← SolveState.siteBit a.obj
    for x in inits do
      let S ← gen d Γ x
      modify fun st => st.storeMask obj S
    return obj
  | .makeAt (.bound t r pre) _ inits =>
    let obj ← SolveState.siteBit a.obj
    for x in inits do
      let S ← gen d Γ x
      modify fun st => st.storeMask obj S
    return obj ||| ((t :: r :: pre).foldl (fun acc u => acc ||| part u) 0)
  | .makeAt (.graph ar E K s caps _ rest comp) _ inits =>
    let obj ← SolveState.siteBit a.obj
    for x in inits do
      let S ← gen d Γ x
      modify fun st => st.storeMask obj S
    if P.ofC comp then
      match (table.find? fun e => e.2.isSome && e.1.code == (E, K)).bind (·.2) with
      | some ci =>
        for cj in allCx ci do
          for i in List.range caps.length do
            match caps[i]? with
            | some u => modify fun st => st.slot cj s (capSlot ar rest i) (part u)
            | none => pure ()
        return obj ||| (← SolveState.siteBit ((← get).toks.getD ci none))
      | none => return obj
    else return obj ||| (caps.foldl (fun acc u => acc ||| part u) 0)
  | .readAt _ x | .indexAt x _ =>
    let Sx ← gen d Γ x
    match e with
    | .indexAt _ k => let _ ← gen d Γ k
    | _ => pure ()
    let st ← get
    return st.reachableContents Sx
  | .writeAt _ x y =>
    let Sx ← gen d Γ x
    let Sy ← gen d Γ y
    modify fun st => st.storeMask Sx Sy
    return 0
  | .test _ x | .lenOf x => let _ ← gen d Γ x; return 0
  | .ite c x y =>
    let _ ← gen d Γ c
    return (← gen d Γ x) ||| (← gen d Γ y)
  | .arith _ x y => let _ ← gen d Γ x; let _ ← gen d Γ y; return 0
  | .arrLit inits =>
    let arr ← SolveState.siteBit a.arr
    for x in inits do
      let S ← gen d Γ x
      modify fun st => st.storeMask arr S
    return arr
  | .elemAt x i =>
    let Sx ← gen d Γ x
    let _ ← gen d Γ i
    return (← get).readMask Sx
  | .setElem x i v =>
    let arr ← SolveState.siteBit a.arr
    let Sx ← gen d Γ x
    let _ ← gen d Γ i
    let Sv ← gen d Γ v
    modify fun st => st.storeMask (arr ||| Sx) Sv
    return arr ||| Sx
  | .throw x =>
    let Sx ← gen d Γ x
    modify fun st => st.toOutside Sx
    return 0
  | .merge _ x y =>
    let obj ← SolveState.siteBit a.obj
    let Sx ← gen d Γ x
    let Sy ← gen d Γ y
    let st₀ ← get
    let values := st₀.reachableContents (Sx ||| Sy)
    modify fun st => st.storeMask obj values
    return obj
  | .makeKey k x =>
    let obj ← SolveState.siteBit a.obj
    let _ ← gen d Γ k
    let Sx ← gen d Γ x
    modify fun st => st.storeMask obj Sx
    return obj
  | _ => return 0
where
  part : Tm → Nat
    | .var i => if i < d then Γ i else τ (i - d)
    | _ => 0
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
(`oVars`), the slots a caller of unknown callee fills at the entry of each
closure's code whose token lies in `O` (`entryVars`, `OpenAt`); the
returns of each code whose token lies in `O`, at its entry context; and
what outside code may supply (outside storage and the tokens `O` holds,
`Supplied`) at the unit's entry slots (`noneVars`) and at the capture
slots of each such code, at each of its contexts. A slot naming a module
function's signature at a code's entry holds that function's token where
a closure of the code is held (`tokVars`): the unit's entry holds its
captures' closures, outside code those of each code whose token lies in
`O`, and each held closure its captures' closures. -/
def closeO (oVars : List Nat) (entryVars : List (Option P.Site × List Nat × List Nat)) (noneVars : List Nat)
    (entries : Array Bool) (units : List Nat) (nb : Nat) (tokVars : List (Nat × Nat × Nat × Option P.Site))
    (st : SolveState P) : SolveState P := Id.run do
  let stored := SolveState.foldBits st.outside st.outside fun acc b => acc ||| st.stores.getD b 0
  let mut st := st.toOutside stored
  for v in oVars do
    st := st.grow v st.outside
  let supplied := st.toks.foldl (fun mask t => mask ||| (st.bits.getD t 0 &&& st.outside)) (st.bits.getD none 0)
  for (t, vs, ws) in entryVars do
    if st.bits.getD t 0 &&& st.outside != 0 then
      for v in vs do
        st := st.grow v st.outside
      for w in ws do
        st := st.grow w supplied
  -- the returns of each code whose token lies in `O`, at its entry context
  for ((rs, t), e) in (st.rets.toList.zip st.toks.toList).zip entries.toList do
    if e && st.bits.getD t 0 &&& st.outside != 0 then
      for v in rs do
        st := st.toOutside (st.varMask v)
  -- the unit's entry slots: what outside code may supply
  for v in noneVars do
    st := st.grow v supplied
  -- the closures of the module's codes held: the unit's entry's, those of
  -- each code whose token lies in `O`, and those a held closure captures
  let mut held : List Nat := units ++ (List.range nb).filter fun b =>
    match st.toks.getD b none with
    | some t => st.bits.getD (some t) 0 &&& st.outside != 0
    | none => false
  for _ in [0:tokVars.length + 1] do
    let new := ((tokVars.filter fun (h, _, cj, _) => h ∈ held && cj ∉ held).map (·.2.2.1)).eraseDups
    if new.isEmpty then break
    held := held ++ new
  for (h, v, _, t) in tokVars do
    if h ∈ held then
      let (b, next) := (SolveState.siteBit t).run st
      st := next.grow v b
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
the edges, each variable's readers, and the nodes reading the heap of sites
or `O`. -/
structure SolveStart (P : Package) [DecidableEq P.Site] [Hashable P.Site] where
  /-- The codes' copies: each code at its entry context, at its index among
  the codes, then each at the context of each call site naming it. -/
  cs : Array (SolveCode P)
  /-- Each code's index among the codes, of each copy. -/
  base : Array Nat
  /-- Each code's copies: their contexts and indices. -/
  ctxOf : Array (List (Nat × Nat))
  /-- Each code's nodes' contexts. -/
  nodeCx : Array (Array Nat)
  codes : Array (Array Tm × Array (Continuation × Option Target))
  table : Array (FnSig × Option Nat)
  fns : Array (Array (Array FnIx))
  /-- The variables each variable is copied into. -/
  succ : Array (List Nat)
  /-- Nodes whose expression may read each inclusion variable. -/
  readerOf : Array (List (Nat × Nat))
  heapReaders : List (Nat × Nat)
  oReaders : List (Nat × Nat)
  /-- The variables outside code fills: the value a handler binds. -/
  oVars : List Nat
  /-- The entry slots of each closure's code, with its token: those a caller
  of unknown callee fills, at its entry context, and its captures' slots. -/
  entryVars : List (Option P.Site × List Nat × List Nat)
  /-- The slots of the unit's entry. -/
  noneVars : List Nat
  /-- The codes entered as a unit, not as a closure, and the number of
  codes before their copies. -/
  units : List Nat
  nb : Nat
  /-- Each slot naming a module function's signature at a code's entry:
  the code, the slot's variable, the function's code and token. -/
  tokVars : List (Nat × Nat × Nat × Option P.Site)
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

/-- **The codes a term's known calls enter** (`gen`'s known calls): the
index among `C`'s codes of each callee a slot naming a signature gives. -/
partial def knownCallees (table : Array (FnSig × Option Nat)) (φ : Nat → FnIx) (d : Nat) : Tm → List Nat
  | .invoke f r args =>
    (match f with
      | .var j => if d ≤ j ∧ args.all partB then
          ((φ (j - d)).bind fun t => (table[t]?).bind (·.2)).toList
        else []
      | _ => []) ++ knownCallees table φ d f ++ knownCallees table φ d r ++ args.flatMap (knownCallees table φ d)
  | .letE x b => knownCallees table φ d x ++ knownCallees table φ (d + 1) b
  | .construct f args => knownCallees table φ d f ++ args.flatMap (knownCallees table φ d)
  | .makeAt _ _ inits | .arrLit inits => inits.flatMap (knownCallees table φ d)
  | .indexAt a b | .writeAt _ a b | .arith _ a b | .elemAt a b | .merge _ a b | .makeKey a b =>
    knownCallees table φ d a ++ knownCallees table φ d b
  | .ite a b c | .setElem a b c => knownCallees table φ d a ++ knownCallees table φ d b ++ knownCallees table φ d c
  | .readAt _ a | .test _ a | .lenOf a | .spread a | .throw a => knownCallees table φ d a
  | _ => []

/-- **Whether a term may call outside code** at slots of the sets `τ`: a
call that is no known call (`gen`'s known calls), or a `new`, whose
callee's set may hold outside storage, the token of the closures of
outside code; a callee that is no slot may. -/
partial def callsOut (table : Array (FnSig × Option Nat)) (φ : Nat → FnIx) (τ : Nat → Sites P)
    (inst : Nat → Option Nat) (d : Nat) : Tm → Bool
  | .invoke f r args =>
    let known : Bool := match f with
      | .var j => d ≤ j && args.all partB &&
          ((φ (j - d)).bind fun t => (table[t]?).bind fun (_, ci) => ci.bind inst).isSome
      | _ => false
    (!known && calleeOut f) || callsOut table φ τ inst d f || callsOut table φ τ inst d r ||
      args.any (callsOut table φ τ inst d)
  | .construct f args => calleeOut f || callsOut table φ τ inst d f || args.any (callsOut table φ τ inst d)
  | .letE x b => callsOut table φ τ inst d x || callsOut table φ τ inst (d + 1) b
  | .makeAt _ _ inits | .arrLit inits => inits.any (callsOut table φ τ inst d)
  | .indexAt a b | .writeAt _ a b | .arith _ a b | .elemAt a b | .merge _ a b | .makeKey a b =>
    callsOut table φ τ inst d a || callsOut table φ τ inst d b
  | .ite a b c | .setElem a b c =>
    callsOut table φ τ inst d a || callsOut table φ τ inst d b || callsOut table φ τ inst d c
  | .readAt _ a | .test _ a | .lenOf a | .spread a | .throw a => callsOut table φ τ inst d a
  | _ => false
where
  /-- A callee whose set may hold outside storage. -/
  calleeOut (f : Tm) : Bool := match f with
    | .var j => if d ≤ j then (τ (j - d)).contains none else true
    | _ => true

/-- The closures of the component's code a term creates, with their entry
layouts. -/
partial def closureLayouts (ofC : ComponentTag → Bool) : Tm → List (Code × Nat × Bool × Nat × Nat)
  | .makeAt (.graph ar E K s caps _ rest comp) _ inits =>
    (if ofC comp then [((E, K), ar, rest, caps.length, s)] else []) ++ E.flatMap (closureLayouts ofC) ++
      inits.flatMap (closureLayouts ofC)
  | .invoke f r args => closureLayouts ofC f ++ closureLayouts ofC r ++ args.flatMap (closureLayouts ofC)
  | .construct f args => closureLayouts ofC f ++ args.flatMap (closureLayouts ofC)
  | .makeAt _ _ inits | .arrLit inits => inits.flatMap (closureLayouts ofC)
  | .letE a b | .indexAt a b | .writeAt _ a b | .arith _ a b | .elemAt a b | .merge _ a b | .makeKey a b =>
    closureLayouts ofC a ++ closureLayouts ofC b
  | .ite a b c | .setElem a b c => closureLayouts ofC a ++ closureLayouts ofC b ++ closureLayouts ofC c
  | .readAt _ a | .test _ a | .lenOf a | .spread a | .throw a => closureLayouts ofC a
  | _ => []

/-- The variable for each slot occurrence. A slot with one incoming
copy and no other source has its source's least solution. Follow these
copies to their source; an unseeded cycle has the empty least solution.
`pred[v] = n` denotes no source, and `pred[v] = v` an independent
variable (an entry, a generated value, or a join). -/
private def copyClasses (pred : Array Nat) : Array Nat × Nat := Id.run do
  let n := pred.size
  let mut ids := Array.replicate n (n + 1)
  let mut count := 1  -- class zero has no source
  for v in [0:n] do
    if ids[v]! ≤ n then continue
    let mut atVar := v
    let mut path := []
    let mut id := 0
    for _ in [0:n + 1] do
      if atVar == n then break
      let seen := ids[atVar]!
      if seen ≤ n then
        id := seen
        break
      if seen == n + 2 then break
      let p := pred[atVar]!
      path := atVar :: path
      if p == atVar then
        id := count
        count := count + 1
        break
      ids := ids.set! atVar (n + 2)
      atVar := p
    for w in path do ids := ids.set! w id
  return (ids, count)

def solveStart (cs : List (SolveCode P)) : SolveStart P := Id.run do
  let bases := cs.toArray
  let table := sigTable bases
  let ix (σ? : Option FnSig) : FnIx := σ?.bind fun σ => table.findIdx? (·.1 == σ)
  let baseCodes := bases.map fun c => (c.code.1.toArray, c.code.2.toArray)
  let baseFns : Array (Array (Array FnIx)) := bases.mapIdx fun ci c =>
    let (exprs, conts) := baseCodes.getD ci (#[], #[])
    let self := capSlot c.ar c.rest c.ncaps
    let seed : Array FnIx := (List.range (max c.seeds.length (if c.closure then self + 1 else 0))).toArray.map fun i =>
      if c.closure && i = self then some ci else ix (c.seeds.getD i none)
    fnsOf exprs conts c.start seed
  -- The call sites: each node with a known call, its own context.
  let mut nodeCx : Array (Array Nat) := #[]
  let mut ctxOf : Array (List (Nat × Nat)) := bases.mapIdx fun ci _ => [(entryCx, ci)]
  let mut copies : Array (SolveCode P) := bases
  let mut base : Array Nat := bases.mapIdx fun ci _ => ci
  let mut next := entryCx + 1
  for ci in [0:bases.size] do
    let (exprs, _) := baseCodes.getD ci (#[], #[])
    let fnRows := baseFns.getD ci #[]
    let mut row : Array Nat := #[]
    for l in [0:exprs.size] do
      let fn := fnRows.getD l #[]
      let callees := (knownCallees table (fun i => fn.getD i none) 0 (exprs.getD l .undef)).eraseDups
      if callees.isEmpty then
        row := row.push entryCx
      else
        let k := next
        next := next + 1
        row := row.push k
        for cj in callees do
          if !((ctxOf.getD cj []).any (·.1 == k)) then
            if let some c := bases[cj]? then
              ctxOf := ctxOf.modify cj ((k, copies.size) :: ·)
              copies := copies.push { c with cx := k }
              base := base.push cj
    nodeCx := nodeCx.push row
  let csA := copies
  let codes := base.map fun b => baseCodes.getD b (#[], #[])
  let fns := base.map fun b => baseFns.getD b #[]
  let needs : Array (Array Nat) := csA.mapIdx fun ci c =>
    let (exprs, conts) := codes.getD ci (#[], #[])
    neededWidths exprs conts c.start (max c.seeds.length (capSlot c.ar c.rest c.ncaps + 1))
  -- Number the slot occurrences, including each node's default slot and value.
  let mut offs : Array (Array Nat) := #[]
  let mut n := 0
  for row in needs do
    let mut o : Array Nat := #[]
    for w in row do
      o := o.push n
      n := n + w + 2
    offs := offs.push o
  let mut pred := Array.replicate n n
  let mut joins : List (Nat × Nat) := []
  -- A closure creation can fill captures at the entry its term names.
  let captures := bases.toList.flatMap fun c => c.code.1.flatMap (closureLayouts P.ofC)
  let captureEntries := bases.map fun c =>
    (captures.filter fun d => d.1 == c.code).map fun (_, _, _, _, start) => start
  let mut oVars : List Nat := []
  let mut entryVars : List (Option P.Site × List Nat × List Nat) := []
  let mut tokVars : List (Nat × Nat × Nat × Option P.Site) := []
  let mut noneVars : List Nat := []
  let mut rets : Array (List Nat) := #[]
  for (c, ci) in csA.toList.zipIdx do
    let (_, conts) := codes.getD ci (#[], #[])
    let o := offs.getD ci #[]
    let nd := needs.getD ci #[]
    -- The entry's slots: every slot a caller of unknown callee fills at a
    -- closure's entry holds `O`, at its entry context; every capture's
    -- slot what outside code may supply, at every context; every slot of
    -- the unit's entry outside storage.
    let so := o.getD c.start 0
    let sn := nd.getD c.start 0
    if c.closure then
      let filled := if c.cx == entryCx then
          List.range (capSlot c.ar c.rest 0) ++ [capSlot c.ar c.rest c.ncaps]
        else []
      let caps := (List.range c.ncaps).map (capSlot c.ar c.rest ·)
      entryVars := (c.tok, filled.map (so + min · sn), caps.map (so + min · sn)) :: entryVars
    if c.cx == entryCx && (!c.closure || c.entry) then
      for i in List.range (sn + 1) do
        noneVars := (so + i) :: noneVars
    -- A slot naming a code's signature at the entry holds its token where
    -- a closure of the code is held (`closeO`).
    for (sd, i) in c.seeds.zipIdx do
      match sd.bind (fun σ => (table.find? (·.1 == σ)).bind (·.2)) with
      | some cj => tokVars := (base.getD ci ci, so + min i sn, cj, (csA[cj]?).bind (·.tok)) :: tokVars
      | none => pure ()
    let mut rs : List Nat := []
    for l in [0:conts.size] do
      let off := o.getD l 0
      let val := off + nd.getD l 0 + 1
      let first := if l == c.start || (captureEntries.getD (base.getD ci ci) []).contains l then off else val
      for w in [first:val + 1] do
        let prev := pred.getD w n
        if prev != n && prev != w then joins := (prev, w) :: joins
        pred := pred.set! w w
      let some (k, x) := conts[l]? | continue
      if (match k with | .ret => true | _ => false) then rs := (o.getD l 0 + nd.getD l 0 + 1) :: rs
      oVars := handlerVars o nd l x ++ oVars
      for (v, w) in edgeCopies o nd l k x do
        if v == w then continue
        let prev := pred.getD w n
        if prev == n then pred := pred.set! w v
        else if prev != v then
          if prev != w then
            joins := (prev, w) :: joins
            pred := pred.set! w w
          joins := (v, w) :: joins
    rets := rets.push rs
  for w in oVars do
    let prev := pred.getD w n
    if prev != n && prev != w then joins := (prev, w) :: joins
    pred := pred.set! w w
  let (classes, count) := copyClasses pred
  let mut succ : Array (List Nat) := Array.replicate count []
  for (v, w) in joins do
    let src := classes.getD v 0
    let dst := classes.getD w 0
    if src != dst then succ := succ.modify src (dst :: ·)
  succ := succ.map fun ws => (Std.HashSet.ofList ws).toList
  let mut readerOf : Array (List (Nat × Nat)) := Array.replicate count []
  for ((exprs, _), ci) in codes.toList.zipIdx do
    let offsets := offs.getD ci #[]
    for (e, l) in exprs.toList.zipIdx do
      let off := offsets.getD l 0
      for i in [0:maxVar e] do
        let id := classes.getD (off + i) 0
        if id != 0 then readerOf := readerOf.modify id fun ns =>
          if ns.head? == some (ci, l) then ns else (ci, l) :: ns
  let readers (p : Tm → Bool) : List (Nat × Nat) :=
    (codes.toList.zipIdx.flatMap fun ((exprs, _), ci) =>
      (exprs.toList.zipIdx.filter fun (e, _) => p e).map fun (_, l) => (ci, l))
  let st0 : SolveState P :=
    { outside := 1, sites := #[none], bits := ({} : Std.HashMap _ _).insert none 1,
      vars := Array.replicate count 0, delta := Array.replicate count 0, classes,
      offs, needs, rets, toks := csA.map (·.tok) }
  let st0 := (noneVars ++ oVars).foldl (fun st v => st.grow v 1) st0
  let st0 := st0.toO ((cs.filter (·.entry)).map (·.tok))
  let units := (List.range bases.size).filter fun b => !((bases[b]?).map (·.closure)).getD true
  return ⟨csA, base, ctxOf, nodeCx, codes, table, fns, succ, readerOf, readers readsHeap, readers readsO, oVars,
    entryVars, noneVars, units, bases.size, tokVars, st0⟩

/-- **A node's sets**: its expression's least set at its slots (`gen`), its
value grown by it; a returned value given to `O` where the unit returns it
or the code's token lies in `O` (a closure outside code may call), and its
callers, which read the code's return set, run again (through `grewO`). -/
def siteNode (s : SolveStart P) (st : SolveState P) (ci l : Nat) : SolveState P := Id.run do
  let some c := s.cs[ci]? | return st
  let some (exprs, conts) := s.codes[ci]? | return st
  let some e := exprs[l]? | return st
  let some (k, x) := conts[l]? | return st
  let off := (st.offs.getD ci #[]).getD l 0
  let need := (st.needs.getD ci #[]).getD l 0
  -- (the node's slots read once, so that the state's array is not shared
  -- while the node's term grows it)
  let slots : Array Nat := (Array.range (maxVar e)).map fun i => st.varMask (off + i)
  let τ := fun i => slots.getD (min i need) 0
  let fn := (s.fns.getD ci #[]).getD l #[]
  let κ := (s.nodeCx.getD (s.base.getD ci ci) #[]).getD l entryCx
  let inst (cj : Nat) : Option Nat := ((s.ctxOf.getD cj []).find? (·.1 == κ)).map (·.2)
  let allCx (cj : Nat) : List Nat := (s.ctxOf.getD cj []).map (·.2)
  let a := c.allocAt (k, x)
  let (S, st') := (gen s.table τ (fun i => fn.getD i none) a inst allCx 0 (fun _ => 0) e).run st
  let val := st'.classes.getD (off + need + 1) 0
  let before := st'.vars.getD val 0
  let mut st := st'.grow (off + need + 1) S
  if (match k with | .ret => true | _ => false) then
    -- (a returned value reaches outside code where the unit returns it, or
    -- a closure outside code may call; `closeO` gives the rest)
    if c.cx == entryCx && (!c.closure || st.bits.getD c.tok 0 &&& st.outside != 0) then st := st.toOutside (st.varMask (off + need + 1))
    if st.vars.getD val 0 != before then st := { st with grewO := true }
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
      for (c, m) in s.readerOf.getD v [] do
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
      let S := st.delta.getD v 0
      let delta := st.delta
      st := { st with delta := #[] }
      st := { st with delta := delta.set! v 0 }
      for w in s.succ.getD v [] do
        st := st.growMask w S
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
        st := closeO s.oVars s.entryVars s.noneVars (s.cs.map (·.cx == entryCx)) s.units s.nb s.tokVars st
        let needsClosure := st.grewO
        grewO := grewO || st.grewO
        grewHeap := grewHeap || st.grewHeap
        let more := (if grewO then s.oReaders else []) ++ (if grewHeap then s.heapReaders else [])
        grewO := false
        grewHeap := false
        st := { st with grewO := false, grewHeap := false }
        if !needsClosure && more.isEmpty && st.changedVars.isEmpty then break
        for (c, m) in more do
          if !((nodeQ.getD c #[]).getD m true) then
            nodeQ := nodeQ.modify c (·.set! m true)
            nback := (c, m) :: nback
  return (st, copies, runs)

/-- The finite flow of the result. -/
def SolveStart.flow (s : SolveStart P) (st : SolveState P) : FFlow P :=
  let sigs := s.table.map (·.1)
  let masks := st.vars.foldl (fun (m : Std.HashSet Nat) v => m.insert v) {}
  let views := masks.fold (fun (m : Std.HashMap Nat (Sites P)) v => m.insert v (st.view v)) {}
  let view (v : Nat) := match views[v]? with | some l => l | none => st.view v
  let O := view st.outside
  let shared := Std.HashSet.ofList O
  -- each code's allocation sites per continuation and handler, read once
  -- per code: its entry copy's, which every context shares
  let allocsOf : Array (List (NodeKey × Option P.Site × Option P.Site)) := s.ctxOf.mapIdx fun b _ =>
    match s.cs[b]?, s.codes[b]? with
    | some c₀, some code =>
      let keys := code.2.foldl (fun (seen, acc) kx => if seen.contains kx then (seen, acc) else (seen.insert kx, kx :: acc))
        ((∅ : Std.HashSet NodeKey), ([] : List NodeKey))
      keys.2.reverse.map fun kx => (kx, (c₀.allocAt kx).obj, (c₀.allocAt kx).arr)
    | _, _ => []
  { O := O
    outsideRow := shared.contains
    heap := st.sites.toList.zipIdx.filterMap fun (site, i) =>
      let contents := st.readMask (1 <<< i)
      if contents == 0 || shared.contains site then none else some (site, view contents)
    codes := s.ctxOf.toList.zipIdx.filterMap fun (cxs, b) => (s.cs[b]?).map fun c₀ =>
      (c₀.code, cxs.reverse.map fun (k, ci) =>
      let c := (s.cs[ci]?).getD c₀
      let offs := st.offs.getD ci #[]
      let needs := st.needs.getD ci #[]
      let fns := s.fns.getD ci #[]
      let cxs := s.nodeCx.getD b #[]
      let exprs := ((s.codes[ci]?).map (·.1)).getD #[]
      (k, (⟨exprs.mapIdx (fun l e =>
          let off := offs.getD l 0
          let need := needs.getD l 0
          let fn := fns.getD l #[]
          let env := (Array.range need).map (fun i => view (st.varMask (off + i)))
          let dflt := view (st.varMask (off + need))
          let κ := cxs.getD l entryCx
          let inst (cj : Nat) : Option Nat := ((s.ctxOf.getD cj []).find? (·.1 == κ)).map (·.2)
          ⟨env, dflt, view (st.varMask (off + need + 1)), fn, vfnIx fn e, κ,
            callsOut s.table (fun i => fn.getD i none) (fun i => env.getD i dflt) inst 0 e⟩),
        ⟨#[], [], [], #[], none, entryCx, true⟩, c.alloc, sigs, view (st.retOf ci), c.tok,
        allocsOf.getD b []⟩ : FCode P))) }

/-- Two sets of the same sites. -/
def sameSites (S T : Sites P) : Bool := decide (Sub S T) && decide (Sub T S)

/-- **The flow with the contexts of equal entry sets merged**: two contexts
of a code whose entry nodes' slots hold the same sites are one class,
standing for the first of them (the entry context where it is in it); a
call site's context is the class of its call sites whose callees' classes
are its own, standing for the first of them, or the entry context where
every callee's class is its entry context's. The merged flow is the
proposal for each class's first context, made once, and
each node names its call site's class. Nothing here is trusted: `FFlow.check` decides the merged
flow as any other. -/
def SolveStart.mergeFlow (s : SolveStart P) (F : FFlow P) : FFlow P := Id.run do
  let startOf (b : Nat) : Nat := ((s.cs[b]?).map (·.start)).getD 0
  let entrySets (b : Nat) (c : FCode P) : List (Sites P) := (c.node (startOf b)).dflt :: (c.node (startOf b)).env.toList
  let sameEntry (b : Nat) (c c' : FCode P) : Bool :=
    let x := entrySets b c
    let y := entrySets b c'
    x.length == y.length && (x.zip y).all fun (S, T) => sameSites S T
  let ctxs : Array (List (Nat × FCode P)) := F.codes.toArray.map (·.2)
  -- each context's class in its code: the first context of equal entry
  -- sets, computed once per code
  let reps : Array (Std.HashMap Nat Nat) := ctxs.mapIdx fun b cs => Id.run do
    let mut seen : List (Nat × FCode P) := []
    let mut m : Std.HashMap Nat Nat := {}
    for (k, c) in cs do
      if !m.contains k then
        match seen.find? fun (_, c') => sameEntry b c c' with
        | some (k', _) => m := m.insert k k'
        | none => m := m.insert k k; seen := seen ++ [(k, c)]
    return m
  let rep (b k : Nat) : Nat := ((reps[b]?).bind (·[k]?)).getD k
  -- each call site's callees, with their classes
  let sites : List Nat := (ctxs.toList.flatMap fun cs => cs.map (·.1)).eraseDups.filter (· != entryCx)
  let codesOf : Std.HashMap Nat (List Nat) := ctxs.toList.zipIdx.foldl
    (fun m (cs, b) => cs.foldl (fun m (k, _) => m.insert k ((m.getD k []) ++ [b])) m) {}
  let sigOf (k : Nat) : List (Nat × Nat) := (codesOf.getD k []).eraseDups.map fun b => (b, rep b k)
  -- each signature's first call site
  let firstOf : Std.HashMap (List (Nat × Nat)) Nat := sites.foldl
    (fun m k => let sg := sigOf k; if m.contains sg then m else m.insert sg k) {}
  let newKey : Nat → Nat := fun k =>
    let sg := sigOf k
    if sg.all (·.2 == entryCx) then entryCx
    else firstOf.getD sg k
  let keys : List (Nat × Nat) := sites.map fun k => (k, newKey k)
  let remap (k : Nat) : Nat := if k == entryCx then entryCx else (look k keys).getD k
  let node (x : FNode P) : FNode P := { x with cx := remap x.cx }
  let code (c : FCode P) : FCode P := { c with nodes := c.nodes.map node, dflt := node c.dflt }
  -- Each representative's nodes name the new call contexts.
  let mut codes : List (Code × List (Nat × FCode P)) := []
  for ((m, cs), b) in F.codes.zipIdx do
    let kept := cs.filter fun (k, _) => k == entryCx || (newKey k != entryCx && newKey k == k)
    let mut made : Std.HashMap Nat (FCode P) := {}
    let mut out : List (Nat × FCode P) := []
    for (k, c) in kept do
      let k₀ := if k == entryCx then k else rep b k
      match made[k₀]? with
      | some fc => out := (k, fc) :: out
      | none =>
        let fc := code ((look k₀ cs).getD c)
        made := made.insert k₀ fc
        out := (k, fc) :: out
    codes := (m, out.reverse) :: codes
  return { F with codes := codes.reverse }

/-- **The proposal at a state of the rounds**: its flow, the contexts of
equal entry sets merged and equal sets shared (`mergeFlow`). -/
def SolveStart.propose (s : SolveStart P) (st : SolveState P) : FFlow P := s.mergeFlow (s.flow st)

/-- **The proposed flow** of `C`'s codes: one context per known call site,
the signatures, then the sites until nothing changes or the fuel ends,
then the contexts of equal entry sets merged (`SolveStart.propose`). -/
def solveFlow (cs : List (SolveCode P)) (fuel : Nat) : FFlow P :=
  let s := solveStart cs
  s.propose (solveLoop s fuel s.st).1

end Verification.TolerantFrames.ReadOnly
