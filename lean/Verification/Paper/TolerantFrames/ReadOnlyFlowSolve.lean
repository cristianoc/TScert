import Verification.Paper.TolerantFrames.ReadOnlyFitsDecide

/-! # Read-only handles: proposing the flow of a component's codes

The draft "Read-only handles" (`docs/drafts/readonly-handles.md`, "Deciding
the flow"). The proposal `FFlow.check` decides is computed here from the
lowered graphs of `C`'s codes: nothing here is trusted, and nothing is
proved of it; a proposal it gives is accepted only where `FFlow.check`
holds of it.

- **Signatures** (`fnRound`): a slot names a signature where every edge
  into its node carries a slot naming it, from the entry's named slots and
  the closure's own slot.
- **Sites** (`siteRound`): the least sets of each node expression
  (`gen`, `syn` at the current proposal, its stores and the slots of a
  callee's entry added as requirements), carried along each edge, `O`
  grown until closed, its storage holding all of it and every slot
  accepting it; iterated until nothing changes or the fuel ends. -/
namespace Verification.TolerantFrames.ReadOnly
open Verification ControlFlow

variable {P : Package} [DecidableEq P.Site]

/-- **A code of `C` to propose for**: its graph, the layout of its entry,
the signatures its entry names, and the sites its frames allocate at. -/
structure SolveCode (P : Package) where
  code : Code
  ar : Nat
  rest : Bool
  ncaps : Nat
  start : Nat
  seeds : List (Option FnSig)
  alloc : Alloc P

def SolveCode.sig (c : SolveCode P) : FnSig := ⟨c.code, c.ar, c.start, c.rest, c.ncaps⟩

/-- The union of two sets. -/
def union (S T : Sites P) : Sites P := S ++ T.filter (· ∉ S)

/-- **The state of the proposal**: `O`, the heap of sites, and each code's
nodes. -/
structure SolveState (P : Package) where
  O : Sites P
  heap : List (Option P.Site × Sites P × Sites P)
  nodes : List (List (FNode P))
  changed : Bool

namespace SolveState
variable (st : SolveState P)

def toFlow (cs : List (SolveCode P)) : FFlow P where
  O := st.O
  heap := st.heap
  codes := (cs.zip st.nodes).map fun (c, ns) => (c.code, ⟨ns, ⟨[], st.O, [], [], none⟩, c.alloc⟩)

/-- Add sites to `O`. -/
def toO (S : Sites P) : SolveState P :=
  let O' := union st.O S
  if O'.length = st.O.length then st else { st with O := O', changed := true }

/-- Add sites to the contents and bindings of a site's storage. -/
def store (s : Option P.Site) (S : Sites P) : SolveState P :=
  match look s st.heap with
  | none => if S.isEmpty then st else { st with heap := (s, S, S) :: st.heap, changed := true }
  | some (c, b) =>
    let c' := union c S
    let b' := union b S
    if c'.length = c.length ∧ b'.length = b.length then st
    else { st with heap := st.heap.map (fun e => if e.1 = s then (s, c', b') else e), changed := true }

/-- Grow a node's slot `i` by `S`. -/
def growSlot (x : FNode P) (i : Nat) (S : Sites P) : FNode P × Bool :=
  let env := if i < x.env.length then x.env else x.env ++ List.replicate (i + 1 - x.env.length) x.dflt
  let old := env.getD i []
  let new := union old S
  if new.length = old.length then (x, false) else ({ x with env := env.set i new }, true)

/-- Grow the slot `i` of node `l` of code `ci` by `S`. -/
def slot (ci l i : Nat) (S : Sites P) : SolveState P :=
  match st.nodes[ci]? with
  | none => st
  | some ns => match ns[l]? with
    | none => st
    | some x =>
      let (x', ch) := growSlot x i S
      if ch then { st with nodes := st.nodes.set ci (ns.set l x'), changed := true } else st

/-- Grow every slot of node `l` of code `ci` past the width `n` by `S`. -/
def dfltGrow (ci l n : Nat) (S : Sites P) : SolveState P :=
  match st.nodes[ci]? with
  | none => st
  | some ns => match ns[l]? with
    | none => st
    | some x =>
      let env := if n ≤ x.env.length then x.env else x.env ++ List.replicate (n - x.env.length) x.dflt
      let d' := union x.dflt S
      let env' := env.mapIdx fun i T => if n ≤ i then union T S else T
      if d'.length = x.dflt.length ∧ env'.map List.length = env.map List.length then st
      else { st with nodes := st.nodes.set ci (ns.set l { x with env := env', dflt := d' }), changed := true }

/-- Set node `l` of code `ci`'s value set. -/
def setVal (ci l : Nat) (S : Sites P) : SolveState P :=
  match st.nodes[ci]? with
  | none => st
  | some ns => match ns[l]? with
    | none => st
    | some x =>
      let v := union x.val S
      if v.length = x.val.length then st
      else { st with nodes := st.nodes.set ci (ns.set l { x with val := v }), changed := true }

end SolveState

section gen
variable (cs : List (SolveCode P)) (τ : Nat → Sites P) (φ : Nat → Option FnSig) (a : Alloc P)

/-- The index of a code among `C`'s. -/
def codeIdx (m : Code) : Option Nat := cs.findIdx? (·.code = m)

/-- **A term's sets, proposed** (`syn` at the current proposal): its stores
added to the heap of sites, what reaches outside code added to `O`, the
slots of a callee's entry grown. -/
partial def gen (d : Nat) (Γ : Nat → Option (Sites P)) (e : Tm) : StateM (SolveState P) (Sites P) := do
  let st ← get
  let F := st.toFlow cs
  match e with
  | .var i => return if i < d then (Γ i).getD [] else τ (i - d)
  | .invoke f r args =>
    let Sf ← gen d Γ f
    let Sr ← gen d Γ r
    let Ls ← args.mapM (gen d Γ)
    let viaC : Option (Nat × FnSig) := match f with
      | .var j => if d ≤ j ∧ args.all partB then (φ (j - d)).bind fun σ => (codeIdx cs σ.code).map (·, σ) else none
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
      return (← get).O
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
  | .spread x => return contentsOf F (← gen d Γ x)
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
      match codeIdx cs (E, K) with
      | some ci =>
        for i in List.range caps.length do
          match caps[i]? with
          | some u => modify fun st => st.slot ci s (capSlot ar rest i) ((partSites τ d Γ u).getD [])
          | none => pure ()
      | none => pure ()
      return [a.obj]
    else return a.obj :: ((partsSites τ d Γ caps).getD [])
  | .readAt _ x | .indexAt x _ =>
    let Sx ← gen d Γ x
    match e with
    | .indexAt _ k => let _ ← gen d Γ k
    | _ => pure ()
    let F := (← get).toFlow cs
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
    return contentsOf ((← get).toFlow cs) Sx
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
    let F := (← get).toFlow cs
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

/-- The signatures carried along an edge to a target of width `n`. -/
def carryFn (φ : Nat → Option FnSig) (m : Option (List Nat)) (n : Nat) : List (Option FnSig) :=
  (List.range n).map fun i => φ (mapIdx m i)

/-- Two signature lists meet: a slot keeps a signature both name. -/
def meetFn (x y : List (Option FnSig)) : List (Option FnSig) :=
  (List.range (min x.length y.length)).map fun i => if x.getD i none = y.getD i none then x.getD i none else none

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

/-- The value signature of a node: a slot variable's signature. -/
def vfnOf (fn : List (Option FnSig)) : Tm → Option FnSig
  | .var j => fn.getD j none
  | _ => none

/-- **One round of signatures**: each node's named slots, met with every
edge into it. `none` is a node no edge reached yet. -/
def fnRound (c : SolveCode P) (fns : List (Option (List (Option FnSig)))) : List (Option (List (Option FnSig))) :=
  let m := c.code
  (List.range m.1.length).foldl (fun acc l =>
    match fns.getD l none, m.1[l]?, m.2[l]? with
    | some fn, some e, some (k, x) =>
      (edgesOf (k, x)).foldl (fun acc (y, push) =>
        let src : Nat → Option FnSig := if push then
            pushFn (if (match k with | .branchBind .. => true | _ => false) || (match x with | some y' => y' == y | none => false) then none else vfnOf fn e) (fun i => fn.getD i none)
          else fun i => fn.getD i none
        let w := fn.length + 1 + mlen y.mapping
        let car := carryFn src y.mapping w
        match acc.getD y.label none with
        | none => acc.set y.label (some car)
        | some old => acc.set y.label (some (meetFn old car))) acc
    | _, _, _ => acc) fns

/-- The signatures of a code's nodes: the entry seeded, the rounds run. -/
def fnsOf (c : SolveCode P) (rounds : Nat) : List (List (Option FnSig)) :=
  let self := capSlot c.ar c.rest c.ncaps
  let seed := (List.range (max c.seeds.length (self + 1))).map fun i =>
    if i = self then some c.sig else c.seeds.getD i none
  let init : List (Option (List (Option FnSig))) :=
    (List.range c.code.1.length).map fun l => if l = c.start then some seed else none
  let fin := (List.range rounds).foldl (fun acc _ => fnRound c acc) init
  fin.map (·.getD [])

/-! ## Sites -/

/-- **One round of sites**: each node's expression's sets, its edges'
slots, `O` closed and accepted everywhere. -/
def siteRound (cs : List (SolveCode P)) (st : SolveState P) : SolveState P := Id.run do
  let mut st := { st with changed := false }
  for ci in List.range cs.length do
    let some c := cs[ci]? | continue
    for l in List.range c.code.1.length do
      let some e := c.code.1[l]? | continue
      let some (k, x) := c.code.2[l]? | continue
      let some ns := st.nodes[ci]? | continue
      let some nd := ns[l]? | continue
      let (S, st') := (gen cs nd.envAt nd.fnAt c.alloc 0 (fun _ => none) e).run st
      st := st'.setVal ci l S
      let some ns := st.nodes[ci]? | continue
      let some nd := ns[l]? | continue
      for (y, push) in edgesOf (k, x) do
        let pushed : Option (Sites P) :=
          if !push then none
          else if (match x with | some y' => y' == y | none => false) then some st.O
          else if (match k with | .branchBind .. => true | _ => false) then some []
          else some nd.val
        let τ : Nat → Sites P := match pushed with
          | none => nd.envAt
          | some Sv => pushSites Sv nd.envAt
        let w := nd.env.length + 1 + mlen y.mapping + ((ns.getD y.label nd).env.length)
        for i in List.range w do
          st := st.slot ci y.label i (τ (mapIdx y.mapping i))
        st := st.dfltGrow ci y.label w (τ (mapIdx y.mapping w))
      if (match k with | .ret => true | _ => false) then st := st.toO nd.val
  -- `O` closed under the contents, its storage holding all of it.
  let F := st.toFlow cs
  st := st.toO (contentsOf F st.O)
  for s in st.O do
    st := st.store s st.O
  -- Every slot accepts `O`.
  for ci in List.range cs.length do
    let some ns := st.nodes[ci]? | continue
    for l in List.range ns.length do
      st := st.dfltGrow ci l 0 st.O
  return st

/-- **The proposed flow** of `C`'s codes: the signatures' rounds, then the
sites' rounds until nothing changes or the fuel ends. -/
def solveFlow (cs : List (SolveCode P)) (fuel : Nat) : FFlow P :=
  let nodes0 : List (List (FNode P)) := cs.map fun c =>
    let fns := fnsOf c (c.code.1.length + 1)
    (List.range c.code.1.length).map fun l =>
      let fn := fns.getD l []
      ⟨[], [none], [], fn, (c.code.1[l]?).bind (vfnOf fn)⟩
  let st0 : SolveState P := ⟨[none], [], nodes0, true⟩
  let rec loop : Nat → SolveState P → SolveState P
    | 0, st => st
    | n + 1, st => let st' := siteRound cs st; if st'.changed then loop n st' else st'
  (loop fuel st0).toFlow cs

end Verification.TolerantFrames.ReadOnly
