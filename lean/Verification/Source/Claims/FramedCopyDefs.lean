import Verification.Source.Claims.FramedPaths
import Verification.Paper.TolerantFrames.ReadOnlyCharges

/-! # The tables of copies and the parts of steps, decided

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "Milestone 2: the protected
reading", the decision). The definitions the pass's check of a framed
node runs: a table of copies, its check (`copiesB`) and its proposal
(`copiesOf`), proved in `FramedCopies`; and the check of a step's parts
at a protocol (`stepKeptB`), proved in `FramedReading`. -/

namespace Verification.TolerantFrames.ReadOnly
open Verification ControlFlow Footprints

/-- **A copy entry** `(i, j, π)`: slot `i` holds the reads of the keys `π`
from argument `j`. -/
abbrev CopyEntry := Nat × Nat × List PropKey

/-- **A table of copies**: each label's entries. -/
abbrev CopyTable := List (List CopyEntry)

/-- The entries of a label. -/
def CopyTable.at (cp : CopyTable) (l : Nat) : List CopyEntry := cp.getD l []

/-- **The source slot a target's slot reads** (`envMap`): the slot the map
names, slot `0` past the map; the slot itself where it maps none. -/
def srcOf : Option (List Nat) → Nat → Nat
  | none, i => i
  | some slots, i => slots.getD i 0

/-- **The entry the value a node's expression gives copies**: a slot's
entry for `.var i`; for `readAt f (.var i)` the entry of the path without
its last key `f`. -/
def boundEntryB (cp : CopyTable) (l : Nat) (e : Tm) (j : Nat) (π : List PropKey) : Bool :=
  match e with
  | .var i => (cp.at l).contains (i, j, π)
  | .readAt f (.var i) => π.getLast? == some f && (cp.at l).contains (i, j, π.dropLast)
  | _ => false

/-- **The check of an edge** from node `l` whose expression is `e` to the
target `t`: each entry of the target's table is the source slot's entry
at `l`; where the edge binds a value in front (`bound = some b`), slot `0`
past the map is that value, which has an entry where it is the node's own
value (`b`) and `boundEntryB` gives it. -/
def edgeOkB (cp : CopyTable) (l : Nat) (e : Tm) (bound : Option Bool) (t : Target) : Bool :=
  (cp.at t.label).all fun (i', j, π) =>
    let s := srcOf t.mapping i'
    match bound with
    | none => (cp.at l).contains (s, j, π)
    | some b => if s = 0 then b && boundEntryB cp l e j π else (cp.at l).contains (s - 1, j, π)

/-- The edges of a continuation, each with whether it binds the node's own
value (`some true`), another value (`some false`) or none. -/
def contEdges : Continuation → List (Option Bool × Target)
  | .ret => []
  | .bind t => [(some true, t)]
  | .effect t => [(none, t)]
  | .branch y n => [(none, y), (none, n)]
  | .branchBind y n => [(some false, y), (some false, n)]
  | .tagBind _ y n => [(some true, y), (some true, n)]

/-- The edges of a node: its continuation's, then its handler's, which
binds the thrown value. -/
def nodeEdges (k : Continuation) (x : Option Target) : List (Option Bool × Target) :=
  contEdges k ++ (match x with | some t => [(some false, t)] | none => [])

/-- **The check of a table of copies** at the code `Pe`, `Pk` started at
`start` with `arity` arguments: the start's entries the diagonal below
the arity, and every edge of every node checked (`edgeOkB`). -/
def copiesB (Pe : List Tm) (Pk : List (Continuation × Option Target)) (start arity : Nat) (cp : CopyTable) : Bool :=
  (cp.at start).all (fun (i, j, π) => i == j && π.isEmpty && decide (j < arity)) &&
  (List.range Pk.length).all fun l => match Pe[l]?, Pk[l]? with
    | some e, some (k, x) => (nodeEdges k x).all fun (b, t) => edgeOkB cp l e b t
    | _, _ => true

/-! ## The proposal -/

/-- The entries an edge gives its target from the node's, at most `bound`
keys long. -/
def edgeEntries (cur : List CopyEntry) (e : Tm) (b : Option Bool) (t : Target) (bound : Nat) : List CopyEntry :=
  let fromSlot (s i' : Nat) : List CopyEntry :=
    match b with
    | none => (cur.filter (·.1 == s)).map fun (_, j, π) => (i', j, π)
    | some own => if s = 0 then
        (if own then match e with
          | .var i => (cur.filter (·.1 == i)).map fun (_, j, π) => (i', j, π)
          | .readAt f (.var i) => ((cur.filter (·.1 == i)).filter (·.2.2.length < bound)).map
              fun (_, j, π) => (i', j, π ++ [f])
          | _ => []
        else [])
      else (cur.filter (·.1 == s - 1)).map fun (_, j, π) => (i', j, π)
  match t.mapping with
  | some slots => (List.range slots.length).flatMap fun i' => fromSlot (srcOf t.mapping i') i'
  | none =>
    let slotsOf := (cur.map (·.1)).eraseDups
    let ids := match b with
      | none => slotsOf
      | some _ => 0 :: slotsOf.map (· + 1)
    ids.flatMap fun i' => fromSlot i' i'

/-- One round of the must-analysis: each label's entries, intersected over
its incoming edges, the start's its diagonal. -/
def copiesRound (Pe : List Tm) (Pk : List (Continuation × Option Target)) (start arity bound : Nat)
    (cp : List (Option (List CopyEntry))) : List (Option (List CopyEntry)) :=
  let diag : List CopyEntry := (List.range arity).map fun j => (j, j, [])
  let incoming : List (Nat × List CopyEntry) := (List.range Pk.length).flatMap fun l =>
    match Pe[l]?, Pk[l]?, cp.getD l none with
    | some e, some (k, x), some cur => (nodeEdges k x).map fun (b, t) => (t.label, edgeEntries cur e b t bound)
    | _, _, _ => []
  (List.range Pk.length).map fun l =>
    let ins := (incoming.filter (·.1 == l)).map (·.2)
    let meet : Option (List CopyEntry) := ins.foldl (fun acc s => match acc with
      | none => some s
      | some a => some (a.filter s.contains)) none
    if l = start then some diag else match meet with
      | some m => some m.eraseDups
      | none => cp.getD l none

/-- **The proposal of a table of copies** (`copiesB` decides it): the
must-analysis iterated from the start's diagonal, each key path at most
`bound` long; the empty table where its result fails the check. -/
def copiesOf (Pe : List Tm) (Pk : List (Continuation × Option Target)) (start arity bound : Nat) : CopyTable :=
  let init : List (Option (List CopyEntry)) := (List.range Pk.length).map fun l =>
    if l = start then some ((List.range arity).map fun j => (j, j, [])) else none
  let fin := (List.range (Pk.length * (bound + 2) + 2)).foldl (fun cp _ => copiesRound Pe Pk start arity bound cp) init
  let cp : CopyTable := fin.map (·.getD [])
  if copiesB Pe Pk start arity cp then cp else []



variable {P : Package}

/-- **A step's parts kept**, decided: every part a location of the step may
have, at a kind its bound holds and a key of the step, at the site `none`,
is kept by `Ψ`; refused where the step fixes no finite set of keys. -/
def stepKeptB (Ψ : Protocol P) (q : Region) : Bool :=
  match regionKeys q with
  | some K => (partsOf [none] K q).all fun p => Ψ p == .keep
  | none => false

/-- Every step of a list kept. -/
def stepsKeptB (Ψ : Protocol P) (qs : List Region) : Bool := qs.all (stepKeptB Ψ)

end Verification.TolerantFrames.ReadOnly
