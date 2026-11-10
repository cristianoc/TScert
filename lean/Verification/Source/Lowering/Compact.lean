import Verification.Source.Lowering.State

/-! # Nodes that do nothing, left out

A lowered graph's node that does nothing is left out of the graph its
lowering returns, each edge into it going where its own edge goes: a check
of a slot at the slot's own type, whose value is discarded; a copy of a slot
at the slot's own type, the edge out of it reading the slot itself; a `nul`
whose value is discarded. The slots keep their values (a binding never
changes), so every edge reads the value the left-out node would have given.
A statement entry, a node stating an assertion or candidates, and the graph's
entry stay. -/
namespace Verification.SourceExtraction
open ControlFlow CertificateProducer RequestJson
open EquationGraphs (Tree)

/-- Which nodes the lowering leaves out. -/
structure Compaction where
  /-- A slot's check at its own type, its value discarded. -/
  checks : Bool := true
  /-- A slot's copy at its own type. -/
  copies : Bool := true
  /-- A `nul` whose value is discarded. -/
  discards : Bool := true

/-- The slot of the source context target slot `k` reads, through a mapping
(none: the same slot). -/
private def through (m : Option (Array Nat)) (k : Nat) : Nat :=
  match m with
  | none => k
  | some slots => slots.getD k 0

/-- How an edge into a left-out node continues: the node's own edge, with
the incoming mapping composed. `none` where the node is kept. -/
private def passOn (P : Array Node) (claims : Array (PointClaim Tree)) (c : Compaction) (pinned : Std.HashSet Nat)
    (l : Nat) : Option (Target × (Option (List Nat) → Option (List Nat))) := do
  if pinned.contains l then none
  let n ← P[l]?
  let claim ← claims[l]?
  if n.handler.isSome then none
  match n.expression, n.continuation with
  | .var i, .effect t =>
    if c.checks && claim.context[i]? == some claim.type then
      some (t, fun m1 => let a1 := m1.map List.toArray; let a2 := t.mapping.map List.toArray
        some ((List.range (match t.mapping with
        | some s => s.length
        | none => claim.context.length)).map fun k => through a1 (through a2 k)))
    else none
  | .nul, .effect t =>
    if c.discards then
      some (t, fun m1 => let a1 := m1.map List.toArray; let a2 := t.mapping.map List.toArray
        some ((List.range (match t.mapping with
        | some s => s.length
        | none => claim.context.length)).map fun k => through a1 (through a2 k)))
    else none
  | .var i, .bind t =>
    if c.copies && claim.context[i]? == some claim.type then
      some (t, fun m1 => let a1 := m1.map List.toArray; let a2 := t.mapping.map List.toArray
        some ((List.range (match t.mapping with
        | some s => s.length
        | none => claim.context.length + 1)).map fun k =>
          let s := through a2 k
          through a1 (if s == 0 then i else s - 1)))
    else none
  | _, _ => none

/-- The entries of `xs` at the labels kept. -/
private def keepAt {α : Type} (gone : Array Bool) (xs : List α) : List α :=
  (xs.zipIdx.filter fun (_, l) => !gone.getD l false).map (·.1)

/-- The program without the nodes that do nothing, its claims, source map,
assertions, candidates and statement entries renumbered, and the new label
of each kept node. -/
def compactGraph (c : Compaction) (program : List Node) (claims : List (PointClaim Tree))
    (sourceMap : List (Option SourceMapEntry)) (assertions : List (Nat × HeapKnowledge.Knowledge))
    (candidates : List (Nat × List HeapKnowledge.IndexAtom)) (cuts : List Nat) (entry : Nat) :
    List Node × List (PointClaim Tree) × List (Option SourceMapEntry) × List (Nat × HeapKnowledge.Knowledge) ×
      List (Nat × List HeapKnowledge.IndexAtom) × List Nat × (Nat → Nat) := Id.run do
  let P := program.toArray
  let C := claims.toArray
  let pinned : Std.HashSet Nat := ((entry :: cuts) ++ assertions.map (·.1) ++ candidates.map (·.1)).foldl
    (·.insert ·) {}
  -- For each left-out node, where its edge ends past left-out nodes, and the
  -- slot of the node's context each slot there reads: computed once each.
  let mut final : Array (Option (Nat × Array Nat)) := Array.replicate P.size none
  let mut gone : Array Bool := Array.replicate P.size false
  for l0 in [0:P.size] do
    if (passOn P C c pinned l0).isNone || (final[l0]!).isSome then continue
    -- The chain of left-out nodes from `l0`, at most as many as there are nodes.
    let mut chain : Array (Nat × Array Nat) := #[]
    let mut cur := l0
    let mut endsAt : Option (Nat × Array Nat) := none
    for _ in [0:P.size + 1] do
      match final[cur]! with
      | some r => endsAt := some r; break
      | none =>
        match passOn P C c pinned cur with
        | some (t, compose) =>
          if chain.any (·.1 == cur) then break
          chain := chain.push (cur, ((compose none).getD []).toArray)
          cur := t.label
        | none => endsAt := some (cur, #[]); break
    match endsAt with
    | none => pure ()  -- a cycle of left-out nodes: they stay
    | some (f, M0) =>
      -- `M0` is empty where the chain ends at a kept node: its slots read
      -- the last left-out node's directly.
      let mut acc : Option (Array Nat) := if M0.isEmpty && (final[cur]!).isNone then none else some M0
      for (l, A) in chain.reverse do
        let M := match acc with
          | none => A
          | some M => M.map fun j => A.getD j 0
        final := final.set! l (some (f, M))
        gone := gone.set! l true
        acc := some M
  let resolve := fun (t : Target) => match final[t.label]?.join with
    | some (f, M) => let a1 := t.mapping.map List.toArray; (⟨f, some (M.toList.map fun j => through a1 j)⟩ : Target)
    | none => t
  let mut newLabel : Array Nat := Array.mkEmpty P.size
  let mut count := 0
  for l in [0:P.size] do
    newLabel := newLabel.push count
    if !gone[l]! then count := count + 1
  let relabel := fun (t : Target) => let r := resolve t; (⟨newLabel.getD r.label 0, r.mapping⟩ : Target)
  let fix : Continuation → Continuation
    | .ret => .ret
    | .bind t => .bind (relabel t)
    | .effect t => .effect (relabel t)
    | .branch y m => .branch (relabel y) (relabel m)
    | .branchBind y m => .branchBind (relabel y) (relabel m)
    | .tagBind tg y m => .tagBind tg (relabel y) (relabel m)
  let fixNode := fun (n : Node) => ({ n with continuation := fix n.continuation, handler := n.handler.map relabel } : Node)
  let program' := keepAt gone (program.map fixNode)
  let lab := fun l => newLabel.getD l 0
  return (program', keepAt gone claims, keepAt gone sourceMap, assertions.map fun (l, k) => (lab l, k),
    candidates.map fun (l, a) => (lab l, a), cuts.map lab, lab)

/-- The nodes the lowering leaves out (each kind its own step of the work). -/
def compaction : Compaction := ⟨true, true, true⟩

/-- A lowered graph with its source account, without the nodes that do
nothing, and its entry's new label. -/
def compactLowered (program : List Node) (claims : List (PointClaim Tree)) (source : CodeSource) (entry : Nat) :
    List Node × List (PointClaim Tree) × CodeSource × Nat :=
  let (p, c, sm, a, ca, cu, lab) := compactGraph compaction program claims source.sourceMap source.assertions
    source.candidates source.cuts entry
  (p, c, ⟨sm, a, ca, cu⟩, lab entry)

end Verification.SourceExtraction
