import Verification.Types.ClauseSelection

/-! Controls for clause selection's exclusions on tag sets (UNION-SHAPES.md,
R3; HOST-FAMILIES.md, "Tag sets"). Selection is pruning: a target clause it
excludes is never tried, which no pipeline outcome shows, so a selection
reading literals alone, and not a set's elements, fails here. -/
namespace Verification.SelectionControls
open PositiveNormalization PositiveGraphs ClauseSelection

/-- Label 0 is `1 | 2` as a set, label 1 the literal `3`, label 2 the set
`1 | 2 | 3`. -/
private def G : NormalGraph Nat where
  rows
    | 0 => [.numIn [0x3ff0000000000000, 0x4000000000000000]]
    | 1 => [.numLit 0x4008000000000000]
    | _ => [.numIn [0x3ff0000000000000, 0x4000000000000000, 0x4008000000000000]]

/-- `{ f: 1 | 2 }` and `{ f: 3 }`, each the record of one field. -/
private def source : Clause (List Nat) := .refs [("f", [0])] [] []
private def three : Clause (List Nat) := .refs [("f", [1])] [] []
private def upToThree : Clause (List Nat) := .refs [("f", [2])] [] []

-- A source field at the set `1 | 2` excludes a target field at `3`: its
-- element `1` is a value the target does not admit.
#guard litExcl G source three
-- It does not exclude one at `1 | 2 | 3`, which admits each element.
#guard !litExcl G source upToThree

end Verification.SelectionControls
