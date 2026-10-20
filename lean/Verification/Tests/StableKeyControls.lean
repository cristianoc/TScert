import Verification.Types.PositiveCertificates

/-! Controls for subtyping over stable keys (HOST-FAMILIES.md, "Stable keys").
No claim states a stable key, which only a family's declarations carry, so
no pipeline case compares a record without a stable key against one stating
it; a subtyping that forgot the target's stable keys fails here. -/
namespace Verification.StableKeyControls
open PositiveNormalization PositiveGraphs PositiveCertificates

/-- Label 0 is `{ readonly f: number }` with `f` stable, label 1 the same
record without the stable key, label 2 `number`. -/
private def G : NormalGraph Nat where
  rows
    | 0 => [.refs [] [] [("f", [2])] [] [] [] ["f"]]
    | 1 => [.refs [] [] [("f", [2])]]
    | _ => [.num]

-- A record stating `f` stable is below one stating it plain: the source's
-- stable key is forgotten.
#guard checkUsing G (finiteInstanceImages G) [0] [1] {}
-- The record without it is not below the one stating it: every stable key
-- of the target must be the source's.
#guard !checkUsing G (finiteInstanceImages G) [1] [0] {}

end Verification.StableKeyControls
