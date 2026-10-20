import Verification.Programs.CertificateProducer

/-! Speed control for instance search: each of 24 targets has two distinct
respellings. Their Cartesian product contains 2^24 patches. The shared
budget covers both fixed and variadic targets before combination. -/
namespace Verification.InstanceGrowthControls
open PositiveGraphs PositiveNormalization CertificateProducer CallEffects

private def G : NormalGraph Nat where
  rows := fun _ => []

private instance : Instantiates Nat where
  propose := fun _ _ _ => some ([], [(0, [], [0]), (1, [], [1])])

private def scheme : SchemeRow Nat where
  binders := []
  signatures := [⟨[], [], [1, 0], .ordinary⟩]
  variadic := [⟨[], ([], []), [1, 0], .ordinary⟩]

private def fixed (n : Nat) : PositiveRules.Ops Nat :=
  (List.range n).map fun i => ⟨[], [], [0, i + 100], .ordinary⟩

private def rest (n : Nat) : List (RestArrow (List Nat)) :=
  (List.range n).map fun i => ⟨[], ([], []), [0, i + 200], .ordinary⟩

-- The syntactic proposal and optional row match add at most two candidates.
-- Saturation also checks that the control really generates alternatives.
private def bounded (n m : Nat) : Bool :=
  let count := (instanceCandidates G none 0 scheme (fixed n) (rest m)).length
  count ≥ instancePatchLimit + 1 && count ≤ instancePatchLimit + 2

#guard bounded 24 0
#guard bounded 0 24
#guard bounded 12 12

end Verification.InstanceGrowthControls
