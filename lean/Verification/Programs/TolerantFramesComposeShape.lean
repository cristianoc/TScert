import Verification.Programs.TolerantFramesNodeWalk

/-! # Tolerant frames: a continuation's shape from the claim's type

`NodeAccepted.shape` asks that every value of the node's claim type has the
shape its continuation takes (`ShapeOk`): at a branch, a Boolean. The proved
checker checks it of a branch's evidence (`ControlFlow.checkNodeResult`,
`decide (expand G (result c) = [.bool])`); the pass's claims are the
producer's, and `run` makes no such check. `branchShape_of` proves the
checker's test gives the shape, so the test at a branch node of `run`
(`passShapeCheck`, with `onlyBoolean` at a `branchBind`) discharges
`shape`; `nodeShape_of` gives it at every continuation. -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules

section Shape
variable {ι : Type} [DecidableEq ι]

/-- The shape check a continuation's claim type needs, the proved checker's
(`ControlFlow.checkNodeResult`): at a branch the type exactly Boolean, at a
`branchBind` only Boolean values (`onlyBoolean`); other continuations need
none. -/
def passShapeCheck (G : NormalGraph ι) (A : Ty ι) : Continuation → Bool
  | .branch _ _ => decide (PositiveRules.expand G A = [.bool])
  | .branchBind _ _ => BranchRefinement.onlyBoolean G A
  | .ret | .bind _ | .effect _ | .tagBind _ _ _ => true

/-- **A Boolean claim type gives a branch's shape**: a value of a type
represented by the Boolean clause is `true` or `false`. -/
theorem branchShape_of {G : NormalGraph ι} {A : Ty ι} {y no : Target}
    (hb : decide (PositiveRules.expand G A = [.bool]) = true) {n : Nat} {W : WorldT n} {v : Tm}
    (hv : meaning G A n W v) : ShapeOk v (.branch y no) := by
  have hr : Represents G A .bool := of_decide_eq_true (p := PositiveRules.expand G A = [.bool]) hb
  have hc := represents_raw hr n W v hv
  simpa [ShapeOk, PositiveNormalization.semWithArgs, boolT] using hc

/-- **The shape check gives every value its continuation's shape**
(`NodeAccepted.shape`): where `passShapeCheck` accepts the claim type at
the continuation. -/
theorem nodeShape_of {G : NormalGraph ι} {A : Ty ι} {k : Continuation} (hs : passShapeCheck G A k = true)
    {n : Nat} {W : WorldT n} {v : Tm} (hv : meaning G A n W v) : ShapeOk v k := by
  cases k with
  | ret | bind _ | effect _ => trivial
  | branch y no => exact branchShape_of hs hv
  | branchBind _ _ => exact BranchRefinement.onlyBoolean_sound hs hv
  | tagBind _ _ _ => trivial

end Shape

end Verification.TolerantFrames
