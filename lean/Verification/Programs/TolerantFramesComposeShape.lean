import Verification.Programs.TolerantFramesNodeWalk

/-! # Tolerant frames: a continuation's shape from the claim's type

`NodeMeaning.shape` asks that every value of the node's claim type has the
shape its continuation takes (`ShapeOk`): at a `branch` and a `branchBind`,
a Boolean. `run` checks the claim type at every node
(`SinglePass.passShapeCheck'`: the Boolean type at a `branch`, only
Booleans at a `branchBind`). Proved: `branchShape_of` (a Boolean claim type
gives a branch's shape), `nodeShape_of` (the check gives every value its
continuation's shape). -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules

section Shape
variable {ι : Type} [DecidableEq ι]

/-- **A Boolean claim type gives a branch's shape**: a value of a type
represented by the Boolean clause is `true` or `false`. -/
theorem branchShape_of {G : NormalGraph ι} {A : Ty ι} {y no : Target}
    (hb : decide (PositiveRules.expand G A = [.bool]) = true) {n : Nat} {W : WorldT n} {v : Tm}
    (hv : meaning G A n W v) : ShapeOk v (.branch y no) := by
  have hr : Represents G A .bool := of_decide_eq_true (p := PositiveRules.expand G A = [.bool]) hb
  have hc := represents_raw hr n W v hv
  simpa [ShapeOk, PositiveNormalization.semWithArgs, boolT] using hc

/-- **The shape check gives every value its continuation's shape**
(`NodeMeaning.shape`): where `run`'s shape check `passShapeCheck'`
accepts the claim type at the continuation. -/
theorem nodeShape_of {G : NormalGraph ι} {A : Ty ι} {k : Continuation}
    (hs : SinglePass.passShapeCheck' G A k = true) {n : Nat} {W : WorldT n} {v : Tm} (hv : meaning G A n W v) :
    ShapeOk v k := by
  cases k with
  | ret | bind _ | effect _ => trivial
  | branch y no => exact branchShape_of (by simpa [SinglePass.passShapeCheck', SinglePass.passShapeCheck] using hs) hv
  | branchBind _ _ => exact BranchRefinement.onlyBoolean_sound (by simpa [SinglePass.passShapeCheck'] using hs) hv
  | tagBind _ _ _ => trivial

end Shape

end Verification.TolerantFrames
