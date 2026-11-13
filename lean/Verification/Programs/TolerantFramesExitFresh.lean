import Verification.Programs.TolerantFramesExitAux

/-! # Tolerant frames: a run's values meet what every terminating run's value meets

`passOutFreshChecked_fresh` states the step's result fresh for every
normal run of the node's term within the step index; the exits read that
freshness from the state after the step. Proved
(`SafePostExc.and_steps`): a safe run whose every terminating run ends in a
value meeting `P` is safe with each returned value also meeting `P`; so the
step's judgment carries the result's freshness (`stepFresh_judgment`). -/
namespace Verification.TolerantFrames
open Verification HeapObservations PositiveRules

section Fresh
open Footprints HeapExpressionRules ControlFlow PositiveGraphs PositiveCertificates LabelStore ProgramTyping ProgramCertificates CertificateProducer
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

end Fresh

end Verification.TolerantFrames
