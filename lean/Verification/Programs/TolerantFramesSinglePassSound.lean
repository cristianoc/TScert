import Verification.Programs.TolerantFramesComposeYields
import Verification.Programs.TolerantFramesDriverSettle
import Verification.Programs.TolerantFramesRegionalHeld
import Verification.Programs.TolerantFramesDriverSetup
import Verification.Programs.TolerantFramesExitWidths

/-! # Tolerant frames: the single pass's graph theorem

`run_sound_single_pass` composes the per-node side's graph theorem
(`run_sound_pass`) with the walk side's record soundness and checks
(`recordsSound_of`, `recordsChecked_of`): its premises are the hypotheses still open, each a
statement about the pass's setup, one visit, or a loop the pass runs. -/
namespace Verification.TolerantFrames
open Verification PositiveGraphs PositiveCertificates LabelStore

section Run
variable {ι : Type} [Labels ι]

/-- The graph theorem from the remaining summary, exit-delivery and
regional premises. Setup, exit widths and subtype answers are proved by
`setupRecords_of`, `exitsWidth` and `subtypeAnswersAll`. -/
theorem run_sound_single_pass
    (hdir : ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (env : SinglePass.WalkEnv ι G I),
      DirectKeepsSummaries G I env.undefTy)
    (hsrch : ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (env : SinglePass.WalkEnv ι G I),
      SearchKeepsSummaries G I env.pool env.fuel env.suggestions env.index env.codes env.aliases
        env.passChecker.checker)
    (hex : ExitsYield ι) (hrec : RegionsRecorded ι)
    (htyped : RegionsTyped ι) : Target.RunSound ι :=
  have hv := visitsRecord_of (visitsRest_of (exitsPushOk_of exitsWidth) (visitsSettle_of hdir hsrch) visitsImplications)
  run_sound_pass (recordsSound_of setupRecords_of hv) (recordsChecked_of setupRecords_of hv) (nodesYield_of subtypeAnswersAll hex) linearNearFuelEq
    (regionsHeld_of hrec htyped)

end Run

end Verification.TolerantFrames
