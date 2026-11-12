import Verification.Programs.TolerantFramesExitStructural
import Verification.Programs.TolerantFramesVisitSummaries
import Verification.Programs.TolerantFramesRegionalTyping
import Verification.Programs.TolerantFramesRegionalReadback
import Verification.Programs.TolerantFramesDriverSetup
import Verification.Programs.TolerantFramesExitWidths

/-! # Tolerant frames: the single pass's graph theorem

`run_sound_single_pass` composes the per-node side's graph theorem
(`run_sound_pass`) with the walk side's record soundness and checks
(`recordsSound_of`, `recordsChecked_of`) and `exitsYield_of_kept`. Its premise
states start-contract projection. -/
namespace Verification.TolerantFrames
open Verification PositiveGraphs PositiveCertificates LabelStore PositiveRules

section Run
variable {ι : Type} [Labels ι]

/-- The graph theorem under exit delivery. -/
theorem run_sound_single_pass_of_exits
    (hex : ExitsYield ι) : Target.RunSound ι :=
  have htables := regionalVisitTables_of_recordedAgreement
    (regionalRecordedTableAgreement regionalRecordedReadback)
  have hstep := regionalStepBridge (ι := ι)
  have hv := visitsRecord_of (visitsRest_of (exitsPushOk_of exitsWidth) (visitsSettle_of (visitStepPrefix_of_exitStep exitStepPrefix)) visitsImplications) visitExits_answers_prefix
  run_sound_pass (recordsSound_of setupRecords_of hv) (recordsChecked_of setupRecords_of hv) (nodesYield_of subtypeAnswersAll hex) linearNearFuelEq
    (regionsHeld_of (regionsRecorded_of_visitTables htables) (regionsTyped_of_visitTables htables hstep))

/-- The graph theorem under start-contract projection. -/
theorem run_sound_single_pass
    (startWrittenSound : ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I)
      after admits, RunPremises G I c after admits → ∀ r : RunWalkA G I c,
        WalkChecked c r → ExitChecks.StartWrittenImpliesStated r) : Target.RunSound ι :=
  run_sound_single_pass_of_exits (exitsYield_of_kept startWrittenSound)

end Run

end Verification.TolerantFrames
