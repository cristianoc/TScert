import Verification.Programs.TolerantFramesVisitSummaries
import Verification.Programs.TolerantFramesRegionalTyping
import Verification.Programs.TolerantFramesRegionalReadback
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

/-- The graph theorem under exit delivery, discarded
separation recovery and selected-proof header alignment. -/
theorem run_sound_single_pass
    (hex : ExitsYield ι)
    (hdiscard : RegionalDiscardedSeparation ι) (hheader : RegionalStepHeader ι) : Target.RunSound ι :=
  have htables := regionalVisitTables_of_recordedAgreement
    (regionalRecordedTableAgreement (regionalRecordedReadback hheader))
  have hstep := regionalStepBridge hdiscard hheader
  have hv := visitsRecord_of (visitsRest_of (exitsPushOk_of exitsWidth) (visitsSettle_of (visitStepPrefix_of_exitStep exitStepPrefix)) visitsImplications) visitExits_answers_prefix
  run_sound_pass (recordsSound_of setupRecords_of hv) (recordsChecked_of setupRecords_of hv) (nodesYield_of subtypeAnswersAll hex) linearNearFuelEq
    (regionsHeld_of (regionsRecorded_of_visitTables htables) (regionsTyped_of_visitTables htables hstep))

end Run

end Verification.TolerantFrames
