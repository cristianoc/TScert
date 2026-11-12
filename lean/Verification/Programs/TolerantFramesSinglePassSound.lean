import Verification.Programs.TolerantFramesSubtypeAnswers
import Verification.Programs.TolerantFramesVisitSummaries
import Verification.Programs.TolerantFramesRegionalTyping
import Verification.Programs.TolerantFramesRegionalRecorded
import Verification.Programs.TolerantFramesDriverSetup

/-! # Tolerant frames: the single pass's graph theorem

`run_sound_single_pass` composes the per-node side's graph theorem
(`run_sound_pass`) with the walk side's record soundness and checks
(`recordsSound_of`, `recordsChecked_of`): its premises are the hypotheses still open, each a
statement about the pass's setup, one visit, or a loop the pass runs. -/
namespace Verification.TolerantFrames
open Verification PositiveGraphs PositiveCertificates LabelStore

section Run
variable {ι : Type} [Labels ι]

/-- The graph theorem under exit width, exit summary-prefix preservation, exit yields,
and regional recording and typing. Subtype answers are sound by `subtypeAnswersAll`;
`visitStepPrefix_of_exitStep` and `visitsSettle_of` connect the final sound summary table
to each checked node. -/
theorem run_sound_single_pass (hp : ExitsWidth ι)
    (hprefix : ExitStepPrefix ι)
    (hex : ExitsYield ι) (hrec : RegionsRecorded ι)
    (htyped : RegionsTyped ι) : Target.RunSound ι :=
  have hv := visitsRecord_of (visitsRest_of (exitsPushOk_of hp) (visitsSettle_of (visitStepPrefix_of_exitStep hprefix)) visitsImplications)
  run_sound_pass (recordsSound_of setupRecords_of hv) (recordsChecked_of setupRecords_of hv) (nodesYield_of subtypeAnswersAll hex) linearNearFuelEq
    (regionsHeld_of hrec htyped)

end Run

end Verification.TolerantFrames
