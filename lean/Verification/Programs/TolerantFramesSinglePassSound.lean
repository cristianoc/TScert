import Verification.Programs.TolerantFramesComposeYields
import Verification.Programs.TolerantFramesDriverVisitRest
import Verification.Programs.TolerantFramesRegionalHeld

/-! # Tolerant frames: the single pass's graph theorem

`run_sound_single_pass` composes the per-node side's graph theorem
(`run_sound_pass`) with the walk side's record soundness and checks
(`recordsSound_of`, `recordsChecked_of`): its premises are the hypotheses still open, each a
statement about the pass's setup, one visit, or a loop the pass runs. -/
namespace Verification.TolerantFrames
open LabelStore

section Run
variable {ι : Type} [Labels ι]

/-- **THE GRAPH THEOREM of the single pass, over its open premises**: what
the setup records (`SetupRecords`); of each visit, the states its exits
push meeting `PushOk` (`ExitsPushOk`), its step's fresh counter not below
its own (`StepFresh`) and its label settled, its checks at the node it
visits included, the yields it keeps among them (`VisitsSettle`; the rest
of what a visit records, `visitsRecord_of` and `visitsRest_of`); the
answered subtype requests sound
(`SubtypeAnswersAll`), each checked node's exits and handler delivering
with its kept yields (`ExitsYield`), the visits' regional checks over the
graph's tables (`RegionsRecorded`) and the regional evidence typed
(`RegionsTyped`) ⟹ `RunSound` (each node's kept yields judged and meeting
the return's goal, `nodesYield_of`; the regional premise,
`regionsHeld_of`; the pass's `linearNear` its search on fuel by
definition, `linearNearFuelEq`). -/
theorem run_sound_single_pass (hs : SetupRecords ι) (hp : ExitsPushOk ι) (hf : StepFresh ι)
    (hst : VisitsSettle ι) (hsub : SubtypeAnswersAll ι) (hex : ExitsYield ι) (hrec : RegionsRecorded ι)
    (htyped : RegionsTyped ι) : Target.RunSound ι :=
  have hv := visitsRecord_of (visitsRest_of hp hf hst)
  run_sound_pass (recordsSound_of hs hv) (recordsChecked_of hs hv) (nodesYield_of hsub hex) linearNearFuelEq
    (regionsHeld_of hrec htyped)

end Run

end Verification.TolerantFrames
