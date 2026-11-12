import Verification.Programs.TolerantFramesComposeYields
import Verification.Programs.TolerantFramesDriverVisit
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
the setup records (`SetupRecords`), what each visit records, its checks at
the node it visits included, the yields it keeps among them
(`VisitsRecord`), the answered subtype requests sound
(`SubtypeAnswersAll`), each checked node's exits and handler delivering
with its kept yields (`ExitsYield`), the visits' regional checks over the
graph's tables (`RegionsRecorded`) and the regional evidence typed
(`RegionsTyped`) ⟹ `RunSound` (each node's kept yields judged and meeting
the return's goal, `nodesYield_of`; the regional premise,
`regionsHeld_of`; the pass's `linearNear` its search on fuel by
definition, `linearNearFuelEq`). -/
theorem run_sound_single_pass (hs : SetupRecords ι) (hv : VisitsRecord ι) (hsub : SubtypeAnswersAll ι)
    (hex : ExitsYield ι) (hrec : RegionsRecorded ι) (htyped : RegionsTyped ι) :
    Target.RunSound ι :=
  run_sound_pass (recordsSound_of hs hv) (recordsChecked_of hs hv) (nodesYield_of hsub hex) linearNearFuelEq
    (regionsHeld_of hrec htyped)

end Run

end Verification.TolerantFrames
