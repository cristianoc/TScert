import Verification.Programs.TolerantFramesComposeYields
import Verification.Programs.TolerantFramesDriverVisit

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
the setup records (`SetupRecords`), what each visit records,
its checks at the node it visits included (`VisitsRecord`), each checked
node's kept yields (`NodesYield`) and the regional premise (`RegionsHeld`)
⟹ `RunSound` (the pass's `linearNear` its search on fuel by definition,
`linearNearFuelEq`). -/
theorem run_sound_single_pass (hs : SetupRecords ι) (hv : VisitsRecord ι)
    (hyield : NodesYield ι) (hreg : RegionsHeld ι) :
    Target.RunSound ι :=
  run_sound_pass (recordsSound_of hs hv) (recordsChecked_of hs hv) hyield linearNearFuelEq hreg

end Run

end Verification.TolerantFrames
