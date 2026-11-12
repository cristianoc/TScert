import Verification.Programs.TolerantFramesComposeYields
import Verification.Programs.TolerantFramesDriverSettle
import Verification.Programs.TolerantFramesRegionalHeld
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

/-- **THE GRAPH THEOREM of the single pass, over its open premises**: the
setup starting the walk's invariant by proof (`setupRecords_of`); of each visit, each exit's mapping of
its target's width (`ExitsWidth`; the states its exits push then meet
`PushOk`, `exitsPushOk_of`) and its label settled, its checks at the node it
visits included, the yields it keeps among them (`visitsSettle_of`, under `DirectKeepsSummaries` and `SearchKeepsSummaries`; the rest
of what a visit records, `visitsRecord_of` and `visitsRest_of`); the
answered subtype requests sound
(`SubtypeAnswersAll`), each checked node's exits and handler delivering
with its kept yields (`ExitsYield`), the visits' regional checks over the
graph's tables (`RegionsRecorded`) and the regional evidence typed
(`RegionsTyped`) ⟹ `RunSound` (each node's kept yields judged and meeting
the return's goal, `nodesYield_of`; the regional premise,
`regionsHeld_of`; the pass's `linearNear` its search on fuel by
definition, `linearNearFuelEq`). -/
theorem run_sound_single_pass (hp : ExitsWidth ι)
    (hdir : ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (env : SinglePass.WalkEnv ι G I),
      DirectKeepsSummaries G I env.undefTy)
    (hsrch : ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (env : SinglePass.WalkEnv ι G I),
      SearchKeepsSummaries G I env.pool env.fuel env.suggestions env.index env.codes env.aliases
        env.passChecker.checker)
    (hsub : SubtypeAnswersAll ι) (hex : ExitsYield ι) (hrec : RegionsRecorded ι)
    (htyped : RegionsTyped ι) : Target.RunSound ι :=
  have hv := visitsRecord_of (visitsRest_of (exitsPushOk_of hp) (visitsSettle_of hdir hsrch) visitsImplications)
  run_sound_pass (recordsSound_of setupRecords_of hv) (recordsChecked_of setupRecords_of hv) (nodesYield_of hsub hex) linearNearFuelEq
    (regionsHeld_of hrec htyped)

end Run

end Verification.TolerantFrames
