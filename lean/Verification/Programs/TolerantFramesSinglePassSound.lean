import Verification.Programs.TolerantFramesExitStart
import Verification.Programs.TolerantFramesExitStructural
import Verification.Programs.TolerantFramesVisitSummaries
import Verification.Programs.TolerantFramesRegionalTyping
import Verification.Programs.TolerantFramesRegionalReadback
import Verification.Programs.TolerantFramesDriverSetup
import Verification.Programs.TolerantFramesExitWidths

/-! # Tolerant frames: the single pass's graph theorem

`run_sound_single_pass` composes the per-node side's graph theorem
(`run_sound_pass`) with the walk side's record soundness and checks
(`recordsSound_of`, `recordsChecked_of`) and `exitsYield_of_kept`.
The accepted setup supplies start-contract projection. -/
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

/-- Every checked walk preserves its start's written assertion. -/
theorem WalkChecked.startWrittenImpliesStated {G : NormalGraph ι} {I : InstanceImageCheck G}
    {c : Target.RunCall G I} {r : RunWalkA G I c} (hc : WalkChecked c r) :
    ExitChecks.StartWrittenImpliesStated r := by
  obtain ⟨dead, hn, hg, hm, σ, reach, hw, hr, hs⟩ := hc
  obtain ⟨env, σ0, hsetup, hE, hi⟩ := returnedWalk_setup_inv hw
  have kept := hE.startKept
  unfold passStated at kept
  rw [← r.stated_eq] at kept
  exact fun _ _ h => Verification.TolerantFrames.startWrittenImpliesStated kept h

/-- An accepted single pass gives the graph's modeled safety property. -/
theorem run_sound_single_pass : Target.RunSound ι :=
  run_sound_single_pass_of_exits (exitsYield_of_kept
    (fun _ _ _ _ _ _ _ hc => hc.startWrittenImpliesStated))

end Run

end Verification.TolerantFrames
