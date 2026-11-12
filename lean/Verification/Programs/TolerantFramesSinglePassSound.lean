import Verification.Programs.TolerantFramesExitStructural
import Verification.Programs.TolerantFramesVisitSummaries
import Verification.Programs.TolerantFramesRegionalTyping
import Verification.Programs.TolerantFramesRegionalReadback
import Verification.Programs.TolerantFramesDriverSetup
import Verification.Programs.TolerantFramesExitWidths

/-! # Tolerant frames: the single pass's graph theorem

`run_sound_single_pass` composes the per-node side's graph theorem
(`run_sound_pass`) with the walk side's record soundness and checks
(`recordsSound_of`, `recordsChecked_of`) and `exitsYield_of_yields`. Its four
premises state start-contract projection, source and initial yield judgments,
and final-world realization. -/
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

/-- The graph theorem under start-contract projection, exit-yield judgments,
initial-yield judgments, and their final-world realization. -/
theorem run_sound_single_pass
    (startWrittenSound : ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I)
      after admits, RunPremises G I c after admits → ∀ r : RunWalkA G I c,
        WalkChecked c r → ExitChecks.StartWrittenImpliesStated r)
    (yieldSourcesJudged : ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I)
      after admits, RunPremises G I c after admits → ∀ r : RunWalkA G I c,
        WalkChecked c r → ∀ η, admits η → ∀ l (hl : r.w.visited l) (s : ExitChecks.Site c r l hl),
        ∀ ys, ExitYieldSource s.env l s.en s.sd s.sd.yields ys →
          ExitYieldsJudged (reassign G η) r.w (List.range c.inputs.length) l
            (r.node l hl).node (r.node l hl).c (r.node l hl).entry (r.node l hl).st ys)
    (initialYieldsJudged : ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I)
      after admits, RunPremises G I c after admits → ∀ r : RunWalkA G I c,
        WalkChecked c r → ∀ η, admits η → ∀ l (hl : r.w.visited l) (s : ExitChecks.Site c r l hl),
          ExitYieldsJudged (reassign G η) r.w (List.range c.inputs.length) l
            (r.node l hl).node (r.node l hl).c (r.node l hl).entry (r.node l hl).st s.ysA)
    (realization : ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I)
      after admits, RunPremises G I c after admits → ∀ r : RunWalkA G I c,
        WalkChecked c r → ∀ η, admits η → ∀ l (hl : r.w.visited l) (s : ExitChecks.Site c r l hl),
          ExitChecks.Realization s η) : Target.RunSound ι :=
  run_sound_single_pass_of_exits
    (exitsYield_of_yields startWrittenSound yieldSourcesJudged initialYieldsJudged realization)

end Run

end Verification.TolerantFrames
