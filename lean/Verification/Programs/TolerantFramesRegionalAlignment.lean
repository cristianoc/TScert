import Verification.Programs.TolerantFramesRegionalRecorded
import Verification.Programs.TolerantFramesDriverSetup
import Verification.Programs.TolerantFramesVisitSummaries
import Verification.Programs.TolerantFramesExitWidths

/-! # Alignment with the accepted driver's record -/
namespace Verification.TolerantFrames
open Verification SinglePass ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open ProgramTyping LabelStore GraphCode GraphCode.ArgumentRegionGraph
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

/-- The local evidence obligation for every successful visit matching a final
label record. The prefix relates that visit's regional summaries to the accepted
run's summaries; the tables agree with the recorded graph at the node and its targets. -/
@[nospecialize] def RegionalVisitEvidence (ι : Type) [Labels ι] : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I)
    (env : WalkEnv ι G I) (σ : WalkState ι G) (reach : Nat) (rg : Regional),
    RunCall.walk c = .ok (σ, reach) → reach ≤ σ.walk.visited →
    EnvFacts c env → RecInv c env σ → env.regional = some rg →
    ∀ l, visB σ.walk l = true → ∀ (before : WalkState ι G) (en : Entered ι)
      (sd : StepDone ι G) (ex : ExitsDone ι G) (done : RegionalDone ι),
      visitEntry G I env before l = .ok en → visitStep G I env before l en = .ok sd →
      visitExits G I env before l en sd = .ok ex →
      regionalAt G I env l en sd rg (exitsYields G I env l en sd).2 before.regionIn = .ok done →
      σ.walk.labels[l]? = some (LabelWalk.ofVisit before.fresh en sd (some done.state)) →
      SumsPrefix (exitsYields G I env l en sd).2 σ.answers ∧
      TablesAgree done.table (recordedRegionFacts σ.walk) done.ft
        (recordedRegionFresh σ.walk rg.names) l env.nodes[l]!

/-- The regional tables of a recorded visit agree with the final graph's
tables. The visit's exit summaries must be a prefix of the final sound table. -/
@[nospecialize] def RegionalRecordedTableAgreement (ι : Type) [Labels ι] : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I)
    (env : WalkEnv ι G I) (σ : WalkState ι G) (reach : Nat) (rg : Regional),
    RunCall.walk c = .ok (σ, reach) → reach ≤ σ.walk.visited →
    EnvFacts c env → RecInv c env σ → env.regional = some rg →
    SummariesSound G I σ.answers.summaries.toList →
    ∀ l, visB σ.walk l = true → ∀ (before : WalkState ι G) (en : Entered ι)
      (sd : StepDone ι G) (ex : ExitsDone ι G) (done : RegionalDone ι),
      visitEntry G I env before l = .ok en → visitStep G I env before l en = .ok sd →
      visitExits G I env before l en sd = .ok ex →
      regionalAt G I env l en sd rg (exitsYields G I env l en sd).2 before.regionIn = .ok done →
      σ.walk.labels[l]? = some (LabelWalk.ofVisit before.fresh en sd (some done.state)) →
      SumsPrefix ex.answers σ.answers →
      TablesAgree done.table (recordedRegionFacts σ.walk) done.ft
        (recordedRegionFresh σ.walk rg.names) l env.nodes[l]!

/-- A checked walk is the accepted run's final driver record. Its invariant,
start visit, regional configuration and sound final summaries are consequences
of execution and the run premises. -/
theorem checkedWalk_final {c : Target.RunCall G I} {after : Answered G} {admits}
    (hp : RunPremises G I c after admits) {r : RunWalkA G I c} (hc : WalkChecked c r)
    {Φ regions exc} (hr : Target.regionOf c.regional = some (Φ, regions, exc)) :
    ∃ (env : WalkEnv ι G I) (σ : WalkState ι G) (reach : Nat) (rg : Regional),
      RunCall.walk c = .ok (σ, reach) ∧ reach ≤ σ.walk.visited ∧
      EnvFacts c env ∧ RecInv c env σ ∧ env.regional = some rg ∧
      c.start = env.start ∧ visB σ.walk c.start = true ∧
      rg.Φ = Φ ∧ rg.regions = regions ∧ rg.exc = exc ∧
      SummariesSound G I σ.answers.summaries.toList ∧
      r.w = ofPass σ.walk (passHeads c) ∧
      ∀ l (hl : r.w.visited l), (σ.walk.labels[l]?).bind (·.stepped) = some (r.node l hl).st := by
  obtain ⟨_, _, σ, reach, hw, heq, hsteps⟩ := hc
  obtain ⟨σ', reach', hw', hle, ha⟩ := walk_of_accepts walkStopsRefuse hp.1
  have hh := hw.symm.trans hw'
  cases Except.ok.inj hh
  have hv : VisitsRecord ι := visitsRecord_of (visitsRest_of (exitsPushOk_of exitsWidth)
    (visitsSettle_of (visitStepPrefix_of_exitStep exitStepPrefix)) visitsImplications) visitExits_answers_prefix
  obtain ⟨env, henv, hi, hreach⟩ := walk_inv setupRecords_of hv hw
  obtain ⟨rg, hrg, hΦ⟩ := Option.map_eq_some_iff.mp hr
  have hparts : rg.Φ = Φ ∧ rg.regions = regions ∧ rg.exc = exc := by
    simpa only [Prod.mk.injEq] using hΦ
  obtain ⟨hΦ, hregions, hexc⟩ := hparts
  refine ⟨env, σ, reach, rg, hw, hle, henv, hi, henv.regional.trans hrg,
    henv.startLabel.symm, ?_, hΦ, hregions, hexc, ha ▸ hp.2.2.2.1, heq, hsteps⟩
  exact hi.all_visited henv (hreach ▸ hle) c.start henv.start.1 henv.start.2

/-- A matching label record determines the chosen node's entry and step.
The claim and graph node are fixed by the exit trace and setup. -/
theorem checkedWalk_nodeAlignment {c : Target.RunCall G I} {r : RunWalkA G I c}
    (hc : WalkChecked c r) {env : WalkEnv ι G I} (he : EnvFacts c env)
    {σ : WalkState ι G} (hw : r.w = ofPass σ.walk (passHeads c))
    (hsteps : ∀ l (hl : r.w.visited l),
      (σ.walk.labels[l]?).bind (·.stepped) = some (r.node l hl).st)
    {l : Nat} (hl : r.w.visited l) {fresh : Nat} {en : Entered ι} {sd : StepDone ι G}
    {region : Option RegionState}
    (hr : σ.walk.labels[l]? = some (LabelWalk.ofVisit fresh en sd region)) :
    env.codes = c.codes ∧ env.claimed[l]! = (r.node l hl).c ∧
      env.nodes[l]! = (r.node l hl).node ∧ en.entry = (r.node l hl).entry ∧ sd.st = (r.node l hl).st := by
  obtain ⟨_, hnodes, _⟩ := hc
  obtain ⟨raw, env', before, en', sd', ex', _, _, hn, hcl, _, _, _, _, _, _, _,
    hnode, hclaim, _⟩ := (hnodes l hl).2
  have hs := hsteps l hl
  rw [hr] at hs
  have hentry := (r.node l hl).hentry
  have hwentry := congrArg (fun w : Walk ι => w.entry l) hw
  have hentry' : (ofPass σ.walk (passHeads c)).entry l = en.entry := by
    simp [ofPass, hr, LabelWalk.ofVisit]
  exact ⟨he.codes, by rw [he.claims, hclaim, hcl], by rw [he.nodes, hnode, hn],
    (hentry.trans (hwentry.trans hentry')).symm, Option.some.inj hs⟩

/-- Every actually recorded regional visit has sound input summaries when
the final table is sound. The same existential supplies the visit and its prefix. -/
theorem RecInv.regionalWitnessSound {c : Target.RunCall G I} {env : WalkEnv ι G I}
    {σ : WalkState ι G} (hi : RecInv c env σ)
    (hsums : SummariesSound G I σ.answers.summaries.toList)
    {l : Nat} (hl : visB σ.walk l = true) {rg : Regional} (hreg : env.regional = some rg) :
    ∃ (before : WalkState ι G) (en : Entered ι) (sd : StepDone ι G) (ex : ExitsDone ι G)
      (done : RegionalDone ι),
      visitEntry G I env before l = .ok en ∧ visitStep G I env before l en = .ok sd ∧
      visitExits G I env before l en sd = .ok ex ∧
      regionalAt G I env l en sd rg (exitsYields G I env l en sd).2 before.regionIn = .ok done ∧
      σ.walk.labels[l]? = some (LabelWalk.ofVisit before.fresh en sd (some done.state)) ∧
      SummariesSound G I (exitsYields G I env l en sd).2.summaries.toList := by
  obtain ⟨before, en, sd, ex, done, he, hs, hx, hd, hr, hp⟩ := hi.regionalWitness hl hreg
  exact ⟨before, en, sd, ex, done, he, hs, hx, hd, hr,
    fun s hm => hsums s (((visitExits_regional_prefix hx).trans hp).mem s hm)⟩

/-- The driver and chosen-node alignment leaves are proved. The remaining
local leaf states summary-prefix and regional-table agreement at matching visits. -/
theorem regionalWalkAlignment (hevidence : RegionalVisitEvidence ι) : RegionalWalkAlignment ι := by
  intro G I c after admits hp r hc Φ regions exc hr
  have final := checkedWalk_final hp hc hr
  obtain ⟨env, σ, reach, rg, hw, hle, henv, hi, hrg, hstart, hstartVis,
    hΦ, hregions, hexc, hsums, heq, hsteps⟩ := final
  have hvis : ∀ l, r.w.visited l → visB σ.walk l = true := by
    intro l hl
    rw [heq] at hl
    exact (ofPass_visited _ _ _).mp hl
  refine ⟨env, σ, rg, hi, hrg, hstart, hstartVis, hΦ, hregions, hexc, hvis, ?_⟩
  intro l hl before en sd ex done hen hsd hex hd hrecord
  have aligned := checkedWalk_nodeAlignment hc henv heq hsteps hl hrecord
  have evidence := hevidence G I c env σ reach rg hw hle henv hi hrg l (hvis l hl)
    before en sd ex done hen hsd hex hd hrecord
  refine ⟨aligned.1, aligned.2.1, aligned.2.2.1, aligned.2.2.2.1, aligned.2.2.2.2, ?_, ?_⟩
  · exact fun s hs => hsums s (evidence.1.mem s hs)
  · rw [← aligned.2.2.1]
    exact evidence.2

/-- The graph uses the actual recorded visits, whose summaries are sound.
Only agreement of their regional tables remains a local premise. -/
theorem regionalVisitTables_of_recordedAgreement (ht : RegionalRecordedTableAgreement ι) :
    RegionalVisitTables ι := by
  intro G I c after admits hp r hc Φ regions exc hr
  obtain ⟨env, σ, reach, rg, hw, hle, henv, hi, hrg, hstart, hstartVis,
    hΦ, hregions, hexc, hsums, heq, hsteps⟩ := checkedWalk_final hp hc hr
  obtain ⟨before, en, sd, ex, done, _, _, _, hd, hrecord, _⟩ := hi.regionalWitness hstartVis hrg
  refine ⟨recordedRegionFacts σ.walk, recordedRegionFresh σ.walk rg.names,
    ⟨env, en, sd, rg, _, before.regionIn, done, hstart, hd, recordedRegion_at hrecord rfl rg.names⟩, ?_⟩
  intro l hl
  have hv : visB σ.walk l = true := (ofPass_visited _ _ _).mp (heq ▸ hl)
  obtain ⟨before, en, sd, ex, done, hen, hsd, hex, hd, hrecord, hprefix⟩ := hi.regionalWitness hv hrg
  obtain ⟨hcodes, hclaim, hnode, hentry, hstep⟩ :=
    checkedWalk_nodeAlignment hc henv heq hsteps hl hrecord
  have hs : SummariesSound G I (exitsYields G I env l en sd).2.summaries.toList :=
    fun s hm => hsums s (((visitExits_regional_prefix hex).trans hprefix).mem s hm)
  have hagree := ht G I c env σ reach rg hw hle henv hi hrg hsums l hv
    before en sd ex done hen hsd hex hd hrecord hprefix
  rw [hnode] at hagree
  exact ⟨env, before, en, sd, rg, _, before.regionIn, done, hsd, hd,
    hcodes, hclaim, hnode, hentry, hstep, hΦ, hregions, hexc, hs, hagree⟩

end Verification.TolerantFrames
