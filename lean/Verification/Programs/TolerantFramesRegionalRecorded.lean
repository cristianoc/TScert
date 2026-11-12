import Verification.Programs.TolerantFramesRegionalTyping
import Verification.Programs.TolerantFramesDriverVisit

/-! # The regional checks returned by a visit -/
namespace Verification.TolerantFrames
open Verification SinglePass ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open ProgramTyping LabelStore GraphCode GraphCode.ArgumentRegionGraph
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

/-- A returned regional state has an accepted derivation check and an accepted regional check
at the entry materialization joined with the step's facts. -/
theorem regionalAt_checks {env : WalkEnv ι G I} {l : Nat} {en : Entered ι} {sd : StepDone ι G}
    {rg : Regional} {a : Answered G} {incoming : Array (List RegionState)} {done : RegionalDone ι}
    (h : regionalAt G I env l en sd rg a incoming = .ok done) :
    regionalDerivChecked G I env.codes a.summaries.toList env.claimed[l]! env.nodes[l]!
      sd.st.stepK sd.st.stepDeriv = true ∧
    done.cEv = passRegionalEvidence env.claimed[l]! env.nodes[l]! sd.st.stepDeriv sd.st.stepEffect
      (regionalFacts (materialize en.entry (env.claimed[l]!).context.length
        (List.range (env.claimed[l]!).context.length) true).1 sd.st.stepK) ∧
    checkNode G I a.summaries.toList rg.Φ rg.regions done.table done.ft rg.exc l env.nodes[l]!
      done.cEv = true := by
  unfold regionalAt at h
  repeat' (first | split at h | extract_lets at h)
  all_goals first | cases h | skip
  all_goals
    have bool_true : ∀ b : Bool, (¬ (!b) = true) → b = true := by
      intro b hb; cases b <;> simp_all
    refine ⟨bool_true _ (by assumption), ?_⟩
    refine ⟨rfl, ?_⟩
    apply bool_true
    assumption

/-- At the start, a returned regional state contains only entry provenance
and has no fresh values, cells, or fields. -/
theorem regionalAt_start {env : WalkEnv ι G I} {l : Nat} {en : Entered ι} {sd : StepDone ι G}
    {rg : Regional} {a : Answered G} {incoming : Array (List RegionState)} {done : RegionalDone ι}
    (hstart : l = env.start) (h : regionalAt G I env l en sd rg a incoming = .ok done) :
    ArgumentPathTracking.checkEntry done.state.facts = true ∧
      done.state.values = [] ∧ done.state.cells = [] ∧ done.state.fields = [] := by
  unfold regionalAt at h
  extract_lets node c width st here sums ordinaryEv kHere at h
  repeat' (first | split at h | extract_lets at h)
  all_goals first | cases h | skip
  all_goals
    have hh : here.values = [] ∧ here.cells = [] ∧ here.fields = [] := by
      simp [here, hstart]
    refine ⟨?_, hh.1, ?_, ?_⟩
    · dsimp only [here]
      simp only [hstart, beq_self_eq_true, ↓reduceIte]
      simp only [ArgumentPathTracking.checkEntry, List.all_eq_true, List.mem_map]
      intro f hf
      obtain ⟨x, hx, rfl⟩ := hf
      have hx := List.mem_eraseDups.mp hx
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
      simp
    · change (if _ then here.cells else []) = []
      rw [hh.2.1]
      split <;> rfl
    · change List.filter _ here.fields = []
      rw [hh.2.2]
      rfl

/-- The graph's regional facts, from each label's own recorded check. -/
def recordedRegionFacts (w : SinglePass.Walk ι) : List (List ArgumentPathTracking.Fact) :=
  w.labels.toList.map fun r => (r.region.getD {}).facts

/-- The graph's freshness tables, from each label's own recorded check. -/
def recordedRegionFresh (w : SinglePass.Walk ι) (names : List String) : ArgumentRegionFresh.FreshTables :=
  ⟨w.labels.toList.map (fun r => (r.region.getD {}).values),
    w.labels.toList.map (fun r => (r.region.getD {}).cells),
    w.labels.toList.map (fun r => (r.region.getD {}).fields), names⟩

/-- A successful visit's record carries precisely the regional state returned by its exits. -/
theorem visitResult_region (σ : WalkState ι G) (l : Nat) (en : Entered ι) (sd : StepDone ι G)
    (ex : ExitsDone ι G) (hl : l < σ.walk.labels.size) :
    ((visitResult σ l en sd ex).walk.labels[l]?).bind (·.region) = ex.regional.map (·.state) := by
  simp only [visitResult, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hl]
  rfl

/-- The graph invariant connecting successful regional visits to one final
table: start facts and freshness, the checked node's inputs, sound summaries,
and agreement at the node and all its targets. -/
@[nospecialize] def RegionalVisitTables (ι : Type) [Labels ι] : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) after admits,
    RunPremises G I c after admits → ∀ r : RunWalkA G I c, WalkChecked c r →
      ∀ Φ regions exc, Target.regionOf c.regional = some (Φ, regions, exc) →
        ∃ (table : List (List ArgumentPathTracking.Fact)) (ft : ArgumentRegionFresh.FreshTables),
          (∃ (env : WalkEnv ι G I) (en : Entered ι) (sd : StepDone ι G) (rg : Regional)
            (a : Answered G) (incoming : Array (List RegionState)) (done : RegionalDone ι),
            c.start = env.start ∧ regionalAt G I env c.start en sd rg a incoming = .ok done ∧
            ArgumentPathTracking.atLabel table c.start = done.state.facts ∧
            factsAt ft.values c.start = done.state.values ∧ factsAt ft.cells c.start = done.state.cells ∧
            fieldsAt ft.fields c.start = done.state.fields) ∧
          ∀ l (hl : r.w.visited l), ∃ (env : WalkEnv ι G I) (σ : WalkState ι G) (en : Entered ι) (sd : StepDone ι G)
            (rg : Regional) (a : Answered G) (incoming : Array (List RegionState)) (done : RegionalDone ι),
            visitStep G I env σ l en = .ok sd ∧ regionalAt G I env l en sd rg a incoming = .ok done ∧
            env.codes = c.codes ∧ env.claimed[l]! = (r.node l hl).c ∧ env.nodes[l]! = (r.node l hl).node ∧
            en.entry = (r.node l hl).entry ∧ sd.st = (r.node l hl).st ∧
            rg.Φ = Φ ∧ rg.regions = regions ∧ rg.exc = exc ∧
            SummariesSound G I a.summaries.toList ∧ TablesAgree done.table table done.ft ft l (r.node l hl).node

/-- Successful regional visits supply the recorded checks once their tables
satisfy the graph invariant. -/
theorem regionsRecorded_of_visitTables (hv : RegionalVisitTables ι) : RegionsRecorded ι := by
  intro G I c after admits hp r hchk Φ regions exc hreg
  obtain ⟨table, ft, hstart, hnodes⟩ := hv G I c after admits hp r hchk Φ regions exc hreg
  obtain ⟨env0, en0, sd0, rg0, a0, incoming0, done0, hlabel, hrun, hfacts, hvalues, hcells, hfields⟩ := hstart
  obtain ⟨hs, hv, hc, hf⟩ := regionalAt_start hlabel hrun
  refine ⟨table, ft, hfacts ▸ hs, ?_, ?_, ?_⟩
  · simp only [hvalues, hcells, hv, hc, List.isEmpty_nil, Bool.and_self]
  · simp only [hfields, hf, List.isEmpty_nil]
  intro l hl
  obtain ⟨env, _, en, sd, rg, a, incoming, done, _, hr, _, hclaim, hnode, hentry, hst,
    hΦ, hregions, hexc, hsums, hagree⟩ := hnodes l hl
  obtain ⟨_, hev, hcheck⟩ := regionalAt_checks hr
  rw [hev, hclaim, hnode, hentry, hst, hΦ, hregions, hexc] at hcheck
  exact ⟨done.table, done.ft, a.summaries.toList, hsums, hcheck, hagree⟩

/-- Regional typing at visited nodes follows from their recorded derivation
checks and the local step bridge, at every admitted reassignment. -/
theorem regionsTyped_of_visitTables (hv : RegionalVisitTables ι) (hb : RegionalStepBridge ι) : RegionsTyped ι := by
  intro G I c after admits hp r hchk Φ regions exc hreg l hl
  obtain ⟨_, _, _, hnodes⟩ := hv G I c after admits hp r hchk Φ regions exc hreg
  obtain ⟨env, σ, en, sd, rg, a, incoming, done, hstep, hr, hcodes, hclaim, hnode, hentry, hst,
    _, _, _, hsums, _⟩ := hnodes l hl
  have hd := (regionalAt_checks hr).1
  rw [hcodes, hclaim, hnode, hst] at hd
  have localTyped : ∀ {H : NormalGraph ι} {J : InstanceImageCheck H} {pc : PassChecker H J}
      (rn : NodeChecked H J c.codes pc c.P r.w (List.range c.inputs.length) r.ctx l),
      regionalDerivChecked H J c.codes a.summaries.toList rn.c rn.node rn.st.stepK rn.st.stepDeriv = true →
      CodesSound H c.codes → SummariesSound H J a.summaries.toList →
      RegionalStepFacts H (passRegionalEvidenceOf rn) rn.st.stepK →
      (rn.st.stepDeriv = none → ControlFlow.entry (passRegionalEvidenceOf rn) = rn.c.context ∧
        ControlFlow.result (passRegionalEvidenceOf rn) = rn.c.type) →
      ControlFlow.entry (passRegionalEvidenceOf rn) = rn.c.context ∧
        RegionalTyped H (passRegionalEvidenceOf rn) rn.node := by
    intro H J pc rn hder hc hs hk hshape
    cases hd' : rn.st.stepDeriv with
    | none => exact regionalTyped_of_step rn (hshape hd') hc hk
    | some d =>
      unfold passRegionalEvidenceOf at hk ⊢
      rw [hd'] at hder hk ⊢
      exact regionalTyped_of_derivation hder hk hc hs
  have hshape : ControlFlow.entry (passRegionalEvidenceOf (r.node l hl)) = (r.node l hl).c.context := by
    cases hd' : (r.node l hl).st.stepDeriv with
    | none =>
      have hh := (hb G I env σ l en sd hstep G.env).2
      rw [hclaim, hnode, hentry, hst] at hh
      exact (hh hd').1
    | some d =>
      rw [hd'] at hd
      simp only [regionalDerivChecked, derivChecked, Bool.and_eq_true, beq_iff_eq] at hd
      simpa [passRegionalEvidenceOf, hd', passRegionalEvidence, ControlFlow.entry, NodeEvidence.expression] using hd.1.2
  refine ⟨hshape, ?_⟩
  intro η hη
  obtain ⟨pc', hpc'⟩ := scope_reassign hp.2.1 hη
  let rn := nodeChecked_reassign hpc' (r.node l hl)
  have hb' := hb G I env σ l en sd hstep η
  dsimp only at hb'
  rw [hclaim, hnode, hentry, hst] at hb'
  exact (localTyped rn
    ((regionalDerivChecked_reassign G η I c.codes a.summaries.toList _ _ _ _).trans hd)
    (codesSound_reassign hp.2.2.1 η)
    (Parametricity.summariesSound_reassign G η I hsums) (regionalStepFacts_of_relations rfl hb'.1) hb'.2).2

end Verification.TolerantFrames
