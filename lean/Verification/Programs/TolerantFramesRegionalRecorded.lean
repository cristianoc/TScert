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

/-- Type checking leaves the regional result intact. -/
theorem exitTypes_regional {env : SinglePass.WalkEnv ι G I} {l : Nat} {en : SinglePass.Entered ι}
    {sd : SinglePass.StepDone ι G} {out : Thunk HeapKnowledge.Knowledge} {t : Target} {tc : PointClaim ι}
    {Γ : List (ProgramTyping.Ty ι)} {names : List Nat} {store : SinglePass.Store} {pushed handler : Bool}
    {observed : Option BranchRefinement.Observation} {first : Bool} {diff : List (Nat × Nat)}
    {a b : SinglePass.ExitsDone ι G} {et : SinglePass.ExitTyped ι}
    (h : SinglePass.exitTypes G I env l en sd out t tc Γ names store pushed handler observed first diff a = .ok (b, et)) :
    b.regional = a.regional := by
  unfold SinglePass.exitTypes at h
  repeat' (first | split at h | extract_lets at h)
  all_goals cases h <;> rfl

/-- The head check leaves the regional result intact. -/
theorem headExit_regional {env : SinglePass.WalkEnv ι G I} {l : Nat} {t : Target} {tc : PointClaim ι}
    {Γ : List (ProgramTyping.Ty ι)} {names : List Nat} {store : SinglePass.Store} {pushed vacuous : Bool}
    {carried : List (PromiseCalls.Implication ι)} {a b : SinglePass.ExitsDone ι G}
    (h : SinglePass.headExit G I env l t tc Γ names store pushed vacuous carried a = .ok b) :
    b.regional = a.regional := by
  unfold SinglePass.headExit at h
  repeat' (first | split at h | extract_lets at h)
  all_goals cases h <;> rfl

/-- The assertion check leaves the regional result intact. -/
theorem assertionExit_regional {env : SinglePass.WalkEnv ι G I} {l : Nat} {t : Target} {tc : PointClaim ι}
    {Γe : Thunk (List (ProgramTyping.Ty ι))} {names : List Nat} {store : SinglePass.Store} {pushed vacuous : Bool}
    {observed : Option BranchRefinement.Observation} {a b : SinglePass.ExitsDone ι G}
    (h : SinglePass.assertionExit G env l t tc Γe names store pushed observed vacuous a = .ok b) :
    b.regional = a.regional := by
  unfold SinglePass.assertionExit at h
  repeat' (first | split at h | extract_lets at h)
  all_goals cases h <;> rfl

/-- A successful exit preserves the complete regional result. -/
theorem exitStep_regional {env : WalkEnv ι G I} {l : Nat} {en : Entered ι}
    {sd : StepDone ι G} {ys : List (PromiseCalls.Yield ι)} {out : Thunk HeapKnowledge.Knowledge}
    {a b : ExitsDone ι G} {e : Exit × Nat}
    (h : exitStep G I env l en sd ys out a e = .ok b) : b.regional = a.regional := by
  unfold exitStep at h
  extract_lets ex first node c width entry st t pushed observed handler pushedNames tr a0 Γ names store unsatΓ vacuous Γe read Γr at h
  split at h
  · cases h
  split at h
  · cases h
  extract_lets diff u a2 typed at h
  generalize ht : typed = T at h
  split at h
  · cases h
  rename_i a1 et
  simp only [typed] at ht
  have hp : a2.regional = a.regional := by
    dsimp only [a2, a0]
    split <;> split <;> rfl
  have hp1 : a1.regional = a.regional := by
    split at ht
    · cases ht; exact hp
    · exact (exitTypes_regional ht).trans hp
  extract_lets freshImpl record at h
  split at h
  · simp only [Except.map] at h
    split at h
    · cases h
    · rename_i a3 hhead
      cases h
      exact (headExit_regional hhead).trans hp1
  · split at h
    · cases h
    rename_i a3 ha
    split at h
    cases h
    exact (assertionExit_regional ha).trans hp1

/-- Every exit in the fold preserves the regional check's result. -/
theorem exitsFold_regional {env : WalkEnv ι G I} {l : Nat} {en : Entered ι}
    {sd : StepDone ι G} {ys : List (PromiseCalls.Yield ι)} {out : Thunk HeapKnowledge.Knowledge}
    (es : List (Exit × Nat)) (a b : ExitsDone ι G)
    (h : es.foldlM (exitStep G I env l en sd ys out) a = .ok b) : b.regional = a.regional := by
  induction es generalizing a with
  | nil => cases h; rfl
  | cons e es ih =>
    rw [List.foldlM_cons] at h
    cases he : exitStep G I env l en sd ys out a e with
    | error stop => rw [he] at h; cases h
    | ok a' =>
      rw [he] at h
      exact (ih a' h).trans (exitStep_regional he)

/-- A successful exits visit has performed its regional check. -/
theorem visitExits_regionalCheck {env : WalkEnv ι G I} {σ : WalkState ι G} {l : Nat}
    {en : Entered ι} {sd : StepDone ι G} {ex : ExitsDone ι G} {rg : Regional}
    (hreg : env.regional = some rg) (h : visitExits G I env σ l en sd = .ok ex) :
    ∃ done, regionalAt G I env l en sd rg (exitsYields G I env l en sd).2 σ.regionIn = .ok done ∧
      ex.regional = some done := by
  unfold visitExits at h
  rw [hreg] at h
  cases hr : regionalAt G I env l en sd rg (exitsYields G I env l en sd).2 σ.regionIn with
  | error why =>
    simp only [hr, Except.map] at h
    cases h
  | ok done =>
    refine ⟨done, rfl, ?_⟩
    simp only [hr, Except.map] at h
    exact exitsFold_regional _ _ _ h

/-- The driver invariant supplies every visited label's successful step
and regional check, together with its retained complete exit result. -/
theorem RecInv.regionalWitness {c : Target.RunCall G I} {env : WalkEnv ι G I} {σ : WalkState ι G}
    (hi : RecInv c env σ) {l : Nat} (hl : visB σ.walk l = true) {rg : Regional}
    (hreg : env.regional = some rg) :
    ∃ (before : WalkState ι G) (en : Entered ι) (sd : StepDone ι G) (ex : ExitsDone ι G)
      (done : RegionalDone ι),
      visitEntry G I env before l = .ok en ∧ visitStep G I env before l en = .ok sd ∧
      visitExits G I env before l en sd = .ok ex ∧
      regionalAt G I env l en sd rg (exitsYields G I env l en sd).2 before.regionIn = .ok done ∧
      σ.walk.labels[l]? = some (LabelWalk.ofVisit before.fresh en sd (some done.state)) ∧
      SumsPrefix ex.answers σ.answers := by
  obtain ⟨before, en, sd, ex, he, hs, hx, hr, hp⟩ := hi.origins l hl
  obtain ⟨done, hd, hdone⟩ := visitExits_regionalCheck hreg hx
  exact ⟨before, en, sd, ex, done, he, hs, hx, hd, by simpa [hdone] using hr, hp⟩

/-- The exits' incoming table is the regional check's output table. -/
theorem visitExits_regionalInputs {env : WalkEnv ι G I} {σ : WalkState ι G} {l : Nat}
    {en : Entered ι} {sd : StepDone ι G} {ex : ExitsDone ι G} {rg : Regional} {done : RegionalDone ι}
    (hreg : env.regional = some rg) (h : visitExits G I env σ l en sd = .ok ex)
    (hd : regionalAt G I env l en sd rg (exitsYields G I env l en sd).2 σ.regionIn = .ok done) :
    ex.regionIn = done.regionIn := by
  unfold visitExits at h
  simp only [hreg, hd, Except.map] at h
  exact exitsFold_regionIn _ _ _ h

/-- A recorded regional visit reads the final incoming list at a non-head,
and every state it accumulates remains in the final incoming table. -/
theorem RecInv.regionalInputWitness {c : Target.RunCall G I} {env : WalkEnv ι G I}
    {σ : WalkState ι G} (hi : RecInv c env σ) {l : Nat} (hl : visB σ.walk l = true)
    {rg : Regional} (hreg : env.regional = some rg) :
    ∃ (before : WalkState ι G) (en : Entered ι) (sd : StepDone ι G) (ex : ExitsDone ι G)
      (done : RegionalDone ι),
      visitEntry G I env before l = .ok en ∧ visitStep G I env before l en = .ok sd ∧
      visitExits G I env before l en sd = .ok ex ∧
      regionalAt G I env l en sd rg (exitsYields G I env l en sd).2 before.regionIn = .ok done ∧
      σ.walk.labels[l]? = some (LabelWalk.ofVisit before.fresh en sd (some done.state)) ∧
      SumsPrefix ex.answers σ.answers ∧
      before.regionIn.size = env.n ∧
      (envHead env l = false → before.regionIn[l]? = σ.regionIn[l]?) ∧
      ∀ (t : Nat) (e : RegionState), e ∈ done.regionIn[t]! → e ∈ σ.regionIn[t]! := by
  obtain ⟨before, en, sd, ex, he, hs, hx, hr, hp, hb, hf, hm⟩ := hi.regionalOrigins l hl
  obtain ⟨done, hd, hdone⟩ := visitExits_regionalCheck hreg hx
  refine ⟨before, en, sd, ex, done, he, hs, hx, hd, ?_, hp, hb, hf, ?_⟩
  · simpa [hdone] using hr
  · rw [← visitExits_regionalInputs hreg hx hd]
    exact hm

/-- Componentwise containment of the four regional tables. -/
def RegionBelow (r s : RegionState) : Prop :=
  (∀ f ∈ r.facts, f ∈ s.facts) ∧ (∀ i ∈ r.values, i ∈ s.values) ∧
  (∀ i ∈ r.cells, i ∈ s.cells) ∧ (∀ p ∈ r.fields, p ∈ s.fields)

theorem RegionBelow.trans {r s t : RegionState} (hrs : RegionBelow r s) (hst : RegionBelow s t) :
    RegionBelow r t :=
  ⟨fun f hf => hst.1 f (hrs.1 f hf), fun i hi => hst.2.1 i (hrs.2.1 i hi),
    fun i hi => hst.2.2.1 i (hrs.2.2.1 i hi), fun p hp => hst.2.2.2 p (hrs.2.2.2 p hp)⟩

/-- A recorded state retains provenance and fresh values from its entry,
and contains only cells and fields of that entry. -/
theorem regionalAt_state {env : WalkEnv ι G I} {l : Nat} {en : Entered ι} {sd : StepDone ι G}
    {rg : Regional} {a : Answered G} {incoming : Array (List RegionState)} {done : RegionalDone ι}
    (h : regionalAt G I env l en sd rg a incoming = .ok done) :
    let here : RegionState := if l == env.start then
      { facts := ((rg.regions.map fun (x : Footprints.ArgumentStoreRegion) =>
          (⟨x.position, []⟩ : Footprints.ArgumentStoreRegion)).eraseDups).map fun x => ⟨x.position, x⟩ }
      else if env.isHead[l]! then ((rg.heads[l]?).join).getD {}
      else RegionState.meet (incoming[l]!)
    done.state.facts = here.facts ∧ done.state.values = here.values ∧ RegionBelow done.state here := by
  unfold regionalAt at h
  extract_lets node c width st here sums ordinaryEv kHere cEv t0 F C Fs at h
  repeat' (first | split at h | extract_lets at h)
  all_goals first | cases h | skip
  all_goals
    refine ⟨rfl, rfl, fun _ h => h, fun _ h => h, ?_, ?_⟩
    · dsimp only [C]
      split
      · exact fun _ h => h
      · simp
    · exact fun _ h => (List.mem_filter.mp h).1

/-- The field-name table is fixed by the regional configuration. -/
theorem regionalAt_names {env : WalkEnv ι G I} {l : Nat} {en : Entered ι} {sd : StepDone ι G}
    {rg : Regional} {a : Answered G} {incoming : Array (List RegionState)} {done : RegionalDone ι}
    (h : regionalAt G I env l en sd rg a incoming = .ok done) : done.ft.names = rg.names := by
  unfold regionalAt at h
  repeat' (first | split at h | extract_lets at h)
  all_goals cases h <;> rfl

/-- The state stored at a label, empty when no regional check is recorded. -/
@[nospecialize] def recordedRegionState (w : SinglePass.Walk ι) (l : Nat) : RegionState :=
  ((w.labels[l]?).bind (·.region)).getD {}

/-- A visited non-head's recorded state is within every incoming regional
state, because its incoming list is frozen at its visit. -/
theorem RecInv.regional_nonhead_bound {c : Target.RunCall G I} {env : WalkEnv ι G I}
    {σ : WalkState ι G} (hi : RecInv c env σ) {l : Nat} (hl : visB σ.walk l = true)
    {rg : Regional} (hreg : env.regional = some rg) (hstart : l ≠ env.start)
    (hhead : envHead env l = false) {e : RegionState} (he : e ∈ σ.regionIn[l]!) :
    RegionBelow (recordedRegionState σ.walk l) e := by
  obtain ⟨before, en, sd, ex, done, _, _, _, hd, hr, _, _, hf, _⟩ := hi.regionalInputWitness hl hreg
  have hh : env.isHead[l]! = false := by
    unfold envHead at hhead
    rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
    exact hhead
  have hb := (regionalAt_state hd).2.2
  simp only [beq_eq_false_iff_ne.mpr hstart, Bool.false_eq_true, ↓reduceIte, hh] at hb
  have hin : before.regionIn[l]! = σ.regionIn[l]! := by
    simp only [getElem!_def, hf hhead]
  rw [hin] at hb
  have hmeet : RegionBelow (RegionState.meet σ.regionIn[l]!) e := meet_sub he
  simpa only [recordedRegionState, hr, LabelWalk.ofVisit, Option.bind_some, Option.getD_some] using hb.trans hmeet

/-- A visited head other than the start records only facts from its given
regional state; its cell and field filters can reduce that state. -/
theorem RecInv.regional_head_bound {c : Target.RunCall G I} {env : WalkEnv ι G I}
    {σ : WalkState ι G} (hi : RecInv c env σ) {l : Nat} (hl : visB σ.walk l = true)
    {rg : Regional} (hreg : env.regional = some rg) (hstart : l ≠ env.start)
    (hhead : envHead env l = true) :
    RegionBelow (recordedRegionState σ.walk l) ((rg.heads[l]?).join.getD {}) := by
  obtain ⟨before, en, sd, ex, done, _, _, _, hd, hr, _, _, _, _⟩ := hi.regionalInputWitness hl hreg
  have hh : env.isHead[l]! = true := by
    unfold envHead at hhead
    rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
    exact hhead
  have hb := (regionalAt_state hd).2.2
  simpa only [beq_eq_false_iff_ne.mpr hstart, Bool.false_eq_true, ↓reduceIte, hh,
    recordedRegionState, hr, LabelWalk.ofVisit, Option.bind_some, Option.getD_some] using hb

/-- Every successor of a visited node is visited once the record accounts
for all reached labels. This includes handler targets. -/
theorem RecInv.successor_visited {c : Target.RunCall G I} {env : WalkEnv ι G I}
    {σ : WalkState ι G} (hi : RecInv c env σ) (hE : EnvFacts c env)
    (hle : (env.reached.toList.filter id).length ≤ σ.walk.visited)
    {l t : Nat} (hl : visB σ.walk l = true) (ht : t ∈ exitsOf env l) :
    visB σ.walk t = true :=
  hi.all_visited hE hle t (hi.exits l hl t ht)
    (hE.closed l t (hi.visR l hl).2 ht (hi.exits l hl t ht))

/-- The graph's regional facts, from each label's own recorded check. -/
def recordedRegionFacts (w : SinglePass.Walk ι) : List (List ArgumentPathTracking.Fact) :=
  w.labels.toList.map fun r => (r.region.getD {}).facts

/-- The graph's freshness tables, from each label's own recorded check. -/
def recordedRegionFresh (w : SinglePass.Walk ι) (names : List String) : ArgumentRegionFresh.FreshTables :=
  ⟨w.labels.toList.map (fun r => (r.region.getD {}).values),
    w.labels.toList.map (fun r => (r.region.getD {}).cells),
    w.labels.toList.map (fun r => (r.region.getD {}).fields), names⟩

omit [Labels ι] in
/-- Reading a recorded label reads its four regional components. -/
theorem recordedRegion_at {w : SinglePass.Walk ι} {l : Nat} {r : LabelWalk ι} {state : RegionState}
    (hr : w.labels[l]? = some r) (hs : r.region = some state) (names : List String) :
    ArgumentPathTracking.atLabel (recordedRegionFacts w) l = state.facts ∧
    factsAt (recordedRegionFresh w names).values l = state.values ∧
    factsAt (recordedRegionFresh w names).cells l = state.cells ∧
    fieldsAt (recordedRegionFresh w names).fields l = state.fields := by
  simp [recordedRegionFacts, recordedRegionFresh, ArgumentPathTracking.atLabel, factsAt, fieldsAt,
    List.getD_eq_getElem?_getD, List.getElem?_map, hr, hs]

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
      have hh := (hb G I env σ l en sd hstep rg a incoming done hr G.env).2
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
  have hb' := hb G I env σ l en sd hstep rg a incoming done hr η
  dsimp only at hb'
  rw [hclaim, hnode, hentry, hst] at hb'
  exact (localTyped rn
    ((regionalDerivChecked_reassign G η I c.codes a.summaries.toList _ _ _ _).trans hd)
    (codesSound_reassign hp.2.2.1 η)
    (Parametricity.summariesSound_reassign G η I hsums) (regionalStepFacts_of_relations rfl hb'.1) hb'.2).2

end Verification.TolerantFrames
