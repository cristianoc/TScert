import Verification.Programs.SinglePass

/-! # The walk under a bound its visits admit

The bound enters a walk at its footprint check alone (`boundOk`, in
`visitStep`) and at the no-return region that check reads (`deadRegion`):
entry, step and exit transfers read neither. So where every visit of the
walk with no bound passes the footprint check at a bound (`DriveAdmits`,
stated over `drive`'s own recursion), the walk at that bound is the walk
with no bound: the same visits, the same state, the same verdict
(`run_rebound`), by induction over `drive` (proposals by the pass,
section 4). -/

namespace Verification.SinglePass
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open HeapKnowledge (Knowledge)

variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

/-- The walk's environment with its bound and no-return region replaced. -/
def WalkEnv.rebound {G : NormalGraph ι} {images : InstanceImageCheck G} (env : WalkEnv ι G images)
    (bound : Option RunBound) (deadArr : Array Bool) : WalkEnv ι G images :=
  { env with bound, deadArr }

theorem stepRun_rebound (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) b d l entry
    fresh answers counts trace :
    stepRun G images (env.rebound b d) l entry fresh answers counts trace =
      stepRun G images env l entry fresh answers counts trace := rfl

theorem stepYields_rebound (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) b d l entry
    implies st answers :
    stepYields G images (env.rebound b d) l entry implies st answers = stepYields G images env l entry implies st answers :=
  rfl

omit [Instantiates ι] in
theorem thrownTyOf_rebound {G : NormalGraph ι} {images : InstanceImageCheck G} (env : WalkEnv ι G images) b d node :
    thrownTyOf (env.rebound b d) node = thrownTyOf env node := rfl

theorem returnRun_rebound (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) b d l entry st
    yields answers :
    returnRun G images (env.rebound b d) l entry st yields answers = returnRun G images env l entry st yields answers := by
  unfold returnRun
  simp only [WalkEnv.rebound]

omit [Hashable ι] [Instantiates ι] in
theorem boundOk_none (G : NormalGraph ι) (images : InstanceImageCheck G) codes d l node c entry sums stepK deriv :
    boundOk G images codes none d l node c entry sums stepK deriv = true := rfl

omit [Instantiates ι] in
/-- **A visit's check and record under a bound its step admits** (proved):
where the walk has no bound and the step's check at `b` and `d` passes, the
check and record at `b` are those with no bound. -/
theorem stepCheck_rebound (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images)
    (b : Option RunBound) (d : Array Bool) (l : Nat) (entry : State)
    (sums : List (ReadSummary ι)) (stepK : Knowledge) (deriv : ProgramCertificates.Evidence ι)
    (hnone : env.bound = none)
    (hok : boundOk G images env.codes b d l env.nodes[l]! env.claimed[l]! entry sums stepK deriv = true) :
    stepCheck G images (env.rebound b d) l entry sums stepK deriv
        (outFreshOf G images env.codes sums env.claimed[l]! env.nodes[l]! entry stepK deriv) =
      stepCheck G images env l entry sums stepK deriv
        (outFreshOf G images env.codes sums env.claimed[l]! env.nodes[l]! entry stepK deriv) := by
  have h1 := stepCheck_fst G images (env.rebound b d) l entry sums stepK deriv
  have h2 := stepCheck_fst G images env l entry sums stepK deriv
  simp only [WalkEnv.rebound] at h1
  rw [hok] at h1
  rw [hnone] at h2
  apply Prod.ext
  · simp only [WalkEnv.rebound] at h1 ⊢
    rw [h1, h2]; rfl
  · unfold stepCheck
    simp only [WalkEnv.rebound]
    by_cases hg : env.grading = true
    · simp only [hg, ite_true]
    · simp only [Bool.not_eq_true] at hg
      simp only [hg, Bool.false_eq_true, ite_false]

/-- **A step's visit does not see a bound its step admits** (proved): where
the walk with no bound's step at `l` passes the footprint check at the
bound `b` and its no-return region `d`, the visit under `b` is the visit with
no bound. -/
theorem visitStep_rebound (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images)
    (b : Option RunBound) (d : Array Bool) (σ : WalkState ι G) (l : Nat) (en : Entered ι)
    (hnone : env.bound = none)
    (hok : ∀ ms st stats a, stepRun G images env l en.entry en.fresh σ.answers en.counts en.trace = .ok (ms, st, stats, a) →
      boundOk G images env.codes b d l env.nodes[l]! env.claimed[l]! en.entry a.summaries.toList st.stepK
        (derivOf env.claimed[l]! env.nodes[l]! st) = true) :
    visitStep G images (env.rebound b d) σ l en = visitStep G images env σ l en := by
  unfold visitStep
  simp only [stepRun_rebound, stepYields_rebound, thrownTyOf_rebound, returnRun_rebound]
  cases hs : stepRun G images env l en.entry en.fresh σ.answers en.counts en.trace with
  | error stop => rfl
  | ok x =>
    obtain ⟨ms, st, stats, a⟩ := x
    have h1 := hok ms st stats a hs
    have h3 := stepCheck_rebound G images env b d l en.entry a.summaries.toList st.stepK
      (derivOf env.claimed[l]! env.nodes[l]! st) hnone h1
    simp only [WalkEnv.rebound] at h3 ⊢
    simp only [h3]
    rfl

omit [Instantiates ι] in
theorem visitEntry_rebound (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) b d σ l :
    visitEntry G images (env.rebound b d) σ l = visitEntry G images env σ l := by
  unfold visitEntry
  simp only [WalkEnv.rebound]
  rfl

omit [Instantiates ι] in
theorem keptDone_rebound {G : NormalGraph ι} {images : InstanceImageCheck G} (env : WalkEnv ι G images) b d l en sd :
    keptDone (env.rebound b d) l en sd = keptDone env l en sd := rfl

theorem visitExits_rebound (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) b d σ l en sd :
    visitExits G images (env.rebound b d) σ l en sd = visitExits G images env σ l en sd := by
  unfold visitExits
  simp only [WalkEnv.rebound]
  rfl

/-- The footprint check at `b` and `d` passes at `l`'s visit from `σ`, as
the walk with no bound makes it: its entry, its step, and the check over the
read summaries after the step. -/
def VisitAdmits (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images)
    (b : Option RunBound) (d : Array Bool) (σ : WalkState ι G) (l : Nat) : Prop :=
  ∀ en, visitEntry G images env σ l = .ok en →
    ∀ ms st stats a, stepRun G images env l en.entry en.fresh σ.answers en.counts en.trace = .ok (ms, st, stats, a) →
      boundOk G images env.codes b d l env.nodes[l]! env.claimed[l]! en.entry a.summaries.toList st.stepK
        (derivOf env.claimed[l]! env.nodes[l]! st) = true

theorem visit_rebound (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) b d σ l
    (hnone : env.bound = none) (h : VisitAdmits G images env b d σ l) :
    visit G images (env.rebound b d) σ l = visit G images env σ l := by
  unfold visit visitBody
  rw [visitEntry_rebound]
  cases he : visitEntry G images env σ l with
  | error _ => rfl
  | ok en =>
    simp only [visitStep_rebound G images env b d σ l en hnone (h en he), keptDone_rebound, visitExits_rebound]

/-- **Every visit of the walk with no bound passes the footprint check at
`b` and `d`**: by `drive`'s own recursion. -/
def DriveAdmits (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images)
    (b : Option RunBound) (d : Array Bool) : Nat → WalkState ι G → Prop
  | 0, _ => True
  | fuel + 1, σ => match σ.queue with
    | [] => True
    | l :: rest => VisitAdmits G images env b d { σ with queue := rest } l ∧
      match visit G images env { σ with queue := rest } l with
      | .ok σ' => DriveAdmits G images env b d fuel σ'
      | .error _ => True

/-- **The walk under a bound its every visit admits is the walk with no
bound** (proved): `drive` under `b` and its no-return region `d` makes the
same visits and ends in the same state, by induction over `drive`, each
visit by `visit_rebound` (the transfers read no bound). -/
theorem drive_rebound (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) b d
    (hnone : env.bound = none) :
    ∀ fuel σ, DriveAdmits G images env b d fuel σ →
      drive (visit G images (env.rebound b d)) fuel σ = drive (visit G images env) fuel σ := by
  intro fuel
  induction fuel with
  | zero => intro σ _; rfl
  | succ fuel ih =>
    intro σ h
    unfold drive
    unfold DriveAdmits at h
    split
    · rfl
    · rename_i l rest hq
      rw [hq] at h
      obtain ⟨hv, hrest⟩ := h
      rw [visit_rebound G images env b d _ l hnone hv]
      cases hvis : visit G images env { σ with queue := rest } l with
      | error _ => rfl
      | ok σ' =>
        rw [hvis] at hrest
        exact ih σ' hrest

/-! ### The visits' records

Under `grading` each visit records its step's local effect over the read
summaries that visit's step left (`stepCheck`), and the walk keeps every
record it was given (`Walk.visits`, appended to). So the footprint checks
read off the records of a walk that returned (`recordsAdmit`) are the checks
its visits would have made at the bound (`boundOk_eq_admits`): they give
`DriveAdmits` (`driveAdmits_of_records`). -/

/-- **A returned step and its record** (proved): the step was checked by
`stepRun` from the visit's entry, leaving the answers the footprint check
reads (`steppedAnswers`), and the visit's record is `stepCheck`'s over
their read summaries, at the freshness `outFreshOf` computes over them. -/
theorem visitStep_record (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images)
    (σ : WalkState ι G) (l : Nat) (en : Entered ι) (sd : StepDone ι G)
    (h : visitStep G images env σ l en = .ok sd) :
    (∃ ms stats, stepRun G images env l en.entry en.fresh σ.answers en.counts en.trace =
        .ok (ms, sd.st, stats, sd.steppedAnswers)) ∧
      sd.record = (stepCheck G images env l en.entry sd.steppedAnswers.summaries.toList sd.st.stepK
        (derivOf env.claimed[l]! env.nodes[l]! sd.st)
        (outFreshOf G images env.codes sd.steppedAnswers.summaries.toList env.claimed[l]! env.nodes[l]! en.entry
          sd.st.stepK (derivOf env.claimed[l]! env.nodes[l]! sd.st))).2 := by
  unfold visitStep at h
  split at h
  · cases h
  rename_i ms st stats a hrun
  repeat' (first | split at h | extract_lets at h)
  all_goals first | (cases h; exact ⟨⟨ms, stats, hrun⟩, rfl⟩) | cases h

/-- **A returned visit appends its record** (proved): the visit's entry and
step returned, and the walk's records after it are those before it with
the step's record, where it made one. -/
theorem visit_record (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images)
    (σ σ' : WalkState ι G) (l : Nat) (h : visit G images env σ l = .ok σ') :
    ∃ en sd, visitEntry G images env σ l = .ok en ∧ visitStep G images env σ l en = .ok sd ∧
      σ'.walk.visits = pushRecord σ.walk.visits sd.record := by
  unfold visit at h
  split at h
  · rename_i σ'' hb
    cases h
    unfold visitBody at hb
    split at hb
    · cases hb
    rename_i en hen
    split at hb
    · cases hb
    rename_i sd hsd
    split at hb
    · cases hb
    cases hb
    exact ⟨en, sd, hen, hsd, rfl⟩
  · cases h

/-- **The walk keeps its records** (proved): a `drive` that returns ends
with the records it started from, then the ones its visits appended. -/
theorem drive_visits (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) :
    ∀ fuel (σ σf : WalkState ι G), drive (visit G images env) fuel σ = .ok σf →
      ∃ more, σf.walk.visits = σ.walk.visits ++ more := by
  intro fuel
  induction fuel with
  | zero =>
    intro σ σf h
    unfold drive at h
    split at h
    · cases h; exact ⟨#[], by simp⟩
    · cases h
  | succ fuel ih =>
    intro σ σf h
    unfold drive at h
    split at h
    · cases h; exact ⟨#[], by simp⟩
    · rename_i l rest _
      split at h
      · rename_i σ' hv
        obtain ⟨more, hm⟩ := ih σ' σf h
        obtain ⟨en, sd, -, -, hp⟩ := visit_record G images env _ σ' l hv
        rw [hm, hp]
        cases sd.record with
        | none => exact ⟨more, rfl⟩
        | some r => exact ⟨#[r] ++ more, by simp [pushRecord]⟩
      · cases h

/-- **The records of a returned walk give `DriveAdmits`** (proved): under
`grading`, where the footprint check read off every record of the walk a
`drive` returns admits the bound `B` with the no-return region `d`, every
visit of that `drive` passes the footprint check at `B` and `d`: its record
is the one it appended (`visit_record`, `visitStep_record`), kept to the end
(`drive_visits`), and its check is that record's (`boundOk_eq_admits`). -/
theorem driveAdmits_of_records (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images)
    (B : RunBound) (d : Array Bool) (hg : env.grading = true) :
    ∀ fuel (σ σf : WalkState ι G), drive (visit G images env) fuel σ = .ok σf →
      recordsAdmit G env.nodes env.claimed B d σf.walk.visits = true →
      DriveAdmits G images env (some B) d fuel σ := by
  intro fuel
  induction fuel with
  | zero => intro σ σf _ _; trivial
  | succ fuel ih =>
    intro σ σf h hall
    unfold drive at h
    unfold DriveAdmits
    split
    · trivial
    · rename_i l rest hq
      rw [hq] at h
      simp only at h
      cases hv : visit G images env { σ with queue := rest } l with
      | error _ => rw [hv] at h; cases h
      | ok σ' =>
        rw [hv] at h
        simp only at h
        refine ⟨?_, ?_⟩
        · intro en' hen' ms st stats a hrun
          obtain ⟨en, sd, hen, hsd, hp⟩ := visit_record G images env _ σ' l hv
          rw [hen] at hen'
          injection hen' with he
          subst he
          obtain ⟨⟨ms0, stats0, hrun0⟩, hrec⟩ := visitStep_record G images env _ l en sd hsd
          rw [hrun0] at hrun
          cases hrun
          obtain ⟨more, hm⟩ := drive_visits G images env fuel σ' σf h
          have hmem : VisitRecord.of G images env.codes l env.nodes[l]! env.claimed[l]! en.entry
              sd.steppedAnswers.summaries.toList sd.st.stepK (derivOf env.claimed[l]! env.nodes[l]! sd.st)
              (outFreshOf G images env.codes sd.steppedAnswers.summaries.toList env.claimed[l]! env.nodes[l]!
                en.entry sd.st.stepK (derivOf env.claimed[l]! env.nodes[l]! sd.st)) ∈ σf.walk.visits := by
            rw [hm, hp, hrec]
            simp only [stepCheck, hg, ite_true, pushRecord, VisitRecord.of]
            exact Array.mem_append_left _ (Array.mem_push_self)
          unfold recordsAdmit at hall
          rw [boundOk_eq_admits]
          exact (Array.all_eq_true_iff_forall_mem.mp hall) _ hmem
        · exact ih σ' σf h hall

omit [Instantiates ι] in
/-- The setup under a bound is the setup with no bound, its environment at
that bound and its no-return region (proved). -/
theorem setup_rebound (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) (fuel : Nat)
    (P : Program) (claims : List (PointClaim ι)) (start : Nat) (inputs : List (Ty ι)) (goal : Goal ι)
    (assertions : List (Nat × Knowledge)) (cuts : List Nat)
    (candidates : List (Nat × List HeapKnowledge.Candidate)) (entryIndices : List HeapKnowledge.IndexAtom)
    (suggestions : List (Sequent ι)) (known : List (ProgramCertificates.Evidence ι)) (codes : CodeEntry ι → Bool)
    (aliases : List (ι × ι)) (passChecker : PassChecker G images)
    (answers : Answered G) (reference : Array Knowledge) (debugNode : Nat)
    (B : RunBound)
    (givenImplies : Array (List (PromiseCalls.Implication ι))) (givenArgs : Array (List Nat))
    (ensures : List HeapKnowledge.IndexFact) (givenInputs : Array (List (Nat × Nat)))
    (entrySeparation : HeapSeparation.Separation) (observe : Option Nat) (tracing observeEntry : Bool)
    (regional : Option Regional) (grading : Bool) :
    setup G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode (some B) givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional grading =
      (setup G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode none givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional grading).map fun (env, σ) =>
          (env.rebound (some B) (deadRegion G P.toArray claims.toArray (some B)), σ) := by
  unfold setup
  dsimp only
  -- (the first two refusals decided by hand: `split`'s simplification of
  -- the whole setup exceeds its step budget there)
  by_cases h1 : (claims.toArray.size != (List.toArray P).size) = true
  · rw [ite_eq_left h1, ite_eq_left h1]; rfl
  rw [ite_eq_right h1, ite_eq_right h1]
  by_cases h2 : (!P.all fun node => ObjectCoherence.sourceTerm node.expression) = true
  · rw [ite_eq_left h2, ite_eq_left h2]; rfl
  rw [ite_eq_right h2, ite_eq_right h2]
  repeat' (first | rfl | split)

omit [Instantiates ι] in
/-- The setup's environment holds the bound and the grading it was given,
and the program's nodes and claims (proved). -/
theorem setup_env (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) (fuel : Nat)
    (P : Program) (claims : List (PointClaim ι)) (start : Nat) (inputs : List (Ty ι)) (goal : Goal ι)
    (assertions : List (Nat × Knowledge)) (cuts : List Nat)
    (candidates : List (Nat × List HeapKnowledge.Candidate)) (entryIndices : List HeapKnowledge.IndexAtom)
    (suggestions : List (Sequent ι)) (known : List (ProgramCertificates.Evidence ι)) (codes : CodeEntry ι → Bool)
    (aliases : List (ι × ι)) (passChecker : PassChecker G images)
    (answers : Answered G) (reference : Array Knowledge) (debugNode : Nat)
    (givenImplies : Array (List (PromiseCalls.Implication ι))) (givenArgs : Array (List Nat))
    (ensures : List HeapKnowledge.IndexFact) (givenInputs : Array (List (Nat × Nat)))
    (entrySeparation : HeapSeparation.Separation) (observe : Option Nat) (tracing observeEntry : Bool)
    (regional : Option Regional) (grading : Bool) (bnd : Option RunBound)
    (env : WalkEnv ι G images) (σ0 : WalkState ι G)
    (h : setup G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode bnd givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional grading = .ok (env, σ0)) :
    env.bound = bnd ∧ env.grading = grading ∧ env.nodes = P.toArray ∧ env.claimed = claims.toArray := by
  unfold setup at h
  dsimp only at h
  repeat' (first | (cases h; exact ⟨rfl, rfl, rfl, rfl⟩) | (cases h; done) | split at h)

/-- **The walk under a bound its every visit admits** (proved): where every
visit of the walk with no bound passes the footprint check at `B` and the
no-return region `B` gives (`DriveAdmits`), the walk at `B` is the walk with
no bound, its state and the nodes it reaches. -/
theorem runWalk_rebound (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) (fuel : Nat)
    (P : Program) (claims : List (PointClaim ι)) (start : Nat) (inputs : List (Ty ι)) (goal : Goal ι)
    (assertions : List (Nat × Knowledge)) (cuts : List Nat)
    (candidates : List (Nat × List HeapKnowledge.Candidate)) (entryIndices : List HeapKnowledge.IndexAtom)
    (suggestions : List (Sequent ι)) (known : List (ProgramCertificates.Evidence ι)) (codes : CodeEntry ι → Bool)
    (aliases : List (ι × ι)) (passChecker : PassChecker G images)
    (answers : Answered G) (reference : Array Knowledge) (debugNode : Nat)
    (givenImplies : Array (List (PromiseCalls.Implication ι))) (givenArgs : Array (List Nat))
    (ensures : List HeapKnowledge.IndexFact) (givenInputs : Array (List (Nat × Nat)))
    (entrySeparation : HeapSeparation.Separation) (observe : Option Nat) (tracing observeEntry : Bool)
    (regional : Option Regional) (grading : Bool) (B : RunBound)
    (hadm : ∀ env σ0, setup G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode none givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional grading = .ok (env, σ0) →
      DriveAdmits G images env (some B) (deadRegion G P.toArray claims.toArray (some B)) (env.n + 1) σ0) :
    runWalk G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode (some B) givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional grading =
      runWalk G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode none givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional grading := by
  unfold runWalk
  rw [setup_rebound]
  cases hs : setup G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode none givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional grading with
  | error _ => rfl
  | ok x =>
    obtain ⟨env, σ0⟩ := x
    have hnone := (setup_env _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ none env σ0 hs).1
    simp only [Except.map, bind, Except.bind]
    rw [show (env.rebound (some B) (deadRegion G P.toArray claims.toArray (some B))).n = env.n from rfl,
      drive_rebound G images env _ _ hnone _ σ0 (hadm env σ0 hs)]
    rfl

/-- **The pass's run under a bound every visit admits** (proved): its
verdict, counts, answers and trace are those of the run with no bound. -/
theorem run_rebound (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) (fuel : Nat)
    (P : Program) (claims : List (PointClaim ι)) (start : Nat) (inputs : List (Ty ι)) (goal : Goal ι)
    (assertions : List (Nat × Knowledge)) (cuts : List Nat)
    (candidates : List (Nat × List HeapKnowledge.Candidate)) (entryIndices : List HeapKnowledge.IndexAtom)
    (suggestions : List (Sequent ι)) (known : List (ProgramCertificates.Evidence ι)) (codes : CodeEntry ι → Bool)
    (aliases : List (ι × ι)) (passChecker : PassChecker G images)
    (answers : Answered G) (reference : Array Knowledge) (debugNode : Nat)
    (givenImplies : Array (List (PromiseCalls.Implication ι))) (givenArgs : Array (List Nat))
    (ensures : List HeapKnowledge.IndexFact) (givenInputs : Array (List (Nat × Nat)))
    (entrySeparation : HeapSeparation.Separation) (observe : Option Nat) (tracing observeEntry : Bool)
    (regional : Option Regional) (B : RunBound) (grading : Bool)
    (hadm : ∀ env σ0, setup G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode none givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional grading = .ok (env, σ0) →
      DriveAdmits G images env (some B) (deadRegion G P.toArray claims.toArray (some B)) (env.n + 1) σ0) :
    run G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode (some B) givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional grading =
      run G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode none givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional grading := by
  unfold run
  rw [runWalk_rebound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ grading B hadm]

/-- **The direct run at a bound its records admit** (proved): where the
pass's walk with no bound under `grading` returns, and the footprint checks
read off its records (`recordsAdmit`) admit the bound `B` with the no-return
region `B` gives, the run at `B` is the run with no bound, its verdict,
counts, answers and trace (`driveAdmits_of_records`, `run_rebound`). -/
theorem run_rebound_of_records (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) (fuel : Nat)
    (P : Program) (claims : List (PointClaim ι)) (start : Nat) (inputs : List (Ty ι)) (goal : Goal ι)
    (assertions : List (Nat × Knowledge)) (cuts : List Nat)
    (candidates : List (Nat × List HeapKnowledge.Candidate)) (entryIndices : List HeapKnowledge.IndexAtom)
    (suggestions : List (Sequent ι)) (known : List (ProgramCertificates.Evidence ι)) (codes : CodeEntry ι → Bool)
    (aliases : List (ι × ι)) (passChecker : PassChecker G images)
    (answers : Answered G) (reference : Array Knowledge) (debugNode : Nat)
    (givenImplies : Array (List (PromiseCalls.Implication ι))) (givenArgs : Array (List Nat))
    (ensures : List HeapKnowledge.IndexFact) (givenInputs : Array (List (Nat × Nat)))
    (entrySeparation : HeapSeparation.Separation) (observe : Option Nat) (tracing observeEntry : Bool)
    (regional : Option Regional) (B : RunBound) (σf : WalkState ι G) (reach : Nat)
    (hw : runWalk G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode none givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional true = .ok (σf, reach))
    (hrec : recordsAdmit G P.toArray claims.toArray B (deadRegion G P.toArray claims.toArray (some B))
        σf.walk.visits = true) :
    run G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode (some B) givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional true =
      run G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode none givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional true := by
  apply run_rebound
  intro env σ0 hs
  obtain ⟨-, hg, hn, hc⟩ := setup_env _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ none env σ0 hs
  unfold runWalk at hw
  rw [hs] at hw
  simp only [bind, Except.bind] at hw
  cases hd : drive (visit G images env) (env.n + 1) σ0 with
  | error _ => rw [hd] at hw; cases hw
  | ok σ =>
    rw [hd] at hw
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, -⟩ := hw
    rw [← hn, ← hc] at hrec ⊢
    exact driveAdmits_of_records G images env B _ hg _ σ0 σ hd hrec

/-! ### Grading erased

A walk that grades and the same walk that does not make the same checks
and the same visits: they differ in the records alone. -/

/-- The environment with no grading. -/
def WalkEnv.ungraded {G : NormalGraph ι} {images : InstanceImageCheck G} (env : WalkEnv ι G images) :
    WalkEnv ι G images :=
  { env with grading := false }

/-- The walk's state with no records. -/
def WalkState.unrecorded {G : NormalGraph ι} (σ : WalkState ι G) : WalkState ι G :=
  { σ with walk := { σ.walk with visits := #[] } }

/-- A step's result with no record. -/
def StepDone.unrecorded {G : NormalGraph ι} (sd : StepDone ι G) : StepDone ι G :=
  { sd with record := none }

omit [Instantiates ι] in
theorem visitEntry_ungraded (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) σ l :
    visitEntry G images env.ungraded σ.unrecorded l = visitEntry G images env σ l := by
  unfold visitEntry
  simp only [WalkEnv.ungraded, WalkState.unrecorded]
  rfl

omit [Instantiates ι] in
theorem keptDone_ungraded {G : NormalGraph ι} {images : InstanceImageCheck G} (env : WalkEnv ι G images) l en
    (sd : StepDone ι G) : keptDone env.ungraded l en sd.unrecorded = (keptDone env l en sd).unrecorded := rfl

theorem visitExits_ungraded (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) σ l en sd :
    visitExits G images env.ungraded σ.unrecorded l en sd.unrecorded = visitExits G images env σ l en sd := by
  unfold visitExits
  simp only [WalkEnv.ungraded, WalkState.unrecorded, StepDone.unrecorded]
  rfl

theorem stepRun_ungraded (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) :
    stepRun G images env.ungraded = stepRun G images env := by
  rfl

theorem stepYields_ungraded (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) :
    stepYields G images env.ungraded = stepYields G images env := by
  rfl

theorem returnRun_ungraded (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) :
    returnRun G images env.ungraded = returnRun G images env := by
  funext l entry st yields answers
  unfold returnRun
  simp only [WalkEnv.ungraded]

omit [Instantiates ι] in
theorem thrownTyOf_ungraded {G : NormalGraph ι} {images : InstanceImageCheck G} (env : WalkEnv ι G images) :
    thrownTyOf env.ungraded = thrownTyOf env := by
  rfl

/-- **A step graded makes the step ungraded's check** (proved): the graded
step's result is the ungraded one's with its record, by `stepCheck_fst`. -/
theorem visitStep_ungraded (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images)
    (σ : WalkState ι G) (l : Nat) (en : Entered ι) :
    (visitStep G images env σ l en).map StepDone.unrecorded = visitStep G images env.ungraded σ.unrecorded l en := by
  have hc : ∀ entry sums stepK deriv,
      stepCheck G images env.ungraded l entry sums stepK deriv
          (outFreshOf G images env.ungraded.codes sums env.ungraded.claimed[l]! env.ungraded.nodes[l]! entry stepK
            deriv) =
        ((stepCheck G images env l entry sums stepK deriv
          (outFreshOf G images env.codes sums env.claimed[l]! env.nodes[l]! entry stepK deriv)).1, none) := by
    intro entry sums stepK deriv
    rw [stepCheck_fst]
    unfold stepCheck
    simp only [WalkEnv.ungraded, Bool.false_eq_true, ite_false] <;> rfl
  unfold visitStep
  simp only [stepRun_ungraded, stepYields_ungraded, returnRun_ungraded, thrownTyOf_ungraded,
    WalkState.unrecorded]
  cases hs : stepRun G images env l en.entry en.fresh σ.answers en.counts en.trace with
  | error stop => rfl
  | ok x =>
    obtain ⟨ms, st, stats, a⟩ := x
    simp only [hc]
    simp only [WalkEnv.ungraded, apply_ite (Except.map StepDone.unrecorded)]
    repeat' (first | rfl |
      (split <;> rename_i hsplit <;> first | rw [ite_eq_left hsplit] | rw [ite_eq_right hsplit] | simp only [hsplit] | skip))


/-- **A visit graded makes the visit ungraded** (proved): from a state with
no records, the ungraded visit returns the graded one's state without its
records, or stops where it stops. -/
theorem visit_ungraded (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images)
    (σ : WalkState ι G) (l : Nat) :
    (visit G images env σ l).map WalkState.unrecorded = visit G images env.ungraded σ.unrecorded l := by
  have hs := visitStep_ungraded G images env σ l
  unfold visit visitBody
  rw [visitEntry_ungraded]
  cases he : visitEntry G images env σ l with
  | error stop => rfl
  | ok en =>
    simp only
    have hs := hs en
    cases hsd : visitStep G images env σ l en with
    | error stop =>
      rw [hsd] at hs
      rw [← hs]
      rfl
    | ok sd =>
      rw [hsd] at hs
      rw [← hs]
      simp only [Except.map]
      rw [keptDone_ungraded, visitExits_ungraded]
      cases hx : visitExits G images env σ l en (keptDone env l en sd) with
      | error stop => rfl
      | ok ex => rfl

/-- **The walk graded makes the walk ungraded** (proved): `drive` from a
state, graded, returns the state the ungraded `drive` returns from it with no
records, without its records, or stops where it stops (by induction over
`drive`, each visit by `visit_ungraded`). -/
theorem drive_ungraded (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) :
    ∀ fuel (σ : WalkState ι G),
      (drive (visit G images env) fuel σ).map WalkState.unrecorded =
        drive (visit G images env.ungraded) fuel σ.unrecorded := by
  intro fuel
  induction fuel with
  | zero =>
    intro σ
    unfold drive
    simp only [WalkState.unrecorded]
    split <;> rfl
  | succ fuel ih =>
    intro σ
    unfold drive
    simp only [show (WalkState.unrecorded σ).queue = σ.queue from rfl]
    split
    · rfl
    · rename_i l rest _
      have hv := visit_ungraded G images env { σ with queue := rest } l
      rw [show { WalkState.unrecorded σ with queue := rest } = WalkState.unrecorded { σ with queue := rest } from rfl,
        ← hv]
      cases visit G images env { σ with queue := rest } l with
      | error stop => rfl
      | ok σ' => exact ih σ'


omit [Instantiates ι] in
/-- The setup graded is the setup ungraded, its environment grading
(proved). -/
theorem setup_graded (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) (fuel : Nat)
    (P : Program) (claims : List (PointClaim ι)) (start : Nat) (inputs : List (Ty ι)) (goal : Goal ι)
    (assertions : List (Nat × Knowledge)) (cuts : List Nat)
    (candidates : List (Nat × List HeapKnowledge.Candidate)) (entryIndices : List HeapKnowledge.IndexAtom)
    (suggestions : List (Sequent ι)) (known : List (ProgramCertificates.Evidence ι)) (codes : CodeEntry ι → Bool)
    (aliases : List (ι × ι)) (passChecker : PassChecker G images)
    (answers : Answered G) (reference : Array Knowledge) (debugNode : Nat)
    (bound : Option RunBound)
    (givenImplies : Array (List (PromiseCalls.Implication ι))) (givenArgs : Array (List Nat))
    (ensures : List HeapKnowledge.IndexFact) (givenInputs : Array (List (Nat × Nat)))
    (entrySeparation : HeapSeparation.Separation) (observe : Option Nat) (tracing observeEntry : Bool)
    (regional : Option Regional) :
    setup G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode bound givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional true =
      (setup G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode bound givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional false).map fun (env, σ) => ({ env with grading := true }, σ) := by
  unfold setup
  dsimp only
  by_cases h1 : (claims.toArray.size != (List.toArray P).size) = true
  · rw [ite_eq_left h1, ite_eq_left h1]; rfl
  rw [ite_eq_right h1, ite_eq_right h1]
  by_cases h2 : (!P.all fun node => ObjectCoherence.sourceTerm node.expression) = true
  · rw [ite_eq_left h2, ite_eq_left h2]; rfl
  rw [ite_eq_right h2, ite_eq_right h2]
  repeat' (first | rfl | split)

omit [Instantiates ι] in
/-- The state the first visit starts from holds no records (proved). -/
theorem setup_unrecorded (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) (fuel : Nat)
    (P : Program) (claims : List (PointClaim ι)) (start : Nat) (inputs : List (Ty ι)) (goal : Goal ι)
    (assertions : List (Nat × Knowledge)) (cuts : List Nat)
    (candidates : List (Nat × List HeapKnowledge.Candidate)) (entryIndices : List HeapKnowledge.IndexAtom)
    (suggestions : List (Sequent ι)) (known : List (ProgramCertificates.Evidence ι)) (codes : CodeEntry ι → Bool)
    (aliases : List (ι × ι)) (passChecker : PassChecker G images)
    (answers : Answered G) (reference : Array Knowledge) (debugNode : Nat)
    (bound : Option RunBound)
    (givenImplies : Array (List (PromiseCalls.Implication ι))) (givenArgs : Array (List Nat))
    (ensures : List HeapKnowledge.IndexFact) (givenInputs : Array (List (Nat × Nat)))
    (entrySeparation : HeapSeparation.Separation) (observe : Option Nat) (tracing observeEntry : Bool)
    (regional : Option Regional) (grading : Bool)
    (env : WalkEnv ι G images) (σ0 : WalkState ι G)
    (h : setup G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode bound givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional grading = .ok (env, σ0)) : σ0.unrecorded = σ0 := by
  unfold setup at h
  dsimp only at h
  repeat' (first | (cases h; rfl) | (cases h; done) | split at h)

/-- **The walk graded is the walk ungraded with records** (proved): the
graded walk returns the ungraded walk's state with its records, or stops
where it stops (`setup_graded`, `drive_ungraded`). -/
theorem runWalk_ungraded (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) (fuel : Nat)
    (P : Program) (claims : List (PointClaim ι)) (start : Nat) (inputs : List (Ty ι)) (goal : Goal ι)
    (assertions : List (Nat × Knowledge)) (cuts : List Nat)
    (candidates : List (Nat × List HeapKnowledge.Candidate)) (entryIndices : List HeapKnowledge.IndexAtom)
    (suggestions : List (Sequent ι)) (known : List (ProgramCertificates.Evidence ι)) (codes : CodeEntry ι → Bool)
    (aliases : List (ι × ι)) (passChecker : PassChecker G images)
    (answers : Answered G) (reference : Array Knowledge) (debugNode : Nat)
    (bound : Option RunBound)
    (givenImplies : Array (List (PromiseCalls.Implication ι))) (givenArgs : Array (List Nat))
    (ensures : List HeapKnowledge.IndexFact) (givenInputs : Array (List (Nat × Nat)))
    (entrySeparation : HeapSeparation.Separation) (observe : Option Nat) (tracing observeEntry : Bool)
    (regional : Option Regional) :
    (runWalk G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode bound givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional true).map (fun (σ, reach) => (σ.unrecorded, reach)) =
      runWalk G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode bound givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional false := by
  unfold runWalk
  rw [setup_graded]
  cases hs : setup G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode bound givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional false with
  | error stop => rfl
  | ok x =>
    obtain ⟨env, σ0⟩ := x
    have hg := (setup_env _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ env σ0 hs).2.1
    have h0 := setup_unrecorded _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ env σ0 hs
    have he : ({ env with grading := true } : WalkEnv ι G images).ungraded = env := by
      cases env; simp_all [WalkEnv.ungraded]
    have hd := drive_ungraded G images { env with grading := true } (env.n + 1) σ0
    rw [he, h0] at hd
    simp only [Except.map, bind, Except.bind]
    rw [← hd]
    cases drive (visit G images { env with grading := true }) (env.n + 1) σ0 with
    | error stop => rfl
    | ok σ => rfl

/-- **The pass graded decides as the pass ungraded** (proved): the run with
`grading` has the run's verdict, answers and trace without it, and the same
counts but for the records (`runWalk_ungraded`). -/
theorem run_ungraded (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) (fuel : Nat)
    (P : Program) (claims : List (PointClaim ι)) (start : Nat) (inputs : List (Ty ι)) (goal : Goal ι)
    (assertions : List (Nat × Knowledge)) (cuts : List Nat)
    (candidates : List (Nat × List HeapKnowledge.Candidate)) (entryIndices : List HeapKnowledge.IndexAtom)
    (suggestions : List (Sequent ι)) (known : List (ProgramCertificates.Evidence ι)) (codes : CodeEntry ι → Bool)
    (aliases : List (ι × ι)) (passChecker : PassChecker G images)
    (answers : Answered G) (reference : Array Knowledge) (debugNode : Nat)
    (bound : Option RunBound)
    (givenImplies : Array (List (PromiseCalls.Implication ι))) (givenArgs : Array (List Nat))
    (ensures : List HeapKnowledge.IndexFact) (givenInputs : Array (List (Nat × Nat)))
    (entrySeparation : HeapSeparation.Separation) (observe : Option Nat) (tracing observeEntry : Bool)
    (regional : Option Regional) :
    (run G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode bound givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional true).1 = (run G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode bound givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional false).1 ∧
    { (run G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode bound givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional true).2.1 with grades := #[] } =
      { (run G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode bound givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional false).2.1 with grades := #[] } ∧
    (run G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode bound givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional true).2.2 = (run G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode bound givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional false).2.2 := by
  have hw := runWalk_ungraded G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices
    suggestions known codes aliases passChecker answers reference debugNode bound givenImplies givenArgs ensures
    givenInputs entrySeparation observe tracing observeEntry regional
  unfold run
  rw [← hw]
  cases runWalk G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode bound givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional true with
  | error stop => exact ⟨rfl, rfl, rfl⟩
  | ok x => exact ⟨rfl, rfl, rfl⟩

end Verification.SinglePass
