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
    (bound : Option (Footprints.Closed × Bool × Bool)) (deadArr : Array Bool) : WalkEnv ι G images :=
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

/-- **A step's visit does not see a bound its step admits** (proved): where
the walk with no bound's step at `l` passes the footprint check at the
bound `b` and its no-return region `d`, the visit under `b` is the visit with
no bound. -/
theorem visitStep_rebound (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images)
    (b : Option (Footprints.Closed × Bool × Bool)) (d : Array Bool) (σ : WalkState ι G) (l : Nat) (en : Entered ι)
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
    have h2 : boundOk G images env.codes env.bound env.deadArr l env.nodes[l]! env.claimed[l]! en.entry
        a.summaries.toList st.stepK (derivOf env.claimed[l]! env.nodes[l]! st) = true := by
      rw [hnone]; rfl
    simp only [WalkEnv.rebound] at h1 ⊢
    simp only [h1, hnone, boundOk_none]
    rfl

omit [Instantiates ι] in
theorem visitEntry_rebound (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) b d σ l :
    visitEntry G images (env.rebound b d) σ l = visitEntry G images env σ l := by
  unfold visitEntry
  simp only [WalkEnv.rebound]
  rfl

theorem visitExits_rebound (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) b d σ l en sd :
    visitExits G images (env.rebound b d) σ l en sd = visitExits G images env σ l en sd := by
  unfold visitExits
  simp only [WalkEnv.rebound]
  rfl

/-- The footprint check at `b` and `d` passes at `l`'s visit from `σ`, as
the walk with no bound makes it: its entry, its step, and the check over the
read summaries after the step. -/
def VisitAdmits (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images)
    (b : Option (Footprints.Closed × Bool × Bool)) (d : Array Bool) (σ : WalkState ι G) (l : Nat) : Prop :=
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
    simp only [visitStep_rebound G images env b d σ l en hnone (h en he), visitExits_rebound]

/-- **Every visit of the walk with no bound passes the footprint check at
`b` and `d`**: by `drive`'s own recursion. -/
def DriveAdmits (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images)
    (b : Option (Footprints.Closed × Bool × Bool)) (d : Array Bool) : Nat → WalkState ι G → Prop
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

omit [Instantiates ι] in
/-- The setup under a bound is the setup with no bound, its environment at
that bound and its no-return region (proved). -/
theorem setup_rebound (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) (fuel : Nat)
    (P : Program) (claims : List (PointClaim ι)) (start : Nat) (inputs : List (Ty ι)) (goal : Goal ι)
    (assertions : List (Nat × Knowledge)) (cuts : List Nat)
    (candidates : List (Nat × List HeapKnowledge.IndexAtom)) (entryIndices : List HeapKnowledge.IndexAtom)
    (suggestions : List (Sequent ι)) (known : List (ProgramCertificates.Evidence ι)) (codes : CodeEntry ι → Bool)
    (aliases : List (ι × ι)) (passChecker : PassChecker G images)
    (answers : Answered G) (reference : Array Knowledge) (debugNode : Nat)
    (B : Footprints.Closed × Bool × Bool)
    (givenImplies : Array (List (PromiseCalls.Implication ι))) (givenArgs : Array (List Nat))
    (ensures : List HeapKnowledge.IndexFact) (givenInputs : Array (List (Nat × Nat)))
    (entrySeparation : HeapSeparation.Separation) (observe : Option Nat) (tracing observeEntry : Bool)
    (regional : Option Regional) :
    setup G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode (some B) givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional =
      (setup G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode none givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional).map fun (env, σ) =>
          (env.rebound (some B) (deadRegion G P.toArray claims.toArray (some B)), σ) := by
  unfold setup
  dsimp only
  repeat' (first | rfl | split)

omit [Instantiates ι] in
/-- The setup's environment holds the bound it was given (proved). -/
theorem setup_bound (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) (fuel : Nat)
    (P : Program) (claims : List (PointClaim ι)) (start : Nat) (inputs : List (Ty ι)) (goal : Goal ι)
    (assertions : List (Nat × Knowledge)) (cuts : List Nat)
    (candidates : List (Nat × List HeapKnowledge.IndexAtom)) (entryIndices : List HeapKnowledge.IndexAtom)
    (suggestions : List (Sequent ι)) (known : List (ProgramCertificates.Evidence ι)) (codes : CodeEntry ι → Bool)
    (aliases : List (ι × ι)) (passChecker : PassChecker G images)
    (answers : Answered G) (reference : Array Knowledge) (debugNode : Nat)
    (givenImplies : Array (List (PromiseCalls.Implication ι))) (givenArgs : Array (List Nat))
    (ensures : List HeapKnowledge.IndexFact) (givenInputs : Array (List (Nat × Nat)))
    (entrySeparation : HeapSeparation.Separation) (observe : Option Nat) (tracing observeEntry : Bool)
    (regional : Option Regional) (bnd : Option (Footprints.Closed × Bool × Bool)) (env : WalkEnv ι G images) (σ0 : WalkState ι G)
    (h : setup G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode bnd givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional = .ok (env, σ0)) : env.bound = bnd := by
  unfold setup at h
  dsimp only at h
  repeat' (first | (cases h; rfl) | (cases h; done) | split at h)

/-- **The walk under a bound its every visit admits** (proved): where every
visit of the walk with no bound passes the footprint check at `B` and the
no-return region `B` gives (`DriveAdmits`), the walk at `B` is the walk with
no bound, its state and the nodes it reaches. -/
theorem runWalk_rebound (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) (fuel : Nat)
    (P : Program) (claims : List (PointClaim ι)) (start : Nat) (inputs : List (Ty ι)) (goal : Goal ι)
    (assertions : List (Nat × Knowledge)) (cuts : List Nat)
    (candidates : List (Nat × List HeapKnowledge.IndexAtom)) (entryIndices : List HeapKnowledge.IndexAtom)
    (suggestions : List (Sequent ι)) (known : List (ProgramCertificates.Evidence ι)) (codes : CodeEntry ι → Bool)
    (aliases : List (ι × ι)) (passChecker : PassChecker G images)
    (answers : Answered G) (reference : Array Knowledge) (debugNode : Nat)
    (givenImplies : Array (List (PromiseCalls.Implication ι))) (givenArgs : Array (List Nat))
    (ensures : List HeapKnowledge.IndexFact) (givenInputs : Array (List (Nat × Nat)))
    (entrySeparation : HeapSeparation.Separation) (observe : Option Nat) (tracing observeEntry : Bool)
    (regional : Option Regional) (B : Footprints.Closed × Bool × Bool)
    (hadm : ∀ env σ0, setup G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode none givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional = .ok (env, σ0) →
      DriveAdmits G images env (some B) (deadRegion G P.toArray claims.toArray (some B)) (env.n + 1) σ0) :
    runWalk G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode (some B) givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional =
      runWalk G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode none givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional := by
  unfold runWalk
  rw [setup_rebound]
  cases hs : setup G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode none givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional with
  | error _ => rfl
  | ok x =>
    obtain ⟨env, σ0⟩ := x
    have hnone := setup_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ none env σ0 hs
    simp only [Except.map, bind, Except.bind]
    rw [show (env.rebound (some B) (deadRegion G P.toArray claims.toArray (some B))).n = env.n from rfl,
      drive_rebound G images env _ _ hnone _ σ0 (hadm env σ0 hs)]
    rfl

/-- **The pass's run under a bound every visit admits** (proved): its
verdict, counts, answers and trace are those of the run with no bound. -/
theorem run_rebound (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) (fuel : Nat)
    (P : Program) (claims : List (PointClaim ι)) (start : Nat) (inputs : List (Ty ι)) (goal : Goal ι)
    (assertions : List (Nat × Knowledge)) (cuts : List Nat)
    (candidates : List (Nat × List HeapKnowledge.IndexAtom)) (entryIndices : List HeapKnowledge.IndexAtom)
    (suggestions : List (Sequent ι)) (known : List (ProgramCertificates.Evidence ι)) (codes : CodeEntry ι → Bool)
    (aliases : List (ι × ι)) (passChecker : PassChecker G images)
    (answers : Answered G) (reference : Array Knowledge) (debugNode : Nat)
    (givenImplies : Array (List (PromiseCalls.Implication ι))) (givenArgs : Array (List Nat))
    (ensures : List HeapKnowledge.IndexFact) (givenInputs : Array (List (Nat × Nat)))
    (entrySeparation : HeapSeparation.Separation) (observe : Option Nat) (tracing observeEntry : Bool)
    (regional : Option Regional) (B : Footprints.Closed × Bool × Bool) (grading : Bool)
    (hadm : ∀ env σ0, setup G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode none givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional = .ok (env, σ0) →
      DriveAdmits G images env (some B) (deadRegion G P.toArray claims.toArray (some B)) (env.n + 1) σ0) :
    run G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode (some B) givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional grading =
      run G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
        codes aliases passChecker answers reference debugNode none givenImplies givenArgs ensures givenInputs
        entrySeparation observe tracing observeEntry regional grading := by
  unfold run
  rw [runWalk_rebound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ B hadm]

end Verification.SinglePass
