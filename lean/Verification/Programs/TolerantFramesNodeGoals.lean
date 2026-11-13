import Verification.Programs.TolerantFramesNodeReturns
import Verification.Programs.TolerantFramesNodeWalk

/-! # Tolerant frames: a guard's and an assertion's goal at a return

`NodeAccepted.ret` asks every value of the claim's type to meet the result
type, while a type guard's goal (`x is T`) and an assertion function's
(`asserts x is T`) read the promised argument, which the state after the
step fixes: the argument's slots (`argName`) and their types as the step's
yields refine them. `returnCheck` checks that promise as the certificate
checker's `checkReturnResult` does (`ControlFlow.ReturnOk`): the answer's
type Boolean (`undefined` for an assertion), and the answer impossible or
the argument, at a slot holding its name, refined within the promise by a
subtype answer. `returnOk_of_check` reads that check; `goalHolds_at` is
`ControlFlow.goal_return` at the state's own level; `goalHolds_of_return`
gives the goal at the state after the step, under the step's yields holding
(`YieldsOk`, pass change D2) and the subtype answers' soundness
(`SubtypeAnswersSound`, pass change D5). -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules

section Goals
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

/-- `returnCheck`'s yields at the entry's slots: each yield at every slot
holding its target's name. -/
def passReturnYields (entry : SinglePass.State) (yields : List (PromiseCalls.Yield ι)) : List (PromiseCalls.Yield ι) :=
  yields.flatMap fun y => match entry.names[y.target]? with
    | some nm => (entry.names.zipIdx.filter (·.1 == nm)).map fun (_, j) => { y with target := j }
    | none => [y]

/-- `returnCheck`'s slots holding the promised argument's name. -/
def passHeld (entry : SinglePass.State) (argName : Option Nat) : List Nat :=
  match argName with
  | some a => (entry.names.zipIdx.filter fun (x : Nat × Nat) => x.1 == a).map fun (x : Nat × Nat) => x.2
  | none => []

/-- `returnCheck`'s search for a slot whose refined type is within the
promise, threading the subtype answers. -/
def returnWithin (G : NormalGraph ι) (images : InstanceImageCheck G) (refined : List (Ty ι)) (T : Ty ι)
    (held : List Nat) (answers : Answered G) : Bool × Answered G :=
  held.foldl (fun (within, answers) p =>
    if within then (within, answers) else match refined[p]? with
      | some B => let (res, a') := subtypeUsing G images B T answers; (res.value.isSome, a')
      | none => (false, answers)) (false, answers)

/-- **The subtype answers are sound**:
an answer `subtypeUsing` accepts, from any table of answers, states an
inclusion of meanings. -/
def SubtypeAnswersSound (G : NormalGraph ι) (images : InstanceImageCheck G) : Prop :=
  ∀ (A B : Ty ι) (ans : Answered G), ((subtypeUsing G images A B ans).1).value.isSome = true →
    ∀ n (W : WorldT n) v, meaning G A n W v → meaning G B n W v

/-- Every accepted subtype answer carries a proved inclusion. -/
theorem subtypeAnswersSound (G : NormalGraph ι) (images : InstanceImageCheck G) :
    SubtypeAnswersSound G images := by
  intro A B ans h n W v hv
  have hincl : ∀ η, FamLe (mixedMeaning G η A) (mixedMeaning G η B) := by
    unfold subtypeUsing at h
    split at h
    · rename_i r hr
      split at h
      · cases h
      · rename_i hc
        have hp : ans.proved.contains (A, B) = true := by
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
          by_cases hp : ans.proved.contains (A, B) = true
          · exact hp
          · have hf : ans.proved.contains (A, B) = false := Bool.eq_false_iff.mpr hp
            exact False.elim (hc ⟨h, hf⟩)
        exact ans.proved_sound A B hp
    · exact subtypeSearch_sound h
  exact hincl G.env n W (.inl v) hv

theorem returnWithin_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {refined : List (Ty ι)}
    {T : Ty ι} {held : List Nat} :
    ∀ (w0 : Bool) (a0 : Answered G), (held.foldl (fun (x : Bool × Answered G) p =>
      if x.1 then x else match refined[p]? with
        | some B => ((subtypeUsing G images B T x.2).1.value.isSome, (subtypeUsing G images B T x.2).2)
        | none => (false, x.2)) (w0, a0)).1 = true →
      w0 = true ∨ ∃ p ∈ held, ∃ B a, refined[p]? = some B ∧ ((subtypeUsing G images B T a).1).value.isSome = true := by
  induction held with
  | nil => intro w0 a0 h; exact .inl h
  | cons p ps ih =>
    intro w0 a0 h
    simp only [List.foldl_cons] at h
    cases w0 with
    | true => exact .inl rfl
    | false =>
      simp only [Bool.false_eq_true, if_false] at h
      cases hr : refined[p]? with
      | none =>
        rw [hr] at h
        rcases ih false a0 h with h' | ⟨q, hq, B, a, h1, h2⟩
        · cases h'
        · exact .inr ⟨q, List.mem_cons_of_mem _ hq, B, a, h1, h2⟩
      | some B =>
        rw [hr] at h
        rcases ih _ _ h with h' | ⟨q, hq, B', a, h1, h2⟩
        · exact .inr ⟨p, List.mem_cons_self .., B, a0, hr, h'⟩
        · exact .inr ⟨q, List.mem_cons_of_mem _ hq, B', a, h1, h2⟩

/-- **`returnCheck` accepting a type guard's return** gives the
certificate checker's `ReturnOk` premise: the claim's type Boolean, and
the answer `true` impossible or a slot holding the argument's name within
the promise as the yields leave it on `true`. -/
theorem returnGuard_of_check {G : NormalGraph ι} {images : InstanceImageCheck G}
    {ensures : List HeapKnowledge.IndexFact} {c : PointClaim ι} {l : Nat} {entry : SinglePass.State}
    {store : Store} {result start : Nat} {startNames : List Nat} {argName : Option Nat}
    {yields : List (PromiseCalls.Yield ι)} {debugNode : Nat} {answers : Answered G} {T : Ty ι} {sl : Nat}
    (h : (returnCheck G images (.guards T sl) ensures c l entry store result start startNames argName yields
      debugNode answers).1 = none) :
    BranchRefinement.onlyBoolean G c.type = true ∧
      (BranchRefinement.impossible G c.type (.boolean true) = true ∨
        (returnWithin G images (PromiseCalls.refineBy G c.context
          (PromiseCalls.yieldFacts (passReturnYields entry yields) true) 0) T (passHeld entry argName) answers).1 =
          true) := by
  have fin : ∀ {X : Bool} {str : String},
      (if (!(BranchRefinement.onlyBoolean G c.type &&
        (BranchRefinement.impossible G c.type (.boolean true) || X))) = true then some str else none) = none →
      BranchRefinement.onlyBoolean G c.type = true ∧ (BranchRefinement.impossible G c.type (.boolean true) = true ∨
        X = true) := by
    intro X str hx
    cases h1 : BranchRefinement.onlyBoolean G c.type <;> cases h2 : BranchRefinement.impossible G c.type (.boolean true) <;>
      cases X <;> simp_all
  by_cases hc : (!ensures.isEmpty && !(ExpressionEffects.emptyType G c.type ||
      c.context.any (ExpressionEffects.emptyType G ·))) = true
  · cases hn : GraphCode.returnEntails (KnowledgeExpand.expandLinks
        (HeapKnowledge.setsCtx (HeapKnowledge.typeSets G c.context) 1)
        (materialize ⟨result :: entry.names, store, []⟩ (c.context.length + 1)
          (0 :: (passTracked ensures entry startNames).map (·.1 + 1)) false).1)
        (passTracked ensures entry startNames) ensures with
    | false =>
      unfold returnCheck at h
      simp only [hc, ite_true] at h
      unfold passTracked at hn
      simp only [hn, Bool.not_false, ite_true] at h
      cases h
    | true =>
      unfold returnCheck at h
      simp only [hc, ite_true] at h
      unfold passTracked at hn
      simp only [hn, Bool.not_true, Bool.false_eq_true, ite_false] at h
      cases argName <;> exact fin h
  · unfold returnCheck at h
    simp only [hc, Bool.false_eq_true, ite_false] at h
    cases argName <;> exact fin h

/-- **`returnCheck` accepting an assertion function's return** gives the
certificate checker's `ReturnOk` premise: the claim's type `undefined`,
and the type empty or a slot holding the argument's name within the
promise as the yields leave it on a normal return. -/
theorem returnAssert_of_check {G : NormalGraph ι} {images : InstanceImageCheck G}
    {ensures : List HeapKnowledge.IndexFact} {c : PointClaim ι} {l : Nat} {entry : SinglePass.State}
    {store : Store} {result start : Nat} {startNames : List Nat} {argName : Option Nat}
    {yields : List (PromiseCalls.Yield ι)} {debugNode : Nat} {answers : Answered G} {T : Ty ι} {sl : Nat}
    (h : (returnCheck G images (.asserts T sl) ensures c l entry store result start startNames argName yields
      debugNode answers).1 = none) :
    PromiseCalls.onlyUndef G c.type = true ∧
      (c.type.isEmpty = true ∨
        (returnWithin G images (PromiseCalls.refineBy G c.context
          (PromiseCalls.yieldFacts (passReturnYields entry yields) false) 0) T (passHeld entry argName) answers).1 =
          true) := by
  have fin : ∀ {X : Bool} {str : String},
      (if (!(PromiseCalls.onlyUndef G c.type &&
        (c.type.isEmpty || X))) = true then some str else none) = none →
      PromiseCalls.onlyUndef G c.type = true ∧ (c.type.isEmpty = true ∨
        X = true) := by
    intro X str hx
    cases h1 : PromiseCalls.onlyUndef G c.type <;> cases h2 : c.type.isEmpty <;>
      cases X <;> simp_all
  by_cases hc : (!ensures.isEmpty && !(ExpressionEffects.emptyType G c.type ||
      c.context.any (ExpressionEffects.emptyType G ·))) = true
  · cases hn : GraphCode.returnEntails (KnowledgeExpand.expandLinks
        (HeapKnowledge.setsCtx (HeapKnowledge.typeSets G c.context) 1)
        (materialize ⟨result :: entry.names, store, []⟩ (c.context.length + 1)
          (0 :: (passTracked ensures entry startNames).map (·.1 + 1)) false).1)
        (passTracked ensures entry startNames) ensures with
    | false =>
      unfold returnCheck at h
      simp only [hc, ite_true] at h
      unfold passTracked at hn
      simp only [hn, Bool.not_false, ite_true] at h
      cases h
    | true =>
      unfold returnCheck at h
      simp only [hc, ite_true] at h
      unfold passTracked at hn
      simp only [hn, Bool.not_true, Bool.false_eq_true, ite_false] at h
      cases argName <;> exact fin h
  · unfold returnCheck at h
    simp only [hc, Bool.false_eq_true, ite_false] at h
    cases argName <;> exact fin h

omit [DecidableEq ι] [Hashable ι] [Instantiates ι] in
/-- A slot holding the start name of the input `q` in a holding state reads
the input's entry value. -/
theorem slot_start {G : NormalGraph ι} {st : SinglePass.State} {I : List (PromiseCalls.Implication ι)}
    {start : List Nat} {ρ : Env} {m : Nat} {s : IndexedHeap} (hS : StateHolds G st I start ε ρ m s) {j q x : Nat}
    (hj : st.names[j]? = some x) (hq : start[q]? = some x) : ρ j = ε.env q := by
  obtain ⟨η, hn, -, -, -, hst⟩ := hS
  exact (hn _ _ hj).trans (hst q x hq)

omit [DecidableEq ι] [Hashable ι] [Instantiates ι] in
/-- **Each slot `returnCheck` holds the argument at reads the promised
argument**: a slot of the entry's names holding `argName`, the start name
of the goal's slot, reads that input's entry value. -/
theorem passHeld_argument {G : NormalGraph ι} {entry : SinglePass.State} {I : List (PromiseCalls.Implication ι)}
    {start : List Nat} {ρ : Env} {m : Nat} {s : IndexedHeap} (hS : StateHolds G entry I start ε ρ m s)
    {goal : Goal ι} {sl : Nat} (hsl : goal.slot = some sl) {argName : Option Nat}
    (harg : argName = goal.slot.bind (start[·]?)) :
    PromiseCalls.ArgumentsOk (passHeld entry argName) ρ (goal.argument ε.env) := by
  intro p hp
  rw [hsl] at harg
  simp only [Option.bind_some] at harg
  cases ha : start[sl]? with
  | none => rw [ha] at harg; subst harg; simp [passHeld] at hp
  | some a =>
    rw [ha] at harg; subst harg
    simp only [passHeld, List.mem_map, List.mem_filter, beq_iff_eq] at hp
    obtain ⟨⟨x, j⟩, ⟨hm, hx⟩, rfl⟩ := hp
    simp only at hx; subst hx
    have hj : entry.names[j]? = some x := List.mem_zipIdx_iff_getElem?.mp hm
    rw [Goal.argument, hsl]
    exact slot_start hS hj ha

omit [Hashable ι] [Instantiates ι] in
/-- **A return meets its goal at the state's level** (`ControlFlow.goal_return`
without the step down): the return check's premise, the context typing the
environment, the value of the claim's type, the yields holding and the
argument's slots reading the promised argument. -/
theorem goalHolds_at {G : NormalGraph ι} {goal : Goal ι} {Γ : List (Ty ι)} {A : Ty ι}
    {ys : List (PromiseCalls.Yield ι)} {arg : List Nat} {ρ : Env} {n : Nat} {W : WorldT (n + 1)} {v0 t : Tm}
    {h : Heap} (hh : HeapOk (n + 1) W h) (hr : ReturnOk G goal Γ A ys arg) (he : EnvOk G Γ ρ (n + 1) W)
    (ht : meaning G A (n + 1) W t) (hy : PromiseCalls.YieldsOk G ys ρ (n + 1) W t)
    (ha : PromiseCalls.ArgumentsOk arg ρ v0) : GoalHolds G goal v0 (n + 1) W t := by
  have promised : ∀ {answered p B T}, (answered = true → t = .tru) → p ∈ arg →
      (PromiseCalls.refineBy G Γ (PromiseCalls.yieldFacts ys answered) 0)[p]? = some B →
      FamLe (meaning G B) (meaning G T) → meaning G T (n + 1) W v0 := by
    intro answered p B T hans hp hB hle
    have henv := refined_env (falsified := false) hh he hy hans (fun h => by cases h)
    rw [← ha p hp]
    exact hle _ _ _ (henv.2 p B hB)
  cases goal with
  | plain R =>
    rcases (hr : A = R ∨ A = []) with rfl | rfl
    · exact ht
    · obtain ⟨a, ha, _⟩ := ht
      cases ha
  | guards T s =>
    obtain ⟨hb, hcase⟩ := hr
    rcases BranchRefinement.onlyBoolean_sound hb ht with rfl | rfl
    · refine .inl ⟨rfl, ?_⟩
      rcases hcase with himp | ⟨p, B, hp, hB, hle⟩
      · exact (himp _ _ _ ht rfl).elim
      · exact promised (fun _ => rfl) hp hB hle
    · exact .inr rfl
  | asserts T s =>
    obtain ⟨hu, hcase⟩ := hr
    rcases hcase with rfl | ⟨p, B, hp, hB, hle⟩
    · obtain ⟨a, ha, _⟩ := ht
      cases ha
    · exact ⟨hu _ _ _ ht, promised (answered := false) (fun h => by cases h) hp hB hle⟩

/-- **`returnCheck` accepting a promise's return gives `ReturnOk`**, under
the subtype answers' soundness: the check's within-promise slot is a slot
of `passHeld` whose refined type the answer places within the promise. -/
theorem returnOk_of_check {G : NormalGraph ι} {images : InstanceImageCheck G}
    {ensures : List HeapKnowledge.IndexFact} {c : PointClaim ι} {l : Nat} {entry : SinglePass.State}
    {store : Store} {result start : Nat} {startNames : List Nat} {argName : Option Nat}
    {yields : List (PromiseCalls.Yield ι)} {debugNode : Nat} {answers : Answered G} {goal : Goal ι}
    (hsub : SubtypeAnswersSound G images)
    (h : (returnCheck G images goal ensures c l entry store result start startNames argName yields
      debugNode answers).1 = none) :
    ReturnOk G goal c.context c.type (passReturnYields entry yields) (passHeld entry argName) ∨
      ∃ R, goal = .plain R := by
  cases goal with
  | plain R => exact .inr ⟨R, rfl⟩
  | guards T sl =>
    obtain ⟨hb, hcase⟩ := returnGuard_of_check h
    refine .inl ⟨hb, hcase.imp (fun hi n W v hv ht => ?_) (fun hw => ?_)⟩
    · exact BranchRefinement.impossible_sound hi hv (by simp [BranchRefinement.Observation.holds, ht])
    · rcases returnWithin_sound false answers hw with h0 | ⟨p, hp, B, a, hB, hs⟩
      · cases h0
      · exact ⟨p, B, hp, hB, hsub B T a hs⟩
  | asserts T sl =>
    obtain ⟨hu, hcase⟩ := returnAssert_of_check h
    refine .inl ⟨fun n W v hv => PromiseCalls.onlyUndef_sound hu hv, hcase.imp (fun he => ?_) (fun hw => ?_)⟩
    · simpa using he
    · rcases returnWithin_sound false answers hw with h0 | ⟨p, hp, B, a, hB, hs⟩
      · cases h0
      · exact ⟨p, B, hp, hB, hsub B T a hs⟩


/-- **A return meets its goal at the state after the step**: the
state-dependent form of `NodeAccepted.ret`. Where `returnCheck` accepts
the return at the step's output, the subtype answers are sound (D5), the
promised argument's name is the start name of the goal's slot, and at the
state after the step (`StateHolds` at the pushed environment) the value
has the claim's type and the step's yields hold of it (`YieldsOk`, D2),
the value meets the goal at the promised argument's entry value. -/
theorem goalHolds_of_return {G : NormalGraph ι} {images : InstanceImageCheck G}
    {ensures : List HeapKnowledge.IndexFact} {c : PointClaim ι} {l : Nat} {entry : SinglePass.State}
    {store : Store} {result start : Nat} {startNames : List Nat} {argName : Option Nat}
    {yields : List (PromiseCalls.Yield ι)} {debugNode : Nat} {answers : Answered G} {goal : Goal ι}
    {I : List (PromiseCalls.Implication ι)} {ρ : Env} {m : Nat} {s' : IndexedHeap} {v : Tm}
    (hsub : SubtypeAnswersSound G images)
    (h : (returnCheck G images goal ensures c l entry store result start startNames argName yields
      debugNode answers).1 = none)
    (harg : argName = goal.slot.bind (startNames[·]?))
    (hS : StateHolds G ⟨result :: entry.names, store, entry.fresh⟩ I startNames ε (push v ρ) m s')
    (he : EnvOk G (c.type :: c.context) (push v ρ) s'.n s'.W)
    (hY : PromiseCalls.YieldsOk G (passReturnYields entry yields) ρ s'.n s'.W v)
    (hplain : ∀ R, goal = .plain R → ∀ n (W : WorldT n) v, meaning G c.type n W v → meaning G R n W v) :
    GoalHolds G goal (goal.argument ε.env) s'.n s'.W v := by
  obtain ⟨n, W, h', pos, adm, ok⟩ := s'
  cases n with
  | zero => exact absurd pos (Nat.lt_irrefl 0)
  | succ n =>
    have ht : meaning G c.type (n + 1) W v := by simpa [push] using he.2 0 c.type rfl
    rcases returnOk_of_check (yields := yields) hsub h with hr | ⟨R, rfl⟩
    · cases hsl : goal.slot with
      | none =>
        cases goal with
        | plain R => exact hplain R rfl _ _ v ht
        | guards T sl => simp [Goal.slot] at hsl
        | asserts T sl => simp [Goal.slot] at hsl
      | some sl =>
        exact goalHolds_at ok hr (envOk_tail he) ht hY (passHeld_argument (stateHolds_tail hS) hsl harg)
    · exact hplain R rfl _ _ v ht

end Goals

end Verification.TolerantFrames
