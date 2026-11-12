import Verification.Programs.TolerantFramesStepSummaries
import Verification.Programs.TolerantFramesDriverSettle

/-! # Prefix preservation inside a visit -/
namespace Verification.TolerantFrames
open Verification SinglePass ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates ProgramTyping LabelStore
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

/-- A fold of table extensions extends its initial table. -/
theorem sumsPrefix_fold {α β : Type} (get : α → Answered G) (f : α → β → α)
    (hf : ∀ a x, SumsPrefix (get a) (get (f a x))) (xs : List β) (a : α) :
    SumsPrefix (get a) (get (xs.foldl f a)) := by
  induction xs generalizing a with
  | nil => exact .refl _
  | cons x xs ih => exact (hf a x).trans (ih (f a x))

/-- Computing yields preserves the step's table. -/
theorem stepYields_prefix (env : WalkEnv ι G I) (l : Nat) (en : SinglePass.State)
    (imp : List (PromiseCalls.Implication ι)) (st : Stepped ι) (a : Answered G) :
    SumsPrefix a (stepYields G I env l en imp st a).2 := by
  unfold stepYields
  repeat' (first | split | extract_lets)
  all_goals first | exact .refl _ | exact keep_prefix _ _

/-- Return checking preserves its input table. -/
theorem returnRun_prefix {env : WalkEnv ι G I} {l : Nat} {en : SinglePass.State} {st : Stepped ι}
    {ys : List (PromiseCalls.Yield ι)} {a b : Answered G} {why : Option String} {q : Option Nat}
    (h : returnRun G I env l en st ys a = some (why, b, q)) : SumsPrefix a b := by
  unfold returnRun at h
  repeat' (first | split at h | extract_lets at h)
  all_goals first | cases h | skip
  all_goals exact keep_prefix _ _

/-- An equation form of yield prefix preservation. -/
theorem stepYields_prefix_of {env : WalkEnv ι G I} {l : Nat} {en : SinglePass.State}
    {imp : List (PromiseCalls.Implication ι)} {st : Stepped ι} {a b : Answered G}
    {ys : Option (List (PromiseCalls.Yield ι))}
    (h : stepYields G I env l en imp st a = (ys, b)) : SumsPrefix a b := by
  have hp := stepYields_prefix env l en imp st a
  rw [h] at hp
  exact hp

set_option maxHeartbeats 1000000 in
/-- The step's yielded and return-checked table extends its checked-step table. -/
theorem visitStep_prefix {env : WalkEnv ι G I} {σ : WalkState ι G} {l : Nat}
    {en : Entered ι} {sd : StepDone ι G} (h : visitStep G I env σ l en = .ok sd) :
    SumsPrefix sd.steppedAnswers sd.answers := by
  unfold visitStep at h
  repeat' (first | split at h | extract_lets at h)
  all_goals first | cases h | skip
  all_goals
    have hy := stepYields_prefix_of ‹stepYields G I env l en.entry en.implies _ _ = _›
    first
    | exact hy
    | exact hy.trans (returnRun_prefix ‹returnRun G I env l en.entry _ _ _ = some _›)

/-- Exit yield computation preserves its input table. -/
theorem exitsYields_prefix (env : WalkEnv ι G I) (l : Nat) (en : Entered ι) (sd : StepDone ι G) :
    SumsPrefix sd.answers (exitsYields G I env l en sd).2 := by
  unfold exitsYields
  repeat' (first | split | extract_lets)
  all_goals first | exact .refl _ | exact keep_prefix _ _

/-- Slotwise subtype checks preserve the summary table. -/
theorem diffSubtypes_prefix (Γ Δ : List (Ty ι)) (diff : List (Nat × Nat))
    (obs : Option BranchRefinement.Observation) (a : Answered G) :
    SumsPrefix a (diffSubtypes G I Γ Δ diff obs a).2 := by
  unfold diffSubtypes
  refine sumsPrefix_fold Prod.snd _ ?_ _ (true, a)
  intro acc x
  rcases x with ⟨i, s⟩
  repeat' (first | split | extract_lets)
  all_goals first | exact .refl _ | exact keep_prefix _ _

/-- Implication comparison preserves its input table. -/
theorem impliesHeld_prefix (x : PromiseCalls.Implication ι) (held : List (PromiseCalls.Implication ι)) (a : Answered G) :
    SumsPrefix a (impliesHeld G I x held a).2 := by
  unfold impliesHeld
  refine sumsPrefix_fold Prod.snd _ ?_ _ (false, a)
  intro acc y
  repeat' (first | split | extract_lets)
  all_goals first | exact .refl _ | exact keep_prefix _ _

/-- Checking a head's implications preserves its input table. -/
theorem headImplies_prefix (env : WalkEnv ι G I) (t : Target) (names : List Nat)
    (carried : List (PromiseCalls.Implication ι)) (a : Answered G) :
    SumsPrefix a (headImplies G I env t names carried a).2 := by
  unfold headImplies
  refine sumsPrefix_fold Prod.snd _ ?_ _ (true, a)
  intro acc x
  split
  · exact .refl _
  · exact impliesHeld_prefix _ _ _

/-- Keeping an existing prefix leaves the later summary table unchanged. -/
theorem keepSummaries_table {a b : Answered G} (h : SumsPrefix a b) :
    (keepSummaries a b).summaries.toList = b.summaries.toList := by
  simp only [keepSummaries, Array.toList_append, Array.toList_extract, List.extract]
  rw [List.take_of_length_le (by simp)]
  exact List.prefix_iff_eq_append.mp h

/-- A successful checked step extends its input table. -/
theorem checkedStep_prefix {pool : List (Ty ι)} {fuel : Nat}
    {suggestions : List (Sequent ι)} {index : KnownIndex ι} {codes : CodeEntry ι → Bool}
    {aliases : List (ι × ι)} {pc : PassChecker G I} {undefTy : Option (Ty ι)}
    {l : Nat} {node : Node} {c : PointClaim ι} {entry : SinglePass.State} {ms : List Nat} {fresh : Nat}
    {answers : Answered G} {st : Stepped ι} {stats : StepStats} {ans : Answered G}
    (h : checkedStep G I pool fuel suggestions index codes aliases pc undefTy l node c entry ms fresh
      answers = (Except.ok st, stats, ans)) : SumsPrefix answers ans := by
  rcases checkedStep_ok h with ⟨_, _, _, _, _, _, _, _, rfl⟩ | ⟨_, _, a0, a1, ha0, ha1, _, hans⟩
  · exact .refl _
  · subst hans
    have h0 : SumsPrefix answers a0 := by
      rcases ha0 with rfl | ⟨_, rfl⟩
      · exact .refl _
      · exact keep_prefix _ _
    have h1 : SumsPrefix a0 ans := by
      rcases ha1 with rfl | ⟨_, _, _, rfl⟩
      · exact .refl _
      · exact keep_prefix _ _
    exact h0.trans h1

/-- The input table is a prefix of the table checked by the step. -/
theorem visitStep_input_prefix {env : WalkEnv ι G I} {σ : WalkState ι G} {l : Nat}
    {en : Entered ι} {sd : StepDone ι G} (h : visitStep G I env σ l en = .ok sd) :
    SumsPrefix σ.answers sd.steppedAnswers := by
  obtain ⟨⟨_, _, hr⟩, _, _⟩ := visitStep_ok h
  exact checkedStep_prefix (stepRun_ok hr)

/-- The remaining local summary obligation: a successful exit extends its input table. -/
def ExitStepPrefix (ι : Type) [Labels ι] : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (env : WalkEnv ι G I) (l : Nat)
    (en : Entered ι) (sd : StepDone ι G) (ys : List (PromiseCalls.Yield ι)) (out : Thunk HeapKnowledge.Knowledge)
    (acc result : ExitsDone ι G) (ex : Exit × Nat),
    exitStep G I env l en sd ys out acc ex = .ok result → SumsPrefix acc.answers result.answers

/-- Successful exit folds preserve the summary prefix under the local exit obligation. -/
theorem exitsFold_prefix (hp : ExitStepPrefix ι) {env : WalkEnv ι G I} {l : Nat} {en : Entered ι}
    {sd : StepDone ι G} {ys : List (PromiseCalls.Yield ι)} {out : Thunk HeapKnowledge.Knowledge}
    (es : List (Exit × Nat)) (acc result : ExitsDone ι G)
    (h : es.foldlM (exitStep G I env l en sd ys out) acc = .ok result) :
    SumsPrefix acc.answers result.answers := by
  induction es generalizing acc with
  | nil => cases h; exact .refl _
  | cons e es ih =>
    rw [List.foldlM_cons] at h
    cases he : exitStep G I env l en sd ys out acc e with
    | error stop => rw [he] at h; cases h
    | ok a =>
      rw [he] at h
      exact (hp G I env l en sd ys out acc a e he).trans (ih a h)

/-- A visit's exits extend the step's final table under the local exit obligation. -/
theorem visitExits_prefix (hp : ExitStepPrefix ι) {env : WalkEnv ι G I} {σ : WalkState ι G} {l : Nat}
    {en : Entered ι} {sd : StepDone ι G} {ex : ExitsDone ι G}
    (h : visitExits G I env σ l en sd = .ok ex) : SumsPrefix sd.answers ex.answers := by
  unfold visitExits at h
  extract_lets node c at h
  split at h
  rename_i yields answers heq
  extract_lets outAll regional at h
  generalize regional = R at h
  split at h
  · cases h
  · have hy := exitsYields_prefix env l en sd
    rw [heq] at hy
    exact hy.trans (exitsFold_prefix hp _ _ _ h)

/-- The successful visit retains its checked-step table under the local exit obligation. -/
theorem visitStepPrefix_of_exitStep (hp : ExitStepPrefix ι) : VisitStepPrefix ι := by
  intro G I env σ l en sd ex hs he
  have hse := (visitStep_prefix hs).trans (visitExits_prefix hp he)
  have hstart := (visitStep_input_prefix hs).trans hse
  unfold SumsPrefix
  rw [keepSummaries_table hstart]
  exact hse

end Verification.TolerantFrames
