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

/-- Refining a mixed context preserves the summary table. -/
theorem mixedContext_prefix (Γ Γ' Δ : List (Ty ι)) (m : PointClaims.Mapping) (a : Answered G) :
    SumsPrefix a (mixedContext G I Γ Γ' Δ m a).2 := by
  unfold mixedContext
  dsimp only
  refine sumsPrefix_fold Prod.snd _ ?_ _ (#[], a)
  intro acc x
  dsimp only
  refine sumsPrefix_fold Prod.snd _ ?_ _ (true, acc.2)
  intro fa i
  repeat' (first | split | extract_lets)
  all_goals first | exact .refl _ | exact keep_prefix _ _

set_option maxHeartbeats 2000000 in
/-- Every successful exit type check preserves its input summary table. -/
theorem exitTypes_prefix {env : WalkEnv ι G I} {l : Nat} {en : Entered ι} {sd : StepDone ι G}
    {out : Thunk HeapKnowledge.Knowledge} {t : Target} {tc : PointClaim ι} {Γ : List (Ty ι)}
    {names : List Nat} {store : Store} {pushed handler first : Bool}
    {obs : Option BranchRefinement.Observation} {diff : List (Nat × Nat)}
    {acc result : ExitsDone ι G} {typed : SinglePass.ExitTyped ι}
    (h : exitTypes G I env l en sd out t tc Γ names store pushed handler obs first diff acc = .ok (result, typed)) :
    SumsPrefix acc.answers result.answers := by
  unfold exitTypes at h
  extract_lets node c width entry at h
  split at h
  rename_i ok a hd
  have hp := diffSubtypes_prefix (I := I) Γ tc.context diff obs acc.answers
  rw [hd] at hp
  split at h
  · cases h; exact hp
  · split at h
    extract_lets ko at h
    split at h
    rename_i found a1 hf
    extract_lets answers at h
    have hp1 : SumsPrefix acc.answers answers := hp.trans (keep_prefix _ _)
    split at h
    · cases h
    · split at h
      · cases h; exact hp1
      · split at h
        rename_i ys a2 hys
        have hp2 : SumsPrefix acc.answers a2 := by
          cases hc : acc.yields with
          | some xs =>
            simp only [hc] at hys
            cases hys; exact hp1
          | none =>
            simp only [hc] at hys
            split at hys
            cases hys
            exact hp1.trans (keep_prefix _ _)
        extract_lets Γr at h
        split at h
        extract_lets answersR at h
        have hp3 : SumsPrefix acc.answers answersR := hp2.trans (keep_prefix _ _)
        split at h
        rename_i foundM a4 typ hmixed
        have hp4 : SumsPrefix acc.answers a4 := by
          split at hmixed
          · cases hmixed; exact hp3
          · split at hmixed
            rename_i Γm am hmix
            have hm := mixedContext_prefix (I := I) Γ Γr tc.context t.mapping answersR
            rw [hmix] at hm
            split at hmixed
            · split at hmixed
              cases hmixed
              exact (hp3.trans hm).trans (keep_prefix _ _)
            · cases hmixed; exact hp3.trans hm
        split at h
        · cases h
        · cases h; exact hp4

/-- A successful head exit preserves its input summary table. -/
theorem headExit_prefix {env : WalkEnv ι G I} {l : Nat} {t : Target} {tc : PointClaim ι}
    {Γ : List (Ty ι)} {names : List Nat} {store : Store} {pushed vacuous : Bool}
    {carried : List (PromiseCalls.Implication ι)} {acc result : ExitsDone ι G}
    (h : headExit G I env l t tc Γ names store pushed vacuous carried acc = .ok result) :
    SumsPrefix acc.answers result.answers := by
  cases vacuous
  all_goals unfold headExit at h
  all_goals simp only [Bool.false_eq_true, ↓reduceIte] at h
  repeat' (first | split at h | extract_lets at h)
  all_goals first | cases h | skip
  all_goals first
    | exact .refl _
    | exact headImplies_prefix env t names carried acc.answers

/-- Assertion checking leaves the summary table unchanged. -/
theorem assertionExit_answers {env : WalkEnv ι G I} {l : Nat} {t : Target} {tc : PointClaim ι}
    {Γ : Thunk (List (Ty ι))} {names : List Nat} {store : Store} {pushed vacuous : Bool}
    {obs : Option BranchRefinement.Observation} {acc result : ExitsDone ι G}
    (h : assertionExit G env l t tc Γ names store pushed obs vacuous acc = .ok result) :
    result.answers = acc.answers := by
  unfold assertionExit at h
  repeat' (first | split at h | extract_lets at h)
  all_goals cases h <;> rfl

/-- A successful exit preserves the input summary table. -/
theorem exitStepPrefix : ExitStepPrefix ι := by
  intro G I env l en sd ys out a b e h
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
  have hp : a2.answers = a.answers := by
    dsimp only [a2, a0]
    split <;> split <;> rfl
  have hp1 : SumsPrefix a.answers a1.answers := by
    split at ht
    · cases ht; rw [hp]; exact .refl _
    · rw [← hp]; exact exitTypes_prefix ht
  extract_lets freshImpl record at h
  split at h
  · simp only [Except.map] at h
    split at h
    · cases h
    · rename_i a3 hhead
      cases h
      change SumsPrefix a.answers a3.answers
      exact hp1.trans (headExit_prefix hhead)
  · split at h
    · cases h
    rename_i a3 ha
    split at h
    cases h
    change SumsPrefix a.answers a3.answers
    rw [assertionExit_answers ha]
    exact hp1

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

/-- Regional checking's input summaries are a prefix of the exit result. -/
theorem visitExits_regional_prefix {env : WalkEnv ι G I} {σ : WalkState ι G} {l : Nat}
    {en : Entered ι} {sd : StepDone ι G} {ex : ExitsDone ι G}
    (h : visitExits G I env σ l en sd = .ok ex) :
    SumsPrefix (exitsYields G I env l en sd).2 ex.answers := by
  unfold visitExits at h
  extract_lets node c at h
  split at h
  rename_i yields answers heq
  extract_lets outAll regional at h
  generalize regional = R at h
  split at h
  · cases h
  · rw [heq]
    exact exitsFold_prefix exitStepPrefix _ _ _ h

/-- The exit result's complete summary table survives the visit boundary. -/
theorem visitExits_answers_prefix (G : NormalGraph ι) (I : InstanceImageCheck G)
    (env : WalkEnv ι G I) (σ : WalkState ι G) (l : Nat) (en : Entered ι)
    (sd : StepDone ι G) (ex : ExitsDone ι G)
    (hs : visitStep G I env σ l en = .ok sd) (he : visitExits G I env σ l en sd = .ok ex) :
    SumsPrefix ex.answers (keepSummaries σ.answers ex.answers) := by
  have hp := (visitStep_input_prefix hs).trans
    ((visitStep_prefix hs).trans (visitExits_prefix exitStepPrefix he))
  unfold SumsPrefix
  rw [keepSummaries_table hp]
  exact List.prefix_refl _

/-- The successful visit retains its checked-step table under the local exit obligation. -/
theorem visitStepPrefix_of_exitStep (hp : ExitStepPrefix ι) : VisitStepPrefix ι := by
  intro G I env σ l en sd ex hs he
  have hse := (visitStep_prefix hs).trans (visitExits_prefix hp he)
  have hstart := (visitStep_input_prefix hs).trans hse
  unfold SumsPrefix
  rw [keepSummaries_table hstart]
  exact hse

end Verification.TolerantFrames
