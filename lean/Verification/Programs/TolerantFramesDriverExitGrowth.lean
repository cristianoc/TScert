import Verification.Programs.TolerantFramesDriverExits
import Verification.Programs.TolerantFramesWalkExtends

/-! # The exit checks preserve earlier incoming records -/
namespace Verification.TolerantFrames
open Verification ControlFlow CertificateProducer PositiveCertificates PositiveGraphs LabelStore

section Growth
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

omit [Labels ι] in
/-- Prepending at an array position preserves its old list as a suffix. -/
theorem modify_cons_suffix {α : Type} (a : Array (List α)) (x : Nat) (v : α) (y : Nat) :
    ∃ ns, ((a.modify x (v :: ·))[y]?).getD [] = ns ++ (a[y]?).getD [] := by
  by_cases hy : y = x
  · subst hy
    exact ⟨_, getD_modify_cons a _ v⟩
  · exact ⟨[], getD_modify_ne a x y (v :: ·) [] hy⟩

/-- A pushed merge edge preserves every earlier merge edge. -/
theorem pushExit_mergeGrowth (env : SinglePass.WalkEnv ι G I) (l : Nat) (t : Target)
    (target : SinglePass.State) (carried : List (PromiseCalls.Implication ι))
    (Γe : Thunk (List (ProgramTyping.Ty ι))) (names : List Nat) (pushed vacuous : Bool)
    (acc : SinglePass.ExitsDone ι G) (y : Nat) :
    ∃ es, ((SinglePass.pushExit env l t target carried Γe names pushed vacuous acc).incomingEdges[y]?).getD [] =
      es ++ (acc.incomingEdges[y]?).getD [] := by
  unfold SinglePass.pushExit
  dsimp only
  split
  · exact modify_cons_suffix _ _ _ _
  · exact ⟨[], rfl⟩

/-- A successful exit preserves every earlier merge edge. -/
theorem exitStep_mergeGrowth {env : SinglePass.WalkEnv ι G I} {l : Nat} {en : SinglePass.Entered ι}
    {sd : SinglePass.StepDone ι G} {ysAll : List (PromiseCalls.Yield ι)} {outAll : Thunk HeapKnowledge.Knowledge}
    {acc acc' : SinglePass.ExitsDone ι G} {exi : SinglePass.Exit × Nat}
    (h : SinglePass.exitStep G I env l en sd ysAll outAll acc exi = .ok acc') (y : Nat) :
    ∃ es, (acc'.incomingEdges[y]?).getD [] = es ++ (acc.incomingEdges[y]?).getD [] := by
  unfold SinglePass.exitStep at h
  extract_lets at h
  split at h
  · cases h
  split at h
  · cases h
  extract_lets diff u acc2 typed at h
  generalize ht : typed = T at h
  split at h
  · cases h
  rename_i acc1 et
  simp only [typed] at ht
  have hp : SameCore acc acc2 ∧ acc2.edges = acc.edges :=
    sameCore_unsat (sameCore_trace _ _ _) _ _
  have hc1 : SameCore acc acc1 := by
    split at ht
    · cases ht; exact hp.1
    · exact hp.1.trans (exitTypes_core ht).1
  extract_lets freshImpl record at h
  split at h
  · simp only [Except.map] at h
    split at h
    · cases h
    · rename_i a hh
      cases h
      have hc2 := (headExit_core hh).1
      exact ⟨[], by rw [hc2.incomingEdges, hc1.incomingEdges]; rfl⟩
  · split at h
    · cases h
    rename_i acc3 hA
    have hc3 := (assertionExit_core hA).1
    split at h
    cases h
    obtain ⟨es, he⟩ := pushExit_mergeGrowth env l _ _ _ _ _ _ _ acc3 y
    exact ⟨es, by rw [he, hc3.incomingEdges, hc1.incomingEdges]⟩

/-- Merge edges persist through the whole exit fold. -/
theorem exitsFold_mergeGrowth {env : SinglePass.WalkEnv ι G I} {l : Nat} {en : SinglePass.Entered ι}
    {sd : SinglePass.StepDone ι G} {ysAll : List (PromiseCalls.Yield ι)} {outAll : Thunk HeapKnowledge.Knowledge} :
    ∀ (es : List (SinglePass.Exit × Nat)) (acc r : SinglePass.ExitsDone ι G),
      es.foldlM (SinglePass.exitStep G I env l en sd ysAll outAll) acc = .ok r →
      ∀ y : Nat, ∃ ns, (r.incomingEdges[y]?).getD [] = ns ++ (acc.incomingEdges[y]?).getD []
  | [], acc, r, h, y => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨[], rfl⟩
  | e :: es, acc, r, h, y => by
    rw [List.foldlM_cons] at h
    cases ha : SinglePass.exitStep G I env l en sd ysAll outAll acc e with
    | error stop => rw [ha] at h; cases h
    | ok a =>
      rw [ha] at h
      obtain ⟨ns, hn⟩ := exitsFold_mergeGrowth es a r h y
      obtain ⟨ms, hm⟩ := exitStep_mergeGrowth ha y
      exact ⟨ns ++ ms, by rw [hn, hm, List.append_assoc]⟩

/-- A successful exit visit preserves merge edges at every label. -/
theorem visitExits_mergeGrowth {env : SinglePass.WalkEnv ι G I} {σ : SinglePass.WalkState ι G} {l : Nat}
    {en : SinglePass.Entered ι} {sd : SinglePass.StepDone ι G} {ex : SinglePass.ExitsDone ι G}
    (h : SinglePass.visitExits G I env σ l en sd = .ok ex) :
    ∀ y : Nat, ∃ ns, (ex.incomingEdges[y]?).getD [] = ns ++ (σ.walk.incomingEdges[y]?).getD [] := by
  unfold SinglePass.visitExits at h
  extract_lets node c at h
  split at h
  extract_lets outAll regional at h
  generalize regional = R at h
  split at h
  · cases h
  · exact exitsFold_mergeGrowth _ _ _ h

/-- The walk returned by a visit extends all incoming records together. -/
theorem visitExits_extends {env : SinglePass.WalkEnv ι G I} {σ : SinglePass.WalkState ι G} {l : Nat}
    {en : SinglePass.Entered ι} {sd : SinglePass.StepDone ι G} {ex : SinglePass.ExitsDone ι G}
    (h : SinglePass.visitExits G I env σ l en sd = .ok ex)
    (hs : σ.walk.incoming.size = σ.walk.incomingImpl.size) :
    WalkExtends σ.walk (visitResult σ l en sd ex).walk := by
  obtain ⟨a, h1, h2, -, h4, -, -, hf⟩ := visitExits_fold h
  refine ⟨fun t => ?_, visitExits_mergeGrowth h, ?_⟩
  · obtain ⟨ns, nis, g1, g2, g3, -⟩ := hf.pushes t
    exact ⟨ns, nis, by rw [← h1]; exact g1, by rw [← h2]; exact g2,
      g3 (by rw [h1, h2]; exact hs)⟩
  · obtain ⟨es, he, -⟩ := hf.edges
    exact ⟨es, by rw [← h4]; exact he⟩

open SinglePass ProgramTyping

/-- All three incoming arrays keep their allocated sizes through one exit. -/
theorem exitStep_arraySizes {env : WalkEnv ι G I} {l : Nat} {en : Entered ι} {sd : StepDone ι G}
    {ys : List (PromiseCalls.Yield ι)} {out : Thunk HeapKnowledge.Knowledge}
    {a b : ExitsDone ι G} {e : Exit × Nat}
    (h : exitStep G I env l en sd ys out a e = .ok b) :
    b.incoming.size = a.incoming.size ∧ b.incomingImpl.size = a.incomingImpl.size ∧
      b.incomingEdges.size = a.incomingEdges.size := by
  unfold exitStep at h
  extract_lets at h
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
  have hp : SameCore a a2 ∧ a2.edges = a.edges :=
    sameCore_unsat (sameCore_trace _ _ _) _ _
  have hc : SameCore a a1 := by
    split at ht
    · cases ht; exact hp.1
    · exact hp.1.trans (exitTypes_core ht).1
  extract_lets freshImpl record at h
  split at h
  · simp only [Except.map] at h
    split at h
    · cases h
    · rename_i a3 ha
      cases h
      have hc' := hc.trans (headExit_core ha).1
      exact ⟨congrArg Array.size hc'.incoming, congrArg Array.size hc'.incomingImpl,
        congrArg Array.size hc'.incomingEdges⟩
  · split at h
    · cases h
    rename_i a3 ha
    split at h
    cases h
    have hc' := hc.trans (assertionExit_core ha).1
    dsimp only [pushExit]
    split <;> simp only [Array.size_modify, hc'.incoming, hc'.incomingImpl, hc'.incomingEdges, and_self]

/-- The exit fold preserves all incoming array sizes. -/
theorem exitsFold_arraySizes {env : WalkEnv ι G I} {l : Nat} {en : Entered ι} {sd : StepDone ι G}
    {ys : List (PromiseCalls.Yield ι)} {out : Thunk HeapKnowledge.Knowledge} :
    ∀ (es : List (Exit × Nat)) (a b : ExitsDone ι G),
      es.foldlM (exitStep G I env l en sd ys out) a = .ok b →
      b.incoming.size = a.incoming.size ∧ b.incomingImpl.size = a.incomingImpl.size ∧
        b.incomingEdges.size = a.incomingEdges.size
  | [], a, b, h => by cases h; exact ⟨rfl, rfl, rfl⟩
  | e :: es, a, b, h => by
    rw [List.foldlM_cons] at h
    cases ha : exitStep G I env l en sd ys out a e with
    | error stop => rw [ha] at h; cases h
    | ok a' =>
      rw [ha] at h
      obtain ⟨h1, h2, h3⟩ := exitStep_arraySizes ha
      obtain ⟨g1, g2, g3⟩ := exitsFold_arraySizes es a' b h
      exact ⟨g1.trans h1, g2.trans h2, g3.trans h3⟩

/-- A successful exit visit preserves the setup's allocation. -/
theorem visitExits_arraySizes {env : WalkEnv ι G I} {σ : WalkState ι G} {l : Nat}
    {en : Entered ι} {sd : StepDone ι G} {ex : ExitsDone ι G}
    (h : visitExits G I env σ l en sd = .ok ex) :
    ex.incoming.size = σ.walk.incoming.size ∧ ex.incomingImpl.size = σ.walk.incomingImpl.size ∧
      ex.incomingEdges.size = σ.walk.incomingEdges.size := by
  unfold visitExits at h
  extract_lets at h
  split at h
  extract_lets outAll regional at h
  generalize regional = R at h
  split at h
  · cases h
  · exact exitsFold_arraySizes _ _ _ h

end Growth
end Verification.TolerantFrames
