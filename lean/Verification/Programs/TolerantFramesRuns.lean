import Verification.Semantics.TolerantFrames
import Verification.Programs.ControlFlow

/-! # Tolerant frames: graph runs

A graph run that `SafeGraph` covers, with budget left, ends in a state an
admissible transition reaches, by determinism of the graph machine's
transitions. -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations

/-! ## Graph runs -/

open ControlFlow in
/-- Finite closure of the graph machine's transitions, with its count. -/
inductive Transitions (P : Program) : Nat → Heap → State → Heap → State → Prop where
  | refl : Transitions P 0 h s h s
  | next : Transition P h s h' s' → Transitions P k h' s' h'' s'' → Transitions P (k + 1) h s h'' s''

open ControlFlow in
/-- **The graph machine is deterministic**: one state in one heap has at most
one next state. -/
theorem transition_det {P : Program} {h h₁ h₂ : Heap} {s s₁ s₂ : State}
    (t₁ : Transition P h s h₁ s₁) (t₂ : Transition P h s h₂ s₂) : h₁ = h₂ ∧ s₁ = s₂ := by
  cases t₁ with
  | enter hn =>
    cases t₂ with
    | enter hn' => rw [hn] at hn'; cases hn'; exact ⟨rfl, rfl⟩
  | expr st =>
    cases t₂ <;> first
      | (rename_i st'; obtain ⟨rfl, rfl⟩ := Step_det st st'; exact ⟨rfl, rfl⟩)
      | exact absurd st (value_no_step (by assumption))
      | exact absurd st (value_no_step rfl)
      | exact absurd st (raises_no_step (by assumption))
  | handle hr =>
    cases t₂ <;> first
      | (rename_i hr'; cases Raises_det hr hr'; exact ⟨rfl, rfl⟩)
      | exact absurd ‹Step _ _ _ _› (raises_no_step hr)
      | (exfalso; have hv := raises_not_val hr; simp_all [isVal])
  | raise hr =>
    cases t₂ <;> first
      | (rename_i hr'; cases Raises_det hr hr'; exact ⟨rfl, rfl⟩)
      | exact absurd ‹Step _ _ _ _› (raises_no_step hr)
      | (exfalso; have hv := raises_not_val hr; simp_all [isVal])
  | ret _ | bind _ | effect _ | tagBind _ | yes | no | yesBind | noBind =>
    cases t₂ <;> first
      | exact ⟨rfl, rfl⟩
      | exact absurd ‹Step _ _ _ _› (value_no_step (by assumption))
      | exact absurd ‹Step _ _ _ _› (value_no_step rfl)
      | (exfalso; have hv := raises_not_val ‹Raises _ _›; simp_all [isVal])

open ControlFlow in
/-- **A graph run that `SafeGraph` covers, with budget left, ends in a state
an admissible transition reaches**, the graph's safety continuing there. -/
theorem graph_run {Ξ T : Fam} {P : Program} :
    ∀ {k h st h' st'}, Transitions P k h st h' st' → ∀ (s : IndexedHeap), s.h = h → k < s.n →
      SafeGraph Ξ P T s.n s.W s.h st →
      ∃ s' : IndexedHeap, Admissible s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧
        SafeGraph Ξ P T s'.n s'.W s'.h st' := by
  intro k h st h' st' hst
  induction hst with
  | refl => intro s hs _ hsafe; exact ⟨s, Admissible.refl s, hs, rfl, hsafe⟩
  | next tr _ ih =>
    intro s hs hk hsafe
    obtain ⟨n, W, h₀, pos, adm, ok⟩ := s
    simp only at hs hk hsafe ⊢
    subst hs
    cases n with
    | zero => omega
    | succ m =>
      rcases hsafe with (⟨v, rfl, -⟩ | ⟨v, rfl, -⟩) | ⟨U, h₁, st₁, hx, hu, tr', hh, hs'⟩
      · cases tr
      · cases tr
      · obtain ⟨rfl, rfl⟩ := transition_det tr tr'
        obtain ⟨s', ha, he, hn, hsafe'⟩ :=
          ih ⟨m, U, _, by omega, hu, hh⟩ rfl (by simp only; omega) hs'
        exact ⟨s', Admissible.trans ⟨Nat.le_succ m, hx⟩ ha, he, by simp only at hn; omega, hsafe'⟩

end Verification.TolerantFrames
