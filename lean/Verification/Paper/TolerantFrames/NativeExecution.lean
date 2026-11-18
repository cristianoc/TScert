import Verification.Paper.TolerantFrames.Commands
import Verification.Semantics.ExceptionalPosts

/-! # Shared safety with exact thrown-value postconditions reaches indexed exits

Extend the existing deterministic indexed-run proof to SafePostExcV. The same
shared Steps, truncation, world extension and heap invariant are used. This
allows supplied native contracts to describe exact exceptional values as well
as their heap effects, without discarding execution safety.
-/
namespace Verification.Paper.TolerantFrames
open Verification TolerantFrames HeapObservations

/-- Source-value and root guarantees used by actual native exits. -/
def NativeSourceValues : Fam := fun _ W v => isSourceVal v = true ∧ RefsOk W v

theorem run_native_safety {Ξ T : Fam} {Q : WPost} {R : WExcV} :
    ∀ {k h t h' t'}, Steps k h t h' t' → ∀ (s : IndexedHeap), s.h = h → k < s.n →
      SafePostExcV Ξ T Q R s.n s.W s.h t →
      ∃ s' : IndexedHeap, Admissible s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧
        SafePostExcV Ξ T Q R s'.n s'.W s'.h t' := by
  intro k h t h' t' execution
  induction execution with
  | refl => intro s heap _ safety; exact ⟨s, Admissible.refl s, heap, rfl, safety⟩
  | next step _ ih =>
    intro s heap budget safety
    obtain ⟨n, W, h₀, positive, adm, ok⟩ := s
    simp only at heap budget safety ⊢
    subst heap
    cases n with
    | zero => omega
    | succ m =>
      rcases safety.2 with (⟨value, _, _⟩ | ⟨v, raised, _, _, _⟩) |
        ⟨U, h₁, t₁, extended, world, actual, heapOk, continuing⟩
      · exact absurd step (value_no_step value)
      · exact absurd step (raises_no_step raised)
      · obtain ⟨rfl, rfl⟩ := Step_det step actual
        obtain ⟨s', reachable, heap', count, safety'⟩ :=
          ih ⟨m, U, _, by omega, world, heapOk⟩ rfl (by simp only; omega) continuing
        exact ⟨s', Admissible.trans ⟨Nat.le_succ m, extended⟩ reachable,
          heap', by simp only at count; omega, safety'⟩

theorem native_exit_value {Ξ T : Fam} {Q : WPost} {R : WExcV}
    {n : Nat} {W : WorldT n} {h : Heap} {v : Tm}
    (positive : 0 < n) (value : isVal v = true) (safety : SafePostExcV Ξ T Q R n W h v) :
    T n W v ∧ Q n W h v := by
  cases n with
  | zero => omega
  | succ n =>
    rcases safety.2 with (⟨_, member, post⟩ | ⟨e, raised, _, _, _⟩) | ⟨_, _, _, _, _, step, _, _⟩
    · exact ⟨member, post⟩
    · exact absurd value (by rw [raises_not_val raised]; simp)
    · exact absurd step (value_no_step value)

theorem native_exit_raise {Ξ T : Fam} {Q : WPost} {R : WExcV}
    {n : Nat} {W : WorldT n} {h : Heap} {term v : Tm}
    (positive : 0 < n) (raised : Raises term v) (safety : SafePostExcV Ξ T Q R n W h term) :
    Ξ n W v ∧ R n W h v := by
  cases n with
  | zero => omega
  | succ n =>
    rcases safety.2 with (⟨value, _, _⟩ | ⟨e, actual, _, member, post⟩) | ⟨_, _, _, _, _, step, _, _⟩
    · exact absurd value (by rw [raises_not_val raised]; simp)
    · cases Raises_det raised actual
      exact ⟨member, post⟩
    · exact absurd step (raises_no_step raised)

/-- Positive execution safety excludes stuck terms, even when there is no
completed run on which a partial contract could be tested. -/
theorem native_safe_progress {Ξ T : Fam} {Q : WPost} {R : WExcV}
    {n : Nat} {W : WorldT n} {h : Heap} {term : Tm}
    (positive : 0 < n) (safety : SafePostExcV Ξ T Q R n W h term) :
    isVal term = true ∨ (∃ v, Raises term v) ∨ ∃ h' term', Step h term h' term' := by
  cases n with
  | zero => omega
  | succ n =>
    rcases safety.2 with (⟨value, _, _⟩ | ⟨v, raised, _, _, _⟩) | ⟨_, h', term', _, _, step, _, _⟩
    · exact .inl value
    · exact .inr (.inl ⟨v, raised⟩)
    · exact .inr (.inr ⟨h', term', step⟩)

end Verification.Paper.TolerantFrames
