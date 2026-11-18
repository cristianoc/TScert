import Verification.Semantics.ExceptionalPosts

/-! # Safety along the executions that keep an obligation

`SafeUnder K next J Ξ T Q R` is `SafePostExcW Ξ T Q R` read over the
executions whose every step keeps the obligation `K`, a ghost of type `γ`
threaded along them by `next`, with the state property `J` at every state
reached within the budget. Its steps are the calculus's, and progress is
required at every state as in `SafePostExcW`: a state is a value, a throw,
or takes a step of `Step` with an admissible world and a typed heap. What
the obligation removes is the claim about what follows a step that breaks
it: after such a step the execution is outside the executions the claim is
about, and nothing is claimed of it.

- `SafeUnder.erase`: where an invariant of the ghost and the term makes
  every step from it keep the obligation, `SafeUnder` gives
  `SafePostExcW`, and `J` at every state reached (`SafeUnder.reach`, by the
  calculus's determinism, `Step_det`).
- `SafeUnder.of_safe`: `SafePostExcW` with `J` at every state reached gives
  `SafeUnder` for every obligation. So where the obligation holds at every
  step, `SafeUnder` is exactly `SafePostExcW` with `J` along the run. -/
namespace Verification.HeapObservations
open Verification

/-- **Safety along the executions keeping `K`**: at every budget the running
term's references are valid; at positive budget `J` holds of the state, and
it is a value of `T` meeting `Q`, a throw of `Ξ` meeting `R`, or it steps
to a state, with an admissible world and a heap it types, from which the
run is again safe if the step keeps `K` at the ghost `g`, the ghost after
it being `next g`. -/
def SafeUnder {γ : Type} (K : γ → (k : Nat) → WorldT k → Heap → Tm → Heap → Tm → Prop)
    (next : γ → Heap → Tm → Heap → Tm → γ) (J : Heap → Tm → Prop) (Ξ T : Fam) (Q : WPost) (R : WExc) :
    (n : Nat) → WorldT n → γ → Heap → Tm → Prop
  | 0, W, _, _, t => RefsOk W t
  | n + 1, W, g, h, t => RefsOk W t ∧ J h t ∧
      (((isVal t = true ∧ T (n + 1) W t ∧ Q (n + 1) W h t) ∨ (Thrown Ξ (n + 1) W t ∧ R (n + 1) W h)) ∨
      (∃ (U : WorldT n) (h' : Heap) (t' : Tm),
        WExt (trunc n (Nat.le_succ n) W) U ∧ WorldAdm U ∧ Step h t h' t' ∧ HeapOk n U h' ∧
          (K g (n + 1) W h t h' t' → SafeUnder K next J Ξ T Q R n U (next g h t h' t') h' t')))

section
variable {γ : Type} {K : γ → (k : Nat) → WorldT k → Heap → Tm → Heap → Tm → Prop}
  {next : γ → Heap → Tm → Heap → Tm → γ} {J : Heap → Tm → Prop} {Ξ T : Fam} {Q : WPost} {R : WExc}

/-- **An invariant on which the obligation is met**: every step from a state
meeting `I` keeps `K`, at every world, and leaves a state meeting `I`. -/
def KeepsOn (K : γ → (k : Nat) → WorldT k → Heap → Tm → Heap → Tm → Prop)
    (next : γ → Heap → Tm → Heap → Tm → γ) (I : γ → Heap → Tm → Prop) : Prop :=
  ∀ g h t h' t', I g h t → Step h t h' t' →
    (∀ (k : Nat) (W : WorldT k), K g k W h t h' t') ∧ I (next g h t h' t') h' t'

/-- **Where the obligation is met, `SafeUnder` is ordinary safety**
(proved): from a state meeting an invariant on which every step keeps the
obligation, `SafeUnder` gives `SafePostExcW` at every budget. -/
theorem SafeUnder.erase {I : γ → Heap → Tm → Prop} (hk : KeepsOn K next I) :
    ∀ {n : Nat} {W : WorldT n} {g : γ} {h : Heap} {t : Tm}, I g h t →
      SafeUnder K next J Ξ T Q R n W g h t → SafePostExcW Ξ T Q R n W h t := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ hs; exact hs
  | succ n ih =>
    intro W g h t hi hs
    obtain ⟨hrf, -, hs⟩ := hs
    refine ⟨hrf, ?_⟩
    rcases hs with hv | ⟨U, h', t', hx, hu, st, hh, hs⟩
    · exact .inl hv
    · have ⟨hK, hi'⟩ := hk g h t h' t' hi st
      exact .inr ⟨U, h', t', hx, hu, st, hh, ih hi' (hs (hK _ _))⟩

/-- **`J` holds at every state reached within the budget** (proved): along
the executions meeting an invariant on which every step keeps the
obligation, a state reached in `j < n` steps meets `J`. The calculus is
deterministic (`Step_det`), so the state reached is the one the safety
derivation follows. -/
theorem SafeUnder.reach {I : γ → Heap → Tm → Prop} (hk : KeepsOn K next I) :
    ∀ {n : Nat} {W : WorldT n} {g : γ} {h : Heap} {t : Tm}, I g h t →
      SafeUnder K next J Ξ T Q R n W g h t →
      ∀ {j : Nat} {h' : Heap} {t' : Tm}, j < n → Steps j h t h' t' → J h' t' := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ j _ _ hj; omega
  | succ n ih =>
    intro W g h t hi hs j h' t' hj hst
    obtain ⟨-, hJ, hs⟩ := hs
    cases hst with
    | refl => exact hJ
    | next st₁ hrest =>
      rcases hs with (⟨hv, -⟩ | ⟨hr, -⟩) | ⟨U, h₂, t₂, -, -, st₂, -, hs⟩
      · exact absurd st₁ (value_no_step hv)
      · exact absurd st₁ hr.no_step
      · obtain ⟨rfl, rfl⟩ := Step_det st₁ st₂
        have ⟨hK, hi'⟩ := hk g h t _ _ hi st₂
        exact ih hi' (hs (hK _ _)) (by omega) hrest

/-- **Ordinary safety is safety along every set of executions** (proved):
`SafePostExcW` with `J` at every state reached within the budget gives
`SafeUnder` for every obligation, ghost and threading. -/
theorem SafeUnder.of_safe :
    ∀ {n : Nat} {W : WorldT n} {g : γ} {h : Heap} {t : Tm},
      (∀ {j : Nat} {h' : Heap} {t' : Tm}, j < n → Steps j h t h' t' → J h' t') →
      SafePostExcW Ξ T Q R n W h t → SafeUnder K next J Ξ T Q R n W g h t := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ hs; exact hs
  | succ n ih =>
    intro W g h t hJ hs
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hrf, hJ (Nat.succ_pos n) .refl, ?_⟩
    rcases hs with hv | ⟨U, h', t', hx, hu, st, hh, hs⟩
    · exact .inl hv
    · exact .inr ⟨U, h', t', hx, hu, st, hh, fun _ =>
        ih (fun hj hr => hJ (by omega) (.next st hr)) hs⟩

end
end Verification.HeapObservations
