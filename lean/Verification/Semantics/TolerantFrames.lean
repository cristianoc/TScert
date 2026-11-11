import Verification.Semantics.ArgumentStoreRegions

/-! # Tolerant frames over indexed states

The states of the note "Tolerant frames" read in the indexed model. A
**state** is a budget, a world at that budget and a heap meeting it, the
budget positive: the safety predicates state nothing at budget zero
(`Safe Ξ T 0 W h t` is `True`), so no assertion is read there. An
**admissible transition** drops the budget and extends the truncated world;
heap growth and the contents of every location whose contract admits one value
follow from it. A **safe run** of a term from a state, to a point with budget
left, ends in a state an admissible transition reaches, its intermediate
worlds the ones the safety derivation supplies (`run`). -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations

/-! ## States and admissible transitions -/

/-- A state: budget `n`, positive, a world at `n` whose contracts survive
allocation, and a heap meeting the world. -/
structure IndexedHeap where
  n : Nat
  W : WorldT n
  h : Heap
  pos : 0 < n
  adm : WorldAdm W
  ok : HeapOk n W h

/-- An assertion, read at a name valuation, an entry mark and a state. -/
abbrev Assertion := Env → Nat → IndexedHeap → Prop

/-- `s'` is reachable from `s` by what safe code may do: its budget is at
most `s`'s, and its world extends `s`'s world truncated to its budget. -/
def Admissible (s s' : IndexedHeap) : Prop :=
  ∃ hle : s'.n ≤ s.n, WExt (trunc s'.n hle s.W) s'.W

namespace Admissible

theorem refl (s : IndexedHeap) : Admissible s s :=
  ⟨Nat.le_refl _, by rw [trunc_id]; exact WExt_refl _⟩

/-- Composition through the intermediate state's world. -/
theorem trans {s₁ s₂ s₃ : IndexedHeap} (h₁ : Admissible s₁ s₂) (h₂ : Admissible s₂ s₃) :
    Admissible s₁ s₃ := by
  obtain ⟨hle₁, hx₁⟩ := h₁
  obtain ⟨hle₂, hx₂⟩ := h₂
  refine ⟨Nat.le_trans hle₂ hle₁, ?_⟩
  simpa only [trunc_trunc] using WExt_trans (WExt_trunc hle₂ hx₁) hx₂

theorem budget_le {s s' : IndexedHeap} (ha : Admissible s s') : s'.n ≤ s.n := by
  obtain ⟨hle, -⟩ := ha
  exact hle

/-- The heap grows: each heap is as long as its world, and the world only
grows. -/
theorem length_le {s s' : IndexedHeap} (ha : Admissible s s') : s.h.length ≤ s'.h.length := by
  obtain ⟨hle, tail, ht⟩ := ha
  rw [s.ok.1, s'.ok.1, ht]
  simp [trunc]

/-- Every location of `s`'s world keeps its contract, restricted to the lower
budget. -/
theorem lookup_ext {s s' : IndexedHeap} (ha : Admissible s s') {l : Nat} {c : Ctr s.n}
    (hl : lookup s.W l = some c) :
    ∃ hle : s'.n ≤ s.n, lookup s'.W l = some (fun i hi w => c i (Nat.lt_of_lt_of_le hi hle) w) := by
  obtain ⟨hle, hx⟩ := ha
  exact ⟨hle, WExt_lookup hx (lookup_trunc hle s.W l c hl)⟩

/-- **A location whose contract admits one value holds it after every
admissible transition** (at the positive budget every state has). -/
theorem stable_value {s s' : IndexedHeap} (ha : Admissible s s') {l : Nat} {c : Ctr s.n} {v : Val}
    (hl : lookup s.W l = some c) (hc : CtrStable c v) : s'.h[l]? = some v := by
  obtain ⟨hle, hx⟩ := ha
  exact s'.ok.stable_value s'.pos (WExt_lookup hx (lookup_trunc hle s.W l c hl)) (hc.restrict hle)

/-- A path through locations with single-value contracts stays one. -/
theorem stablePath {s s' : IndexedHeap} (ha : Admissible s s') {x : Val} {p : List String} {v : Val}
    (hp : StablePath s.W x p v) : StablePath s'.W x p v := by
  obtain ⟨hle, hx⟩ := ha
  exact hp.transfer hle hx

/-- **A stable path reads its value after every admissible transition.** -/
theorem readPath {s s' : IndexedHeap} (ha : Admissible s s') {x : Val} {p : List String} {v : Val}
    (hp : StablePath s.W x p v) : HeapKnowledge.readPath s'.h x p = some v :=
  (ha.stablePath hp).read s'.pos s'.ok

end Admissible

theorem IndexedHeap.stable_value (s : IndexedHeap) {l : Nat} {c : Ctr s.n} {v : Val}
    (hl : lookup s.W l = some c) (hc : CtrStable c v) : s.h[l]? = some v :=
  s.ok.stable_value s.pos hl hc

/-- At budget zero safety states nothing: the obligation the positive-budget
convention leaves out. -/
theorem safe_zero {Ξ T : Fam} {W : WorldT 0} {h : Heap} {t : Tm} : Safe Ξ T 0 W h t := trivial

/-! ## Adequacy: safe runs are admissible -/

/-- **A run that a safety derivation covers, with budget left, ends in a
state an admissible transition reaches**, the safety derivation continuing
there. The intermediate worlds are those the derivation supplies at each
step; determinism of the step relation matches them to the run. -/
theorem run {Ξ T : Fam} {Q : Post} {R : Heap → Prop} :
    ∀ {k h t h' t'}, Steps k h t h' t' → ∀ (s : IndexedHeap), s.h = h → k < s.n →
      SafePostExc Ξ T Q R s.n s.W s.h t →
      ∃ s' : IndexedHeap, Admissible s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧
        SafePostExc Ξ T Q R s'.n s'.W s'.h t' := by
  intro k h t h' t' hst
  induction hst with
  | refl => intro s hs _ hsafe; exact ⟨s, Admissible.refl s, hs, rfl, hsafe⟩
  | next st _ ih =>
    intro s hs hk hsafe
    obtain ⟨n, W, h₀, pos, adm, ok⟩ := s
    simp only at hs hk hsafe ⊢
    subst hs
    cases n with
    | zero => omega
    | succ m =>
      rcases hsafe with (⟨hv, -, -⟩ | ⟨hr, -⟩) | ⟨U, h₁, t₁, hx, hu, st', hh, hs'⟩
      · exact absurd st (value_no_step hv)
      · exact absurd st hr.no_step
      · obtain ⟨rfl, rfl⟩ := Step_det st st'
        obtain ⟨s', ha, he, hn, hsafe'⟩ :=
          ih ⟨m, U, _, by omega, hu, hh⟩ rfl (by simp only; omega) hs'
        exact ⟨s', Admissible.trans ⟨Nat.le_succ m, hx⟩ ha, he, by simp only at hn; omega, hsafe'⟩

/-- At positive budget, a value's safety gives its type and the
postcondition. -/
theorem exit_value {Ξ T : Fam} {Q : Post} {R : Heap → Prop} {n : Nat} {W : WorldT n} {h : Heap} {v : Tm}
    (hn : 0 < n) (hv : isVal v = true) (hs : SafePostExc Ξ T Q R n W h v) : T n W v ∧ Q h v := by
  cases n with
  | zero => exact absurd hn (Nat.lt_irrefl 0)
  | succ j =>
    rcases hs with (⟨-, hT, hQ⟩ | ⟨hr, -⟩) | ⟨_, _, _, _, _, st, _, _⟩
    · exact ⟨hT, hQ⟩
    · exact absurd hv (by rw [hr.not_val]; simp)
    · exact absurd st (value_no_step hv)

/-- At positive budget, a raise's safety gives a thrown value of the
exception family and the throw's postcondition. -/
theorem exit_raise {Ξ T : Fam} {Q : Post} {R : Heap → Prop} {n : Nat} {W : WorldT n} {h : Heap} {t e : Tm}
    (hn : 0 < n) (hr : Raises t e) (hs : SafePostExc Ξ T Q R n W h t) : Thrown Ξ n W t ∧ R h := by
  cases n with
  | zero => exact absurd hn (Nat.lt_irrefl 0)
  | succ j =>
    rcases hs with (⟨hv, -, -⟩ | ⟨hth, hR⟩) | ⟨_, _, _, _, _, st, _, _⟩
    · rw [raises_not_val hr] at hv; cases hv
    · exact ⟨hth, hR⟩
    · exact absurd st (raises_no_step hr)

/-- The normal exit: a run to a value, with budget left, ends in an
admissible state where the value meets its type and the postcondition. -/
theorem run_normal {Ξ T : Fam} {Q : Post} {R : Heap → Prop} {s : IndexedHeap} {t v : Tm} {h' : Heap} {k : Nat}
    (hsafe : SafePostExc Ξ T Q R s.n s.W s.h t) (hst : Steps k s.h t h' v) (hv : isVal v = true)
    (hk : k < s.n) :
    ∃ s' : IndexedHeap, Admissible s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧ T s'.n s'.W v ∧ Q h' v := by
  obtain ⟨s', ha, he, hn, hs'⟩ := run hst s rfl hk hsafe
  exact ⟨s', ha, he, hn, he ▸ exit_value s'.pos hv hs'⟩

/-- The exceptional exit: a run to a raise, with budget left, ends in an
admissible state where the thrown value is of the exception family and the
throw's postcondition holds. -/
theorem run_throw {Ξ T : Fam} {Q : Post} {R : Heap → Prop} {s : IndexedHeap} {t t' e : Tm} {h' : Heap} {k : Nat}
    (hsafe : SafePostExc Ξ T Q R s.n s.W s.h t) (hst : Steps k s.h t h' t') (hr : Raises t' e)
    (hk : k < s.n) :
    ∃ s' : IndexedHeap, Admissible s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧ Thrown Ξ s'.n s'.W t' ∧ R h' := by
  obtain ⟨s', ha, he, hn, hs'⟩ := run hst s rfl hk hsafe
  exact ⟨s', ha, he, hn, he ▸ exit_raise s'.pos hr hs'⟩

/-- Plain safety: a run with budget left ends in an admissible state, safety
continuing there. -/
theorem safe_run {Ξ T : Fam} {s : IndexedHeap} {t t' : Tm} {h' : Heap} {k : Nat}
    (hsafe : Safe Ξ T s.n s.W s.h t) (hst : Steps k s.h t h' t') (hk : k < s.n) :
    ∃ s' : IndexedHeap, Admissible s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧ Safe Ξ T s'.n s'.W s'.h t' := by
  have hp : SafePostExc Ξ T (fun _ _ => True) (fun _ => True) s.n s.W s.h t :=
    SafePostExc.of_post (fun _ => trivial) (of_value_property (fun _ _ _ _ _ => trivial) hsafe)
  obtain ⟨s', ha, he, hn, hs'⟩ := run hst s rfl hk hp
  exact ⟨s', ha, he, hn, erase hs'.post⟩

end Verification.TolerantFrames
