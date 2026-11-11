import Verification.Semantics.ArgumentStoreRegions

/-! # Tolerant frames over indexed states

The states of the note "Tolerant frames" read in the indexed model. A
**state** is a budget, a world at that budget and a heap meeting it, the
budget positive: the safety predicates state nothing at budget zero
(`Safe Ξ T 0 W h t` is `True`), so no assertion is read there. An
**admissible transition** drops the budget and extends the truncated world;
heap growth and the contents of every location whose contract admits one value
follow from it. -/
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

end Verification.TolerantFrames
