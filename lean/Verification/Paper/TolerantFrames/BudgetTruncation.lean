import Verification.Paper.TolerantFrames.WorldIndependence

/-! # Exact budget transport for syntactic assertions

The existing shared world restriction preserves the heap. An action's future
can be projected to positive budget one without changing any footprint reading.
Structural induction therefore gives equivalence under truncation for the whole
positive assertion grammar, including modalities. Arbitrary semantic predicates
are not covered. Entry/current transition transport has explicit budget bounds.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge HeapObservations TolerantFrames

/-- General positive restriction extends the existing one-level HeapOk_trunc. -/
theorem heapOk_restrict (s : IndexedHeap) {j : Nat} (hj : j ≤ s.n) : HeapOk j (trunc j hj s.W) s.h := by
  refine ⟨⟨by simpa using s.ok.1.1, ?_⟩, Shaped_trunc hj s.ok.2⟩
  intro l c hc
  obtain ⟨d, hd, rfl⟩ := lookup_trunc_inv hj s.W l c hc
  obtain ⟨v, hv, hm⟩ := s.ok.1.2 l d hd
  refine ⟨v, hv, fun i hi => ?_⟩
  rw [trunc_trunc]
  exact hm i (Nat.lt_of_lt_of_le hi hj)

def truncateBudget (s : IndexedHeap) (j : Nat) (hpos : 0 < j) (hj : j ≤ s.n) : IndexedHeap :=
  ⟨j, trunc j hj s.W, s.h, hpos, WorldAdm_trunc hj s.adm, heapOk_restrict s hj⟩

theorem truncateBudget_reachable (s : IndexedHeap) (j : Nat) (hpos : 0 < j) (hj : j ≤ s.n) :
    Admissible s (truncateBudget s j hpos hj) := ⟨hj, WExt_refl _⟩

/-- The unchanged heap and world-role restriction preserve program roots. -/
theorem ValidContext.truncate_budget {ρ m s} (hv : ValidContext ρ m s)
    (j : Nat) (hpos : 0 < j) (hj : j ≤ s.n) : ValidContext ρ m (truncateBudget s j hpos hj) :=
  ⟨fun x => RefsOk_trunc hj (hv.1 x), hv.2.1, hv.2.2⟩

/-- Returned/thrown source values keep their world references at restriction. -/
theorem ExitValid.truncate_budget {e s} (hv : ExitValid e s)
    (j : Nat) (hpos : 0 < j) (hj : j ≤ s.n) : ExitValid e (truncateBudget s j hpos hj) := by
  cases e with
  | normal | «break» => trivial
  | returned _ | thrown _ => exact ⟨hv.1, RefsOk_trunc hj hv.2⟩

/-- Project any original future to a future of any positive source restriction. -/
theorem future_project_one {s t : IndexedHeap} (ha : Admissible s t)
    (j : Nat) (hpos : 0 < j) (hj : j ≤ s.n) :
    Admissible (truncateBudget s j hpos hj) (truncateBudget t 1 Nat.one_pos t.pos) := by
  obtain ⟨ht, hx⟩ := ha
  refine ⟨hpos, ?_⟩
  change WExt (trunc 1 hpos (trunc j hj s.W)) (trunc 1 t.pos t.W)
  rw [trunc_trunc]
  simpa only [trunc_trunc] using WExt_trunc t.pos hx

/-- At a known lower-budget exit, source restriction neither adds nor removes
an action. Its regional postcondition is literally the same heap predicate. -/
theorem action_truncate_source_iff {s t : IndexedHeap} {Φ : Footprint} {ρ : Env}
    (j : Nat) (hpos : 0 < j) (hj : j ≤ s.n) (ht : t.n ≤ j) :
    Action Φ ρ s t ↔ Action Φ ρ (truncateBudget s j hpos hj) t := by
  constructor
  · rintro ⟨⟨_, hx⟩, hp⟩
    refine ⟨⟨ht, ?_⟩, hp⟩
    simpa only [truncateBudget, trunc_trunc] using hx
  · rintro ⟨ha, hp⟩
    exact ⟨(truncateBudget_reachable s j hpos hj).trans ha, hp⟩

/-- The entire syntactic assertion grammar is invariant under positive
same-heap world restriction. This is stronger than modality-free heap reading,
but weaker than independence from worlds with different contracts. -/
theorem Formula.holds_truncate (F : Formula) (ρ : Env) (m : Nat) (s : IndexedHeap)
    (j : Nat) (hpos : 0 < j) (hj : j ≤ s.n) :
    F.Holds ρ m s ↔ F.Holds ρ m (truncateBudget s j hpos hj) := by
  induction F generalizing ρ s j with
  | truth | falsity | atom _ | separated _ _ | apart _ _ | fresh _ => rfl
  | and _ _ ih₁ ih₂ => exact and_congr (ih₁ ρ s j hpos hj) (ih₂ ρ s j hpos hj)
  | or _ _ ih₁ ih₂ => exact or_congr (ih₁ ρ s j hpos hj) (ih₂ ρ s j hpos hj)
  | existsValue _ ih =>
    exact exists_congr fun v => and_congr_right fun _ => and_congr_right fun _ => ih (push v ρ) s j hpos hj
  | box Φ F ih =>
    constructor
    · intro hb t ha
      exact hb t ⟨(truncateBudget_reachable s j hpos hj).trans ha.1, ha.2⟩
    · intro hb t ha
      have hlow : F.Holds ρ m (truncateBudget t 1 Nat.one_pos t.pos) :=
        hb _ ⟨future_project_one ha.1 j hpos hj, ha.2⟩
      exact (ih ρ t 1 Nat.one_pos t.pos).mpr hlow

namespace TwoState

/-- Entry metadata is read only by old TERMS inside an assertion; it is not
the focus of an old assertion until Post.old selects it. -/
theorem Assertion.entry_heap {F : Assertion} {entry entry' : State} (he : SameHeapReads entry entry')
    (focus : State) (m : Nat) (η : LogicalEnv) : F.Holds entry focus m η ↔ F.Holds entry' focus m η := by
  induction F generalizing focus η with
  | truth | falsity | separated _ _ | apart _ _ | fresh _ => rfl
  | atom a => exact a.holds_heap he ⟨rfl, rfl⟩ η
  | and _ _ ih₁ ih₂ => exact and_congr (ih₁ focus η) (ih₂ focus η)
  | or _ _ ih₁ ih₂ => exact or_congr (ih₁ focus η) (ih₂ focus η)
  | existsValue _ ih =>
    exact exists_congr fun v => and_congr_right fun _ => and_congr_right fun _ => ih focus {η with values := push v η.values}
  | box Φ F ih => exact forall_congr' fun t => imp_congr Iff.rfl (ih {focus with heap := t} η)

theorem Assertion.focus_truncate (F : Assertion) (entry focus : State) (m : Nat) (η : LogicalEnv)
    (j : Nat) (hpos : 0 < j) (hj : j ≤ focus.heap.n) :
    F.Holds entry focus m η ↔ F.Holds entry {focus with heap := truncateBudget focus.heap j hpos hj} m η := by
  induction F generalizing focus η j with
  | truth | falsity | separated _ _ | apart _ _ | fresh _ => rfl
  | atom a =>
    exact a.holds_heap (entry := entry) (entry' := entry) (focus := focus)
      (focus' := {focus with heap := truncateBudget focus.heap j hpos hj}) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ η
  | and _ _ ih₁ ih₂ => exact and_congr (ih₁ focus η j hpos hj) (ih₂ focus η j hpos hj)
  | or _ _ ih₁ ih₂ => exact or_congr (ih₁ focus η j hpos hj) (ih₂ focus η j hpos hj)
  | existsValue _ ih =>
    exact exists_congr fun v => and_congr_right fun _ => and_congr_right fun _ =>
      ih focus {η with values := push v η.values} j hpos hj
  | box Φ F ih =>
    constructor
    · intro hb t ha
      exact hb t ⟨(truncateBudget_reachable focus.heap j hpos hj).trans ha.1, ha.2⟩
    · intro hb t ha
      have hlow := hb _ ⟨future_project_one ha.1 j hpos hj, ha.2⟩
      exact (ih {focus with heap := t} η 1 Nat.one_pos t.pos).mpr hlow

/-- Exact entry restriction for full postconditions, including arbitrary
implication. Transition atoms require the known exit budget bound. -/
theorem Post.entry_truncate (Q : Post) (c : Context) (η : LogicalEnv)
    (j : Nat) (hpos : 0 < j) (hj : j ≤ c.entry.heap.n) (ht : c.current.heap.n ≤ j) :
    Q.Holds c η ↔ Q.Holds {c with entry := {c.entry with heap := truncateBudget c.entry.heap j hpos hj}} η := by
  induction Q generalizing η with
  | assertion F => exact F.entry_heap (entry := c.entry) (entry' := {c.entry with heap := truncateBudget c.entry.heap j hpos hj}) ⟨rfl, rfl⟩ c.current c.mark η
  | old F =>
    exact (F.entry_heap (entry := c.entry) (entry' := {c.entry with heap := truncateBudget c.entry.heap j hpos hj}) ⟨rfl, rfl⟩ c.entry c.mark η).trans
      (F.focus_truncate {c.entry with heap := truncateBudget c.entry.heap j hpos hj} c.entry c.mark η j hpos hj)
  | transition Φ => exact action_truncate_source_iff j hpos hj ht
  | and _ _ ih₁ ih₂ => exact and_congr (ih₁ η) (ih₂ η)
  | or _ _ ih₁ ih₂ => exact or_congr (ih₁ η) (ih₂ η)
  | implication _ _ ih₁ ih₂ => exact imp_congr (ih₁ η) (ih₂ η)
  | forallIndex _ ih => exact forall_congr' fun i => ih {η with indices := pushIndex i η.indices}
  | forallValue _ ih => exact forall_congr' fun v => imp_congr Iff.rfl (imp_congr Iff.rfl (ih {η with values := push v η.values}))

/-- Restrict a chosen actual exit, keeping its heap. Original admissibility
is essential for reflecting transition atoms; arbitrary pairs are not covered. -/
theorem Post.current_truncate (Q : Post) (c : Context) (η : LogicalEnv)
    (j : Nat) (hpos : 0 < j) (hj : j ≤ c.current.heap.n)
    (ha : Admissible c.entry.heap c.current.heap) :
    Q.Holds c η ↔ Q.Holds {c with current := {c.current with heap := truncateBudget c.current.heap j hpos hj}} η := by
  induction Q generalizing η with
  | assertion F => exact F.focus_truncate c.entry c.current c.mark η j hpos hj
  | old F => rfl
  | transition Φ =>
    have hat := ha.trans (truncateBudget_reachable c.current.heap j hpos hj)
    exact ⟨fun hp => ⟨hat, hp.2⟩, fun hp => ⟨ha, hp.2⟩⟩
  | and _ _ ih₁ ih₂ => exact and_congr (ih₁ η) (ih₂ η)
  | or _ _ ih₁ ih₂ => exact or_congr (ih₁ η) (ih₂ η)
  | implication _ _ ih₁ ih₂ => exact imp_congr (ih₁ η) (ih₂ η)
  | forallIndex _ ih => exact forall_congr' fun i => ih {η with indices := pushIndex i η.indices}
  | forallValue _ ih => exact forall_congr' fun v => imp_congr Iff.rfl (imp_congr Iff.rfl (ih {η with values := push v η.values}))

end TwoState
end Verification.Paper.TolerantFrames
