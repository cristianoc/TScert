import Verification.Semantics.Footprints
import Verification.Semantics.HeapObservations

/-! # Closed footprints

A **closed footprint** mentions only the two classes of contents: a change for
the old locations holding a value and one for the old locations holding an
array store. On a value, `grow` is `keep`, so there are six. They are ordered
exactly by their entries (`closed_order_exact`), their postcondition reads no
slot, and the empty one and the one letting everything change are the two
heap effects of a call signature that state no footprint relation beyond
prefix and growth (`Closed.holds_empty`, `Closed.holds_top`). Heaps only grow
under steps, so every run meets the latter (`Closed.top_safe`). -/
namespace Verification.Footprints

/-! ## Heaps grow -/

theorem step_length_le {h t h' t'} (st : Step h t h' t') : h.length ≤ h'.length := by
  induction st <;> simp_all [List.length_append, List.length_set] <;> omega

theorem steps_grow {k h t h' t'} (st : HeapObservations.Steps k h t h' t') : h.length ≤ h'.length := by
  induction st with
  | refl => exact Nat.le_refl _
  | next s _ ih => exact Nat.le_trans (step_length_le s) ih

/-! ## Closed footprints -/

/-- A closed footprint: a change for each class of contents. -/
structure Closed where
  value : Change
  store : Change
  deriving DecidableEq, Repr

def Closed.fp (c : Closed) : Footprint := [(.cls .value, c.value), (.cls .store, c.store)]

/-- On contents of class `value`, `grow` is `keep`. -/
def Change.onValue : Change → Change
  | .grow => .keep
  | d => d

def Closed.le (a b : Closed) : Bool := a.value.onValue.le b.value.onValue && a.store.le b.store

private theorem value_change {δ δ' : Change} {b v v'} (hv : isArr v = false)
    (hle : δ.onValue.le δ'.onValue = true) (h : δ.Holds b v v') : δ'.Holds b v v' := by
  cases δ with
  | grow => rw [h.grow_value hv]; exact Change.Holds.refl _ _ _
  | keep => simp only [Change.Holds] at h; rw [h]; exact Change.Holds.refl _ _ _
  | any => cases δ' <;> simp_all [Change.onValue, Change.le, Change.Holds]

theorem Closed.post_mono {a b : Closed} (hle : a.le b = true) {ρ h h'} (hp : Post a.fp ρ h h') :
    Post b.fp ρ h h' := by
  simp only [Closed.le, Bool.and_eq_true] at hle
  refine ⟨hp.1, fun l v hv => ?_⟩
  obtain ⟨v', hv', ha⟩ := hp.2 l v hv
  refine ⟨v', hv', ?_⟩
  rcases ha with rfl | ⟨e, he, hm, hh⟩
  · exact .inl rfl
  · simp only [Closed.fp, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · have hc : isArr v = false := by simpa [Region.mem, hv, Cls.has] using hm
      exact .inr ⟨_, List.mem_cons_self .., hm, value_change hc hle.1 hh⟩
    · exact .inr ⟨(.cls .store, b.store), by simp [Closed.fp], hm, hh.mono hle.2⟩

private def ρ₀ : Env := fun _ => .undef

private theorem single_post {Φ : Footprint} {v v' : Val} (hp : Post Φ ρ₀ [v] [v']) :
    v' = v ∨ ∃ e ∈ Φ, e.1.mem ρ₀ [v] 0 = true ∧ e.2.Holds 1 v v' := by
  obtain ⟨v₁, hv₁, ha⟩ := hp.2 0 v rfl
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hv₁
  subst hv₁
  exact ha

/-- **The closed footprints are ordered exactly by their entries.** -/
theorem closed_order_exact (a b : Closed) :
    a.le b = true ↔ ∀ ρ h h', Post a.fp ρ h h' → Post b.fp ρ h h' := by
  refine ⟨fun hle _ _ _ => Closed.post_mono hle, fun H => ?_⟩
  simp only [Closed.le, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · -- a value location changes arbitrarily
    cases ha : a.value <;> cases hb : b.value <;> simp [Change.onValue, Change.le] <;>
    · have hp : Post a.fp ρ₀ [.nul] [.tru] :=
        ⟨by simp, fun l v hv => by
          cases l with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hv; subst hv
            exact ⟨.tru, rfl, .inr ⟨(.cls .value, a.value), List.mem_cons_self .., by simp [Region.mem, Cls.has, isArr], by
              show a.value.Holds _ _ _
              rw [ha]; trivial⟩⟩
          | succ l => simp at hv⟩
      rcases single_post (H _ _ _ hp) with h | ⟨e, he, hm, hh⟩
      · cases h
      · simp only [Closed.fp, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · simp only [hb] at hh
          simp [Change.Holds] at hh
        · simp [Region.mem, Cls.has, isArr] at hm
  · cases ha : a.store <;> cases hb : b.store <;> simp [Change.le]
    · -- grow against keep: a store gains a fresh element location
      have hp : Post a.fp ρ₀ [.arr []] [.arr [some 1]] :=
        ⟨by simp, fun l v hv => by
          cases l with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hv; subst hv
            exact ⟨_, rfl, .inr ⟨(.cls .store, a.store), by simp [Closed.fp], by simp [Region.mem, Cls.has, isArr], by
              show a.store.Holds _ _ _
              rw [ha]; exact (Change.holdsB_iff _ _ _ _).mp (by decide)⟩⟩
          | succ l => simp at hv⟩
      rcases single_post (H _ _ _ hp) with h | ⟨e, he, hm, hh⟩
      · cases h
      · simp only [Closed.fp, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · simp [Region.mem, Cls.has, isArr] at hm
        · simp only [hb] at hh
          simp [Change.Holds] at hh
    all_goals
      -- any against keep or grow: a dense store loses its index
      have hp : Post a.fp ρ₀ [.arr [some 0]] [.arr []] :=
        ⟨by simp, fun l v hv => by
          cases l with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hv; subst hv
            exact ⟨_, rfl, .inr ⟨(.cls .store, a.store), by simp [Closed.fp], by simp [Region.mem, Cls.has, isArr], by
              show a.store.Holds _ _ _
              rw [ha]; trivial⟩⟩
          | succ l => simp at hv⟩
      rcases single_post (H _ _ _ hp) with h | ⟨e, he, hm, hh⟩
      · cases h
      · simp only [Closed.fp, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · simp [Region.mem, Cls.has, isArr] at hm
        · simp only [hb] at hh
          exact absurd ((Change.holdsB_iff _ _ _ _).mpr hh) (by decide)

/-! ## Closed footprints as call effects -/

/-- The footprint letting no old location change, and the one letting every
old location change. -/
def Closed.empty : Closed := ⟨.keep, .keep⟩
def Closed.top : Closed := ⟨.any, .any⟩

/-- The change a closed footprint allows on contents `v`, by their class. -/
def Closed.at (c : Closed) (v : Val) : Change := if isArr v then c.store else c.value

/-- A closed footprint's postcondition, from the heap a call starts in to the
heap it returns with. Its regions read no slot. -/
def Closed.Holds (c : Closed) (h h' : Heap) : Prop := Post c.fp (fun _ => .undef) h h'

theorem Closed.allowed_iff {c : Closed} {ρ : Env} {h : Heap} {l : Nat} {v v' : Val}
    (hv : h[l]? = some v) : Allowed c.fp ρ h l v v' ↔ (c.at v).Holds h.length v v' := by
  constructor
  · rintro (rfl | ⟨e, he, hm, hh⟩)
    · exact Change.Holds.refl _ _ _
    · simp only [Closed.fp, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> cases ha : isArr v <;>
        simp_all [Region.mem, Cls.has, Closed.at]
  · intro hh
    refine .inr ?_
    cases ha : isArr v
    · exact ⟨(.cls .value, c.value), by simp [Closed.fp], by simp [Region.mem, hv, Cls.has, ha],
        by simpa [Closed.at, ha] using hh⟩
    · exact ⟨(.cls .store, c.store), by simp [Closed.fp], by simp [Region.mem, hv, Cls.has, ha],
        by simpa [Closed.at, ha] using hh⟩

/-- A closed footprint's postcondition at any assignment of slots: each old
location changes within its class's change. -/
theorem Closed.post_iff {c : Closed} {ρ : Env} {h h' : Heap} :
    Post c.fp ρ h h' ↔ h.length ≤ h'.length ∧
      ∀ (l : Nat) (v : Val), h[l]? = some v → ∃ v', h'[l]? = some v' ∧ (c.at v).Holds h.length v v' :=
  and_congr Iff.rfl (forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun hv =>
    exists_congr fun _ => and_congr Iff.rfl (Closed.allowed_iff hv))

theorem Closed.holds_iff {c : Closed} {h h' : Heap} :
    c.Holds h h' ↔ h.length ≤ h'.length ∧
      ∀ (l : Nat) (v : Val), h[l]? = some v → ∃ v', h'[l]? = some v' ∧ (c.at v).Holds h.length v v' :=
  Closed.post_iff

theorem Closed.Holds.mono {a b : Closed} (hle : a.le b = true) {h h' : Heap} (hp : a.Holds h h') :
    b.Holds h h' :=
  Closed.post_mono hle hp

/-- **The empty closed footprint is heap preservation.** -/
theorem Closed.holds_empty {h h' : Heap} : Closed.empty.Holds h h' ↔ h.IsPrefix h' := by
  rw [Closed.holds_iff, ← Post.empty_iff (ρ := fun _ => .undef)]
  refine and_congr Iff.rfl (forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    exists_congr fun _ => and_congr Iff.rfl ?_)
  simp [Closed.at, Closed.empty, Allowed, Change.Holds]

/-- **The closed footprint letting everything change is growth**, which every
run meets (`Closed.top_safe`). -/
theorem Closed.holds_top {h h' : Heap} : Closed.top.Holds h h' ↔ h.length ≤ h'.length := by
  rw [Closed.holds_iff]
  refine ⟨fun hp => hp.1, fun hlen => ⟨hlen, fun l v hv => ?_⟩⟩
  have hl := (List.getElem?_eq_some_iff.mp hv).1
  refine ⟨h'[l], List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hl hlen), ?_⟩
  simp only [Closed.at, Closed.top]
  split <;> trivial

theorem Closed.empty_le (c : Closed) : Closed.empty.le c = true := by
  cases c with
  | mk v s => cases v <;> cases s <;> rfl

/-- On contents a change other than `any` keeps, a closed footprint allows
the same change. -/
private theorem Closed.at_of_holds {c : Closed} {b v v'} (h : (c.at v).Holds b v v')
    (hne : c.at v ≠ .any) : c.at v' = c.at v := by
  have := Change.Holds.same_class hne h .store
  simp only [Cls.has] at this
  simp only [Closed.at, this]

/-- **A closed footprint composes with itself**: two runs each within it are
within it together. -/
theorem Closed.Holds.trans {c : Closed} {h₀ h h' : Heap} (h₁ : c.Holds h₀ h) (h₂ : c.Holds h h') :
    c.Holds h₀ h' := by
  rw [Closed.holds_iff] at h₁ h₂ ⊢
  refine ⟨Nat.le_trans h₁.1 h₂.1, fun l v hv => ?_⟩
  obtain ⟨v₁, hv₁, hc₁⟩ := h₁.2 l v hv
  obtain ⟨v₂, hv₂, hc₂⟩ := h₂.2 l v₁ hv₁
  refine ⟨v₂, hv₂, ?_⟩
  by_cases hany : c.at v = .any
  · rw [hany]; trivial
  · have heq := Closed.at_of_holds hc₁ hany
    rw [heq] at hc₂
    exact hc₁.trans h₁.1 hc₂

theorem Closed.Holds.refl (c : Closed) (h : Heap) : c.Holds h h :=
  Closed.Holds.mono (Closed.empty_le c) (Closed.holds_empty.mpr (List.prefix_refl h))

/-- A footprint from a later heap holds from an earlier one the later one
extends: fresh allocation before a call composes with the call's footprint. -/
theorem Closed.Holds.prefix_left {c : Closed} {h₀ h h' : Heap} (hpre : h₀.IsPrefix h)
    (hp : c.Holds h h') : c.Holds h₀ h' := by
  rw [Closed.holds_iff] at hp ⊢
  refine ⟨Nat.le_trans hpre.length_le hp.1, fun l v hv => ?_⟩
  have hv₀ : h[l]? = some v := by
    obtain ⟨t, rfl⟩ := hpre
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hv).1, hv]
  obtain ⟨v', hv', hc⟩ := hp.2 l v hv₀
  exact ⟨v', hv', hc.lower hpre.length_le⟩

/-- The weaker of two changes. -/
def Change.min (a b : Change) : Change := if a.le b then a else b

theorem Change.min_holds {a b : Change} {n v v'} :
    (a.min b).Holds n v v' ↔ a.Holds n v v' ∧ b.Holds n v v' := by
  unfold Change.min
  split
  · rename_i hle
    exact ⟨fun h => ⟨h, h.mono hle⟩, And.left⟩
  · rename_i hle
    have hle' : b.le a = true := by cases a <;> cases b <;> simp_all [Change.le]
    exact ⟨fun h => ⟨h.mono hle', h⟩, And.right⟩

/-- Both of two closed footprints: what two signatures of one call guarantee
together. -/
def Closed.meet (a b : Closed) : Closed := ⟨a.value.min b.value, a.store.min b.store⟩

theorem Closed.at_meet (a b : Closed) (v : Val) : (a.meet b).at v = (a.at v).min (b.at v) := by
  unfold Closed.at Closed.meet
  split <;> rfl

theorem Closed.holds_meet {a b : Closed} {h h' : Heap} :
    (a.meet b).Holds h h' ↔ a.Holds h h' ∧ b.Holds h h' := by
  simp only [Closed.holds_iff, Closed.at_meet, Change.min_holds]
  constructor
  · rintro ⟨hl, hall⟩
    refine ⟨⟨hl, fun l v hv => ?_⟩, ⟨hl, fun l v hv => ?_⟩⟩
    · obtain ⟨v', h1, h2⟩ := hall l v hv
      exact ⟨v', h1, h2.1⟩
    · obtain ⟨v', h1, h2⟩ := hall l v hv
      exact ⟨v', h1, h2.2⟩
  · rintro ⟨⟨hl, ha⟩, ⟨-, hb⟩⟩
    refine ⟨hl, fun l v hv => ?_⟩
    obtain ⟨v₁, h1, ha'⟩ := ha l v hv
    obtain ⟨v₂, h2, hb'⟩ := hb l v hv
    obtain rfl : v₁ = v₂ := Option.some.inj (h1.symm.trans h2)
    exact ⟨v₁, h1, ha', hb'⟩

/-- Every run keeps the heap at least as long as a bound it starts above. -/
theorem grow_safe {Ξ R : Fam} {b : Nat} : ∀ {n W h t}, b ≤ h.length → Safe Ξ R n W h t →
    HeapObservations.SafePost Ξ R (fun h' _ => b ≤ h'.length) n W h t := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hb hs
    rcases hs with (⟨hv, ht⟩ | hth) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · exact .inl (.inl ⟨hv, ht, hb⟩)
    · exact .inl (.inr hth)
    · exact .inr ⟨U, h', t', hx, hu, step, hh, ih (Nat.le_trans hb (step_length_le step)) hs⟩

/-- **Every safe run meets the footprint letting everything change.** -/
theorem Closed.top_safe {Ξ R : Fam} {n W h t} (hs : Safe Ξ R n W h t) :
    HeapObservations.SafePost Ξ R (fun h' _ => Closed.top.Holds h h') n W h t :=
  HeapObservations.weaken (fun _ _ hb => Closed.holds_top.mpr hb) (grow_safe (Nat.le_refl _) hs)

/-! ## Footprints on some old locations

A call may change one store beyond its footprint, its receiver's: its
postcondition is the footprint on the old locations other than that store.
A run whose every such store was allocated after a heap of length `b` is
within the footprint on the locations below `b`. -/

/-- A closed footprint's postcondition on the old locations `P` admits. -/
def Closed.HoldsOn (c : Closed) (P : Nat → Prop) (h h' : Heap) : Prop :=
  h.length ≤ h'.length ∧
    ∀ (l : Nat) (v : Val), P l → h[l]? = some v → ∃ v', h'[l]? = some v' ∧ (c.at v).Holds h.length v v'

theorem Closed.Holds.on {c : Closed} {h h' : Heap} (P : Nat → Prop) (hp : c.Holds h h') : c.HoldsOn P h h' := by
  rw [Closed.holds_iff] at hp
  exact ⟨hp.1, fun l v _ hv => hp.2 l v hv⟩

theorem Closed.HoldsOn.weaken {c : Closed} {P Q : Nat → Prop} {h h' : Heap} (hpq : ∀ l, Q l → P l)
    (hp : c.HoldsOn P h h') : c.HoldsOn Q h h' :=
  ⟨hp.1, fun l v hq hv => hp.2 l v (hpq l hq) hv⟩

theorem Closed.holds_of_on {c : Closed} {h h' : Heap} (hp : c.HoldsOn (fun _ => True) h h') : c.Holds h h' := by
  rw [Closed.holds_iff]
  exact ⟨hp.1, fun l v hv => hp.2 l v trivial hv⟩

private theorem Closed.at_mono {a b : Closed} (hle : a.le b = true) {n v v'}
    (h : (a.at v).Holds n v v') : (b.at v).Holds n v v' := by
  simp only [Closed.le, Bool.and_eq_true] at hle
  unfold Closed.at at h ⊢
  cases hv : isArr v
  · simp only [hv] at h ⊢
    exact value_change (by simpa using hv) hle.1 h
  · simp only [hv, if_true] at h ⊢
    exact h.mono hle.2

theorem Closed.HoldsOn.mono {a b : Closed} (hle : a.le b = true) {P : Nat → Prop} {h h' : Heap}
    (hp : a.HoldsOn P h h') : b.HoldsOn P h h' :=
  ⟨hp.1, fun l v hl hv => by
    obtain ⟨v', hv', hc⟩ := hp.2 l v hl hv
    exact ⟨v', hv', Closed.at_mono hle hc⟩⟩

/-- **A run within a footprint, then one within it on the locations below
where the first started, is within it.** -/
theorem Closed.Holds.trans_on {c : Closed} {h₀ h h' : Heap} (h₁ : c.Holds h₀ h)
    (h₂ : c.HoldsOn (· < h₀.length) h h') : c.Holds h₀ h' := by
  rw [Closed.holds_iff] at h₁ ⊢
  refine ⟨Nat.le_trans h₁.1 h₂.1, fun l v hv => ?_⟩
  obtain ⟨v₁, hv₁, hc₁⟩ := h₁.2 l v hv
  obtain ⟨v₂, hv₂, hc₂⟩ := h₂.2 l v₁ (List.getElem?_eq_some_iff.mp hv).1 hv₁
  refine ⟨v₂, hv₂, ?_⟩
  by_cases hany : c.at v = .any
  · rw [hany]; trivial
  · have heq := Closed.at_of_holds hc₁ hany
    rw [heq] at hc₂
    exact hc₁.trans h₁.1 hc₂

theorem Closed.HoldsOn.prefix_left {c : Closed} {P : Nat → Prop} {h₀ h h' : Heap} (hpre : h₀.IsPrefix h)
    (hp : c.HoldsOn P h h') : c.HoldsOn P h₀ h' := by
  refine ⟨Nat.le_trans hpre.length_le hp.1, fun l v hl hv => ?_⟩
  have hv₀ : h[l]? = some v := by
    obtain ⟨t, rfl⟩ := hpre
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hv).1, hv]
  obtain ⟨v', hv', hc⟩ := hp.2 l v hl hv₀
  exact ⟨v', hv', hc.lower hpre.length_le⟩

theorem Closed.holdsOn_meet {a b : Closed} {P : Nat → Prop} {h h' : Heap} :
    (a.meet b).HoldsOn P h h' ↔ a.HoldsOn P h h' ∧ b.HoldsOn P h h' := by
  simp only [Closed.HoldsOn, Closed.at_meet, Change.min_holds]
  constructor
  · rintro ⟨hl, hall⟩
    refine ⟨⟨hl, fun l v hp hv => ?_⟩, ⟨hl, fun l v hp hv => ?_⟩⟩
    · obtain ⟨v', h1, h2⟩ := hall l v hp hv
      exact ⟨v', h1, h2.1⟩
    · obtain ⟨v', h1, h2⟩ := hall l v hp hv
      exact ⟨v', h1, h2.2⟩
  · rintro ⟨⟨hl, ha⟩, ⟨-, hb⟩⟩
    refine ⟨hl, fun l v hp hv => ?_⟩
    obtain ⟨v₁, h1, ha'⟩ := ha l v hp hv
    obtain ⟨v₂, h2, hb'⟩ := hb l v hp hv
    obtain rfl : v₁ = v₂ := Option.some.inj (h1.symm.trans h2)
    exact ⟨v₁, h1, ha', hb'⟩

/-- Any run within a footprint on some locations is within the one letting
everything change. -/
theorem Closed.HoldsOn.top {c : Closed} {P : Nat → Prop} {h h' : Heap} (hp : c.HoldsOn P h h') :
    Closed.top.Holds h h' :=
  Closed.holds_top.mpr hp.1

/-! ## Fresh stores -/

/-- The location of a value's array store, where it has one. -/
def storeOf (v : Tm) : Option Nat := (fieldsOf v).lookup arrayStoreKey

/-- A value whose array store was allocated after a heap of length `b`:
its store's location is at least `b`. It reads no heap: an object's fields
are fixed at its allocation. -/
def FreshAt (b : Nat) (v : Tm) : Prop := ∃ s, storeOf v = some s ∧ b ≤ s

theorem FreshAt.lower {b b' : Nat} {v : Tm} (hb : b ≤ b') (h : FreshAt b' v) : FreshAt b v := by
  obtain ⟨s, hs, hle⟩ := h
  exact ⟨s, hs, Nat.le_trans hb hle⟩

/-- A change on every old location but a fresh value's store is a change on
every location below where it was allocated. -/
theorem Closed.HoldsOn.below_fresh {c : Closed} {b : Nat} {r : Tm} {h h' : Heap} (hf : FreshAt b r)
    (hp : c.HoldsOn (fun l => storeOf r ≠ some l) h h') : c.HoldsOn (· < b) h h' := by
  obtain ⟨s, hs, hle⟩ := hf
  refine hp.weaken fun l hl => ?_
  rw [hs]
  intro he
  cases he
  omega

end Verification.Footprints
