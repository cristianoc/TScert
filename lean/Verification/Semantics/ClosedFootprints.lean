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

/-- A closed footprint: a change for each class of contents. -/
structure Closed where
  value : Change
  store : Change
  deriving DecidableEq, Repr

def Closed.fp (c : Closed) : Footprint := [(.cls .value, c.value), (.cls .store, c.store)]

/-- On contents of class `value`, `grow` is `scalar`. -/
def Change.onValue : Change → Change
  | .grow => .scalar
  | d => d

/-- On a store, `init` and `scalar` are `keep`. -/
def Change.onStore : Change → Change
  | .init | .scalar => .keep
  | d => d

def Closed.le (a b : Closed) : Bool := a.value.onValue.le b.value.onValue && a.store.onStore.le b.store.onStore

private theorem value_change {δ δ' : Change} {b v v'} (hv : isArr v = false)
    (hle : δ.onValue.le δ'.onValue = true) (h : δ.Holds b v v') : δ'.Holds b v v' := by
  have h' : δ.onValue.Holds b v v' := by
    cases δ with
    | grow => exact h.grow_value hv
    | _ => exact h
  have h'' := h'.mono hle
  cases δ' with
  | grow => exact Change.scalar_le_grow h''
  | _ => exact h''

private theorem store_change {δ δ' : Change} {b ls v'}
    (hle : δ.onStore.le δ'.onStore = true) (h : δ.Holds b (.arr ls) v') : δ'.Holds b (.arr ls) v' := by
  have h' : δ.onStore.Holds b (.arr ls) v' := by
    cases δ with
    | init => exact h.init_store
    | scalar => exact h.scalar_store
    | _ => exact h
  have h'' := h'.mono hle
  cases δ' with
  | init => exact .inl h''
  | scalar => exact .inl h''
  | _ => exact h''

private theorem class_change {δ δ' : Change} {b v v'}
    (hv : isArr v = false → δ.onValue.le δ'.onValue = true)
    (hs : isArr v = true → δ.onStore.le δ'.onStore = true) (h : δ.Holds b v v') : δ'.Holds b v v' := by
  cases ha : isArr v
  · exact value_change ha (hv ha) h
  · cases v <;> simp [isArr] at ha
    exact store_change (hs rfl) h

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
    · have hc : isArr v = true := by simpa [Region.mem, hv, Cls.has] using hm
      exact .inr ⟨(.cls .store, b.store), by simp [Closed.fp], hm,
        class_change (fun h => by rw [hc] at h; cases h) (fun _ => hle.2) hh⟩

private def ρ₀ : Env := fun _ => .undef

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

/-- **The closed footprints are ordered exactly by their entries.** -/
theorem closed_order_exact (a b : Closed) :
    a.le b = true ↔ ∀ ρ h h', Post a.fp ρ h h' → Post b.fp ρ h h' := by
  refine ⟨fun hle _ _ _ => Closed.post_mono hle, fun H => ?_⟩
  -- a one-location heap whose change `a` allows and `b` does not
  have refute : ∀ v v', (a.at v).holdsB 1 v v' = true → (b.at v).holdsB 1 v v' = false → False := by
    intro v v' ha hb
    have hp : Post a.fp ρ₀ [v] [v'] := Closed.post_iff.mpr ⟨by simp, fun l u hu => by
      cases l with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hu; subst hu
        exact ⟨v', rfl, (Change.holdsB_iff _ _ _ _).mp ha⟩
      | succ l => simp at hu⟩
    obtain ⟨-, hq⟩ := Closed.post_iff.mp (H _ _ _ hp)
    obtain ⟨u, hu, hh⟩ := hq 0 v rfl
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hu; subst hu
    have h2 := (Change.holdsB_iff _ _ _ _).mpr hh
    simp only [List.length_singleton] at h2
    rw [h2] at hb
    cases hb
  have atv : ∀ c : Closed, c.at .nul = c.value := fun c => by simp [Closed.at, isArr]
  have ats : ∀ (c : Closed) ls, c.at (.arr ls) = c.store := fun c ls => by simp [Closed.at, isArr]
  simp only [Closed.le, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · -- a value location initialized, a number changed, or a number replaced by a store
    have v1 := refute .nul .tru
    have v2 := refute (.num 0) (.num 1)
    have v3 := refute (.num 0) (.arr [])
    have atn : ∀ (c : Closed) b, c.at (.num b) = c.value := fun c b => by simp [Closed.at, isArr]
    rw [atv a, atv b] at v1
    rw [atn a, atn b] at v2 v3
    cases ha : a.value <;> cases hb : b.value <;> rw [ha, hb] at v1 v2 v3 <;>
      simp only [Change.onValue, Change.le, Change.rank] <;> first
        | decide
        | exact (v1 (by decide) (by decide)).elim
        | exact (v2 (by decide) (by decide)).elim
        | exact (v3 (by decide) (by decide)).elim
  · -- a store gaining a fresh element location, or losing a present one
    have s1 := refute (.arr []) (.arr [some 1])
    have s2 := refute (.arr [some 0]) (.arr [])
    rw [ats a, ats b] at s1 s2
    cases ha : a.store <;> cases hb : b.store <;> rw [ha, hb] at s1 s2 <;>
      simp only [Change.onStore, Change.le, Change.rank] <;> first
        | decide
        | exact (s1 (by decide) (by decide)).elim
        | exact (s2 (by decide) (by decide)).elim

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

/-- The join of two closed footprints: each component's larger change. -/
def Closed.join (a b : Closed) : Closed := ⟨a.value.max b.value, a.store.max b.store⟩

/-- **The join is below a footprint exactly where both are** (proved). -/
private theorem Change.max_onValue_le (a b c : Change) :
    (a.max b).onValue.le c.onValue = (a.onValue.le c.onValue && b.onValue.le c.onValue) := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem Change.max_onStore_le (a b c : Change) :
    (a.max b).onStore.le c.onStore = (a.onStore.le c.onStore && b.onStore.le c.onStore) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem Closed.join_le (a b c : Closed) : (a.join b).le c = (a.le c && b.le c) := by
  simp only [Closed.join, Closed.le, Change.max_onValue_le, Change.max_onStore_le]
  cases a.value.onValue.le c.value.onValue <;> cases b.value.onValue.le c.value.onValue <;> simp

theorem Closed.le_top (a : Closed) : a.le Closed.top = true := by
  cases a with | mk v s => cases v <;> cases s <;> rfl

/-- `top` is below exactly itself (proved). -/
theorem Closed.top_le (c : Closed) : Closed.top.le c = (c == Closed.top) := by
  cases c with | mk v s => cases v <;> cases s <;> rfl

/-- On contents a change other than `any` keeps, a closed footprint allows
the same change. -/
private theorem Closed.at_of_holds {c : Closed} {b v v'} (h : (c.at v).Holds b v v')
    (hne : c.at v ≠ .any) : c.at v' = c.at v := by
  have := Change.Holds.same_class hne h .store
  simp only [Cls.has] at this
  simp only [Closed.at, this]

theorem Closed.Holds.refl (c : Closed) (h : Heap) : c.Holds h h :=
  Closed.Holds.mono (Closed.empty_le c) (Closed.holds_empty.mpr (List.prefix_refl h))

/-- The weaker of two changes. -/
def Change.min (a b : Change) : Change := if a.le b then a else b

theorem Change.min_holds {a b : Change} {n v v'} :
    (a.min b).Holds n v v' ↔ a.Holds n v v' ∧ b.Holds n v v' := by
  unfold Change.min
  split
  · rename_i hle
    exact ⟨fun h => ⟨h, h.mono hle⟩, And.left⟩
  · rename_i hle
    have hle' : b.le a = true := by simp only [Change.le, decide_eq_true_eq, Nat.not_le] at hle ⊢; omega
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

/-- A closed footprint beside one region at `any` is the closed footprint on
every location outside that region. -/
theorem Closed.post_extra_any {c : Closed} {R : Region} {ρ : Env} {h h' : Heap} :
    Post (c.fp ++ [(R, .any)]) ρ h h' ↔ c.HoldsOn (fun l => R.mem ρ h l = false) h h' := by
  constructor
  · intro hp
    refine ⟨hp.1, fun l v hR hv => ?_⟩
    obtain ⟨v', hv', ha⟩ := hp.2 l v hv
    refine ⟨v', hv', (Closed.allowed_iff (ρ := ρ) hv).mp ?_⟩
    rcases ha with h | ⟨e, he, hm, hh⟩
    · exact .inl h
    · rcases List.mem_append.mp he with he | he
      · exact .inr ⟨e, he, hm, hh⟩
      · simp only [List.mem_singleton] at he
        subst he
        rw [hR] at hm; cases hm
  · intro hw
    refine ⟨hw.1, fun l v hv => ?_⟩
    have hl := (List.getElem?_eq_some_iff.mp hv).1
    cases hR : R.mem ρ h l
    · obtain ⟨v', hv', hc⟩ := hw.2 l v hR hv
      refine ⟨v', hv', ?_⟩
      rcases (Closed.allowed_iff (ρ := ρ) (v' := v') hv).mpr hc with h | ⟨e, he, hm, hh⟩
      · exact .inl h
      · exact .inr ⟨e, List.mem_append_left _ he, hm, hh⟩
    · have hla : l < h'.length := Nat.lt_of_lt_of_le hl hw.1
      exact ⟨h'[l], List.getElem?_eq_getElem hla,
        .inr ⟨(R, .any), List.mem_append_right _ (List.mem_singleton_self _), hR, trivial⟩⟩

theorem Closed.HoldsOn.congr {c : Closed} {P Q : Nat → Prop} {h h' : Heap} (hpq : ∀ l, P l ↔ Q l) :
    c.HoldsOn P h h' ↔ c.HoldsOn Q h h' :=
  ⟨fun hp => hp.weaken fun l hq => (hpq l).mpr hq, fun hq => hq.weaken fun l hp => (hpq l).mp hp⟩

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
    exact class_change (fun h => by rw [hv] at h; cases h) (fun _ => hle.2) h

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

/-- A value's own locations: one per field it was allocated with, its store's
among them. -/
def ownOf (v : Tm) : List Nat := (fieldsOf v).map Prod.snd

/-- An object every own location of which was allocated after a heap of
length `b`. It reads no heap. -/
def FreshObjectAt (b : Nat) (v : Tm) : Prop :=
  (∃ fs c oid, v = .objAt fs c oid) ∧ ∀ l ∈ ownOf v, b ≤ l

theorem FreshObjectAt.lower {b b' : Nat} {v : Tm} (hb : b ≤ b') (h : FreshObjectAt b' v) :
    FreshObjectAt b v :=
  ⟨h.1, fun l hl => Nat.le_trans hb (h.2 l hl)⟩

/-- A change on every old location but a fresh object's own ones is a change
on every location below where it was allocated. -/
theorem Closed.HoldsOn.below_fresh_object {c : Closed} {b : Nat} {r : Tm} {h h' : Heap}
    (hf : FreshObjectAt b r) (hp : c.HoldsOn (fun l => l ∉ ownOf r) h h') : c.HoldsOn (· < b) h h' :=
  hp.weaken fun l hl hm => by have := hf.2 l hm; omega

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
