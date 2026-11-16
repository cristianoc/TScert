import Verification.Semantics.Footprints
import Verification.Semantics.HeapObservations

/-! # Closed footprints

A **closed footprint** mentions only the three class regions, the content
categories that partition the locations (`Selector.partition`): one change
for the old locations holding a value, one for those holding an ordinary
array's spine and one for those holding a typed array's view spine. These
are three components, each holding a change. On a value `grow` is `scalar`
(`Change.onValue`), and on either kind of spine `init` and `scalar` are
`keep` (`Change.onSpine`), so a component is read through its normalization
(`Closed.normal`, `Closed.post_normal`). Closed footprints are ordered
exactly by their normalized components (`closed_order_exact`), their
postcondition reads no slot, and the empty one and the one letting
everything change are the two heap effects of a call signature that state
no footprint relation beyond prefix and growth (`Closed.holds_empty`,
`Closed.holds_top`). Heaps only grow under steps, so every run meets the
latter (`Closed.top_safe`).

A closed footprint stating one change for both spine categories,
`Closed.ofSpines`, is the footprint `{values: δ, spines: δ'}`
(`Closed.ofSpines_post_iff`). A footprint of class regions alone has an
exact closed form (`Footprint.closed?`, `Footprint.closed?_sound`); every
footprint has a closed bound, which it implies (`Footprint.close`,
`Footprint.close_sound`). -/
namespace Verification.Footprints

/-! ## Heaps grow -/

theorem step_length_le {h t h' t'} (st : Step h t h' t') : h.length ≤ h'.length := by
  induction st <;> simp_all [List.length_append, List.length_set] <;> omega

/-- A closed footprint: a change for each category of contents. -/
structure Closed where
  value : Change
  array : Change
  view : Change
  deriving DecidableEq, Repr

/-- One entry per content category, the three disjoint class regions. -/
def Closed.fp (c : Closed) : Footprint :=
  [(.cls .values, c.value), (.cls .arrays, c.array), (.cls .views, c.view)]

/-- The closed footprint stating `value` for the values and `spine` for both
kinds of spine: the footprint `{values: value, spines: spine}`
(`Closed.ofSpines_post_iff`). -/
def Closed.ofSpines (value spine : Change) : Closed := ⟨value, spine, spine⟩

/-- The least change bounding both spine components: the change the closed
footprint allows on the class `spines`. -/
def Closed.spines (c : Closed) : Change := c.array.max c.view

theorem Change.max_self (a : Change) : a.max a = a := by cases a <;> rfl

@[simp] theorem Closed.spines_ofSpines (v s : Change) : (Closed.ofSpines v s).spines = s :=
  Change.max_self s

@[simp] theorem Closed.value_ofSpines (v s : Change) : (Closed.ofSpines v s).value = v := rfl

/-- On contents of class `value`, `grow` is `scalar`. -/
def Change.onValue : Change → Change
  | .grow => .scalar
  | d => d

/-- On a spine, an array's or a view spine, `init` and `scalar` are
`keep`. -/
def Change.onSpine : Change → Change
  | .init | .scalar => .keep
  | d => d

def Closed.le (a b : Closed) : Bool :=
  a.value.onValue.le b.value.onValue && a.array.onSpine.le b.array.onSpine && a.view.onSpine.le b.view.onSpine

/-- The order of closed footprints stating one change for both spines is the
order of their two components. -/
theorem Closed.le_ofSpines (v s v' s' : Change) :
    (Closed.ofSpines v s).le (Closed.ofSpines v' s') = (v.onValue.le v'.onValue && s.onSpine.le s'.onSpine) := by
  simp only [Closed.le, Closed.ofSpines, Bool.and_assoc, Bool.and_self]

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

private theorem spine_change {δ δ' : Change} {b v v'} (hv : isArr v = true)
    (hle : δ.onSpine.le δ'.onSpine = true) (h : δ.Holds b v v') : δ'.Holds b v v' := by
  have h' : δ.onSpine.Holds b v v' := by
    cases δ with
    | init => exact h.init_isArr hv
    | scalar => exact h.scalar_isArr hv
    | _ => exact h
  have h'' := h'.mono hle
  cases δ' with
  | init => exact .inl h''
  | scalar => exact .inl h''
  | _ => exact h''

/-- Whether contents are a typed array's view spine. -/
def isViewSpine : Val → Bool
  | .viewSpine .. => true
  | _ => false

/-- The change a closed footprint allows on contents `v`, by their category
(`Closed.at_category`): a value's, an array spine's or a view spine's. -/
def Closed.at (c : Closed) (v : Val) : Change :=
  if isArr v then (if isViewSpine v then c.view else c.array) else c.value

/-- **The change on contents is their category's component.** -/
theorem Closed.at_category (c : Closed) (v : Val) : c.at v = match contentsCategory v with
    | .value => c.value
    | .array => c.array
    | .view => c.view := by
  cases v <;> rfl

theorem Closed.at_value {c : Closed} {v : Val} (hv : isArr v = false) : c.at v = c.value := by
  rw [Closed.at_category, (contentsCategory_value v).mpr hv]

@[simp] theorem Closed.at_arr (c : Closed) (ls : List (Option Nat)) : c.at (.arr ls) = c.array := rfl

@[simp] theorem Closed.at_viewSpine (c : Closed) (f : ViewFormat) (cs : List Nat) :
    c.at (.viewSpine f cs) = c.view := rfl

/-- On a closed footprint stating one change for both spines, the change on
contents is the value's or the spine's, by whether they are a spine. -/
theorem Closed.at_ofSpines (v s : Change) (u : Val) :
    (Closed.ofSpines v s).at u = if isArr u then s else v := by
  cases u <;> rfl

private theorem cls_mem {S : Selector} {ρ : Env} {h : Heap} {l : Nat} {v : Val} (hv : h[l]? = some v) :
    (Region.cls S).mem ρ h l = S.has (contentsCategory v) := by
  simp [Region.mem, hv, Selector.selects]

theorem Closed.allowed_iff {c : Closed} {ρ : Env} {h : Heap} {l : Nat} {v v' : Val}
    (hv : h[l]? = some v) : Allowed c.fp ρ h l v v' ↔ (c.at v).Holds h.length v v' := by
  constructor
  · rintro (rfl | ⟨e, he, hm, hh⟩)
    · exact Change.Holds.refl _ _ _
    · simp only [Closed.fp, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl <;> rw [cls_mem hv] at hm <;> rw [Closed.at_category] <;>
        revert hm <;> cases contentsCategory v <;> simp_all [Selector.has]
  · intro hh
    refine .inr ?_
    cases hc : contentsCategory v <;> simp only [Closed.at_category, hc] at hh
    · exact ⟨(.cls .values, c.value), by simp [Closed.fp], by rw [cls_mem hv, hc]; rfl, hh⟩
    · exact ⟨(.cls .arrays, c.array), by simp [Closed.fp], by rw [cls_mem hv, hc]; rfl, hh⟩
    · exact ⟨(.cls .views, c.view), by simp [Closed.fp], by rw [cls_mem hv, hc]; rfl, hh⟩

/-- An entry of a closed footprint covering a location states the change
its category's component does. -/
theorem Closed.fp_entry_at {c : Closed} {x : Region × Change} (hx : x ∈ c.fp) {ρ : Env} {h : Heap} {l : Nat}
    {v : Val} (hm : x.1.mem ρ h l = true) (hv : h[l]? = some v) : x.2 = c.at v := by
  simp only [Closed.fp, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> rw [cls_mem hv] at hm <;> rw [Closed.at_category] <;>
    revert hm <;> cases contentsCategory v <;> simp [Selector.has]

/-- Every entry of a closed footprint is a class region. -/
theorem Closed.fp_entry_cls {c : Closed} {x : Region × Change} (hx : x ∈ c.fp) : ∃ S, x.1 = .cls S := by
  simp only [Closed.fp, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> exact ⟨_, rfl⟩

/-- A closed footprint's postcondition at any assignment of slots: each old
location changes within its category's change. -/
theorem Closed.post_iff {c : Closed} {ρ : Env} {h h' : Heap} :
    Post c.fp ρ h h' ↔ h.length ≤ h'.length ∧
      ∀ (l : Nat) (v : Val), h[l]? = some v → ∃ v', h'[l]? = some v' ∧ (c.at v).Holds h.length v v' :=
  and_congr Iff.rfl (forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun hv =>
    exists_congr fun _ => and_congr Iff.rfl (Closed.allowed_iff hv))

private theorem Closed.at_mono {a b : Closed} (hle : a.le b = true) {n v v'}
    (h : (a.at v).Holds n v v') : (b.at v).Holds n v v' := by
  simp only [Closed.le, Bool.and_eq_true] at hle
  cases hc : contentsCategory v <;> simp only [Closed.at_category, hc] at h ⊢
  · exact value_change ((contentsCategory_value v).mp hc) hle.1.1 h
  · exact spine_change (by cases v <;> simp_all [contentsCategory, isArr]) hle.1.2 h
  · exact spine_change (by cases v <;> simp_all [contentsCategory, isArr]) hle.2 h

theorem Closed.post_mono {a b : Closed} (hle : a.le b = true) {ρ h h'} (hp : Post a.fp ρ h h') :
    Post b.fp ρ h h' := by
  rw [Closed.post_iff] at hp ⊢
  exact ⟨hp.1, fun l v hv => let ⟨v', hv', hc⟩ := hp.2 l v hv; ⟨v', hv', Closed.at_mono hle hc⟩⟩

/-- **The exact embedding of a closed footprint stating one change for both
spines**: its postcondition is that of `{values: value, spines: spine}`. -/
theorem Closed.ofSpines_post_iff {v s : Change} {ρ : Env} {h h' : Heap} :
    Post (Closed.ofSpines v s).fp ρ h h' ↔ Post [(.cls .values, v), (.cls .spines, s)] ρ h h' := by
  refine and_congr Iff.rfl (forall_congr' fun l => forall_congr' fun u => forall_congr' fun hu =>
    exists_congr fun u' => and_congr Iff.rfl ?_)
  rw [Closed.allowed_iff hu, Closed.at_ofSpines]
  constructor
  · intro hh
    refine .inr ?_
    cases ha : isArr u
    · refine ⟨(.cls .values, v), by simp, ?_, by simpa [ha] using hh⟩
      rw [cls_mem hu]; cases u <;> simp_all [contentsCategory, isArr, Selector.has]
    · refine ⟨(.cls .spines, s), by simp, ?_, by simpa [ha] using hh⟩
      rw [cls_mem hu]; cases u <;> simp_all [contentsCategory, isArr, Selector.has]
  · rintro (rfl | ⟨e, he, hm, hh⟩)
    · exact Change.Holds.refl _ _ _
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> rw [cls_mem hu] at hm <;> cases u <;>
        simp_all [contentsCategory, isArr, Selector.has]

private def ρ₀ : Env := fun _ => .undef

/-! ## Normalization -/

/-- **The normal form of a closed footprint**: each component read on its
category (`Change.onValue` on values, `Change.onSpine` on either spine). -/
def Closed.normal (c : Closed) : Closed := ⟨c.value.onValue, c.array.onSpine, c.view.onSpine⟩

private theorem onValue_holds {δ : Change} {b v v'} (hv : isArr v = false) :
    δ.onValue.Holds b v v' ↔ δ.Holds b v v' := by
  cases δ with
  | grow => exact ⟨Change.scalar_le_grow, fun h => h.grow_value hv⟩
  | _ => exact Iff.rfl

private theorem onSpine_holds {δ : Change} {b v v'} (hv : isArr v = true) :
    δ.onSpine.Holds b v v' ↔ δ.Holds b v v' := by
  cases δ with
  | init => exact ⟨fun h => .inl h, fun h => h.init_isArr hv⟩
  | scalar => exact ⟨fun h => .inl h, fun h => h.scalar_isArr hv⟩
  | _ => exact Iff.rfl

/-- **Normalization keeps the meaning** (proved). -/
theorem Closed.post_normal {c : Closed} {ρ : Env} {h h' : Heap} :
    Post c.normal.fp ρ h h' ↔ Post c.fp ρ h h' := by
  rw [Closed.post_iff, Closed.post_iff]
  refine and_congr Iff.rfl (forall_congr' fun _ => forall_congr' fun v => forall_congr' fun _ =>
    exists_congr fun _ => and_congr Iff.rfl ?_)
  rw [Closed.at_category, Closed.at_category]; unfold Closed.normal
  cases hc : contentsCategory v <;> simp only
  · exact onValue_holds ((contentsCategory_value v).mp hc)
  · exact onSpine_holds (by cases v <;> simp_all [contentsCategory, isArr])
  · exact onSpine_holds (by cases v <;> simp_all [contentsCategory, isArr])

/-! ## Closed footprints as call effects -/

/-- The footprint letting no old location change, and the one letting every
old location change: the note's `⊤`, `{values: any, arrays: any, views:
any}`. -/
def Closed.empty : Closed := ⟨.keep, .keep, .keep⟩
def Closed.top : Closed := ⟨.any, .any, .any⟩

theorem Closed.empty_eq : Closed.empty = Closed.ofSpines .keep .keep := rfl
theorem Closed.top_eq : Closed.top = Closed.ofSpines .any .any := rfl

theorem Closed.at_empty (v : Val) : Closed.empty.at v = .keep := by
  rw [Closed.at_category]; split <;> rfl

theorem Closed.at_top (v : Val) : Closed.top.at v = .any := by
  rw [Closed.at_category]; split <;> rfl

/-- A closed footprint's postcondition, from the heap a call starts in to the
heap it returns with. Its regions read no slot. -/
def Closed.Holds (c : Closed) (h h' : Heap) : Prop := Post c.fp (fun _ => .undef) h h'

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
  have atv : ∀ c : Closed, c.at .nul = c.value := fun c => rfl
  have atn : ∀ (c : Closed) b, c.at (.num b) = c.value := fun c b => rfl
  simp only [Closed.le, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- a value location initialized, a number changed, or a number replaced by a spine
    have v1 := refute .nul .tru
    have v2 := refute (.num 0) (.num 1)
    have v3 := refute (.num 0) (.arr [])
    rw [atv a, atv b] at v1
    rw [atn a, atn b] at v2 v3
    cases ha : a.value <;> cases hb : b.value <;> rw [ha, hb] at v1 v2 v3 <;>
      simp only [Change.onValue, Change.le, Change.rank] <;> first
        | decide
        | exact (v1 (by decide) (by decide)).elim
        | exact (v2 (by decide) (by decide)).elim
        | exact (v3 (by decide) (by decide)).elim
  · -- an array's spine gaining a fresh element location, or losing a present one
    have s1 := refute (.arr []) (.arr [some 1])
    have s2 := refute (.arr [some 0]) (.arr [])
    simp only [Closed.at_arr] at s1 s2
    cases ha : a.array <;> cases hb : b.array <;> rw [ha, hb] at s1 s2 <;>
      simp only [Change.onSpine, Change.le, Change.rank] <;> first
        | decide
        | exact (s1 (by decide) (by decide)).elim
        | exact (s2 (by decide) (by decide)).elim
  · -- a view spine listing a fresh cell, or replaced by an array's spine
    have w1 := refute (.viewSpine .uint8 [0]) (.viewSpine .uint8 [1])
    have w2 := refute (.viewSpine .uint8 [0]) (.arr [])
    simp only [Closed.at_viewSpine] at w1 w2
    cases ha : a.view <;> cases hb : b.view <;> rw [ha, hb] at w1 w2 <;>
      simp only [Change.onSpine, Change.le, Change.rank] <;> first
        | decide
        | exact (w1 (by decide) (by decide)).elim
        | exact (w2 (by decide) (by decide)).elim

theorem Closed.Holds.mono {a b : Closed} (hle : a.le b = true) {h h' : Heap} (hp : a.Holds h h') :
    b.Holds h h' :=
  Closed.post_mono hle hp

/-- **The empty closed footprint is heap preservation.** -/
theorem Closed.holds_empty {h h' : Heap} : Closed.empty.Holds h h' ↔ h.IsPrefix h' := by
  rw [Closed.holds_iff, ← Post.empty_iff (ρ := fun _ => .undef)]
  refine and_congr Iff.rfl (forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    exists_congr fun _ => and_congr Iff.rfl ?_)
  simp [Closed.at_empty, Allowed, Change.Holds]

/-- **The closed footprint letting everything change is growth**, which every
run meets (`Closed.top_safe`). -/
theorem Closed.holds_top {h h' : Heap} : Closed.top.Holds h h' ↔ h.length ≤ h'.length := by
  rw [Closed.holds_iff]
  refine ⟨fun hp => hp.1, fun hlen => ⟨hlen, fun l v hv => ?_⟩⟩
  have hl := (List.getElem?_eq_some_iff.mp hv).1
  refine ⟨h'[l], List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hl hlen), ?_⟩
  rw [Closed.at_top]; trivial

theorem Closed.empty_le (c : Closed) : Closed.empty.le c = true := by
  cases c with
  | mk v s w => cases v <;> cases s <;> cases w <;> rfl

/-- The join of two closed footprints: each component's larger change. -/
def Closed.join (a b : Closed) : Closed := ⟨a.value.max b.value, a.array.max b.array, a.view.max b.view⟩

/-- **The join is below a footprint exactly where both are** (proved). -/
private theorem Change.max_onValue_le (a b c : Change) :
    (a.max b).onValue.le c.onValue = (a.onValue.le c.onValue && b.onValue.le c.onValue) := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem Change.max_onSpine_le (a b c : Change) :
    (a.max b).onSpine.le c.onSpine = (a.onSpine.le c.onSpine && b.onSpine.le c.onSpine) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem Closed.join_le (a b c : Closed) : (a.join b).le c = (a.le c && b.le c) := by
  simp only [Closed.join, Closed.le, Change.max_onValue_le, Change.max_onSpine_le]
  cases a.value.onValue.le c.value.onValue <;> cases b.value.onValue.le c.value.onValue <;>
    cases a.array.onSpine.le c.array.onSpine <;> cases b.array.onSpine.le c.array.onSpine <;> simp

theorem Closed.join_ofSpines (v s v' s' : Change) :
    (Closed.ofSpines v s).join (Closed.ofSpines v' s') = Closed.ofSpines (v.max v') (s.max s') := rfl

/-- A closed footprint is below the one stating its spine bound on both
spines (`Closed.spines`); the two are equal where its spines agree. -/
theorem Closed.le_ofSpines_spines (c : Closed) : c.le (Closed.ofSpines c.value c.spines) = true := by
  cases c with | mk v a w => cases v <;> cases a <;> cases w <;> rfl

/-- Where the spine bound is `keep` on spines, so is each spine component. -/
theorem Closed.spines_onSpine_keep {c : Closed} (h : c.spines.onSpine = .keep) :
    c.array.onSpine = .keep ∧ c.view.onSpine = .keep := by
  cases c with
  | mk v a w => cases a <;> cases w <;> simp_all [Closed.spines, Change.max, Change.le, Change.rank, Change.onSpine]

theorem Closed.ofSpines_self {v s : Change} : Closed.ofSpines (Closed.ofSpines v s).value (Closed.ofSpines v s).spines =
    Closed.ofSpines v s := by
  simp

theorem Closed.le_top (a : Closed) : a.le Closed.top = true := by
  cases a with | mk v s w => cases v <;> cases s <;> cases w <;> rfl

/-- `top` is below exactly itself (proved). -/
theorem Closed.top_le (c : Closed) : Closed.top.le c = (c == Closed.top) := by
  cases c with | mk v s w => cases v <;> cases s <;> cases w <;> rfl

/-- On contents a change other than `any` keeps, a closed footprint allows
the same change. -/
theorem Closed.at_of_holds {c : Closed} {b v v'} (h : (c.at v).Holds b v v')
    (hne : c.at v ≠ .any) : c.at v' = c.at v := by
  rw [Closed.at_category, Closed.at_category, h.same_category hne]

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
def Closed.meet (a b : Closed) : Closed := ⟨a.value.min b.value, a.array.min b.array, a.view.min b.view⟩

theorem Closed.meet_ofSpines (v s v' s' : Change) :
    (Closed.ofSpines v s).meet (Closed.ofSpines v' s') = Closed.ofSpines (v.min v') (s.min s') := rfl

theorem Closed.le_refl (c : Closed) : c.le c = true := by
  cases c with | mk v s w => cases v <;> cases s <;> cases w <;> rfl

private theorem Change.min_le_left (a b : Change) : (a.min b).le a = true := by
  cases a <;> cases b <;> rfl

private theorem Change.min_le_right (a b : Change) : (a.min b).le b = true := by
  cases a <;> cases b <;> rfl

private theorem Change.le_onValue {a b : Change} (h : a.le b = true) : a.onValue.le b.onValue = true := by
  cases a <;> cases b <;> simp_all [Change.le, Change.rank, Change.onValue]

private theorem Change.le_onSpine {a b : Change} (h : a.le b = true) : a.onSpine.le b.onSpine = true := by
  cases a <;> cases b <;> simp_all [Change.le, Change.rank, Change.onSpine]

theorem Closed.meet_le_left (a b : Closed) : (a.meet b).le a = true := by
  simp only [Closed.le, Closed.meet, Bool.and_eq_true]
  exact ⟨⟨Change.le_onValue (Change.min_le_left _ _), Change.le_onSpine (Change.min_le_left _ _)⟩,
    Change.le_onSpine (Change.min_le_left _ _)⟩

theorem Closed.meet_le_right (a b : Closed) : (a.meet b).le b = true := by
  simp only [Closed.le, Closed.meet, Bool.and_eq_true]
  exact ⟨⟨Change.le_onValue (Change.min_le_right _ _), Change.le_onSpine (Change.min_le_right _ _)⟩,
    Change.le_onSpine (Change.min_le_right _ _)⟩

theorem Closed.at_meet (a b : Closed) (v : Val) : (a.meet b).at v = (a.at v).min (b.at v) := by
  rw [Closed.at_category, Closed.at_category, Closed.at_category]; unfold Closed.meet
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
  | zero => intros; assumption
  | succ n ih =>
    intro W h t hb hs
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hrf, ?_⟩
    rcases hs with (⟨hv, ht⟩ | hth) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · exact .inl (.inl ⟨hv, ht, hb⟩)
    · exact .inl (.inr hth)
    · exact .inr ⟨U, h', t', hx, hu, step, hh, ih (Nat.le_trans hb (step_length_le step)) hs⟩

/-- **Every safe run meets the footprint letting everything change.** -/
theorem Closed.top_safe {Ξ R : Fam} {n W h t} (hs : Safe Ξ R n W h t) :
    HeapObservations.SafePost Ξ R (fun h' _ => Closed.top.Holds h h') n W h t :=
  HeapObservations.weaken (fun _ _ hb => Closed.holds_top.mpr hb) (grow_safe (Nat.le_refl _) hs)

/-! ## The closed form of a footprint

A region's locations hold contents of the categories `Region.cats` names: a
class region's selector, a cell's values, and every category otherwise. A
footprint's closed bound gives each category the largest change of an entry
whose region may hold it (`Footprint.close`); it is implied by the
footprint (`Footprint.close_sound`), and equivalent to it where every region
is a class region (`Footprint.closed?_sound`). A general footprint is never
recovered from its closed bound. -/

/-- The categories a region's locations may hold. -/
def Region.cats : Region → Selector
  | .cls S => S
  | .inCls _ S => S
  | _ => .all

/-- **A region's locations hold contents of the categories it names.** -/
theorem Region.cats_mem {r : Region} {ρ : Env} {h : Heap} {l : Nat} {v : Val} (hv : h[l]? = some v)
    (hm : r.mem ρ h l = true) : r.cats.has (contentsCategory v) = true := by
  cases r with
  | cls S => simpa [Region.cats, Region.mem, hv, Selector.selects] using hm
  | inCls r S =>
    simp only [Region.mem, hv, Bool.and_eq_true] at hm
    simpa [Region.cats, Selector.selects] using hm.2
  | _ => exact Selector.has_all _

/-- The largest change of an entry whose region may hold contents of
category `k`. -/
def Footprint.changeAt (Φ : Footprint) (k : Category) : Change :=
  Φ.foldr (fun e d => if e.1.cats.has k then e.2.max d else d) .keep

theorem Change.max_holds {a b : Change} {n v v'} : (a.max b).Holds n v v' ↔ a.Holds n v v' ∨ b.Holds n v v' := by
  refine ⟨fun h => ?_, fun h => h.elim (·.mono (Change.le_max_left a b)) (·.mono (Change.le_max_right a b))⟩
  rcases Change.max_cases a b with he | he <;> rw [he] at h
  · exact .inl h
  · exact .inr h

theorem Footprint.changeAt_holds (Φ : Footprint) (k : Category) {n : Nat} {v v' : Val} :
    (Φ.changeAt k).Holds n v v' ↔ v' = v ∨ ∃ e ∈ Φ, e.1.cats.has k = true ∧ e.2.Holds n v v' := by
  induction Φ with
  | nil => simp [Footprint.changeAt, Change.Holds]
  | cons e Φ ih =>
    unfold Footprint.changeAt at ih ⊢
    simp only [List.foldr_cons]
    split
    · rename_i hk
      rw [Change.max_holds, ih]
      constructor
      · rintro (h | h | ⟨f, hf, hfk, hh⟩)
        · exact .inr ⟨e, List.mem_cons_self .., hk, h⟩
        · exact .inl h
        · exact .inr ⟨f, List.mem_cons_of_mem _ hf, hfk, hh⟩
      · rintro (h | ⟨f, hf, hfk, hh⟩)
        · exact .inr (.inl h)
        · rcases List.mem_cons.mp hf with rfl | hf
          · exact .inl hh
          · exact .inr (.inr ⟨f, hf, hfk, hh⟩)
    · rename_i hk
      rw [ih]
      constructor
      · rintro (h | ⟨f, hf, hfk, hh⟩)
        · exact .inl h
        · exact .inr ⟨f, List.mem_cons_of_mem _ hf, hfk, hh⟩
      · rintro (h | ⟨f, hf, hfk, hh⟩)
        · exact .inl h
        · rcases List.mem_cons.mp hf with rfl | hf
          · exact absurd hfk hk
          · exact .inr ⟨f, hf, hfk, hh⟩

/-- **The closed bound of a footprint**: each category's largest covering
change. -/
def Footprint.close (Φ : Footprint) : Closed :=
  ⟨Φ.changeAt .value, Φ.changeAt .array, Φ.changeAt .view⟩

theorem Footprint.close_at (Φ : Footprint) (v : Val) : Φ.close.at v = Φ.changeAt (contentsCategory v) := by
  rw [Closed.at_category]; unfold Footprint.close
  split <;> rename_i h <;> rw [h]

/-- **A footprint implies its closed bound** (proved). -/
theorem Footprint.close_sound {Φ : Footprint} {ρ : Env} {h h' : Heap} (hp : Post Φ ρ h h') :
    Post Φ.close.fp ρ h h' := by
  rw [Closed.post_iff]
  refine ⟨hp.1, fun l v hv => ?_⟩
  obtain ⟨v', hv', ha⟩ := hp.2 l v hv
  refine ⟨v', hv', ?_⟩
  rw [Footprint.close_at, Footprint.changeAt_holds]
  rcases ha with rfl | ⟨e, he, hm, hh⟩
  · exact .inl rfl
  · exact .inr ⟨e, he, Region.cats_mem hv hm, hh⟩

/-- Whether a region is a class region. -/
def Region.isClass : Region → Bool
  | .cls _ => true
  | _ => false

/-- **The exact closed form** of a footprint of class regions alone. -/
def Footprint.closed? (Φ : Footprint) : Option Closed :=
  if Φ.all (·.1.isClass) then some Φ.close else none

/-- **A footprint of class regions is its closed form** (proved). -/
theorem Footprint.closed?_sound {Φ : Footprint} {c : Closed} (hc : Φ.closed? = some c) {ρ : Env}
    {h h' : Heap} : Post Φ ρ h h' ↔ Post c.fp ρ h h' := by
  unfold Footprint.closed? at hc
  split at hc
  · rename_i hall
    cases hc
    refine ⟨Footprint.close_sound, fun hp => ?_⟩
    rw [Closed.post_iff] at hp
    refine ⟨hp.1, fun l v hv => ?_⟩
    obtain ⟨v', hv', hh⟩ := hp.2 l v hv
    refine ⟨v', hv', ?_⟩
    rw [Footprint.close_at, Footprint.changeAt_holds] at hh
    rcases hh with rfl | ⟨e, he, hk, hh⟩
    · exact .inl rfl
    · refine .inr ⟨e, he, ?_, hh⟩
      have hcl := List.all_eq_true.mp hall e he
      obtain ⟨r, δ⟩ := e
      cases r <;> simp only [Region.isClass, Bool.false_eq_true] at hcl
      simpa [Region.cats, Region.mem, hv, Selector.selects] using hk
  · cases hc

/-- The class entries of a footprint. -/
def Footprint.classes (Ψ : Footprint) : Footprint := Ψ.filter (·.1.isClass)

/-- A footprint's entries over regions other than class regions. -/
def Footprint.nonClasses (Ψ : Footprint) : Footprint := Ψ.filter (!·.1.isClass)

/-- **The closed bound of a footprint's class entries**: the bound a run
within which meets the footprint (`Footprint.classBound_sound`). -/
def Footprint.classBound (Φ : Footprint) : Closed := Φ.classes.close

/-- **A run within a footprint's class bound meets the footprint**
(proved): the class entries are their closed form
(`Footprint.closed?_sound`), whose meaning reads no environment
(`Closed.post_iff`), and each is an entry of the footprint. -/
theorem Footprint.classBound_sound {Φ : Footprint} {ρ : Env} {h h' : Heap} (hb : Φ.classBound.Holds h h') :
    Post Φ ρ h h' := by
  have hc : Φ.classes.closed? = some Φ.classBound := by
    simp [Footprint.closed?, Footprint.classBound, Footprint.classes, List.all_filter]
  have hp : Post Φ.classes ρ h h' :=
    (Footprint.closed?_sound hc).mpr (Closed.post_iff.mpr (Closed.holds_iff.mp hb))
  refine ⟨hp.1, fun l v hv => ?_⟩
  obtain ⟨v', hv', ha⟩ := hp.2 l v hv
  refine ⟨v', hv', ?_⟩
  rcases ha with h | ⟨e, he, hm, hh⟩
  · exact .inl h
  · exact .inr ⟨e, (List.mem_filter.mp he).1, hm, hh⟩

/-- The closed form of a closed footprint's entries is itself. -/
theorem Closed.closed?_fp (c : Closed) : c.fp.closed? = some c := by
  cases c with
  | mk v a w =>
    cases v <;> cases a <;> cases w <;> rfl


/-! ## Footprints on some old locations

A call may change one spine beyond its footprint, its receiver's: its
postcondition is the footprint on the old locations other than that spine.
A run whose every such spine was allocated after a heap of length `b` is
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

/-! ## Fresh spines -/

/-- The location of a value's array spine, where it has one: its `[]`
slot's, which the calculus's array steps read and write. A typed array's
element facts read the spine its descriptor selects instead
(`HeapKnowledge.elementsOf`). -/
def spineOf (v : Tm) : Option Nat := (fieldsOf v).lookup arraySpineKey

theorem spineOf_lookup {v : Tm} {s : Nat} (h : spineOf v = some s) :
    (fieldsOf v).lookup arraySpineKey = some s := h

/-- A value whose array spine was allocated after a heap of length `b`:
its spine's location is at least `b`. It reads no heap: an object's fields
are fixed at its allocation. -/
def FreshAt (b : Nat) (v : Tm) : Prop := ∃ s, spineOf v = some s ∧ b ≤ s

theorem FreshAt.lower {b b' : Nat} {v : Tm} (hb : b ≤ b') (h : FreshAt b' v) : FreshAt b v := by
  obtain ⟨s, hs, hle⟩ := h
  exact ⟨s, hs, Nat.le_trans hb hle⟩

/-- A value's own locations: one per field it was allocated with, its spine's
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

/-- A change on every old location but a fresh value's spine is a change on
every location below where it was allocated. -/
theorem Closed.HoldsOn.below_fresh {c : Closed} {b : Nat} {r : Tm} {h h' : Heap} (hf : FreshAt b r)
    (hp : c.HoldsOn (fun l => (fieldsOf r).lookup arraySpineKey ≠ some l) h h') : c.HoldsOn (· < b) h h' := by
  obtain ⟨s, hs, hle⟩ := hf
  refine hp.weaken fun l hl => ?_
  rw [spineOf_lookup hs]
  intro he
  cases he
  omega

end Verification.Footprints
