import Verification.Semantics.KindsAllocation
/-!
# Writes preserve kinds

A write replaces the contents of one location and keeps every role. The raw
steps (`Step.writeField`, `Step.setPresent`, `Step.setGrow`) admit any
machine value as the payload, so each write preserves the structural part of
kinded satisfaction under one typing premise: the payload has the category its
target's role demands (`Cat`). The payload's references are valid because the
written term's are.
-/
namespace Verification.Kinds

theorem RefsOk_arr_iff {k : Nat} {W : WorldT k} {ls : List (Option Nat)} :
    RefsOk W (.arr ls) ↔ ∀ l, some l ∈ ls → roleAt W l = some .elem := by
  constructor
  · intro h l hl
    have := h (.elem l) (by simp only [refs, storeRefs]; exact List.mem_filterMap.mpr ⟨some l, hl, rfl⟩)
    simpa [RefOk] using this
  · intro h r hr
    simp only [refs, storeRefs, List.mem_filterMap] at hr
    obtain ⟨o, ho, hro⟩ := hr
    cases o with
    | none => cases hro
    | some l => cases hro; exact h l ho

/-- A store listing only cells another valid store lists is valid. -/
theorem RefsOk_arr_of_subset {k : Nat} {W : WorldT k} {ls ls' : List (Option Nat)}
    (hsub : ∀ l, some l ∈ ls' → some l ∈ ls) (h : RefsOk W (.arr ls)) : RefsOk W (.arr ls') :=
  RefsOk_arr_iff.mpr fun l hl => RefsOk_arr_iff.mp h l (hsub l hl)

/-! ## Writing one location -/

/-- **Structural satisfaction survives a write of contents of the target's
role's shape.** -/
theorem Shaped_set {k : Nat} {W : WorldT k} {h : Heap} {l : Nat} {r : Role} {v : Val}
    (hsh : Shaped W h) (hr : roleAt W l = some r) (hv : Shape W r v) : Shaped W (h.set l v) := by
  intro l' r' hr'
  by_cases he : l' = l
  · subst he
    rw [hr] at hr'; cases hr'
    obtain ⟨u, hu, -⟩ := hsh l' r hr
    have hlt : l' < h.length := (List.getElem?_eq_some_iff.mp hu).1
    exact ⟨v, by simp [hlt], hv⟩
  · obtain ⟨u, hu, hs⟩ := hsh l' r' hr'
    exact ⟨u, by rw [List.getElem?_set_ne (Ne.symm he)]; exact hu, hs⟩

/-- **Kinded `write_sound`**: a write meeting the location's contract and its
role's shape preserves both parts of satisfaction. -/
theorem write_sound (n : Nat) (W : WorldT n) (h : Heap) (l : Nat) (c : Ctr n) (r : Role) (v : Val)
    (hok : HeapOk n W h) (hl : lookup W l = some c) (hr : roleAt W l = some r)
    (hv : ∀ (j : Nat) (hj : j < n), c j hj (trunc j (Nat.le_of_lt hj) W) v)
    (hs : Shape W r v) : HeapOk n W (h.set l v) := by
  obtain ⟨⟨hlen, hall⟩, hsh⟩ := hok
  refine ⟨⟨by simpa using hlen, fun k d hk => ?_⟩, Shaped_set hsh hr hs⟩
  by_cases hkl : k = l
  · subst hkl
    rw [hl] at hk; cases hk
    obtain ⟨u, hu, -⟩ := hall k c hl
    have hlt : k < h.length := (List.getElem?_eq_some_iff.mp hu).1
    exact ⟨v, by simp [hlt], hv⟩
  · obtain ⟨w, hw, hmem⟩ := hall k d hk
    exact ⟨w, by rwa [List.getElem?_set_ne (fun hc => hkl hc.symm)], hmem⟩

/-! ## Field writes -/

theorem lookup_mem {fs : List (PropKey × Nat)} {f : PropKey} {l : Nat}
    (h : fs.lookup f = some l) : (f, l) ∈ fs := by
  induction fs with
  | nil => simp at h
  | cons p ps ih =>
    obtain ⟨k, m⟩ := p
    simp only [List.lookup] at h
    split at h
    · rename_i hk; cases h; simp at hk; subst hk; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

/-- The target of a field write has a role fitting its key. -/
theorem fieldTarget_role {k : Nat} {W : WorldT k} {fs : List (PropKey × Nat)} {c : CallCode}
    {oid : Nat} {f : PropKey} {l : Nat} (hobj : RefsOk W (.objAt fs c oid)) (hl : fs.lookup f = some l) :
    ∃ r, roleAt W l = some r ∧ SlotRole f (some r) := by
  have := hobj (.slot f l) (by
    rw [refs_objAt]; exact List.mem_append_left _
      (by simp only [objRefs, List.mem_cons, List.mem_map]; exact .inr (.inr ⟨(f, l), lookup_mem hl, rfl⟩)))
  simp only [RefOk] at this
  rcases hr : roleAt W l with _ | r
  · rw [hr] at this; cases this
  · rw [hr] at this; exact ⟨r, rfl, this⟩

/-- **A field write preserves kinds** (`Step.writeField`,
`writeAt f o v ⟶ null`, writing `o`'s location `l` under `f`).

Typing premise: `v` has the category of `l`'s role (`Cat`): a source value
where `l` is a field or a cell, a store where it is a store. The step admits
any machine value. -/
theorem writeField_shaped {k : Nat} {W : WorldT k} {h : Heap} {fs : List (PropKey × Nat)}
    {c : CallCode} {oid : Nat} {f : PropKey} {l : Nat} {v : Val}
    (hsh : Shaped W h) (href : RefsOk W (.writeAt f (.objAt fs c oid) v)) (hl : fs.lookup f = some l)
    (hcat : ∀ r, roleAt W l = some r → Cat r v) :
    Shaped W (h.set l v) ∧ RefsOk W .nul := by
  have hobj : RefsOk W (.objAt fs c oid) := fun r hr => href r (by simp [refs, hr])
  have hv : RefsOk W v := fun r hr => href r (by simp [refs, hr])
  obtain ⟨r, hr, -⟩ := fieldTarget_role hobj hl
  exact ⟨Shaped_set hsh hr ⟨hcat r hr, hv⟩, fun _ h => by simp [refs] at h⟩

/-- An ordinary property's write, under a key other than the store slots:
its target is a field or a cell, so a source value is the payload's
category. -/
theorem writeOrdinary_shaped {k : Nat} {W : WorldT k} {h : Heap} {fs : List (PropKey × Nat)}
    {c : CallCode} {oid : Nat} {f : PropKey} {l : Nat} {v : Val}
    (hsh : Shaped W h) (href : RefsOk W (.writeAt f (.objAt fs c oid) v)) (hl : fs.lookup f = some l)
    (hkey : f ≠ arrayStoreKey ∧ f ≠ viewElementsKey) (hsrc : isSourceVal v = true) :
    Shaped W (h.set l v) := by
  have hobj : RefsOk W (.objAt fs c oid) := fun r hr => href r (by simp [refs, hr])
  refine (writeField_shaped hsh href hl fun r hr => ?_).1
  obtain ⟨r', hr', hs⟩ := fieldTarget_role hobj hl
  rw [hr] at hr'; cases hr'
  cases r with
  | field | cell | elem => exact hsrc
  | store fm => cases fm <;> simp only [SlotRole] at hs <;> simp_all
  | identity => simp [SlotRole] at hs

/-- **A binding update** writes a binding cell's location, a cell; a
source value is its category. -/
theorem bindingWrite_shaped {k : Nat} {W : WorldT k} {h : Heap} {l : Nat} {v : Val}
    (hsh : Shaped W h) (hr : roleAt W l = some .cell) (hv : RefsOk W v) (hsrc : isSourceVal v = true) :
    Shaped W (h.set l v) := Shaped_set hsh hr ⟨hsrc, hv⟩

/-- **A store write** writes an array's store slot `[]`, an array store;
a store is its category, and its cells are element cells because the
written term's are. This covers the writeback of a grown store and the
store a length write computes (`RefsOk_arr_of_subset`). -/
theorem storeWrite_shaped {k : Nat} {W : WorldT k} {h : Heap} {fs : List (PropKey × Nat)}
    {c : CallCode} {oid : Nat} {l : Nat} {ls : List (Option Nat)}
    (hsh : Shaped W h) (href : RefsOk W (.writeAt arrayStoreKey (.objAt fs c oid) (.arr ls)))
    (hl : fs.lookup arrayStoreKey = some l) : Shaped W (h.set l (.arr ls)) := by
  have hobj : RefsOk W (.objAt fs c oid) := fun r hr => href r (by simp [refs, hr])
  refine (writeField_shaped hsh href hl fun r hr => ?_).1
  obtain ⟨r', hr', hs⟩ := fieldTarget_role hobj hl
  rw [hr] at hr'; cases hr'
  cases r with
  | store fm =>
    cases fm with
    | array => exact ⟨ls, rfl⟩
    | view N => simp [SlotRole] at hs; exact absurd hs (by decide)
  | field | cell => simp [SlotRole] at hs
  | elem | identity => simp [SlotRole] at hs

/-- A length write's store lists cells of the old store: shortened, or
padded with holes. -/
theorem lengthStore_refs {k : Nat} {W : WorldT k} {ls : List (Option Nat)} (n : Nat)
    (h : RefsOk W (.arr ls)) :
    RefsOk W (.arr (if n ≤ ls.length then ls.take n else ls ++ List.replicate (n - ls.length) none)) := by
  refine RefsOk_arr_of_subset (fun l hl => ?_) h
  split at hl
  · exact List.mem_of_mem_take hl
  · rcases List.mem_append.mp hl with hl | hl
    · exact hl
    · simp [List.mem_replicate] at hl

/-! ## Element writes -/

theorem elemLoc_mem {ls : List (Option Nat)} {b : UInt64} {l : Nat} (h : elemLoc ls b = some l) :
    some l ∈ ls := by
  simp only [elemLoc, Option.bind_eq_some_iff] at h
  obtain ⟨k, -, o, ho, hl⟩ := h
  cases o with
  | none => cases hl
  | some m => cases hl; exact List.mem_of_getElem? ho

/-- **A present element's write preserves kinds** (`Step.setPresent`): the
target is an element cell the store lists. Typing premise: `v` is a source
value. -/
theorem setPresent_shaped {k : Nat} {W : WorldT k} {h : Heap} {ls : List (Option Nat)} {i v : Tm}
    {b : UInt64} {l : Nat} (hsh : Shaped W h) (href : RefsOk W (.setElem (.arr ls) i v))
    (hl : elemLoc ls b = some l) (hsrc : isSourceVal v = true) :
    Shaped W (h.set l v) ∧ RefsOk W (.arr ls) := by
  have hs : RefsOk W (.arr ls) := fun r hr => href r (by simp only [refs] at hr ⊢; simp [hr])
  have hv : RefsOk W v := fun r hr => href r (by simp [refs, hr])
  exact ⟨Shaped_set hsh (RefsOk_arr_iff.mp hs l (elemLoc_mem hl)) ⟨hsrc, hv⟩, hs⟩

theorem mem_placeAt {ls : List (Option Nat)} {k m l : Nat} (h : some l ∈ placeAt ls k m) :
    some l ∈ ls ∨ l = m := by
  unfold placeAt at h
  rcases List.mem_or_eq_of_mem_set h with h | h
  · rcases List.mem_append.mp h with h | h
    · exact .inl h
    · simp [List.mem_replicate] at h
  · cases h; exact .inr rfl

/-- **A hole's or past-the-end write preserves kinds** (`Step.setGrow`): the
fresh location is an element cell the returned store lists beside the old
ones. Typing premise: `v` is a source value. -/
theorem setGrow_shaped {k : Nat} {W : WorldT k} {h : Heap} {ls : List (Option Nat)} {i v : Tm}
    {kk : Nat} (c : Ctr k) (hlen : h.length = (entries W).length) (hsh : Shaped W h)
    (href : RefsOk W (.setElem (.arr ls) i v)) (hsrc : isSourceVal v = true) :
    Shaped (appendWs W [(.elem, c)]) (h ++ [v]) ∧
      RefsOk (appendWs W [(.elem, c)]) (.arr (placeAt ls kk h.length)) := by
  have hs : RefsOk W (.arr ls) := fun r hr => href r (by simp only [refs] at hr ⊢; simp [hr])
  have hv : RefsOk W v := fun r hr => href r (by simp [refs, hr])
  have hxt := WExt_appendWs W [(.elem, c)]
  refine ⟨Shaped_appendWs hlen hsh (fun i r w hr hw => ?_) rfl, RefsOk_arr_iff.mpr fun l hl => ?_⟩
  · obtain rfl : i = 0 := by have := (List.getElem?_eq_some_iff.mp hr).1; simpa using this
    simp at hr hw; subst hr hw
    exact ⟨hsrc, RefsOk_mono hxt hv⟩
  · rcases mem_placeAt hl with hl | rfl
    · exact WExt_roleAt hxt (RefsOk_arr_iff.mp hs l hl)
    · rw [hlen, show (entries W).length = (entries W).length + 0 from rfl, roleAt_appendWs']; rfl

end Verification.Kinds
