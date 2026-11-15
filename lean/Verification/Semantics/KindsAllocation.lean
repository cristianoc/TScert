import Verification.Semantics.Kinds
/-!
# Allocation preserves kinds

An allocation step appends locations to the heap; the typing rule that
justifies it extends the world by one entry per location, whose role it
chooses: an object literal's properties are fields, a binding cell's single
property `value` is a cell, an array's elements are element cells, its store
slot an array store, a typed array's descriptor's store a view store of its
format and length, and every object's identity an identity location. The step is
the calculus's own (`Step.makeFields`, `Step.arrAlloc`, the throwing steps);
the world extension differs.

The theorems below state the structural part (`Shaped`, `RefsOk`) for each
allocation, under exactly the premises the raw step does not give, and the
contract part (`HeapMeets`) once, for any appended entries.
-/
namespace Verification.Kinds

/-- The references of a call descriptor, as an allocation and the object it
makes hold them; `plain` whether the object owns no array-store slot. -/
def codeRefs (plain : Bool) : CallCode → List Ref
  | .absent => []
  | .bound t r pre => refs t ++ refs r ++ refsArgs pre
  | .graph _ E _ _ caps _ _ => refsArgs E ++ refsArgs caps
  | .view s f n => [.view s f n plain]

theorem refs_objAt (fs : List (PropKey × Nat)) (c : CallCode) (i : Nat) :
    refs (.objAt fs c i) = objRefs fs i ++ codeRefs (fs.lookup arrayStoreKey).isNone c := by
  cases c <;> simp [refs, codeRefs]

/-- A field list an allocation names owns an array-store slot exactly when
the allocation names the key. -/
theorem slots_lookup_isNone (base : Nat) (ns : List PropKey) :
    ((slots base ns).lookup arrayStoreKey).isNone = !ns.contains arrayStoreKey := by
  induction ns generalizing base with
  | nil => rfl
  | cons k ns ih =>
    by_cases hk : arrayStoreKey = k
    · subst hk; simp [slots]
    · have hk' : (arrayStoreKey == k) = false := by simpa using hk
      simp [slots, List.lookup, hk', ih]
      exact fun _ => hk

theorem refs_makeAt (c : CallCode) (ns : List PropKey) (xs : List Tm) :
    refs (.makeAt c ns xs) = codeRefs (!ns.contains arrayStoreKey) c ++ xs.flatMap refs := by
  cases c <;> simp [refs, codeRefs]

theorem mem_slots {base : Nat} : ∀ {ns : List PropKey} {p : PropKey × Nat}, p ∈ slots base ns →
    ∃ i, ∃ hi : i < ns.length, p = (ns[i], base + i)
  | [], _, h => by simp [slots] at h
  | f :: fs, p, h => by
    simp only [slots, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, by simp, by simp⟩
    · obtain ⟨i, hi, rfl⟩ := mem_slots h
      exact ⟨i + 1, by simp; omega, by simp; omega⟩

/-- **The identity's contract**: a location holding `null` alone (the
Tolerant frames note's I locations). -/
def idCtr {k : Nat} : Ctr k := fun _ _ _ u => u = .nul

theorem idCtr_adm {k : Nat} : CtrAdm (idCtr (k := k)) :=
  ⟨fun _ _ _ _ _ _ h => h, fun _ _ _ _ h => by rw [show _ = Tm.nul from h]; rfl⟩

/-- The entries an object allocation appends: one per named field with the
role the allocating rule gives it, then the identity, whose contract admits
`null` alone (`idCtr`). -/
def objectEntries {k : Nat} (rs : List Role) (cs : List (Ctr k)) :
    List (Role × Ctr k) :=
  (rs ++ [Role.identity]).zip (cs ++ [idCtr])

/-- **An object allocation appends no view store** where no field role is one. -/
theorem objectEntries_plain {k : Nat} {rs : List Role} {cs : List (Ctr k)}
    (hrs : ∀ r ∈ rs, ∀ f N, r ≠ .store (.view f N)) :
    ∀ e ∈ objectEntries rs cs, ∀ f N, e.1 ≠ .store (.view f N) := by
  intro e he f N
  rcases List.mem_append.mp (List.of_mem_zip he).1 with h | h
  · exact hrs _ h f N
  · simp only [List.mem_singleton] at h; rw [h]; exact fun h => by cases h

theorem objectEntries_fst {k} {rs : List Role} {cs : List (Ctr k)}
    (h : rs.length = cs.length) : (objectEntries rs cs).map Prod.fst = rs ++ [Role.identity] := by
  simp [objectEntries, List.map_fst_zip, h]

theorem objectEntries_length {k} {rs : List Role} {cs : List (Ctr k)}
    (h : rs.length = cs.length) : (objectEntries rs cs).length = rs.length + 1 := by
  simp [objectEntries, h]

/-- **Object allocation preserves kinds** (`Step.makeFields`). The rule
allocating the object gives the `i`-th named field the role `rs[i]` and the
identity the role `identity`.

Typing premises, which the raw step does not give: each role fits its key
(`SlotRole`: an array store under `[]`, a field or a cell under any other
key); and each initializer has its role's category (`Cat`: a source value in
a field or cell, a store in a store slot). -/
theorem makeFields_shaped {k : Nat} {W : WorldT k} {h : Heap} {c : CallCode}
    {ns : List PropKey} {vs : List Tm} (rs : List Role) (cs : List (Ctr k))
    (hlen : h.length = (entries W).length) (hsh : Shaped W h)
    (hrs : rs.length = ns.length) (hcs : cs.length = ns.length) (hns : ns.length = vs.length)
    (href : RefsOk W (.makeAt c ns vs))
    (hslot : ∀ i (hi : i < ns.length), SlotRole ns[i] (some (rs[i]'(by omega))))
    (hcat : ∀ i (hi : i < ns.length), Cat (rs[i]'(by omega)) (vs[i]'(by omega))) :
    Shaped (appendWs W (objectEntries rs cs)) (h ++ vs ++ [.nul]) ∧
      RefsOk (appendWs W (objectEntries rs cs))
        (.objAt (slots h.length ns) c (h.length + vs.length)) := by
  have hxt := WExt_appendWs W (objectEntries rs cs)
  have hfst := objectEntries_fst (show rs.length = cs.length by omega)
  have hvs : ∀ v ∈ vs, RefsOk W v := fun v hv r hr =>
    href r (by rw [refs_makeAt]; exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨v, hv, hr⟩))
  refine ⟨?_, ?_⟩
  · rw [List.append_assoc]
    refine Shaped_appendWs hlen hsh (fun i r v hr hv => ?_) (by
      rw [objectEntries_length (by omega)]; simp; omega)
    rw [hfst] at hr
    by_cases hi : i < rs.length
    · rw [List.getElem?_append_left hi] at hr
      rw [List.getElem?_append_left (by omega)] at hv
      have hr' : rs[i] = r := by simpa [List.getElem?_eq_getElem hi] using hr
      have hv' : vs[i]'(by omega) = v := by simpa [List.getElem?_eq_getElem (show i < vs.length by omega)] using hv
      subst hr' hv'
      exact ⟨hcat i (by omega), RefsOk_mono hxt (hvs _ (List.getElem_mem _))⟩
    · rw [List.getElem?_append_right (by omega)] at hr hv
      have hi' : i - rs.length = 0 := by
        have := (List.getElem?_eq_some_iff.mp hr).1; simp at this; omega
      rw [hi'] at hr; rw [show i - vs.length = 0 by omega] at hv
      simp at hr hv; subst hr hv
      exact ⟨rfl, fun _ hr => by simp [refs] at hr⟩
  · intro r hr
    rw [refs_objAt] at hr
    rcases List.mem_append.mp hr with hr | hr
    · simp only [objRefs, List.mem_cons, List.mem_map] at hr
      rcases hr with rfl | ⟨p, hp, rfl⟩
      · show roleAt _ _ = _
        rw [hlen, roleAt_appendWs', hfst, List.getElem?_append_right (by omega)]
        simp [hrs, hns]
      · obtain ⟨i, hi, rfl⟩ := mem_slots hp
        show SlotRole _ (roleAt _ _)
        rw [hlen, roleAt_appendWs', hfst, List.getElem?_append_left (by omega),
          List.getElem?_eq_getElem (by omega)]
        exact hslot i hi
    · rw [slots_lookup_isNone] at hr
      exact RefOk_mono hxt (href r (by rw [refs_makeAt]; exact List.mem_append_left _ hr))

theorem not_mem_slots {base : Nat} {ns : List PropKey} {f : PropKey} (h : f ∉ ns) (l : Nat) :
    (f, l) ∉ slots base ns := fun he => by
  obtain ⟨i, hi, hp⟩ := mem_slots he
  simp only [Prod.mk.injEq] at hp
  exact absurd (hp.1 ▸ List.getElem_mem hi) h

/-- **An object literal** allocates its properties as fields: under keys other
than the store slot, initializers that are source values. -/
theorem objectLiteral_shaped {k : Nat} {W : WorldT k} {h : Heap} {c : CallCode}
    {ns : List PropKey} {vs : List Tm} (cs : List (Ctr k))
    (hlen : h.length = (entries W).length) (hsh : Shaped W h)
    (hcs : cs.length = ns.length) (hns : ns.length = vs.length)
    (href : RefsOk W (.makeAt c ns vs))
    (hkeys : ∀ f ∈ ns, f ≠ arrayStoreKey)
    (hsrc : ∀ v ∈ vs, isSourceVal v = true) :
    Shaped (appendWs W (objectEntries (ns.map fun _ => .field) cs)) (h ++ vs ++ [.nul]) ∧
      RefsOk (appendWs W (objectEntries (ns.map fun _ => .field) cs))
        (.objAt (slots h.length ns) c (h.length + vs.length)) :=
  makeFields_shaped _ cs hlen hsh (by simp) hcs hns href
    (fun i hi => by simpa [SlotRole] using hkeys _ (List.getElem_mem hi))
    (fun i hi => by simpa [Cat] using hsrc _ (List.getElem_mem (by omega)))

/-! ## Binding cells

A binding cell is, in the calculus, the allocation of an object with one
field `value` and its identity. The rule allocating a binding gives the
field's location the role `cell`; the read and the write of the binding are
the field read and write at that location (`Step.readField`,
`Step.writeField`). -/

/-- **A binding cell's allocation**: its one property is a cell. -/
theorem bindingCell_shaped {k : Nat} {W : WorldT k} {h : Heap} {v : Tm} (c : Ctr k)
    (hlen : h.length = (entries W).length) (hsh : Shaped W h)
    (href : RefsOk W v) (hsrc : isSourceVal v = true) :
    Shaped (appendWs W (objectEntries [.cell] [c])) (h ++ [v] ++ [.nul]) ∧
      RefsOk (appendWs W (objectEntries [.cell] [c]))
        (.objAt [(valueField, h.length)] .absent (h.length + 1)) := by
  have hne1 : valueField ≠ arrayStoreKey := by decide
  have := makeFields_shaped (c := .absent) (ns := [valueField]) (vs := [v]) [.cell] [c] hlen hsh
    rfl rfl rfl (fun r hr => href r (by simpa [refs_makeAt, codeRefs] using hr))
    (fun i hi => by
      obtain rfl : i = 0 := by simpa using hi
      exact hne1)
    (fun i hi => by
      obtain rfl : i = 0 := by simpa using hi
      simpa [Cat] using hsrc)
  simpa [slots] using this

/-- **A binding read** yields the cell's contents, a source value whose
references are valid. -/
theorem bindingRead_shape {k : Nat} {W : WorldT k} {h : Heap} {l : Nat} {v : Val}
    (hsh : Shaped W h) (hr : roleAt W l = some .cell) (hv : h[l]? = some v) :
    isSourceVal v = true ∧ RefsOk W v := by
  obtain ⟨u, hu, hc, hs⟩ := hsh l .cell hr
  rw [hv] at hu; cases hu
  exact ⟨hc, hs⟩

/-! ## Closures -/

/-- **A closure's allocation** (`makeFn`): its code field is a field; its
captures, bound target, receiver, prefix and node expressions keep the
references they had, which the allocation term's validity states. -/
theorem closure_shaped {k : Nat} {W : WorldT k} {h : Heap} {code : CallCode} {a : Tm}
    (c : Ctr k) (hlen : h.length = (entries W).length) (hsh : Shaped W h)
    (href : RefsOk W (.makeFn code a)) (hsrc : isSourceVal a = true) :
    Shaped (appendWs W (objectEntries [.field] [c])) (h ++ [a] ++ [.nul]) ∧
      RefsOk (appendWs W (objectEntries [.field] [c]))
        (.objAt [(codeField, h.length)] code (h.length + 1)) := by
  have hne1 : codeField ≠ arrayStoreKey := by decide
  have := makeFields_shaped (c := code) (ns := [codeField]) (vs := [a]) [.field] [c] hlen hsh
    rfl rfl rfl href
    (fun i hi => by
      obtain rfl : i = 0 := by simpa using hi
      exact hne1)
    (fun i hi => by
      obtain rfl : i = 0 := by simpa using hi
      simpa [Cat] using hsrc)
  simpa [slots] using this

/-! ## Arrays -/

theorem storeRefs_elemSlots (base n : Nat) :
    storeRefs (elemSlots base n) = (List.range n).map fun i => Ref.elem (base + i) := by
  simp [storeRefs, elemSlots, List.filterMap_map, Function.comp_def]

/-- **A store literal's allocation** (`Step.arrAlloc`) appends element cells.
Typing premise: each initializer is a source value. -/
theorem arrAlloc_shaped {k : Nat} {W : WorldT k} {h : Heap} {vs : List Tm} (cs : List (Ctr k))
    (hlen : h.length = (entries W).length) (hsh : Shaped W h) (hcs : cs.length = vs.length)
    (href : RefsOk W (.arrLit vs)) (hsrc : ∀ v ∈ vs, isSourceVal v = true) :
    Shaped (appendWs W ((vs.map fun _ => Role.elem).zip cs)) (h ++ vs) ∧
      RefsOk (appendWs W ((vs.map fun _ => Role.elem).zip cs)) (.arr (elemSlots h.length vs.length)) := by
  have hfst : ((vs.map fun _ => Role.elem).zip cs).map Prod.fst = vs.map fun _ => Role.elem := by
    simp [List.map_fst_zip, hcs]
  have hxt := WExt_appendWs W ((vs.map fun _ => Role.elem).zip cs)
  refine ⟨Shaped_appendWs hlen hsh (fun i r v hr hv => ?_) (by simp [hcs]), ?_⟩
  · rw [hfst] at hr
    have hi : i < vs.length := by have := (List.getElem?_eq_some_iff.mp hr).1; simpa using this
    simp [List.getElem?_eq_getElem hi] at hr
    subst hr
    have hm := List.mem_of_getElem? hv
    exact ⟨by simpa [Cat] using hsrc v hm,
      RefsOk_mono hxt (fun r hr => href r (by simpa [refs] using ⟨v, hm, hr⟩))⟩
  · intro r hr
    simp only [refs, storeRefs_elemSlots, List.mem_map, List.mem_range] at hr
    obtain ⟨i, hi, rfl⟩ := hr
    show roleAt _ _ = _
    rw [hlen, roleAt_appendWs', hfst]
    simp [hi]

/-- **An array's allocation** wraps a store whose cells are element cells in
an object owning it under `[]`, an array store. -/
theorem arrayObject_shaped {k : Nat} {W : WorldT k} {h : Heap} {ls : List (Option Nat)}
    (c : Ctr k) (hlen : h.length = (entries W).length) (hsh : Shaped W h)
    (href : RefsOk W (.arr ls)) :
    Shaped (appendWs W (objectEntries [.store .array] [c])) (h ++ [.arr ls] ++ [.nul]) ∧
      RefsOk (appendWs W (objectEntries [.store .array] [c]))
        (.objAt [(arrayStoreKey, h.length)] .absent (h.length + 1)) := by
  have := makeFields_shaped (c := .absent) (ns := [arrayStoreKey]) (vs := [.arr ls])
    [.store .array] [c] hlen hsh rfl rfl rfl (fun r hr => href r (by simpa [refs_makeAt, codeRefs] using hr))
    (fun i hi => by
      obtain rfl : i = 0 := by simpa using hi
      rfl)
    (fun i hi => by
      obtain rfl : i = 0 := by simpa using hi
      exact ⟨ls, rfl⟩)
  simpa [slots] using this

/-! ## Typed arrays -/

/-- **A view store's allocation** (the note *Tolerant frames*, (W2)): a store
location of form `view_N` of the format `f`, holding a view store of that
format that lists `N` element cells of the world, each index's. The cells
may be fresh or another view's, as a view over shared bytes lists them. -/
theorem viewStore_shaped {k : Nat} {W : WorldT k} {h : Heap} {f : ViewFormat} {cs : List Nat}
    (c : Ctr k) (hlen : h.length = (entries W).length) (hsh : Shaped W h)
    (hcells : ∀ l ∈ cs, roleAt W l = some .elem) :
    Shaped (appendWs W [(.store (.view f cs.length), c)]) (h ++ [.viewStore f cs]) ∧
      RefOk (appendWs W [(.store (.view f cs.length), c)]) (.view h.length f cs.length true) := by
  have hxt := WExt_appendWs W [(.store (.view f cs.length), c)]
  refine ⟨Shaped_appendWs hlen hsh (fun i r v hr hv => ?_) rfl, ?_⟩
  · obtain rfl : i = 0 := by have := (List.getElem?_eq_some_iff.mp hr).1; simpa using this
    simp at hr hv; subst hr hv
    refine ⟨⟨cs, rfl, rfl⟩, fun r hr => ?_⟩
    simp only [refs, List.mem_map] at hr
    obtain ⟨l, hl, rfl⟩ := hr
    exact WExt_roleAt hxt (hcells l hl)
  · refine ⟨rfl, ?_⟩
    rw [hlen, show (entries W).length = (entries W).length + 0 from rfl, roleAt_appendWs']; rfl

/-- **A typed array's allocation** (the note *Tolerant frames*, (W3)), as a
native constructor's or `subarray`'s contract must make it: a view store of
its format and length (`viewStore_shaped`), then an object over it whose
descriptor names that store, its format and its length, with own fields of
the roles its allocation gives them. -/
theorem typedArray_shaped {k : Nat} {W : WorldT k} {h : Heap} {f : ViewFormat} {cs : List Nat}
    {ns : List PropKey} {vs : List Tm} (cstore : Ctr k) (rs : List Role) (ccs : List (Ctr k))
    (hlen : h.length = (entries W).length) (hsh : Shaped W h)
    (hcells : ∀ l ∈ cs, roleAt W l = some .elem)
    (hrs : rs.length = ns.length) (hccs : ccs.length = ns.length) (hns : ns.length = vs.length)
    (hplain : arrayStoreKey ∉ ns) (hargs : ∀ v ∈ vs, RefsOk W v)
    (hslot : ∀ i (hi : i < ns.length), SlotRole ns[i] (some (rs[i]'(by omega))))
    (hcat : ∀ i (hi : i < ns.length), Cat (rs[i]'(by omega)) (vs[i]'(by omega))) :
    let W₁ := appendWs W [(.store (.view f cs.length), cstore)]
    let W' := appendWs W₁ (objectEntries rs ccs)
    Shaped W' (h ++ [.viewStore f cs] ++ vs ++ [.nul]) ∧
      RefsOk W' (.viewAt (slots (h.length + 1) ns) (h.length + 1 + vs.length) h.length f cs.length) := by
  intro W₁ W'
  obtain ⟨hsh₁, hst⟩ := viewStore_shaped (f := f) cstore hlen hsh hcells
  have hxt := WExt_appendWs W [(.store (.view f cs.length), cstore)]
  have hlen₁ : (h ++ [Tm.viewStore f cs]).length = (entries W₁).length := by
    simp [W₁, hlen]
  have href : RefsOk W₁ (.makeAt (.view h.length f cs.length) ns vs) := by
    intro r hr
    rw [refs_makeAt] at hr
    rcases List.mem_append.mp hr with hr | hr
    · simp only [codeRefs, List.mem_singleton] at hr; subst hr
      simpa [hplain] using hst
    · obtain ⟨v, hv, hr⟩ := List.mem_flatMap.mp hr
      exact RefOk_mono hxt (hargs v hv r hr)
  have := makeFields_shaped (c := .view h.length f cs.length) rs ccs hlen₁ hsh₁ hrs hccs hns href hslot hcat
  simpa [Nat.add_assoc] using this

/-! ## Fresh errors -/

/-- **A fresh error's allocation** (`arrAllocThrow`, `arithThrow`,
`lenStrThrow`) appends its identity, holding `null`, and throws an object
with no fields. -/
theorem thrownError_shaped {k : Nat} {W : WorldT k} {h : Heap}
    (hlen : h.length = (entries W).length) (hsh : Shaped W h) :
    Shaped (appendWs W [(.identity, idCtr)]) (h ++ [.nul]) ∧
      RefsOk (appendWs W [(.identity, idCtr)]) (.throw (thrownError h.length)) := by
  refine ⟨Shaped_appendWs hlen hsh (fun i r v hr hv => ?_) rfl, ?_⟩
  · obtain rfl : i = 0 := by have := (List.getElem?_eq_some_iff.mp hr).1; simpa using this
    simp at hr hv; subst hr hv
    exact ⟨rfl, fun _ hr => by simp [refs] at hr⟩
  · intro r hr
    simp only [refs, thrownError, objRefs, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    subst hr
    show roleAt _ _ = _
    rw [hlen, show (entries W).length = (entries W).length + 0 from rfl, roleAt_appendWs']; rfl

end Verification.Kinds
