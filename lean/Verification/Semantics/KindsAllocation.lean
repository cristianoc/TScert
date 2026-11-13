import Verification.Semantics.Kinds
/-!
# Allocation preserves kinds

An allocation step appends locations to the heap; the typing rule that
justifies it extends the world by one entry per location, whose role it
chooses: an object literal's properties are fields, a binding cell's single
property `value` is a cell, an array's elements are element cells, its store
slot an array store, a typed array's elements slot a view store of the
array's length, and every object's identity an identity location. The step is
the calculus's own (`Step.makeFields`, `Step.arrAlloc`, the throwing steps);
the world extension differs.

The theorems below state the structural part (`Shaped`, `RefsOk`) for each
allocation, under exactly the premises the raw step does not give, and the
contract part (`HeapMeets`) once, for any appended entries.
-/
namespace Verification.Kinds

/-! ## Appending entries -/

theorem roleAt_appendWs_lt {k : Nat} (W : WorldT k) (es : List (Role × Ctr k)) {l : Nat}
    (hl : l < (entries W).length) : roleAt (appendWs W es) l = roleAt W l := by
  simp only [roleAt, roles, entries_appendWs, List.map_append]
  rw [List.getElem?_append_left (by simpa using hl)]

theorem lookup_appendWs_lt {k : Nat} (W : WorldT k) (es : List (Role × Ctr k)) {l : Nat}
    (hl : l < (entries W).length) : lookup (appendWs W es) l = lookup W l := by
  simp only [lookup, toList, entries_appendWs, List.map_append]
  rw [List.getElem?_append_left (by simpa using hl)]

theorem lookup_appendWs_ge {k : Nat} (W : WorldT k) (es : List (Role × Ctr k)) {i : Nat} :
    lookup (appendWs W es) ((entries W).length + i) = (es.map Prod.snd)[i]? := by
  simp only [lookup, toList, entries_appendWs, List.map_append]
  rw [List.getElem?_append_right (by simp)]
  simp

theorem roleAt_appendWs' {k : Nat} (W : WorldT k) (es : List (Role × Ctr k)) {i : Nat} :
    roleAt (appendWs W es) ((entries W).length + i) = (es.map Prod.fst)[i]? := by
  rw [roleAt_appendWs_ge W es (by omega)]
  simp

/-- **Structural satisfaction survives appending locations** whose contents
have the shapes their new roles demand in the extended world. -/
theorem Shaped_appendWs {k : Nat} {W : WorldT k} {h : Heap} {es : List (Role × Ctr k)}
    {vs : List Val} (hlen : h.length = (entries W).length) (hsh : Shaped W h)
    (hnew : ∀ (i : Nat) (r : Role) (v : Val), (es.map Prod.fst)[i]? = some r → vs[i]? = some v → Shape (appendWs W es) r v)
    (hes : es.length = vs.length) :
    Shaped (appendWs W es) (h ++ vs) := by
  intro l r hr
  by_cases hl : l < (entries W).length
  · rw [roleAt_appendWs_lt W es hl] at hr
    obtain ⟨u, hu, hs⟩ := hsh l r hr
    exact ⟨u, by rw [List.getElem?_append_left (by omega)]; exact hu,
      Shape_mono (WExt_appendWs W es) hs⟩
  · obtain ⟨i, rfl⟩ : ∃ i, l = (entries W).length + i := ⟨l - (entries W).length, by omega⟩
    rw [roleAt_appendWs'] at hr
    have hi : i < vs.length := by
      have := (List.getElem?_eq_some_iff.mp hr).1; simp at this; omega
    refine ⟨vs[i], by rw [List.getElem?_append_right (by omega)]; simp [hlen, hi], ?_⟩
    exact hnew i r _ hr (List.getElem?_eq_getElem hi)

/-- **The contract part survives appending locations** whose contents meet
their admissible contracts: `heap_allocs` of `Semantics/Heaps.lean` for any
appended entries. -/
theorem HeapMeets_appendWs {n : Nat} {W : WorldT n} {h : Heap} {es : List (Role × Ctr n)}
    {vs : List Val} (hok : HeapMeets n W h) (hadm : WorldAdm W) (hcadm : ∀ e ∈ es, CtrAdm e.2)
    (hes : es.length = vs.length)
    (hv : ∀ (i : Nat) (c : Ctr n) (v : Val), (es.map Prod.snd)[i]? = some c → vs[i]? = some v →
      ∀ (j : Nat) (hj : j < n), c j hj (trunc j (Nat.le_of_lt hj) W) v) :
    HeapMeets n (appendWs W es) (h ++ vs) := by
  obtain ⟨hlen, hall⟩ := hok
  have hlen' : h.length = (entries W).length := by simpa using hlen
  refine ⟨by simp [hlen', hes], fun l c hl => ?_⟩
  have hxt : ∀ (j : Nat) (hj : j < n),
      WExt (trunc j (Nat.le_of_lt hj) W) (trunc j (Nat.le_of_lt hj) (appendWs W es)) :=
    fun j hj => WExt_trunc (Nat.le_of_lt hj) (WExt_appendWs W es)
  by_cases hlt : l < (entries W).length
  · rw [lookup_appendWs_lt W es hlt] at hl
    obtain ⟨v, hv', hm⟩ := hall l c hl
    exact ⟨v, by rw [List.getElem?_append_left (by omega)]; exact hv',
      fun j hj => (hadm l c hl).1 j hj _ _ (hxt j hj) v (hm j hj)⟩
  · obtain ⟨i, rfl⟩ : ∃ i, l = (entries W).length + i := ⟨l - (entries W).length, by omega⟩
    rw [lookup_appendWs_ge] at hl
    have hi : i < vs.length := by
      have := (List.getElem?_eq_some_iff.mp hl).1; simp at this; omega
    have hce : ∃ e ∈ es, e.2 = c := by
      have := List.mem_of_getElem? hl; simpa using this
    obtain ⟨e, he, rfl⟩ := hce
    refine ⟨vs[i], by rw [List.getElem?_append_right (by omega)]; simp [hlen', hi], fun j hj => ?_⟩
    exact (hcadm e he).1 j hj _ _ (hxt j hj) _ (hv i e.2 _ hl (List.getElem?_eq_getElem hi) j hj)

/-- **Kinded allocation**: both parts of satisfaction survive appending
locations whose contents meet their contracts and have their roles' shapes. -/
theorem HeapOk_appendWs {n : Nat} {W : WorldT n} {h : Heap} {es : List (Role × Ctr n)}
    {vs : List Val} (hok : HeapOk n W h) (hadm : WorldAdm W) (hcadm : ∀ e ∈ es, CtrAdm e.2)
    (hes : es.length = vs.length)
    (hv : ∀ (i : Nat) (c : Ctr n) (v : Val), (es.map Prod.snd)[i]? = some c → vs[i]? = some v →
      ∀ (j : Nat) (hj : j < n), c j hj (trunc j (Nat.le_of_lt hj) W) v)
    (hnew : ∀ (i : Nat) (r : Role) (v : Val), (es.map Prod.fst)[i]? = some r → vs[i]? = some v → Shape (appendWs W es) r v) :
    HeapOk n (appendWs W es) (h ++ vs) :=
  ⟨HeapMeets_appendWs hok.1 hadm hcadm hes hv,
    Shaped_appendWs (by simpa using hok.1.1) hok.2 hnew hes⟩

/-! ## Objects -/

/-- The references of a call descriptor, as an allocation and the object it
makes hold them. -/
def codeRefs : CallCode → List Ref
  | .absent => []
  | .bound t r pre => refs t ++ refs r ++ refsArgs pre
  | .graph _ E _ _ caps _ _ => refsArgs E ++ refsArgs caps

theorem refs_objAt (fs : List (PropKey × Nat)) (c : CallCode) (i : Nat) :
    refs (.objAt fs c i) = objRefs fs i ++ codeRefs c := by
  cases c <;> simp [refs, codeRefs]

theorem refs_makeAt (c : CallCode) (ns : List PropKey) (xs : List Tm) :
    refs (.makeAt c ns xs) = codeRefs c ++ xs.flatMap refs := by
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

/-- The entries an object allocation appends: one per named field with the
role the allocating rule gives it, then the identity. -/
def objectEntries {k : Nat} (rs : List Role) (cs : List (Ctr k)) (cid : Ctr k) :
    List (Role × Ctr k) :=
  (rs ++ [Role.identity]).zip (cs ++ [cid])

theorem objectEntries_fst {k} {rs : List Role} {cs : List (Ctr k)} {cid : Ctr k}
    (h : rs.length = cs.length) : (objectEntries rs cs cid).map Prod.fst = rs ++ [Role.identity] := by
  simp [objectEntries, List.map_fst_zip, h]

theorem objectEntries_length {k} {rs : List Role} {cs : List (Ctr k)} {cid : Ctr k}
    (h : rs.length = cs.length) : (objectEntries rs cs cid).length = rs.length + 1 := by
  simp [objectEntries, h]

/-- **Object allocation preserves kinds** (`Step.makeFields`). The rule
allocating the object gives the `i`-th named field the role `rs[i]` and the
identity the role `identity`.

Typing premises, which the raw step does not give: each role fits its key
(`SlotRole`: an array store under `[]`, a view store under `[[viewElements]]`,
a field or a cell under any other key); each initializer has its role's
category (`Cat`: a source value in a field or cell, a store in a store slot);
and the allocated field map meets the view-length condition, which holds
vacuously where no key is `[[viewElements]]` (`viewLengthOk_of_not_mem`). -/
theorem makeFields_shaped {k : Nat} {W : WorldT k} {h : Heap} {c : CallCode}
    {ns : List PropKey} {vs : List Tm} (rs : List Role) (cs : List (Ctr k)) (cid : Ctr k)
    (hlen : h.length = (entries W).length) (hsh : Shaped W h)
    (hrs : rs.length = ns.length) (hcs : cs.length = ns.length) (hns : ns.length = vs.length)
    (href : RefsOk W (.makeAt c ns vs))
    (hslot : ∀ i (hi : i < ns.length), SlotRole ns[i] (some (rs[i]'(by omega))))
    (hcat : ∀ i (hi : i < ns.length), Cat (rs[i]'(by omega)) (vs[i]'(by omega)))
    (hview : ViewLengthOk (appendWs W (objectEntries rs cs cid)) (slots h.length ns)) :
    Shaped (appendWs W (objectEntries rs cs cid)) (h ++ vs ++ [.nul]) ∧
      RefsOk (appendWs W (objectEntries rs cs cid))
        (.objAt (slots h.length ns) c (h.length + vs.length)) := by
  have hxt := WExt_appendWs W (objectEntries rs cs cid)
  have hfst := objectEntries_fst (cid := cid) (show rs.length = cs.length by omega)
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
      rcases hr with rfl | rfl | ⟨p, hp, rfl⟩
      · show roleAt _ _ = _
        rw [hlen, roleAt_appendWs', hfst, List.getElem?_append_right (by omega)]
        simp [hrs, hns]
      · exact hview
      · obtain ⟨i, hi, rfl⟩ := mem_slots hp
        show SlotRole _ (roleAt _ _)
        rw [hlen, roleAt_appendWs', hfst, List.getElem?_append_left (by omega),
          List.getElem?_eq_getElem (by omega)]
        exact hslot i hi
    · exact RefOk_mono hxt (href r (by rw [refs_makeAt]; exact List.mem_append_left _ hr))

/-- Without a `[[viewElements]]` key the view-length condition holds. -/
theorem viewLengthOk_of_not_mem {k : Nat} {W : WorldT k} {base : Nat} {ns : List PropKey}
    (h : viewElementsKey ∉ ns) : ViewLengthOk W (slots base ns) := by
  intro e he
  obtain ⟨i, hi, hp⟩ := mem_slots he
  simp only [Prod.mk.injEq] at hp
  exact absurd (hp.1 ▸ List.getElem_mem hi) h

/-- **An object literal** allocates its properties as fields: under keys other
than the store slots, initializers that are source values. -/
theorem objectLiteral_shaped {k : Nat} {W : WorldT k} {h : Heap} {c : CallCode}
    {ns : List PropKey} {vs : List Tm} (cs : List (Ctr k)) (cid : Ctr k)
    (hlen : h.length = (entries W).length) (hsh : Shaped W h)
    (hcs : cs.length = ns.length) (hns : ns.length = vs.length)
    (href : RefsOk W (.makeAt c ns vs))
    (hkeys : ∀ f ∈ ns, f ≠ arrayStoreKey ∧ f ≠ viewElementsKey)
    (hsrc : ∀ v ∈ vs, isSourceVal v = true) :
    Shaped (appendWs W (objectEntries (ns.map fun _ => .field) cs cid)) (h ++ vs ++ [.nul]) ∧
      RefsOk (appendWs W (objectEntries (ns.map fun _ => .field) cs cid))
        (.objAt (slots h.length ns) c (h.length + vs.length)) :=
  makeFields_shaped _ cs cid hlen hsh (by simp) hcs hns href
    (fun i hi => by simpa [SlotRole] using hkeys _ (List.getElem_mem hi))
    (fun i hi => by simpa [Cat] using hsrc _ (List.getElem_mem (by omega)))
    (viewLengthOk_of_not_mem (fun hm => (hkeys _ hm).2 rfl))

/-! ## Binding cells

A binding cell is, in the calculus, the allocation of an object with one
field `value` and its identity. The rule allocating a binding gives the
field's location the role `cell`; the read and the write of the binding are
the field read and write at that location (`Step.readField`,
`Step.writeField`). -/

/-- **A binding cell's allocation**: its one property is a cell. -/
theorem bindingCell_shaped {k : Nat} {W : WorldT k} {h : Heap} {v : Tm} (c : Ctr k) (cid : Ctr k)
    (hlen : h.length = (entries W).length) (hsh : Shaped W h)
    (href : RefsOk W v) (hsrc : isSourceVal v = true) :
    Shaped (appendWs W (objectEntries [.cell] [c] cid)) (h ++ [v] ++ [.nul]) ∧
      RefsOk (appendWs W (objectEntries [.cell] [c] cid))
        (.objAt [(valueField, h.length)] .absent (h.length + 1)) := by
  have hne1 : valueField ≠ arrayStoreKey := by decide
  have hne2 : valueField ≠ viewElementsKey := by decide
  have := makeFields_shaped (c := .absent) (ns := [valueField]) (vs := [v]) [.cell] [c] cid hlen hsh
    rfl rfl rfl (fun r hr => href r (by simpa [refs_makeAt, codeRefs] using hr))
    (fun i hi => by
      obtain rfl : i = 0 := by simpa using hi
      exact ⟨hne1, hne2⟩)
    (fun i hi => by
      obtain rfl : i = 0 := by simpa using hi
      simpa [Cat] using hsrc)
    (viewLengthOk_of_not_mem (by simpa using hne2.symm))
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
    (c : Ctr k) (cid : Ctr k) (hlen : h.length = (entries W).length) (hsh : Shaped W h)
    (href : RefsOk W (.makeFn code a)) (hsrc : isSourceVal a = true) :
    Shaped (appendWs W (objectEntries [.field] [c] cid)) (h ++ [a] ++ [.nul]) ∧
      RefsOk (appendWs W (objectEntries [.field] [c] cid))
        (.objAt [(codeField, h.length)] code (h.length + 1)) := by
  have hne1 : codeField ≠ arrayStoreKey := by decide
  have hne2 : codeField ≠ viewElementsKey := by decide
  have := makeFields_shaped (c := code) (ns := [codeField]) (vs := [a]) [.field] [c] cid hlen hsh
    rfl rfl rfl href
    (fun i hi => by
      obtain rfl : i = 0 := by simpa using hi
      exact ⟨hne1, hne2⟩)
    (fun i hi => by
      obtain rfl : i = 0 := by simpa using hi
      simpa [Cat] using hsrc)
    (viewLengthOk_of_not_mem (by simpa using hne2.symm))
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
    (c : Ctr k) (cid : Ctr k) (hlen : h.length = (entries W).length) (hsh : Shaped W h)
    (href : RefsOk W (.arr ls)) :
    Shaped (appendWs W (objectEntries [.store .array] [c] cid)) (h ++ [.arr ls] ++ [.nul]) ∧
      RefsOk (appendWs W (objectEntries [.store .array] [c] cid))
        (.objAt [(arrayStoreKey, h.length)] .absent (h.length + 1)) := by
  have hne : arrayStoreKey ≠ viewElementsKey := by decide
  have := makeFields_shaped (c := .absent) (ns := [arrayStoreKey]) (vs := [.arr ls])
    [.store .array] [c] cid hlen hsh rfl rfl rfl (fun r hr => href r (by simpa [refs_makeAt, codeRefs] using hr))
    (fun i hi => by
      obtain rfl : i = 0 := by simpa using hi
      rfl)
    (fun i hi => by
      obtain rfl : i = 0 := by simpa using hi
      exact ⟨ls, rfl⟩)
    (viewLengthOk_of_not_mem (fun hm => hne (List.mem_singleton.mp hm).symm))
  simpa [slots] using this

/-! ## Typed arrays -/

/-- **A typed array's allocation**, as a host constructor's contract must
make it: an object owning `[[host]]`, its length `N` in a field whose
contract admits `N` alone, and its elements in a view store of length `N`
listing element cells. -/
theorem typedArray_shaped {k : Nat} {W : WorldT k} {h : Heap} {hv : Tm} {ls : List (Option Nat)}
    (chost clen celem cid : Ctr k) (hlen : h.length = (entries W).length) (hsh : Shaped W h)
    (hhost : isSourceVal hv = true) (hhref : RefsOk W hv) (href : RefsOk W (.arr ls))
    (hstable : CtrStable clen (.num (bitsOfNat ls.length))) :
    let W' := appendWs W (objectEntries [.field, .field, .store (.view ls.length)] [chost, clen, celem] cid)
    Shaped W' (h ++ [hv, .num (bitsOfNat ls.length), .arr ls] ++ [.nul]) ∧
      RefsOk W' (.objAt [(hostKey, h.length), (viewLengthKey, h.length + 1),
        (viewElementsKey, h.length + 2)] .absent (h.length + 3)) := by
  intro W'
  have hd1 : hostKey ≠ arrayStoreKey := by decide
  have hd2 : hostKey ≠ viewElementsKey := by decide
  have hd3 : viewLengthKey ≠ arrayStoreKey := by decide
  have hd4 : viewLengthKey ≠ viewElementsKey := by decide
  have hd5 : viewElementsKey ≠ hostKey := by decide
  have hd6 : viewElementsKey ≠ viewLengthKey := by decide
  have hfst := objectEntries_fst (rs := [.field, .field, .store (.view ls.length)])
    (cs := [chost, clen, celem]) (cid := cid) rfl
  have := makeFields_shaped (c := .absent) (ns := [hostKey, viewLengthKey, viewElementsKey])
    (vs := [hv, .num (bitsOfNat ls.length), .arr ls]) (W := W) (h := h)
    [.field, .field, .store (.view ls.length)] [chost, clen, celem] cid hlen hsh rfl rfl rfl
    (by
      intro r hr
      simp only [refs_makeAt, codeRefs, List.nil_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.mem_append] at hr
      rcases hr with hr | hr | hr
      · exact hhref r hr
      · simp [refs] at hr
      · exact href r hr)
    (fun i hi => by
      match i, hi with
      | 0, _ => exact ⟨hd1, hd2⟩
      | 1, _ => exact ⟨hd3, hd4⟩
      | 2, _ => rfl)
    (fun i hi => by
      match i, hi with
      | 0, _ => simpa [Cat] using hhost
      | 1, _ => rfl
      | 2, _ => exact ⟨ls, rfl, rfl⟩)
    (by
      intro e he
      simp only [slots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at he
      rcases he with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, rfl⟩
      · exact absurd h1 hd5
      · exact absurd h1 hd6
      · refine ⟨ls.length, h.length + 1, clen, ?_, ?_, ?_, ?_, hstable⟩
        · rw [hlen, show (entries W).length + 2 = (entries W).length + 2 from rfl,
            roleAt_appendWs', hfst]; rfl
        · have hb : (viewLengthKey == hostKey) = false := by decide
          have hb' : (viewLengthKey == viewLengthKey) = true := by decide
          simp only [slots, List.lookup, hb, hb']
        · rw [hlen, roleAt_appendWs', hfst]; rfl
        · rw [hlen, lookup_appendWs_ge]; simp [objectEntries])
  simpa [slots, Nat.add_assoc] using this

/-! ## Fresh errors -/

/-- **A fresh error's allocation** (`arrAllocThrow`, `arithThrow`,
`lenStrThrow`) appends its identity, holding `null`, and throws an object
with no fields. -/
theorem thrownError_shaped {k : Nat} {W : WorldT k} {h : Heap} (cid : Ctr k)
    (hlen : h.length = (entries W).length) (hsh : Shaped W h) :
    Shaped (appendWs W [(.identity, cid)]) (h ++ [.nul]) ∧
      RefsOk (appendWs W [(.identity, cid)]) (.throw (thrownError h.length)) := by
  refine ⟨Shaped_appendWs hlen hsh (fun i r v hr hv => ?_) rfl, ?_⟩
  · obtain rfl : i = 0 := by have := (List.getElem?_eq_some_iff.mp hr).1; simpa using this
    simp at hr hv; subst hr hv
    exact ⟨rfl, fun _ hr => by simp [refs] at hr⟩
  · intro r hr
    simp only [refs, thrownError, objRefs, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl
    · show roleAt _ _ = _
      rw [hlen, show (entries W).length = (entries W).length + 0 from rfl, roleAt_appendWs']; rfl
    · intro e he; simp at he

end Verification.Kinds
