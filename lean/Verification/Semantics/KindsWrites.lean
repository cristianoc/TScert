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


/-! ## Administrative steps keep references valid -/

theorem subst_refs (a : Tm) (b : Tm) : ∀ j, ∀ r ∈ refs (subst j a b), r ∈ refs b ∨ r ∈ refs a := by
  induction b using Tm.induct with
  | var i =>
    intro j r hr
    simp only [subst] at hr
    split at hr
    · exact .inr hr
    · split at hr <;> simp [refs] at hr
  | _ =>
    intro j r hr
    simp only [subst, refs, refsArgs_eq, substArgs_eq_map, List.mem_append, List.mem_flatMap,
      List.mem_map] at hr ⊢
    grind

theorem instantiate_refs (ρ : Env) (e : Tm) :
    ∀ d, ∀ r ∈ refs (instantiate d ρ e), r ∈ refs e ∨ ∃ i, r ∈ refs (ρ i) := by
  induction e using Tm.induct with
  | var i =>
    intro d r hr
    simp only [instantiate] at hr
    split at hr
    · simp [refs] at hr
    · exact .inr ⟨_, hr⟩
  | _ =>
    intro d r hr
    simp only [instantiate, refs, refsArgs_eq, instantiateArgs_eq_map, List.mem_append, List.mem_flatMap,
      List.mem_map] at hr ⊢
    grind

/-- A thrown value's references are among the throwing term's. -/
theorem raises_refs {t v : Tm} (h : Raises t v) : ∀ r ∈ refs v, r ∈ refs t := by
  induction h with
  | throwV => intro r hr; simpa [refs] using hr
  | callArg _ _ ha _ _ ih =>
    intro r hr
    simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap]
    exact .inr ⟨_, List.mem_of_getElem? ha, ih r hr⟩
  | constructArg _ ha _ _ ih =>
    intro r hr
    simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap]
    exact .inr ⟨_, List.mem_of_getElem? ha, ih r hr⟩
  | makeArg ha _ _ ih =>
    intro r hr
    rw [refs_makeAt]
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? ha, ih r hr⟩)
  | arrArg ha _ _ ih =>
    intro r hr
    simp only [refs, refsArgs_eq, List.mem_flatMap]
    exact ⟨_, List.mem_of_getElem? ha, ih r hr⟩
  | _ => intro r hr; (try simp only [refs, List.mem_append]); grind

/-- **Every location of a well-formed heap holds contents with valid
references.** -/
theorem heap_refs {k : Nat} {W : WorldT k} {h : Heap} {l : Nat} {v : Val}
    (hlen : h.length = (entries W).length) (hsh : Shaped W h) (hv : h[l]? = some v) : RefsOk W v := by
  have hlt : l < (entries W).length := by have := (List.getElem?_eq_some_iff.mp hv).1; omega
  obtain ⟨r, hr⟩ := roleAt_some hlt
  obtain ⟨u, hu, -, hs⟩ := hsh l r hr
  rw [hv] at hu; cases hu; exact hs

theorem heapVal_refs {k : Nat} {W : WorldT k} {h : Heap} (l : Nat)
    (hlen : h.length = (entries W).length) (hsh : Shaped W h) : RefsOk W (heapVal h l) := by
  unfold heapVal
  split
  · split
    · exact heap_refs hlen hsh (by assumption)
    · exact fun _ h => by simp [refs] at h
  · exact fun _ h => by simp [refs] at h

theorem readElems_refs {k : Nat} {W : WorldT k} {h : Heap}
    (hlen : h.length = (entries W).length) (hsh : Shaped W h) :
    ∀ {ls : List (Option Nat)} {vs : List Tm}, readElems h ls = some vs → ∀ v ∈ vs, RefsOk W v
  | [], vs, he => by simp [readElems] at he; subst he; simp
  | none :: ls, vs, he => by
    simp only [readElems, Option.map_eq_some_iff] at he
    obtain ⟨ws, hws, rfl⟩ := he
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact fun _ h => by simp [refs] at h
    · exact readElems_refs hlen hsh hws v hv
  | some l :: ls, vs, he => by
    simp only [readElems, Option.bind_eq_some_iff, Option.map_eq_some_iff] at he
    obtain ⟨w, hw, ws, hws, rfl⟩ := he
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact heap_refs hlen hsh hw
    · exact readElems_refs hlen hsh hws v hv

theorem parameters_mem : ∀ {n : Nat} {args : List Tm} {x : Tm},
    x ∈ CallArguments.parameters n args → x ∈ args ∨ x = .undef
  | 0, _, _, h => by simp [CallArguments.parameters] at h
  | n + 1, [], x, h => by
    simp only [CallArguments.parameters, List.mem_cons] at h
    rcases h with rfl | h
    · exact .inr rfl
    · exact parameters_mem h
  | n + 1, a :: args, x, h => by
    simp only [CallArguments.parameters, List.mem_cons] at h
    rcases h with rfl | h
    · exact .inl List.mem_cons_self
    · rcases parameters_mem h with h | h
      · exact .inl (List.mem_cons_of_mem _ h)
      · exact .inr h

theorem envMap_refs {m : Option (List Nat)} {L : List Tm} {d : Tm} {r : Ref}
    (hr : r ∈ ((envMap m L d).1.flatMap refs) ∨ r ∈ refs (envMap m L d).2) :
    r ∈ L.flatMap refs ∨ r ∈ refs d := by
  rcases hr with hr | hr
  · obtain ⟨x, hx, hrx⟩ := List.mem_flatMap.mp hr
    rcases envMap_mem (.inl hx) with hx | rfl
    · exact .inl (List.mem_flatMap.mpr ⟨x, hx, hrx⟩)
    · exact .inr hrx
  · rcases envMap_mem (x := (envMap m L d).2) (.inr rfl) with hx | hx
    · exact .inl (List.mem_flatMap.mpr ⟨_, hx, hr⟩)
    · rw [hx] at hr; exact .inr hr

theorem mem_firstKeys' {α : Type} {ps : List (PropKey × α)} {p : PropKey × α}
    (h : p ∈ firstKeys ps) : p ∈ ps := mem_firstKeys h

/-- **A copy's values have valid references**: each is `undefined`, a value
the heap holds, or a string. -/
theorem mergeParts_vals {h : Heap} {d : List PropKey} {a b : Tm} {ps : List (PropKey × Tm)}
    (hm : mergeParts h d a b = some ps) :
    ∀ p ∈ ps, (∃ l, p.2 = heapVal h l) ∨ ∃ s, p.2 = .str s := by
  simp only [mergeParts, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hm
  obtain ⟨p, hp, q, hq, rfl⟩ := hm
  have hown : ∀ e ∈ p, ∃ l, e.2 = heapVal h l := by
    intro e he
    unfold ownAll at hp
    split at hp
    · split at hp
      · cases hp
      · simp only [Option.some.injEq] at hp; subst hp
        have := mem_firstKeys he
        simp only [List.mem_map, List.mem_filter] at this
        obtain ⟨x, -, rfl⟩ := this
        exact ⟨x.2, rfl⟩
    · cases hp
  have hdata : ∀ e ∈ q, (∃ l, e.2 = heapVal h l) ∨ ∃ s, e.2 = .str s := by
    intro e he
    unfold ownData at hq
    split at hq
    · split at hq
      · cases hq
      · simp only [Option.some.injEq] at hq; subst hq
        have := mem_firstKeys he
        rcases List.mem_append.mp this with he | he
        · simp only [List.mem_map, List.mem_filter] at he
          obtain ⟨x, -, rfl⟩ := he
          exact .inl ⟨x.2, rfl⟩
        · unfold storeData at he
          split at he
          · split at he
            · simp only [List.mem_filterMap] at he
              obtain ⟨x, -, hx⟩ := he
              obtain ⟨o, i⟩ := x
              cases o with
              | none => cases hx
              | some m => simp at hx; exact .inl ⟨m, by rw [← hx]⟩
            · simp at he
          · simp at he
    · simp only [Option.some.injEq] at hq; subst hq
      have := mem_firstKeys he
      simp only [stringData, List.mem_map] at this
      obtain ⟨x, -, rfl⟩ := this
      exact .inr ⟨_, rfl⟩
    all_goals (first | (simp only [Option.some.injEq] at hq; subst hq; simp at he) | cases hq)
  intro e he
  simp only [mergeData, List.mem_append, List.mem_filter] at he
  rcases he with ⟨he, -⟩ | ⟨he, -⟩
  · exact .inl (hown e he)
  · exact hdata e he

theorem graphEntry_refs {n : Nat} {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)}
    {s : Nat} {caps : List Tm} {self : Tm} {rest : Bool} {recv : Tm} {args : List Tm} {r : Ref}
    (hr : r ∈ refs (CallArguments.graphEntry n E K s caps self rest recv args)) :
    r ∈ E.flatMap refs ∨ r ∈ caps.flatMap refs ∨ r ∈ refs self ∨ r ∈ refs recv ∨ r ∈ args.flatMap refs := by
  have hp : ∀ x ∈ CallArguments.parameters n args, r ∈ refs x → r ∈ args.flatMap refs := by
    intro x hx hrx
    rcases parameters_mem hx with hx | rfl
    · exact List.mem_flatMap.mpr ⟨x, hx, hrx⟩
    · simp [refs] at hrx
  cases rest with
  | false =>
    simp only [CallArguments.graphEntry, refs, refsArgs_eq, List.flatMap_cons, List.flatMap_append,
      List.mem_append, List.mem_flatMap, List.flatMap_nil] at hr
    grind
  | true =>
    simp only [CallArguments.graphEntry, refs, refsArgs_eq, List.flatMap_cons, List.flatMap_append,
      List.mem_append, List.mem_flatMap, List.flatMap_nil] at hr
    have hd : ∀ x ∈ args.drop n, x ∈ args := fun x hx => List.mem_of_mem_drop hx
    grind

/-- **Steps that change no heap keep references valid**: congruences,
substitution, a run's entry, its environment maps and its handlers, reads
of the heap, copies, comparisons and arithmetic. Each reference of the
result is one of the term's or a valid one. -/
theorem step_refs' {k : Nat} {W : WorldT k} {h h' : Heap} {t t' : Tm} (hs : Step h t h' t') :
    h' = h → h.length = (entries W).length → Shaped W h → ∀ r ∈ refs t', r ∈ refs t ∨ RefOk W r := by
  induction hs
  all_goals try (
    intro heq hlen hsh r hm
    simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap] at hm ⊢
    grind)
  case letV =>
    intro _ _ _ r hm
    simp only [refs, List.mem_append]
    rcases subst_refs _ _ 0 r hm with h | h
    · exact .inl (.inr h)
    · exact .inl (.inl h)
  case callSpread hargs _ hre =>
    intro _ hlen hsh r hm
    subst hargs
    have hvs : ∀ x ∈ _, ∀ r ∈ refs x, RefOk W r := readElems_refs hlen hsh hre
    simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap, List.flatMap_append,
      List.flatMap_cons] at hm ⊢
    grind
  case constructSpread hargs _ hre =>
    intro _ hlen hsh r hm
    subst hargs
    have hvs : ∀ x ∈ _, ∀ r ∈ refs x, RefOk W r := readElems_refs hlen hsh hre
    simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap, List.flatMap_append,
      List.flatMap_cons] at hm ⊢
    grind
  case arrSpread hinit _ hre =>
    intro _ hlen hsh r hm
    subst hinit
    have hvs : ∀ x ∈ _, ∀ r ∈ refs x, RefOk W r := readElems_refs hlen hsh hre
    simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap, List.flatMap_append,
      List.flatMap_cons] at hm ⊢
    grind
  case makeArg ha _ _ ih =>
    intro heq hlen hsh r hm
    rw [refs_makeAt] at hm ⊢
    rcases List.mem_append.mp hm with hm | hm
    · exact .inl (List.mem_append_left _ hm)
    · obtain ⟨x, hx, hrx⟩ := List.mem_flatMap.mp hm
      rcases List.mem_or_eq_of_mem_set hx with hx | rfl
      · exact .inl (List.mem_append_right _ (List.mem_flatMap.mpr ⟨x, hx, hrx⟩))
      · rcases ih heq hlen hsh r hrx with h | h
        · exact .inl (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? ha, h⟩))
        · exact .inr h
  case makeFields =>
    intro heq; have := congrArg List.length heq; simp at this
  case arrAlloc =>
    intro heq _ _ r hm
    have hl := congrArg List.length heq
    simp only [List.length_append, Nat.add_eq_left, List.length_eq_zero_iff] at hl
    subst hl
    simp [refs, storeRefs, elemSlots] at hm
  case readField hv =>
    intro _ hlen hsh r hm; exact .inr (heap_refs hlen hsh hv r hm)
  case readProto hv =>
    intro _ hlen hsh r hm
    simp only [refs] at hm
    exact .inr (heap_refs hlen hsh hv r hm)
  case indexField hv =>
    intro _ hlen hsh r hm; exact .inr (heap_refs hlen hsh hv r hm)
  case indexProto hv =>
    intro _ hlen hsh r hm
    simp only [refs, List.mem_append] at hm ⊢
    rcases hm with hm | hm
    · exact .inr (heap_refs hlen hsh hv r hm)
    · exact .inl (.inr hm)
  case elemRead hv =>
    intro _ hlen hsh r hm; exact .inr (heap_refs hlen hsh hv r hm)
  case testV =>
    intro _ _ _ r hm; split at hm <;> simp [refs] at hm
  case arithV hb =>
    intro _ _ _ r hm; rw [binop_refs hb] at hm; cases hm
  case elemStr =>
    intro _ _ _ r hm; rw [codeUnitAt_refs] at hm; cases hm
  case mergeV hm' =>
    intro _ hlen hsh r hm
    rw [refs_makeAt] at hm
    simp only [codeRefs, List.nil_append, List.mem_flatMap, List.mem_map] at hm
    obtain ⟨x, ⟨p, hp, rfl⟩, hrx⟩ := hm
    rcases mergeParts_vals hm' p hp with ⟨l, hl⟩ | ⟨s, hs⟩
    · rw [hl] at hrx; exact .inr (heapVal_refs l hlen hsh r hrx)
    · rw [hs] at hrx; simp [refs] at hrx
  case callGraph =>
    intro _ _ _ r hm
    rcases graphEntry_refs hm with hm | hm | hm | hm | hm <;>
      simp only [refs, refsArgs_eq, List.mem_append, objRefs] at hm ⊢ <;> grind
  case constructGraph =>
    intro _ _ _ r hm
    rcases graphEntry_refs hm with hm | hm | hm | hm | hm <;>
      simp only [refs, refsArgs_eq, List.mem_append, objRefs] at hm ⊢ <;> grind
  case gotoEnter he _ =>
    intro _ _ _ r hm
    simp only [refs, refsArgs_eq, List.mem_append] at hm ⊢
    rcases hm with ((hm | hm) | hm) | hm
    · exact .inl (.inl (.inl hm))
    · rcases instantiate_refs _ _ 0 r hm with hm | ⟨i, hm⟩
      · exact .inl (.inl (.inl (List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? he, hm⟩)))
      · rcases getD_mem_or _ i _ with hx | hx
        · exact .inl (.inl (.inr (List.mem_flatMap.mpr ⟨_, hx, hm⟩)))
        · simp only [envOf] at hm; rw [hx] at hm; exact .inl (.inr hm)
    · exact .inl (.inl (.inr hm))
    · exact .inl (.inr hm)
  case frameRaise hr =>
    intro _ _ _ r hm
    simp only [refs, refsArgs_eq, List.mem_append] at hm ⊢
    exact .inl (.inl (.inl (.inr (raises_refs hr r hm))))
  case frameHandle hr =>
    intro _ _ _ r hm
    have hv := raises_refs hr
    simp only [refs, refsArgs_eq, List.mem_append] at hm ⊢
    rcases hm with (hm | hm) | hm
    · grind
    · have := envMap_refs (.inl hm); simp only [List.flatMap_cons, List.mem_append] at this; grind
    · have := envMap_refs (.inr hm); simp only [List.flatMap_cons, List.mem_append] at this; grind
  all_goals (
    intro _ _ _ r hm
    simp only [refs, refsArgs_eq, List.mem_append] at hm ⊢
    rcases hm with (hm | hm) | hm
    · grind
    · have := envMap_refs (.inl hm); (try simp only [List.flatMap_cons, List.mem_append, refs, List.not_mem_nil, false_or] at this); grind
    · have := envMap_refs (.inr hm); (try simp only [List.flatMap_cons, List.mem_append, refs, List.not_mem_nil, false_or] at this); grind)

/-- **Steps that change no heap keep reference validity.** -/
theorem step_refs {k : Nat} {W : WorldT k} {h : Heap} {t t' : Tm} (hs : Step h t h t')
    (hlen : h.length = (entries W).length) (hsh : Shaped W h) (ht : RefsOk W t) : RefsOk W t' :=
  fun r hr => (step_refs' hs rfl hlen hsh r hr).elim (ht r) id

/-! ## Copies -/

theorem toString_ne_store (n : Nat) : toString n ≠ "[]" := by
  intro h
  have := congrArg String.toList h
  simp [toString, Nat.repr] at this
  have hd : '[' ∈ Nat.toDigits 10 n := by rw [this]; simp
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hd
  simp at this

theorem toString_ne_viewElements (n : Nat) : toString n ≠ "[[viewElements]]" := by
  intro h
  have := congrArg String.toList h
  simp [toString, Nat.repr] at this
  have hd : '[' ∈ Nat.toDigits 10 n := by rw [this]; simp
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hd
  simp at this

theorem heapVal_src {k : Nat} {W : WorldT k} {h : Heap} {l : Nat} {r : Role}
    (hsh : Shaped W h) (hr : roleAt W l = some r) (hc : r = .field ∨ r = .cell ∨ r = .elem) :
    isSourceVal (heapVal h l) = true := by
  obtain ⟨u, hu, hcat, -⟩ := hsh l r hr
  simp only [heapVal, hu]
  split
  · rcases hc with rfl | rfl | rfl <;> exact hcat
  · rfl

theorem slot_src {k : Nat} {W : WorldT k} {h : Heap} {fs : List (PropKey × Nat)} {c : CallCode}
    {oid : Nat} (hsh : Shaped W h) (ho : RefsOk W (.objAt fs c oid)) {p : PropKey × Nat} (hp : p ∈ fs)
    (h1 : p.1 ≠ arrayStoreKey) (h2 : p.1 ≠ viewElementsKey) : isSourceVal (heapVal h p.2) = true := by
  have := ho (.slot p.1 p.2) (by
    rw [refs_objAt]; exact List.mem_append_left _
      (by simp only [objRefs, List.mem_cons, List.mem_map]; exact .inr (.inr ⟨p, hp, rfl⟩)))
  simp only [RefOk] at this
  rcases hr : roleAt W p.2 with _ | r
  · rw [hr] at this; cases this
  · rw [hr] at this
    refine heapVal_src hsh hr ?_
    cases r with
    | field => exact .inl rfl
    | cell => exact .inr (.inl rfl)
    | elem => cases this
    | identity => cases this
    | store fm => cases fm <;> simp [SlotRole] at this <;> simp_all

/-- **A copy allocates source values under ordinary keys**: every property a
merge reads is under a key other than `[]` and `[[viewElements]]`, and holds
a source value. A copy's accumulator is no host object (`ownAll`), and an
object owning `[[viewElements]]` with valid references is one (`ViewMetaOk`);
its source copies no internal key (`copiedKey`). -/
theorem mergeParts_cat {k : Nat} {W : WorldT k} {h : Heap} {d : List PropKey} {a b : Tm}
    {ps : List (PropKey × Tm)} (hsh : Shaped W h)
    (ha : RefsOk W a) (hb : RefsOk W b) (hm : mergeParts h d a b = some ps) :
    ∀ p ∈ ps, p.1 ≠ arrayStoreKey ∧ p.1 ≠ viewElementsKey ∧ isSourceVal p.2 = true := by
  simp only [mergeParts, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hm
  obtain ⟨p, hp, q, hq, rfl⟩ := hm
  have hown : ∀ e ∈ p, e.1 ≠ arrayStoreKey ∧ e.1 ≠ viewElementsKey ∧ isSourceVal e.2 = true := by
    intro e he
    unfold ownAll at hp
    split at hp
    · split at hp
      · cases hp
      · simp only [Option.some.injEq] at hp; subst hp
        have := mem_firstKeys he
        simp only [List.mem_map, List.mem_filter, bne_iff_ne, ne_eq] at this
        obtain ⟨x, ⟨hx, hk⟩, rfl⟩ := this
        have hv : x.1 ≠ viewElementsKey := by
          intro hv
          rename_i fs₀ _ hhost
          have hmeta : ViewMetaOk W fs₀ := ha (.fields fs₀) (by rw [refs_objAt]; simp [objRefs])
          exact hhost (hmeta.2.2 x.2 (.inl (by rw [← hv]; exact hx)))
        exact ⟨hk, hv, slot_src hsh ha hx hk hv⟩
    · cases hp
  have hdata : ∀ e ∈ q, e.1 ≠ arrayStoreKey ∧ e.1 ≠ viewElementsKey ∧ isSourceVal e.2 = true := by
    intro e he
    unfold ownData at hq
    split at hq
    · split at hq
      · cases hq
      · simp only [Option.some.injEq] at hq; subst hq
        rename_i fs cd oid _
        have := mem_firstKeys he
        rcases List.mem_append.mp this with he | he
        · simp only [List.mem_map, List.mem_filter] at he
          obtain ⟨x, ⟨hx, hk⟩, rfl⟩ := he
          obtain ⟨k1, l1⟩ := x
          have hne : k1 ≠ arrayStoreKey ∧ k1 ≠ viewElementsKey := by
            cases k1 with
            | sym _ => simp [copiedKey] at hk
            | str s =>
              simp only [copiedKey, Bool.and_eq_true, bne_iff_ne, ne_eq] at hk
              refine ⟨fun h => ?_, fun h => ?_⟩ <;> cases h <;> simp_all
          exact ⟨hne.1, hne.2, slot_src hsh hb hx hne.1 hne.2⟩
        · unfold storeData at he
          split at he
          · rename_i ls0 hls0
            split at he
            · rename_i ls hls
              simp only [List.mem_filterMap] at he
              obtain ⟨x, hx, hxe⟩ := he
              obtain ⟨o, i⟩ := x
              cases o with
              | none => cases hxe
              | some m =>
                simp only [Option.map_some, Option.some.injEq] at hxe
                subst hxe
                refine ⟨fun h => toString_ne_store i (PropKey.str.inj h),
                  fun h => toString_ne_viewElements i (PropKey.str.inj h), ?_⟩
                -- the store slot is an array store, whose cells are element cells
                have hst := hb (.slot arrayStoreKey ls0) (by
                  rw [refs_objAt]; exact List.mem_append_left _
                    (by simp only [objRefs, List.mem_cons, List.mem_map]
                        exact .inr (.inr ⟨(arrayStoreKey, ls0), lookup_mem hls0, rfl⟩)))
                simp only [RefOk] at hst
                rcases hr : roleAt W ls0 with _ | r
                · rw [hr] at hst; cases hst
                · obtain ⟨u, hu, -, hs⟩ := hsh ls0 r hr
                  rw [hls] at hu; cases hu
                  have hm : some m ∈ ls := by
                    have := List.mem_zipIdx hx
                    rw [this.2.2]; exact List.getElem_mem _
                  exact heapVal_src hsh (RefsOk_arr_iff.mp hs m hm) (.inr (.inr rfl))
            · simp at he
          · simp at he
    · simp only [Option.some.injEq] at hq; subst hq
      have := mem_firstKeys he
      simp only [stringData, List.mem_map] at this
      obtain ⟨x, -, rfl⟩ := this
      exact ⟨fun h => toString_ne_store x.2 (PropKey.str.inj h),
        fun h => toString_ne_viewElements x.2 (PropKey.str.inj h), rfl⟩
    all_goals (first | (simp only [Option.some.injEq] at hq; subst hq; simp at he) | cases hq)
  intro e he
  simp only [mergeData, List.mem_append, List.mem_filter] at he
  rcases he with ⟨he, -⟩ | ⟨he, -⟩
  · exact hown e he
  · exact hdata e he


theorem toString_ne_viewLength (n : Nat) : toString n ≠ "[[viewLength]]" := by
  intro h
  have := congrArg String.toList h
  simp [toString, Nat.repr] at this
  have hd : '[' ∈ Nat.toDigits 10 n := by rw [this]; simp
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hd
  simp at this

/-- **A copy allocates no view metadata**: no key a merge reads is
`[[viewLength]]`. The accumulator is no host object, and an object naming
`[[viewLength]]` with valid references is one (`ViewMetaOk`); the source
copies no internal key (`copiedKey`), and its store and string entries are
under index spellings. -/
theorem mergeParts_noLength {k : Nat} {W : WorldT k} {h : Heap} {d : List PropKey} {a b : Tm}
    {ps : List (PropKey × Tm)} (ha : RefsOk W a) (hm : mergeParts h d a b = some ps) :
    ∀ p ∈ ps, p.1 ≠ viewLengthKey := by
  simp only [mergeParts, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hm
  obtain ⟨p, hp, q, hq, rfl⟩ := hm
  have hown : ∀ e ∈ p, e.1 ≠ viewLengthKey := by
    intro e he
    unfold ownAll at hp
    split at hp
    · split at hp
      · cases hp
      · simp only [Option.some.injEq] at hp; subst hp
        have := mem_firstKeys he
        simp only [List.mem_map, List.mem_filter, bne_iff_ne, ne_eq] at this
        obtain ⟨x, ⟨hx, -⟩, rfl⟩ := this
        intro hv
        rename_i fs₀ _ hhost
        have hmeta : ViewMetaOk W fs₀ := ha (.fields fs₀) (by rw [refs_objAt]; simp [objRefs])
        exact hhost (hmeta.2.2 x.2 (.inr (by rw [← hv]; exact hx)))
    · cases hp
  have hdata : ∀ e ∈ q, e.1 ≠ viewLengthKey := by
    intro e he
    unfold ownData at hq
    split at hq
    · split at hq
      · cases hq
      · simp only [Option.some.injEq] at hq; subst hq
        have := mem_firstKeys he
        rcases List.mem_append.mp this with he | he
        · simp only [List.mem_map, List.mem_filter] at he
          obtain ⟨x, ⟨-, hk⟩, rfl⟩ := he
          obtain ⟨k1, l1⟩ := x
          cases k1 with
          | sym _ => simp [copiedKey] at hk
          | str s =>
            intro h; cases h
            simp [copiedKey] at hk
        · unfold storeData at he
          split at he
          · split at he
            · simp only [List.mem_filterMap] at he
              obtain ⟨x, -, hxe⟩ := he
              obtain ⟨o, i⟩ := x
              cases o with
              | none => cases hxe
              | some m =>
                simp only [Option.map_some, Option.some.injEq] at hxe
                subst hxe
                exact fun h => toString_ne_viewLength i (PropKey.str.inj h)
            · simp at he
          · simp at he
    · simp only [Option.some.injEq] at hq; subst hq
      have := mem_firstKeys he
      simp only [stringData, List.mem_map] at this
      obtain ⟨x, -, rfl⟩ := this
      exact fun h => toString_ne_viewLength x.2 (PropKey.str.inj h)
    all_goals (first | (simp only [Option.some.injEq] at hq; subst hq; simp at he) | cases hq)
  intro e he
  simp only [mergeData, List.mem_append, List.mem_filter] at he
  rcases he with ⟨he, -⟩ | ⟨he, -⟩
  · exact hown e he
  · exact hdata e he

end Verification.Kinds
