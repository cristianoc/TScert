import Verification.Semantics.KindsWrites
import Verification.Semantics.FootprintNatives
import Verification.Semantics.CallEffects
/-!
# Natives, copies and administrative steps preserve kinds

The array natives are modelled as steps on a store's list of element
locations (`Footprints.Arr`); each keeps the store's cells among the original
ones and fresh ones (`Arr.Within`), and a native's element-storage phase
preserves kinds when its world extension makes the fresh cells element cells
and the contents it writes are source values (`native_shaped`); a whole
native, callbacks included, has the obligation of every call contract
(`NativeContract`, `Semantics/KindsContracts.lean`). A copy (`Tm.merge`) reads only values the heap holds; the
administrative steps (substitution, a run's entry, its environment maps, its
handlers, reads, comparisons) refer to no location the term or the heap did
not. A contract stated as a relation between heaps can meet that obligation
only if every transition it admits from a structurally well-formed heap
reaches one (`RespectsKinds`); the typed-array element write's coarse change
admits one that does not (`elementWrite_not_respects`), and the relation
`ViewWrite` of `Semantics/KindsContracts.lean` is its contract.
-/
namespace Verification.Kinds

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

theorem binop_refs {op : Arith} {a b v : Tm} (h : binop op a b = some v) : refs v = [] := by
  obtain ⟨-, -, hv⟩ := binop_result h
  rcases hv with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl

theorem codeUnitAt_refs (s : String) (b : UInt64) : refs (codeUnitAt s b) = [] := by
  unfold codeUnitAt; split <;> rfl

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
merge reads is under a key other than `[]`, and holds a source value unless
the key is `[[viewElements]]`, whose value is the view store an ordinary
accumulator could own. -/
theorem mergeParts_cat {k : Nat} {W : WorldT k} {h : Heap} {d : List PropKey} {a b : Tm}
    {ps : List (PropKey × Tm)} (hsh : Shaped W h)
    (ha : RefsOk W a) (hb : RefsOk W b) (hm : mergeParts h d a b = some ps) :
    ∀ p ∈ ps, p.1 ≠ arrayStoreKey ∧ (p.1 ≠ viewElementsKey → isSourceVal p.2 = true) := by
  simp only [mergeParts, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hm
  obtain ⟨p, hp, q, hq, rfl⟩ := hm
  have hown : ∀ e ∈ p, e.1 ≠ arrayStoreKey ∧ (e.1 ≠ viewElementsKey → isSourceVal e.2 = true) := by
    intro e he
    unfold ownAll at hp
    split at hp
    · split at hp
      · cases hp
      · simp only [Option.some.injEq] at hp; subst hp
        have := mem_firstKeys he
        simp only [List.mem_map, List.mem_filter, bne_iff_ne, ne_eq] at this
        obtain ⟨x, ⟨hx, hk⟩, rfl⟩ := this
        exact ⟨hk, fun hv => slot_src hsh ha hx hk hv⟩
    · cases hp
  have hdata : ∀ e ∈ q, e.1 ≠ arrayStoreKey ∧ (e.1 ≠ viewElementsKey → isSourceVal e.2 = true) := by
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
          exact ⟨hne.1, fun _ => slot_src hsh hb hx hne.1 hne.2⟩
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
                refine ⟨fun h => toString_ne_store i (PropKey.str.inj h), fun _ => ?_⟩
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
      exact ⟨fun h => toString_ne_store x.2 (PropKey.str.inj h), fun _ => rfl⟩
    all_goals (first | (simp only [Option.some.injEq] at hq; subst hq; simp at he) | cases hq)
  intro e he
  simp only [mergeData, List.mem_append, List.mem_filter] at he
  rcases he with ⟨he, -⟩ | ⟨he, -⟩
  · exact hown e he
  · exact hdata e he

/-! ## Array natives -/

section natives
open Footprints

/-- A native's store lists element cells where the original store does and
the native's world extension makes every fresh cell it lists one. -/
theorem Arr.Within.refs {k : Nat} {W : WorldT k} {b : Nat} {orig : List (Option Nat)} {a : Arr}
    (hw : a.Within b orig) (ho : RefsOk W (.arr orig))
    (hfresh : ∀ l, b ≤ l → some l ∈ a.ls → roleAt W l = some .elem) : RefsOk W (.arr a.ls) :=
  RefsOk_arr_iff.mpr fun l hl => (hw.2 l hl).elim (RefsOk_arr_iff.mp ho l) (fun hb => hfresh l hb hl)

private theorem foldl_within' {b orig} {f : Arr → Nat → Arr}
    (hf : ∀ a k, a.Within b orig → (f a k).Within b orig) :
    ∀ (xs : List Nat) (a : Arr), a.Within b orig → (xs.foldl f a).Within b orig
  | [], _, h => h
  | x :: xs, a, h => foldl_within' hf xs (f a x) (hf a x h)

theorem Arr.pop_within {b} {a : Arr} (h : b ≤ a.next) : a.pop.Within b a.ls := by
  unfold Arr.pop
  split
  · exact (Arr.Within.refl h).setLength _
  · exact ((Arr.Within.refl h).delete _).setLength _

theorem Arr.shift_within {b} {a : Arr} (h : b ≤ a.next) : a.shift.Within b a.ls := by
  unfold Arr.shift
  split
  · exact (Arr.Within.refl h).setLength _
  · refine (Arr.Within.delete ?_ _).setLength _
    refine foldl_within' (fun s j hs => ?_) _ _ (Arr.Within.refl h)
    split
    · exact hs.set _
    · exact hs.delete _

theorem Arr.reverse_within {b} {a : Arr} (h : b ≤ a.next) : a.reverse.Within b a.ls := by
  unfold Arr.reverse
  refine foldl_within' (fun s lower hs => ?_) _ _ (Arr.Within.refl h)
  dsimp only
  split
  · exact (hs.set _).set _
  · exact (hs.set _).delete _
  · exact (hs.delete _).set _
  · exact hs

/-- **Every array native keeps its store's cells among the original and
fresh ones**: `Set`, `Delete`, a length change, `push`, `pop`, `shift`,
`unshift`, `reverse` and `sort`'s writeback. -/
theorem Arr.natives_within {b} {a : Arr} (h : b ≤ a.next) (k n c len : Nat) :
    (a.set k).Within b a.ls ∧ (a.delete k).Within b a.ls ∧ (a.setLength n).Within b a.ls ∧
      a.push.Within b a.ls ∧ a.pop.Within b a.ls ∧ a.shift.Within b a.ls ∧
      a.unshift.Within b a.ls ∧ a.reverse.Within b a.ls ∧ (a.writeback c len).Within b a.ls :=
  ⟨(Arr.Within.refl h).set k, (Arr.Within.refl h).delete k, (Arr.Within.refl h).setLength n,
    Arr.push_within h, Arr.pop_within h, Arr.shift_within h, Arr.unshift_within h,
    Arr.reverse_within h, Arr.writeback_within c len (Arr.Within.refl h)⟩

/-- **An array native's element-storage phase preserves kinds.** From a
well-formed heap `h`, the phase of a native that rewrites the array store at
`s` reaches `h'`: the store holds the native's result `a.ls`, every other old
location keeps its contents or is an element cell now holding a source
value, and every fresh location holds a source value. The world extension
makes the fresh locations element cells.

The premises are stated here: the store's change, the element contents and
the fresh locations' contents. `array_native_post` bounds which locations
change and gives none of them. -/
theorem native_shaped {k : Nat} {W : WorldT k} {h h' : Heap} {s : Nat} {orig : List (Option Nat)}
    {a : Arr} (cs : List (Ctr k)) (hlen : h.length = (entries W).length) (hsh : Shaped W h)
    (hs : roleAt W s = some (.store .array)) (hso : h[s]? = some (.arr orig))
    (hw : a.Within h.length orig)
    (hlen' : h'.length = h.length + cs.length) (hs' : h'[s]? = some (.arr a.ls))
    (hcells : ∀ l, some l ∈ a.ls → l < h'.length)
    (hold : ∀ l, l < h.length → l ≠ s → h'[l]? = h[l]? ∨
      (roleAt W l = some .elem ∧ ∃ v, h'[l]? = some v ∧ isSourceVal v = true ∧
        RefsOk (appendWs W (cs.map fun c => (Role.elem, c))) v))
    (hfresh : ∀ l, h.length ≤ l → l < h'.length → ∃ v, h'[l]? = some v ∧ isSourceVal v = true ∧
        RefsOk (appendWs W (cs.map fun c => (Role.elem, c))) v) :
    Shaped (appendWs W (cs.map fun c => (Role.elem, c))) h' := by
  let W' := appendWs W (cs.map fun c => (Role.elem, c))
  have hxt : WExt W W' := WExt_appendWs W _
  have hroleNew : ∀ l, h.length ≤ l → l < h'.length → roleAt W' l = some .elem := by
    intro l h1 h2
    obtain ⟨i, rfl⟩ : ∃ i, l = (entries W).length + i := ⟨l - (entries W).length, by omega⟩
    rw [roleAt_appendWs']
    simp only [List.map_map, Function.comp_def, List.map_const', List.getElem?_replicate]
    rw [if_pos (by omega)]
  intro l r hr
  by_cases hl : l < h.length
  · have hrW : roleAt W l = some r := by
      rw [roleAt_appendWs_lt W _ (by omega)] at hr; exact hr
    by_cases hls : l = s
    · subst hls
      rw [hs] at hrW; cases hrW
      obtain ⟨u, hu, -, ho⟩ := hsh l _ hs
      rw [hso] at hu; cases hu
      refine ⟨_, hs', ⟨_, rfl⟩, Arr.Within.refs hw (RefsOk_mono hxt ho) fun m hm hm' => ?_⟩
      exact hroleNew m hm (hcells m hm')
    · rcases hold l hl hls with he | ⟨he, v, hv, hsrc, hvr⟩
      · obtain ⟨u, hu, hsu⟩ := hsh l r hrW
        exact ⟨u, by rw [he]; exact hu, Shape_mono hxt hsu⟩
      · rw [he] at hrW; cases hrW
        exact ⟨v, hv, hsrc, hvr⟩
  · have hlt : l < h'.length := by
      have := roleAt_lt hr; simp at this; omega
    rw [hroleNew l (by omega) hlt] at hr; cases hr
    obtain ⟨v, hv, hsrc, hvr⟩ := hfresh l (by omega) hlt
    exact ⟨v, hv, hsrc, hvr⟩

end natives

/-! ## Contracts no step states -/

/-- **A heap relation respects kinds**: every transition it admits from a
heap meeting a world's structural part reaches a heap meeting the structural
part of an extension of that world. A contract stated as a relation between
heaps meets the native-contract condition only if it has this property. -/
def RespectsKinds (R : Heap → Heap → Prop) : Prop :=
  ∀ (k : Nat) (W : WorldT k) (h h' : Heap), h.length = (entries W).length → Shaped W h → R h h' →
    ∃ W' : WorldT k, WExt W W' ∧ h'.length = (entries W').length ∧ Shaped W' h'

/-- **The typed-array element write's coarse change does not respect
kinds** (`ElementWrite.changes`: every location holding no store, object or
number may change, and every store keeps its length). A field holding a
string may come to hold a store; the element write itself excludes that
(`CallEffects.ElementWrite.Holds.not_string_to_store`). -/
theorem elementWrite_not_respects :
    ¬ RespectsKinds (CallEffects.ElementWrite.stores.changes.Holds) := by
  intro H
  let W : WorldT 0 := ofEntries [(.field, fun _ hj _ _ => absurd hj (Nat.not_lt_zero _))]
  have hW : roleAt W 0 = some .field := by simp [W, roleAt, roles]
  have hsh : Shaped W [.str "a"] := by
    intro l r hr
    have hl : l = 0 := by have := roleAt_lt hr; simp [W] at this; omega
    subst hl
    rw [hW] at hr; cases hr
    exact ⟨_, rfl, rfl, fun _ h => by simp [refs] at h⟩
  have hc : CallEffects.ElementWrite.stores.changes.Holds [.str "a"] [.arr []] := by
    refine ⟨fun l v hv halt => ?_, fun _ l ls hl => ?_, fun hg => ?_⟩
    · have : l = 0 := by have := (List.getElem?_eq_some_iff.mp hv).1; simp at this; omega
      subst this; simp at hv; subst hv
      simp [HeapKnowledge.Changes.alters] at halt
    · have : l = 0 := by have := (List.getElem?_eq_some_iff.mp hl).1; simp at this; omega
      subst this; simp at hl
    · simp [CallEffects.ElementWrite.changes] at hg
  obtain ⟨W', hx, -, hsh'⟩ := H 0 W _ _ (by simp [W]) hsh hc
  obtain ⟨u, hu, hcat, -⟩ := hsh' 0 .field (WExt_roleAt hx hW)
  simp at hu; subst hu
  simp [Cat, isSourceVal] at hcat

end Verification.Kinds
