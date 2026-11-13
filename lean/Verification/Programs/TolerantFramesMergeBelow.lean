import Verification.Programs.TolerantFramesStoreOpsBelowNames

/-! # Tolerant frames: a merge's facts below its counter

Every fact of the merged store (`SinglePass.mergeState`) names only names
below the merge's next fresh name (`mergeState_factsBelow`), where every
predecessor's slots, facts and fresh names are below the merge's first fresh
name: the common facts are the first predecessor's; a restated fact names a
predecessor's names and the fresh names its renaming sends them to, which
are slots' names of the merge; a weakest bound names the names of a
predecessor's bound of its form; an entailed bound is a predecessor's
difference; a guarded fact is renamed from slots to the merge's names; and
`Store.drop` keeps facts below (`drop_below`). With `mergeState_wf` this
gives `StateBelow` of the merged state at its counter (`mergeState_below`). -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations
open Verification.SinglePass (Atom Store State)
open ProgramTyping PositiveGraphs

/-! ## The names of a restatement -/

/-- **A fact restated at fresh names** (`Atom.renameEach`) names the
original's names and the names the renaming sends them to. -/
theorem renameEach_names {m : Std.HashMap Nat (List Nat)} {a b : Atom} (hb : b ∈ Atom.renameEach m a) :
    ∀ y ∈ b.names, ∃ x ∈ a.names, y = x ∨ ∃ φs, m[x]? = some φs ∧ y ∈ φs := by
  unfold Atom.renameEach at hb
  obtain ⟨c, hc, hr⟩ := List.mem_filterMap.mp hb
  have inv : ∀ c ∈ a.names.eraseDups.foldl (fun (acc : List (List (Nat × Nat))) x => match m.get? x with
      | some φs => (acc.flatMap fun c => φs.map fun φ => (x, φ) :: c).take 16
      | none => acc) [[]], ∀ x φ, (x, φ) ∈ c → ∃ φs, m[x]? = some φs ∧ φ ∈ φs := by
    refine foldl_inv (fun (acc : List (List (Nat × Nat))) => ∀ c ∈ acc, ∀ x φ, (x, φ) ∈ c → ∃ φs, m[x]? = some φs ∧ φ ∈ φs)
      _ _ _ (fun c hc x φ hx => by simp at hc; subst hc; cases hx) ?_
    intro y _ acc hacc c hc x φ hx
    split at hc
    · rename_i φs hφs
      rw [Std.HashMap.get?_eq_getElem?] at hφs
      obtain ⟨c', hc', hcm⟩ := List.mem_flatMap.mp (List.mem_of_mem_take hc)
      obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hcm
      rcases List.mem_cons.mp hx with he | hx
      · cases he; exact ⟨φs, hφs, hψ⟩
      · exact hacc c' hc' x φ hx
    · exact hacc c hc x φ hx
  intro y hy
  obtain ⟨x, hx, hxy⟩ := atom_rename_names hr y hy
  refine ⟨x, hx, ?_⟩
  cases hl : c.lookup x with
  | none => rw [hl] at hxy; cases hxy; exact .inl rfl
  | some φ =>
    rw [hl] at hxy; cases hxy
    exact .inr (inv c hc x φ (lookup_mem c x φ hl))

theorem mergeEqAtoms_names {int : Bool} {φ x : Nat} {a : Atom} (ha : a ∈ mergeEqAtoms int φ x) :
    ∀ y ∈ a.names, y = φ ∨ y = x := by
  simp only [mergeEqAtoms, List.mem_cons] at ha
  rcases ha with rfl | ha
  · intro y hy; simp only [Atom.names, List.mem_cons, List.mem_nil_iff, or_false] at hy; exact hy
  · cases int with
    | false => simp at ha
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, if_false, List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl <;>
      · intro y hy
        simp [Atom.names, HeapKnowledge.IndexFact.slots, Linear.Fact.vars, HeapKnowledge.Term.slots,
          HeapKnowledge.Term.value] at hy
        rcases hy with h | h
        · exact .inl h
        · exact .inr h

/-- **A predecessor's equalities** (`mergeEqual`) name only names its
renaming renames and their fresh names. -/
theorem mergeEqual_names {st : State} {names : Array Nat} {m : Std.HashMap Nat (List Nat)} {a : Atom}
    (ha : a ∈ mergeEqual st names m) : ∀ y ∈ a.names, ∃ x φs, m[x]? = some φs ∧ (y = x ∨ y ∈ φs) := by
  unfold mergeEqual at ha
  rw [Std.HashMap.fold_eq_foldl_toList] at ha
  revert ha
  refine foldl_inv (fun (acc : List Atom) => a ∈ acc → ∀ y ∈ a.names, ∃ x φs, m[x]? = some φs ∧ (y = x ∨ y ∈ φs))
    _ _ _ (fun h => by cases h) ?_
  intro ⟨x, φs⟩ hp acc hacc ha y hy
  have hm : m[x]? = some φs := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hp
  simp only [List.mem_append, List.mem_flatMap] at ha
  rcases ha with (ha | ⟨⟨φ, ψ⟩, hpair, ha⟩) | ha
  · split at ha
    · obtain ⟨φ, hφs, ha⟩ := List.mem_flatMap.mp ha
      rcases mergeEqAtoms_names ha y hy with rfl | rfl
      · exact ⟨x, φs, hm, .inr hφs⟩
      · exact ⟨y, φs, hm, .inl rfl⟩
    · cases ha
  · obtain ⟨hφ1, hψ1⟩ := zip_tail_eq (P := fun y => y ∈ φs) φs (fun _ h => h) _ hpair
    rcases mergeEqAtoms_names ha y hy with rfl | rfl
    · exact ⟨x, φs, hm, .inr hψ1⟩
    · exact ⟨x, φs, hm, .inr hφ1⟩
  · exact hacc ha y hy

/-! ## The merge's names below its counter -/

section Below
variable {preds : List State} {width fresh0 : Nat}

/-- The predecessors' names, facts and fresh names below the merge's first
fresh name, and their width. -/
structure PredsBelow (preds : List State) (width fresh0 : Nat) : Prop where
  len : ∀ q ∈ preds, q.names.length = width
  below : ∀ q ∈ preds, StateBelow q fresh0
  wf : ∀ q ∈ preds, StoreWF q.store

/-- The merge's next fresh name. -/
abbrev mNext (preds : List State) (width fresh0 : Nat) : Nat := (mergeSlots preds width fresh0).1

theorem PredsBelow.names (B : PredsBelow preds width fresh0) (hne : preds ≠ []) :
    ∀ x ∈ (mNames preds width fresh0).toList, x < mNext preds width fresh0 := by
  have I := mergeSlots_inv preds width fresh0
  have hw : (mergeSlots preds width fresh0).2.1.size = width := I.size
  obtain ⟨q, qs, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hq := List.mem_cons_self (a := q) (l := qs)
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hj' : j < (mergeSlots (q :: qs) width fresh0).2.1.size := by simpa using hj
  simp only [Array.getElem_toList]
  rcases I.slot j hj' with h1 | ⟨-, h2, -⟩
  · rw [← h1 q hq]
    have h0 := pred_below (p := 0) (by simp) B.len (fun q hq => (B.below q hq).1) (hw ▸ hj')
    exact Nat.lt_of_lt_of_le (by simpa using h0) I.ge
  · exact h2

/-- A fresh name a predecessor's renaming sends a name to is a slot's name,
so below the counter. -/
theorem PredsBelow.renamed (B : PredsBelow preds width fresh0) (hne : preds ≠ []) {p : Nat}
    (hp : p < (mRen preds width fresh0).length) {x : Nat} {φs : List Nat}
    (hm : ((mRen preds width fresh0)[p])[x]? = some φs) : ∀ φ ∈ φs, φ < mNext preds width fresh0 := by
  intro φ hφ
  have I := mergeSlots_inv preds width fresh0
  have hg : ((mRen preds width fresh0)[p]).getD x [] = φs := by
    rw [Std.HashMap.getD_eq_getD_getElem?, hm]; rfl
  obtain ⟨j, hj, h1, -, -⟩ := I.ren p hp x φ (hg ▸ hφ)
  rw [← h1]
  exact B.names hne _ (by simp)

theorem PredsBelow.key (B : PredsBelow preds width fresh0) {p : Nat}
    (hp : p < (mRen preds width fresh0).length) {x : Nat} {φs : List Nat}
    (hm : ((mRen preds width fresh0)[p])[x]? = some φs) : x < fresh0 := by
  have hpl : p < preds.length := by rwa [(mergeSlots_inv preds width fresh0).len] at hp
  exact rename_key_below hpl B.len (fun q hq => (B.below q hq).1) hp hm

theorem PredsBelow.ge (_B : PredsBelow preds width fresh0) : fresh0 ≤ mNext preds width fresh0 :=
  (mergeSlots_inv preds width fresh0).ge

theorem PredsBelow.fact (B : PredsBelow preds width fresh0) {p : Nat} (hp : p < preds.length) {a : Atom}
    (ha : a ∈ storeAll (preds[p]).store) : AtomBelow (mNext preds width fresh0) a :=
  fun x hx => Nat.lt_of_lt_of_le ((B.below _ (List.getElem_mem hp)).2.1 a ha x hx) B.ge

/-- **Each predecessor's restatements are below the counter.** -/
theorem PredsBelow.variants (B : PredsBelow preds width fresh0) (hne : preds ≠ []) {p : Nat}
    (hp : p < (mergeVariants preds (mNames preds width fresh0) (mRen preds width fresh0)).length) :
    ∀ a ∈ (mergeVariants preds (mNames preds width fresh0) (mRen preds width fresh0))[p],
      AtomBelow (mNext preds width fresh0) a := by
  have hl : (mergeVariants preds (mNames preds width fresh0) (mRen preds width fresh0)).length = preds.length :=
    mergeVariants_length _ _ _ (mergeSlots_inv _ width fresh0).len
  have hpp : p < preds.length := hl ▸ hp
  have hpr : p < (mRen preds width fresh0).length := by rw [(mergeSlots_inv _ width fresh0).len]; exact hpp
  have hv : (mergeVariants preds (mNames preds width fresh0) (mRen preds width fresh0))[p]? =
      some ((mergeVariants preds (mNames preds width fresh0) (mRen preds width fresh0))[p]) :=
    List.getElem?_eq_getElem hp
  revert hv
  generalize (mergeVariants preds (mNames preds width fresh0) (mRen preds width fresh0))[p] = v
  intro hv
  unfold mergeVariants at hv
  rw [List.getElem?_map, zip_get hpp hpr] at hv
  simp only [Option.map_some, Option.some.injEq] at hv
  subst hv
  intro a ha
  rcases Std.HashSet.mem_insertMany_list.mp ha with ha | ha
  · revert ha
    refine foldl_inv (fun (acc : Std.HashSet Atom) => ∀ a ∈ acc, AtomBelow (mNext preds width fresh0) a) _ _ _
      (fun a ha => by simp at ha) ?_ a
    intro b hb acc hacc a ha
    rcases Std.HashSet.mem_insertMany_list.mp ha with ha | ha
    · exact hacc a ha
    · have hbs : b ∈ storeAll (preds[p]).store := by
        rw [Std.HashMap.fold_eq_foldl_toList] at hb
        revert hb
        refine foldl_inv (fun (acc : List Atom) => b ∈ acc → b ∈ storeAll (preds[p]).store) _ _ _
          (fun h => by cases h) ?_
        intro ⟨x, _⟩ _ acc hacc hb
        rcases List.mem_append.mp hb with hb | hb
        · exact about_storeAll hb
        · exact hacc hb
      intro y hy
      obtain ⟨x, hx, rfl | ⟨φs, hm, hy⟩⟩ := renameEach_names (List.contains_iff_mem.mp ha) y hy
      · exact B.fact hpp hbs y hx
      · exact B.renamed hne hpr hm y hy
  · intro y hy
    obtain ⟨x, φs, hm, rfl | hy⟩ := mergeEqual_names (List.contains_iff_mem.mp ha) y hy
    · exact Nat.lt_of_lt_of_le (B.key hpr hm) B.ge
    · exact B.renamed hne hpr hm y hy

/-- **The met store's facts are below the counter.** -/
theorem PredsBelow.met0 (B : PredsBelow preds width fresh0) (hne : preds ≠ []) :
    FactsBelow (mergeMet0 preds (mNames preds width fresh0) (mRen preds width fresh0)) (mNext preds width fresh0) := by
  unfold mergeMet0
  refine drop_below ?_
  have hvl : 0 < (mergeVariants preds (mNames preds width fresh0) (mRen preds width fresh0)).length := by
    rw [mergeVariants_length _ _ _ (mergeSlots_inv _ width fresh0).len]
    exact List.length_pos_iff.mpr hne
  refine mergeMeet_inv (fun s => FactsBelow s (mNext preds width fresh0)) (AtomBelow (mNext preds width fresh0))
    (fun _ _ hs ha => add_below hs ha) hvl (B.variants hne hvl) ?_
  obtain ⟨w, hsub⟩ := mergeCommon_live B.wf
  have hp0 : 0 < preds.length := List.length_pos_iff.mpr hne
  intro a ha
  exact B.fact hp0 (live_storeAll (hsub 0 hp0 a (storeAll_live w ha)))

/-- **Each predecessor's differences are below the counter**, over a met
store whose facts are. -/
theorem PredsBelow.diffs (B : PredsBelow preds width fresh0) (hne : preds ≠ []) {met0 : Store} :
    ∀ d ∈ mergeDiffs preds (mRen preds width fresh0)
      (mergeVariants preds (mNames preds width fresh0) (mRen preds width fresh0)) met0,
      ∀ a ∈ d, AtomBelow (mNext preds width fresh0) a := by
  intro d hd
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hd
  have hl := mergeDiffs_length preds (mRen preds width fresh0)
    (mergeVariants preds (mNames preds width fresh0) (mRen preds width fresh0)) met0
    (mergeSlots_inv _ width fresh0).len (mergeVariants_length _ _ _ (mergeSlots_inv _ width fresh0).len)
  have hpp : p < preds.length := hl ▸ hp
  have hpr : p < (mRen preds width fresh0).length := by rw [(mergeSlots_inv _ width fresh0).len]; exact hpp
  have hpv : p < (mergeVariants preds (mNames preds width fresh0) (mRen preds width fresh0)).length := by
    rw [mergeVariants_length _ _ _ (mergeSlots_inv _ width fresh0).len]; exact hpp
  have hdp := List.getElem?_eq_getElem hp
  revert hdp
  generalize (mergeDiffs preds (mRen preds width fresh0)
    (mergeVariants preds (mNames preds width fresh0) (mRen preds width fresh0)) met0)[p] = d
  intro hdp
  unfold mergeDiffs at hdp
  rw [List.getElem?_map, zip_get (l := preds.zip _) (by simp only [List.length_zip]; exact Nat.lt_min.mpr ⟨hpp, hpr⟩) hpv,
    List.getElem_zip] at hdp
  simp only [Option.map_some, Option.some.injEq] at hdp
  subst hdp
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · have ha := (List.mem_filter.mp ha).1
    simp only [SinglePass.timedKind, Store.diff] at ha
    exact B.fact hpp (toList_storeAll (List.mem_filter.mp ha).1)
  · rw [Std.HashSet.fold_eq_foldl_toList] at ha
    revert ha
    refine foldl_inv (fun (acc : List Atom) => a ∈ acc → AtomBelow (mNext preds width fresh0) a) _ _ _
      (fun h => by cases h) ?_
    intro b hb acc hacc ha
    split at ha
    · exact hacc ha
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact B.variants hne hpv a (Std.HashSet.mem_toList.mp hb)
      · exact hacc ha

/-- **The merged store's facts are below the counter.** -/
theorem PredsBelow.store (B : PredsBelow preds width fresh0) (hne : preds ≠ []) :
    FactsBelow (mergeStore preds width (mNames preds width fresh0) (mRen preds width fresh0))
      (mNext preds width fresh0) := by
  have hD := B.diffs hne (met0 := mergeMet0 preds (mNames preds width fresh0) (mRen preds width fresh0))
  have hdl : 0 < (mergeDiffs preds (mRen preds width fresh0)
      (mergeVariants preds (mNames preds width fresh0) (mRen preds width fresh0))
      (mergeMet0 preds (mNames preds width fresh0) (mRen preds width fresh0))).length := by
    rw [mergeDiffs_length _ _ _ _ (mergeSlots_inv _ width fresh0).len
      (mergeVariants_length _ _ _ (mergeSlots_inv _ width fresh0).len)]
    exact List.length_pos_iff.mpr hne
  unfold mergeStore
  refine mergeAddGuarded_inv (fun s => FactsBelow s (mNext preds width fresh0)) (AtomBelow (mNext preds width fresh0))
    (fun _ _ hs ha => add_below hs ha) ?_ ?_
  · intro x _ a hr y hy
    obtain ⟨i, -, hi⟩ := atom_rename_names hr y hy
    exact B.names hne y (List.mem_of_getElem? hi)
  refine mergeEntailed_inv (fun s => FactsBelow s (mNext preds width fresh0)) (AtomBelow (mNext preds width fresh0))
    (fun _ _ hs ha => add_below hs ha) (fun d hd F neg ha _ _ => hD d hd _ ha) ?_
  refine mergeBounds_inv (fun s => FactsBelow s (mNext preds width fresh0)) (AtomBelow (mNext preds width fresh0))
    (fun _ _ hs ha => add_below hs ha) ?_ (B.met0 hne)
  intro key w hall
  obtain ⟨d', hd', -⟩ := hall _ (List.mem_map.mpr ⟨_, List.getElem_mem hdl, rfl⟩)
  obtain ⟨F0, hF0, hn⟩ := boundsOf_get hd'
  have hb := hD _ (List.getElem_mem hdl) _ hF0
  intro y hy
  apply hb
  simp only [Atom.names, HeapKnowledge.IndexFact.slots, Linear.Fact.vars, List.mem_append] at hy ⊢
  rcases hy with hy | hy
  · refine .inl ?_
    obtain ⟨t, ht, hy⟩ := List.mem_flatMap.mp hy
    obtain ⟨⟨t', c⟩, hc, rfl⟩ := List.mem_map.mp ht
    rw [← hn] at hc
    exact List.mem_flatMap.mpr ⟨t', normalize_vars F0 t' (List.mem_map.mpr ⟨_, hc, rfl⟩), hy⟩
  · exact .inr hy

end Below

section Merge
variable {ι : Type} [DecidableEq ι] [Hashable ι]

/-- **A merge's facts are below its counter**: where the predecessors are
of the context's width, with well-formed stores and slots', facts' and fresh
names below the merge's first fresh name `fresh`, every fact of the merged
store names only names below the merge's next fresh name. -/
theorem mergeState_factsBelow {G : NormalGraph ι} {context : List (Ty ι)} {preds : List State}
    {edgesIn : List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)} {fresh : Nat}
    (hne : preds ≠ []) (hlen : ∀ q ∈ preds, q.names.length = context.length) (hwf : ∀ q ∈ preds, StoreWF q.store)
    (hbel : ∀ q ∈ preds, StateBelow q fresh) :
    FactsBelow (SinglePass.mergeState G context preds edgesIn fresh).state.store
      (SinglePass.mergeState G context preds edgesIn fresh).fresh := by
  rw [mergeState_state, mergeState_fresh]
  exact (PredsBelow.mk hlen hbel hwf).store hne

/-- **The merged state is below its counter** (`StateBelow`): its names,
facts and fresh names. -/
theorem mergeState_below {G : NormalGraph ι} {context : List (Ty ι)} {preds : List State}
    {edgesIn : List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)} {fresh : Nat}
    (hne : preds ≠ []) (hlen : ∀ q ∈ preds, q.names.length = context.length) (hwf : ∀ q ∈ preds, StoreWF q.store)
    (hbel : ∀ q ∈ preds, StateBelow q fresh) :
    StateBelow (SinglePass.mergeState G context preds edgesIn fresh).state
      (SinglePass.mergeState G context preds edgesIn fresh).fresh := by
  obtain ⟨-, -, hn, hf⟩ := mergeState_wf (G := G) (edgesIn := edgesIn) hne hlen hwf hbel
  exact ⟨hn, mergeState_factsBelow hne hlen hwf hbel, hf⟩

end Merge

end Verification.TolerantFrames
