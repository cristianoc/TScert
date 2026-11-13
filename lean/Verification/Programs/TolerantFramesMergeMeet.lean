import Verification.Programs.TolerantFramesMergeNames

/-! # Tolerant frames: a merge's met store

The facts the merge keeps before its joins (`mergeMet0`): the first
predecessor's store less each fact another lacks (`mergeCommon`), the facts
each predecessor states of the names it renames, restated at the fresh names,
that every predecessor states (`mergeMeet` over `mergeVariants`), the names
renamed away forgotten (`Store.drop`). On the path through predecessor `p`,
whose store holds at `η`, every one of them holds at the merge's valuation
`mergeVal` (`mergeMet0_ok`), and so does each fact `p` states beyond them
(`mergeDiffs_ok`). -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations
open Verification.SinglePass (Atom Store State)

/-! ## A store's live facts -/

theorem live_storeAll {s : Store} {a : Atom} (ha : a ∈ s.live) : a ∈ storeAll s :=
  toList_storeAll (by rw [toList_eq, mem_keysOf]; exact ha)

theorem remove_live {s : Store} (w : StoreWF s) {a b : Atom} (ha : a ∈ s.live) (hb : b ∈ (s.remove a).live) :
    b ∈ s.live ∧ b ≠ a := by
  have hc : a.canon = a := w.canonical a ha
  unfold Store.remove at hb
  simp only [hc] at hb
  split at hb
  · rw [Std.HashSet.mem_erase] at hb
    exact ⟨hb.2, fun e => by subst e; simp at hb⟩
  · exact absurd (Std.HashSet.contains_iff_mem.mpr ha) ‹_›

/-! ## The common facts -/

/-- One predecessor's diff removed: the facts left are the store's and
`q`'s. -/
theorem diffRemove_live {met : Store} {q : Store} (w : StoreWF met) :
    let r : Store := Id.run (forIn (m := Id) (met.toList.filter fun a => !q.live.contains a) met
      (fun a (s : Store) => ForInStep.yield (s.remove a) : Atom → Store → Id (ForInStep Store)))
    StoreWF r ∧ ∀ a ∈ r.live, a ∈ met.live ∧ a ∈ q.live := by
  intro r
  let L := met.toList.filter fun a => !q.live.contains a
  have key := forIn_idx L met (fun a (s : Store) => ForInStep.yield (s.remove a) : Atom → Store → Id (ForInStep Store))
    (fun i st => StoreWF st ∧ (∀ a ∈ st.live, a ∈ met.live) ∧ ∀ a ∈ st.live, ∀ i' < i, L[i']? ≠ some a)
    (fun st => StoreWF st ∧ ∀ a ∈ st.live, a ∈ met.live ∧ a ∈ q.live)
    ⟨w, fun a h => h, fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩ ?_ ?_ ?_
  · exact key
  · intro i a st st' hi ⟨wst, hsub, hnot⟩ hf
    cases hf
    have haL : a ∈ L := List.mem_of_getElem? hi
    have ham : a ∈ met.live := by
      have := (List.mem_filter.mp haL).1; rw [toList_eq, mem_keysOf] at this; exact this
    refine ⟨remove_wf wst a, fun b hb => ?_, fun b hb i' hi' => ?_⟩
    · by_cases hast : a ∈ st.live
      · exact hsub b (remove_live wst hast hb).1
      · have : st.remove a = st := by
          unfold Store.remove
          rw [w.canonical a ham]
          simp only [Std.HashSet.contains_iff_mem, hast]; rfl
        rw [this] at hb; exact hsub b hb
    · by_cases hast : a ∈ st.live
      · obtain ⟨hb1, hb2⟩ := remove_live wst hast hb
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
        · exact hnot b hb1 i' hi'
        · rw [hi]; exact fun e => hb2 (Option.some.inj e).symm
      · have : st.remove a = st := by
          unfold Store.remove
          rw [w.canonical a ham]
          simp only [Std.HashSet.contains_iff_mem, hast]; rfl
        rw [this] at hb
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
        · exact hnot b hb i' hi'
        · rw [hi]; exact fun e => hast ((Option.some.inj e) ▸ hb)
  · intro i a st st' _ _ hf; cases hf
  · intro st ⟨wst, hsub, hnot⟩
    refine ⟨wst, fun a ha => ⟨hsub a ha, ?_⟩⟩
    refine Classical.byContradiction fun hq => ?_
    have haL : a ∈ L := List.mem_filter.mpr ⟨by rw [toList_eq, mem_keysOf]; exact hsub a ha,
      by simpa [Std.HashSet.contains_iff_mem] using hq⟩
    obtain ⟨i', hi', he⟩ := List.getElem_of_mem haL
    exact hnot a ha i' hi' (by rw [List.getElem?_eq_getElem hi', he])

/-- **The common facts are every predecessor's**: the first predecessor's
store less each fact another lacks is well-formed, and each of its facts is
a live fact of every predecessor. -/
theorem mergeCommon_live {preds : List State} (hwf : ∀ q ∈ preds, StoreWF q.store) :
    StoreWF (mergeCommon preds) ∧ ∀ p (hp : p < preds.length), ∀ a ∈ (mergeCommon preds).live,
      a ∈ preds[p].store.live := by
  cases preds with
  | nil => exact ⟨storeWF_empty, fun p hp => absurd hp (Nat.not_lt_zero _)⟩
  | cons s0 rest =>
    unfold mergeCommon SinglePass.timedKind
    simp only [Id.run, List.headD_cons, List.tail_cons]
    refine forIn_idx_bind rest s0.store _
      (fun k met => StoreWF met ∧ (∀ a ∈ met.live, a ∈ s0.store.live) ∧
        ∀ j (hj : j < rest.length), j < k → ∀ a ∈ met.live, a ∈ rest[j].store.live)
      (fun met => StoreWF met ∧ (∀ a ∈ met.live, a ∈ s0.store.live) ∧
        ∀ j (hj : j < rest.length), ∀ a ∈ met.live, a ∈ rest[j].store.live) _
      (fun met => StoreWF met ∧ ∀ p (hp : p < (s0 :: rest).length), ∀ a ∈ met.live, a ∈ (s0 :: rest)[p].store.live)
      ⟨hwf s0 (List.mem_cons_self ..), fun a h => h, fun j _ hj => absurd hj (Nat.not_lt_zero _)⟩ ?_ ?_
      (fun b ⟨w, h0, hj⟩ => ⟨w, h0, fun j hj' => hj j hj' hj'⟩) ?_
    · intro k q b b' hk ⟨w, h0, hj⟩ hf
      change ForInStep.yield (forIn _ b _) = _ at hf
      cases hf
      obtain ⟨w', hsub⟩ := diffRemove_live (q := q.store) w
      refine ⟨w', fun a ha => h0 a (hsub a ha).1, fun j hj' hjk a ha => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hjk with hjk | rfl
      · exact hj j hj' hjk a (hsub a ha).1
      · have : rest[j] = q := Option.some.inj (by rw [← List.getElem?_eq_getElem hj']; exact hk)
        rw [this]; exact (hsub a ha).2
    · intro k q b b' _ _ hf
      change ForInStep.yield (forIn _ b _) = _ at hf
      cases hf
    · intro b ⟨w, h0, hj⟩
      refine ⟨w, fun p hp a ha => ?_⟩
      cases p with
      | zero => exact h0 a ha
      | succ j => exact hj j (by simpa using hp) a ha

/-! ## A fact restated at the fresh names -/

theorem lookup_mem : ∀ (c : List (Nat × Nat)) (x φ : Nat), c.lookup x = some φ → (x, φ) ∈ c
  | [], _, _, h => by simp [List.lookup] at h
  | (k, v) :: c, x, φ, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i he; simp only [beq_iff_eq] at he; subst he; cases h; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (lookup_mem c x φ h)

/-- **A fact restated at fresh names holds** (`Atom.renameEach`) at a
valuation under which each fresh name denotes the name it renames. -/
theorem renameEach_holds {m : Std.HashMap Nat (List Nat)} {a b : Atom} {η : Env} {h : Heap}
    (hm : ∀ x φs, m[x]? = some φs → ∀ φ ∈ φs, η φ = η x) (ha : AtomHolds a η h)
    (hb : b ∈ Atom.renameEach m a) : AtomHolds b η h := by
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
  refine atomHolds_rename (fun x i hxi => ?_) hr ha
  cases hl : c.lookup x with
  | none => rw [hl] at hxi; cases hxi; rfl
  | some φ =>
    rw [hl] at hxi; cases hxi
    obtain ⟨φs, hφs, hφ⟩ := inv c hc x φ (lookup_mem c x φ hl)
    exact hm x φs hφs φ hφ

/-! ## The path through one predecessor -/

/-- The merge's names. -/
abbrev mNames (preds : List State) (width fresh0 : Nat) : Array Nat := (mergeSlots preds width fresh0).2.1

/-- Each predecessor's renaming at the merge. -/
abbrev mRen (preds : List State) (width fresh0 : Nat) : List (Std.HashMap Nat (List Nat)) :=
  (mergeSlots preds width fresh0).2.2.1

/-- The merge's valuation on the path through a predecessor valued by `η`. -/
noncomputable abbrev mVal (preds : List State) (width fresh0 : Nat) (ρ η : Env) : Env :=
  mergeVal ρ η (mNames preds width fresh0).toList fresh0

/-- **The path through predecessor `p`** of a merge of width `width` whose
fresh names start at `fresh0`: every predecessor has `width` slots, its
slots' and facts' names below `fresh0` and a well-formed store; `p`'s slots
hold their names' values under `η` and its facts hold at `η` and `h`. -/
structure OnPath (preds : List State) (width fresh0 p : Nat) (ρ η : Env) (h : Heap) : Prop where
  hp : p < preds.length
  len : ∀ q ∈ preds, q.names.length = width
  bel : ∀ q ∈ preds, ∀ x ∈ q.names, x < fresh0
  facts : ∀ q ∈ preds, ∀ a ∈ storeAll q.store, ∀ x ∈ a.names, x < fresh0
  wf : ∀ q ∈ preds, StoreWF q.store
  slots : SlotsNamed (preds[p]'hp).names ρ η
  store : StoreOk (preds[p]'hp).store η h

section Path
variable {preds : List State} {width fresh0 p : Nat} {ρ η : Env} {h : Heap}

theorem OnPath.ren_len (P : OnPath preds width fresh0 p ρ η h) : p < (mRen preds width fresh0).length := by
  rw [(mergeSlots_inv preds width fresh0).len]; exact P.hp

/-- `p`'s facts hold at the merge's valuation: their names are below the
counter. -/
theorem OnPath.pred_ok (P : OnPath preds width fresh0 p ρ η h) :
    StoreOk (preds[p]'P.hp).store (mVal preds width fresh0 ρ η) h := by
  intro a ha
  refine (atomHolds_congr fun x hx => ?_).mp (P.store a ha)
  exact (mergeVal_below (P.facts _ (List.getElem_mem P.hp) a ha x hx)).symm

theorem OnPath.rename (P : OnPath preds width fresh0 p ρ η h) :
    ∀ x φs, ((mRen preds width fresh0)[p]'P.ren_len)[x]? = some φs → ∀ φ ∈ φs,
      mVal preds width fresh0 ρ η φ = η x := by
  intro x φs hm φ hφ
  refine mergeVal_rename P.hp P.len P.bel P.slots P.ren_len ?_
  rw [Std.HashMap.getD_eq_getD_getElem?, hm]; exact hφ

theorem OnPath.key (P : OnPath preds width fresh0 p ρ η h) :
    ∀ x φs, ((mRen preds width fresh0)[p]'P.ren_len)[x]? = some φs → mVal preds width fresh0 ρ η x = η x :=
  fun _ _ hm => mergeVal_below (rename_key_below P.hp P.len P.bel P.ren_len hm)

theorem OnPath.slotsNamed (P : OnPath preds width fresh0 p ρ η h) :
    SlotsNamed (mNames preds width fresh0).toList ρ (mVal preds width fresh0 ρ η) :=
  mergeVal_slots P.hp P.len P.bel P.slots

theorem zip_get {α β : Type} {l : List α} {l' : List β} {p : Nat} (hp : p < l.length) (hp' : p < l'.length) :
    (l.zip l')[p]? = some (l[p], l'[p]) := by
  simp [List.getElem?_zip_eq_some, List.getElem?_eq_getElem hp, List.getElem?_eq_getElem hp']

/-- **`p`'s restatements hold** at the merge's valuation: its facts about
the names it renames, restated at their fresh names, and its equalities. -/
theorem OnPath.variants_ok (P : OnPath preds width fresh0 p ρ η h) {v : Std.HashSet Atom}
    (hv : (mergeVariants preds (mNames preds width fresh0) (mRen preds width fresh0))[p]? = some v) :
    ∀ a ∈ v, AtomHolds a (mVal preds width fresh0 ρ η) h := by
  unfold mergeVariants at hv
  rw [List.getElem?_map, zip_get P.hp P.ren_len] at hv
  simp only [Option.map_some, Option.some.injEq] at hv
  subst hv
  have hsame : ∀ x φs, ((mRen preds width fresh0)[p]'P.ren_len)[x]? = some φs → ∀ φ ∈ φs,
      mVal preds width fresh0 ρ η φ = mVal preds width fresh0 ρ η x :=
    fun x φs hm φ hφ => by rw [P.rename x φs hm φ hφ, P.key x φs hm]
  intro a ha
  rcases Std.HashSet.mem_insertMany_list.mp ha with ha | ha
  · revert ha
    refine foldl_inv (fun (acc : Std.HashSet Atom) => ∀ a ∈ acc, AtomHolds a (mVal preds width fresh0 ρ η) h) _ _ _
      (fun a ha => by simp at ha) ?_ a
    intro b hb acc hacc a ha
    rcases Std.HashSet.mem_insertMany_list.mp ha with ha | ha
    · exact hacc a ha
    · have hbs : b ∈ storeAll (preds[p]'P.hp).store := by
        rw [Std.HashMap.fold_eq_foldl_toList] at hb
        revert hb
        refine foldl_inv (fun (acc : List Atom) => b ∈ acc → b ∈ storeAll (preds[p]'P.hp).store) _ _ _
          (fun h => by cases h) ?_
        intro ⟨x, _⟩ _ acc hacc hb
        rcases List.mem_append.mp hb with hb | hb
        · exact about_storeAll hb
        · exact hacc hb
      exact renameEach_holds hsame (P.pred_ok b hbs) (List.contains_iff_mem.mp ha)
  · exact mergeEqual_holds P.store P.rename P.key a (List.contains_iff_mem.mp ha)

end Path

/-! ## The met store -/

/-- **The restated facts every predecessor states**, added (`mergeMeet`),
keep a property of stores closed under adding a fact of predecessor `p`'s
restatements. -/
theorem mergeMeet_inv (Pr : Store → Prop) (Q : Atom → Prop) (hadd : ∀ s a, Pr s → Q a → Pr (s.add a))
    {met : Store} {variants : List (Std.HashSet Atom)} {p : Nat} (hp : p < variants.length)
    (hv : ∀ a ∈ variants[p], Q a) (h0 : Pr met) : Pr (mergeMeet met variants) := by
  unfold mergeMeet SinglePass.timedKind
  simp only [Std.HashSet.fold_eq_foldl_toList]
  refine foldl_inv Pr _ _ _ h0 fun a ha acc hacc => ?_
  split
  · rename_i hall
    refine hadd _ _ hacc (hv a ?_)
    cases variants with
    | nil => exact absurd hp (Nat.not_lt_zero _)
    | cons v0 vs =>
      cases p with
      | zero => exact Std.HashSet.mem_toList.mp ha
      | succ j =>
        have hj : j < vs.length := by simpa using hp
        exact Std.HashSet.contains_iff_mem.mp (List.all_eq_true.mp hall _ (List.getElem_mem hj))
  · exact hacc

theorem mergeVariants_length (preds : List State) (names : Array Nat) (renames : List (Std.HashMap Nat (List Nat)))
    (hl : renames.length = preds.length) : (mergeVariants preds names renames).length = preds.length := by
  simp [mergeVariants, hl]

theorem mergeDiffs_length (preds : List State) (renames : List (Std.HashMap Nat (List Nat)))
    (variants : List (Std.HashSet Atom)) (met0 : Store) (hl : renames.length = preds.length)
    (hv : variants.length = preds.length) : (mergeDiffs preds renames variants met0).length = preds.length := by
  simp [mergeDiffs, hl, hv]

/-- **The met store is well-formed** where every predecessor's is. -/
theorem mergeMet0_wf {preds : List State} {width fresh0 : Nat} (hwf : ∀ q ∈ preds, StoreWF q.store) :
    StoreWF (mergeMet0 preds (mNames preds width fresh0) (mRen preds width fresh0)) := by
  unfold mergeMet0
  refine drop_wf ?_ _
  cases preds with
  | nil =>
    unfold mergeMeet SinglePass.timedKind
    simp only [Std.HashSet.fold_eq_foldl_toList]
    exact foldl_inv StoreWF _ _ _ (mergeCommon_live hwf).1 fun a _ acc hacc => by
      split
      · exact add_wf hacc _
      · exact hacc
  | cons q qs =>
    exact mergeMeet_inv StoreWF (fun _ => True) (fun s a hs _ => add_wf hs a)
      (p := 0) (by rw [mergeVariants_length _ _ _ (mergeSlots_inv _ width fresh0).len]; simp)
      (fun _ _ => trivial) (mergeCommon_live hwf).1

section Path
variable {preds : List State} {width fresh0 p : Nat} {ρ η : Env} {h : Heap}

theorem OnPath.variants_len (P : OnPath preds width fresh0 p ρ η h) :
    p < (mergeVariants preds (mNames preds width fresh0) (mRen preds width fresh0)).length := by
  rw [mergeVariants_length _ _ _ (mergeSlots_inv _ width fresh0).len]; exact P.hp

/-- **The met store holds** on the path through `p` at the merge's
valuation: the common facts are `p`'s, the restated facts every predecessor
states are `p`'s restatements, and forgetting names keeps facts holding
(`drop_holds`). -/
theorem OnPath.met0_ok (P : OnPath preds width fresh0 p ρ η h) :
    StoreOk (mergeMet0 preds (mNames preds width fresh0) (mRen preds width fresh0)) (mVal preds width fresh0 ρ η) h := by
  unfold mergeMet0
  refine drop_holds (mergeMeet_inv (fun s => StoreOk s (mVal preds width fresh0 ρ η) h)
    (fun a => AtomHolds a (mVal preds width fresh0 ρ η) h) (fun _ _ hs ha => add_ok hs ha) P.variants_len
    (P.variants_ok (List.getElem?_eq_getElem P.variants_len)) ?_)
  obtain ⟨w, hsub⟩ := mergeCommon_live P.wf
  intro a ha
  exact P.pred_ok a (live_storeAll (hsub p P.hp a (storeAll_live w ha)))

/-- **What `p` states beyond the met store holds** at the merge's
valuation: its facts the met store lacks and its restatements. -/
theorem OnPath.diffs_ok (P : OnPath preds width fresh0 p ρ η h) {met0 : Store} {d : List Atom}
    (hd : (mergeDiffs preds (mRen preds width fresh0)
      (mergeVariants preds (mNames preds width fresh0) (mRen preds width fresh0)) met0)[p]? = some d) :
    ∀ a ∈ d, AtomHolds a (mVal preds width fresh0 ρ η) h := by
  unfold mergeDiffs at hd
  rw [List.getElem?_map, zip_get (l := preds.zip _) (by simp only [List.length_zip]; exact Nat.lt_min.mpr ⟨P.hp, P.ren_len⟩) P.variants_len,
    List.getElem_zip] at hd
  simp only [Option.map_some, Option.some.injEq] at hd
  subst hd
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · have ha := (List.mem_filter.mp ha).1
    simp only [SinglePass.timedKind, Store.diff] at ha
    exact P.pred_ok a (toList_storeAll (List.mem_filter.mp ha).1)
  · rw [Std.HashSet.fold_eq_foldl_toList] at ha
    revert ha
    refine foldl_inv (fun (acc : List Atom) => a ∈ acc → AtomHolds a (mVal preds width fresh0 ρ η) h) _ _ _
      (fun h => by cases h) ?_
    intro b hb acc hacc ha
    split at ha
    · exact hacc ha
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact P.variants_ok (List.getElem?_eq_getElem P.variants_len) a (Std.HashSet.mem_toList.mp hb)
      · exact hacc ha

end Path

end Verification.TolerantFrames
