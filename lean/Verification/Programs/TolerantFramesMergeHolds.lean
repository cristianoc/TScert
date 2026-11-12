import Verification.Programs.TolerantFramesMergeJoin

/-! # Tolerant frames: the merge's state holds

On the path into a merge through predecessor `p`, whose state holds at the
valuation `η`, each part of the merged state (`SinglePass.mergeState`) holds
at the merge's valuation `mVal`: the weakest bounds (`OnPath.bounds_ok`),
the guarded facts where `GuardedHolds` (`OnPath.guarded_ok`), the merge's
implications where the edges' joined implications hold (`mergeImplies_ok`)
and the fresh names (`OnPath.fresh_ok`); the merge theorem composing them is
`mergeState_holdsAt_checked`. The merged store is well-formed and its names
and fresh names are below the merge's next fresh name (`mergeState_wf`). -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations
open Verification.SinglePass (Atom Store State)
open ProgramTyping PositiveGraphs

section Holds
variable {ι : Type} [DecidableEq ι]

/-- The state's meaning at a given valuation `η`: `StateHolds` is its
existential (`stateHolds_iff`). -/
def StateHoldsAt (G : NormalGraph ι) (st : State) (implies : List (PromiseCalls.Implication ι)) (start : List Nat)
    (entry : Env) (η : Env) : Assertion := fun ρ m s =>
  SlotsNamed st.names ρ η ∧ Named (storeAll st.store) η ρ m s ∧
    PromiseCalls.ImpliesOk G implies η s.n s.W ∧ (∀ x ∈ st.fresh, FreshAt m (η x)) ∧
    ∀ q x, start[q]? = some x → η x = entry q

omit [DecidableEq ι] in
theorem stateHolds_iff {G : NormalGraph ι} {st : State} {implies : List (PromiseCalls.Implication ι)}
    {start : List Nat} {entry ρ : Env} {m : Nat} {s : IndexedHeap} :
    StateHolds G st implies start entry ρ m s ↔ ∃ η, StateHoldsAt G st implies start entry η ρ m s := Iff.rfl

end Holds

/-- Every name of a state's slots, facts and fresh names is below `next`
(`StateWF.below`). -/
def StateBelow (st : State) (next : Nat) : Prop :=
  (∀ x ∈ st.names, x < next) ∧ (∀ a ∈ storeAll st.store, ∀ x ∈ a.names, x < next) ∧ ∀ x ∈ st.fresh, x < next

/-- **(Named hypothesis) The guarded join's facts hold on the path**: each
fact `mergeGuarded` keeps, at slots, holds at the slot environment. Its
tagged candidates are checked against every view (`indicesCheckWith`); its
joined facts are `CertificateProducer.joinGuarded`'s, a search function. -/
def GuardedHolds (preds : List State) (width fresh0 : Nat) (ρ : Env) (h : Heap) : Prop :=
  let variants := mergeVariants preds (mNames preds width fresh0) (mRen preds width fresh0)
  let met0 := mergeMet0 preds (mNames preds width fresh0) (mRen preds width fresh0)
  let diffs := mergeDiffs preds (mRen preds width fresh0) variants met0
  let views := mergeViews (mNames preds width fresh0).toList diffs met0
  ∀ x ∈ mergeGuarded width (mNames preds width fresh0).toList met0 diffs views, HeapKnowledge.IndexHolds [x] ρ h

section Path
variable {preds : List State} {width fresh0 p : Nat} {ρ η : Env} {h : Heap}

theorem OnPath.diffs_get (P : OnPath preds width fresh0 p ρ η h) :
    let diffs := mergeDiffs preds (mRen preds width fresh0)
      (mergeVariants preds (mNames preds width fresh0) (mRen preds width fresh0))
      (mergeMet0 preds (mNames preds width fresh0) (mRen preds width fresh0))
    ∃ hd : p < diffs.length, ∀ a ∈ diffs[p], AtomHolds a (mVal preds width fresh0 ρ η) h := by
  intro diffs
  have hl : p < diffs.length := by
    rw [mergeDiffs_length _ _ _ _ (mergeSlots_inv _ width fresh0).len
      (mergeVariants_length _ _ _ (mergeSlots_inv _ width fresh0).len)]
    exact P.hp
  exact ⟨hl, P.diffs_ok (List.getElem?_eq_getElem hl)⟩

/-- **The weakest bounds hold** on the path. -/
theorem OnPath.bounds_ok (P : OnPath preds width fresh0 p ρ η h) {met : Store}
    (hm : StoreOk met (mVal preds width fresh0 ρ η) h) :
    StoreOk (mergeBounds (mergeDiffs preds (mRen preds width fresh0)
      (mergeVariants preds (mNames preds width fresh0) (mRen preds width fresh0))
      (mergeMet0 preds (mNames preds width fresh0) (mRen preds width fresh0))) met) (mVal preds width fresh0 ρ η) h := by
  obtain ⟨hl, hd⟩ := P.diffs_get
  refine mergeBounds_inv (fun s => StoreOk s (mVal preds width fresh0 ρ η) h)
    (fun a => AtomHolds a (mVal preds width fresh0 ρ η) h) (fun _ _ hs ha => add_ok hs ha) ?_ hm
  intro key w hall
  obtain ⟨d', hd', hle⟩ := hall _ (List.mem_map.mpr ⟨_, List.getElem_mem hl, rfl⟩)
  obtain ⟨F0, hF0, hn⟩ := boundsOf_get hd'
  have := linear_weaken (hd _ hF0) hle
  rw [hn] at this; exact this

theorem OnPath.view_ok (P : OnPath preds width fresh0 p ρ η h) :
    let met0 := mergeMet0 preds (mNames preds width fresh0) (mRen preds width fresh0)
    let diffs := mergeDiffs preds (mRen preds width fresh0)
      (mergeVariants preds (mNames preds width fresh0) (mRen preds width fresh0)) met0
    ∃ v ∈ mergeViews (mNames preds width fresh0).toList diffs met0,
      StoreOk v.store (mVal preds width fresh0 ρ η) h ∧
      ∀ (f : State → Bool), (mergeViews (mNames preds width fresh0).toList diffs met0).all f = true → f v = true := by
  intro met0 diffs
  obtain ⟨hl, hd⟩ := P.diffs_get
  refine ⟨{ names := (mNames preds width fresh0).toList, store := diffs[p].foldl Store.add met0 }, ?_, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨_, List.getElem_mem hl, rfl⟩
  · show StoreOk (diffs[p].foldl Store.add met0) _ h
    exact foldl_inv (fun s => StoreOk s (mVal preds width fresh0 ρ η) h) _ _ _ P.met0_ok
      fun a ha s hs => add_ok hs (hd a ha)
  · intro f hall
    exact List.all_eq_true.mp hall _ (List.mem_map.mpr ⟨_, List.getElem_mem hl, rfl⟩)

/-- **The guarded facts hold** on the path, renamed to the merge's names,
with `GuardedHolds`. -/
theorem OnPath.guarded_ok (P : OnPath preds width fresh0 p ρ η h) (hguard : GuardedHolds preds width fresh0 ρ h)
    {met : Store} (hm : StoreOk met (mVal preds width fresh0 ρ η) h) :
    let met0 := mergeMet0 preds (mNames preds width fresh0) (mRen preds width fresh0)
    let diffs := mergeDiffs preds (mRen preds width fresh0)
      (mergeVariants preds (mNames preds width fresh0) (mRen preds width fresh0)) met0
    StoreOk (mergeAddGuarded (mNames preds width fresh0).toList (mergeGuarded width (mNames preds width fresh0).toList
      met0 diffs (mergeViews (mNames preds width fresh0).toList diffs met0)) met) (mVal preds width fresh0 ρ η) h := by
  intro met0 diffs
  refine mergeAddGuarded_inv (fun s => StoreOk s (mVal preds width fresh0 ρ η) h)
    (fun a => AtomHolds a (mVal preds width fresh0 ρ η) h) (fun _ _ hs ha => add_ok hs ha) ?_ hm
  intro x hx a hr
  exact atomHolds_rename (fun i y hy => (P.slotsNamed i y hy).symm) hr (hguard x hx)

/-- **The merged fresh names hold fresh stores** on the path: each is a
fresh name of `p` or a fresh name `p` renames one to. -/
theorem OnPath.fresh_ok (P : OnPath preds width fresh0 p ρ η h) {mark : Nat}
    (hfb : ∀ x ∈ (preds[p]'P.hp).fresh, x < fresh0) (hf : ∀ x ∈ (preds[p]'P.hp).fresh, FreshAt mark (η x)) :
    ∀ x ∈ mergeFresh preds (mRen preds width fresh0), FreshAt mark (mVal preds width fresh0 ρ η x) := by
  intro x hx
  have hmine : x ∈ (preds[p]'P.hp).fresh.flatMap fun y => y :: ((mRen preds width fresh0)[p]'P.ren_len).getD y [] := by
    unfold mergeFresh at hx
    have hget : ((preds.zip (mRen preds width fresh0)).map fun ((st : State), (m : Std.HashMap Nat (List Nat))) =>
        st.fresh.flatMap fun x => x :: m.getD x [])[p]? =
        some ((preds[p]'P.hp).fresh.flatMap fun y => y :: ((mRen preds width fresh0)[p]'P.ren_len).getD y []) := by
      rw [List.getElem?_map, zip_get P.hp P.ren_len]; rfl
    revert hget hx
    generalize ((preds.zip (mRen preds width fresh0)).map fun ((st : State), (m : Std.HashMap Nat (List Nat))) =>
        st.fresh.flatMap fun x => x :: m.getD x []) = lists
    intro hx hget
    cases lists with
    | nil => simp at hget
    | cons f0 fs =>
      obtain ⟨hx0, hall⟩ := List.mem_filter.mp hx
      cases p with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hget; rw [← hget]; exact hx0
      | succ j =>
        simp only [List.getElem?_cons_succ] at hget
        have hj := (List.getElem?_eq_some_iff.mp hget)
        have := List.all_eq_true.mp hall _ (List.getElem_mem hj.1)
        rw [hj.2] at this
        exact List.contains_iff_mem.mp this
  obtain ⟨y, hy, hxy⟩ := List.mem_flatMap.mp hmine
  rcases List.mem_cons.mp hxy with rfl | hxy
  · rw [show mVal preds width fresh0 ρ η x = η x from mergeVal_below (hfb x hy)]; exact hf x hy
  · rw [show mVal preds width fresh0 ρ η x = η y from mergeVal_rename P.hp P.len P.bel P.slots P.ren_len hxy]
    exact hf y hy

end Path

section Implies
variable {ι : Type} [DecidableEq ι] [Hashable ι]

/-- The edges' implications joined at slots
(`CertificateProducer.meetImplications`) that every incoming edge
establishes (`PromiseCalls.impliesCheck`): those the merge keeps. -/
def joinedChecked (G : NormalGraph ι) (context : List (Ty ι))
    (edgesIn : List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)) :
    List (PromiseCalls.Implication ι) :=
  (CertificateProducer.meetImplications G edgesIn context.length context).filter fun x =>
    edgesIn.all fun (Γ, xs, m) => PromiseCalls.impliesCheck G Γ xs m [x]

/-- **The merge's implications hold** at its valuation where the joined
implications the merge keeps (`joinedChecked`) hold at the slot
environment: each is renamed by the merge's names. -/
theorem mergeImplies_ok {G : NormalGraph ι} {context : List (Ty ι)}
    {edgesIn : List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)} {names : List Nat}
    {ρ η : Env} {n : Nat} {W : WorldT n} (hs : SlotsNamed names ρ η)
    (hI : PromiseCalls.ImpliesOk G (joinedChecked G context edgesIn) ρ n W) :
    PromiseCalls.ImpliesOk G (mergeImplies G context edgesIn names) η n W := by
  have key : ∀ {α : Type} (b : Bool) (L : List α) (x : α), x ∈ (if !b then [] else L) → x ∈ L := by
    intro α b L x h; cases b <;> simp_all
  unfold mergeImplies
  intro x hx
  replace hx := key _ _ _ hx
  · obtain ⟨y, hy, hyx⟩ := List.mem_filterMap.mp (keepFirst_sub hx)
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hyx
    obtain ⟨a, ha, b, hb, rfl⟩ := hyx
    intro htest
    rw [← hs _ _ hb]
    exact hI y (by simpa [SinglePass.timedKind, joinedChecked] using hy) (by rw [hs _ _ ha]; exact htest)

end Implies

section Merge
variable {ι : Type} [DecidableEq ι] [Hashable ι]

/-- A name of the merge's first predecessor's fresh names or renames. -/
theorem mergeFresh_head {q : State} {qs : List State} {r : Std.HashMap Nat (List Nat)}
    {rs : List (Std.HashMap Nat (List Nat))} {x : Nat} (hx : x ∈ mergeFresh (q :: qs) (r :: rs)) :
    ∃ y ∈ q.fresh, x = y ∨ x ∈ r.getD y [] := by
  unfold mergeFresh at hx
  simp only [List.zip_cons_cons, List.map_cons] at hx
  obtain ⟨y, hy, hxy⟩ := List.mem_flatMap.mp (List.mem_filter.mp hx).1
  exact ⟨y, hy, List.mem_cons.mp hxy⟩

/-- **The merged state is well-formed**: its store well-formed, the next
fresh name at least `fresh`, its names and fresh names below the next fresh
name. -/
theorem mergeState_wf {G : NormalGraph ι} {context : List (Ty ι)} {preds : List State}
    {edgesIn : List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)} {fresh : Nat}
    (hne : preds ≠ []) (hlen : ∀ q ∈ preds, q.names.length = context.length) (hwf : ∀ q ∈ preds, StoreWF q.store)
    (hbel : ∀ q ∈ preds, StateBelow q fresh) :
    StoreWF (SinglePass.mergeState G context preds edgesIn fresh).state.store ∧
      fresh ≤ (SinglePass.mergeState G context preds edgesIn fresh).fresh ∧
      (∀ x ∈ (SinglePass.mergeState G context preds edgesIn fresh).state.names,
        x < (SinglePass.mergeState G context preds edgesIn fresh).fresh) ∧
      ∀ x ∈ (SinglePass.mergeState G context preds edgesIn fresh).state.fresh,
        x < (SinglePass.mergeState G context preds edgesIn fresh).fresh := by
  rw [mergeState_state, mergeState_fresh]
  have I := mergeSlots_inv preds context.length fresh
  have hw : (mergeSlots preds context.length fresh).2.1.size = context.length := I.size
  obtain ⟨q, qs, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hq := List.mem_cons_self (a := q) (l := qs)
  have hnames : ∀ x ∈ (mergeSlots (q :: qs) context.length fresh).2.1.toList,
      x < (mergeSlots (q :: qs) context.length fresh).1 := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have hj' : j < (mergeSlots (q :: qs) context.length fresh).2.1.size := by simpa using hj
    simp only [Array.getElem_toList]
    rcases I.slot j hj' with h1 | ⟨-, h2, -⟩
    · rw [← h1 q hq]
      have := pred_below (p := 0) (by simp) hlen (fun q hq => (hbel q hq).1) (hw ▸ hj')
      have := I.ge; simp at *; omega
    · exact h2
  refine ⟨?_, I.ge, hnames, fun x hx => ?_⟩
  · show StoreWF (mergeStore _ _ _ _)
    unfold mergeStore
    exact mergeAddGuarded_inv StoreWF (fun _ => True) (fun s a hs _ => add_wf hs a) (fun _ _ _ _ => trivial)
      (mergeEntailed_inv StoreWF (fun _ => True) (fun s a hs _ => add_wf hs a) (fun _ _ _ _ _ _ _ => trivial)
        (mergeBounds_inv StoreWF (fun _ => True) (fun s a hs _ => add_wf hs a) (fun _ _ _ => trivial)
          (mergeMet0_wf hwf)))
  · have hrl : 0 < (mergeSlots (q :: qs) context.length fresh).2.2.1.length := by rw [I.len]; simp
    revert hx
    show x ∈ mergeFresh (q :: qs) (mergeSlots (q :: qs) context.length fresh).2.2.1 → _
    have hR := I.ren 0 hrl
    revert hR
    generalize (mergeSlots (q :: qs) context.length fresh).2.2.1 = R at hrl ⊢
    intro hR hx
    obtain ⟨r, rs, rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hrl)
    obtain ⟨y, hy, rfl | hxy⟩ := mergeFresh_head hx
    · have := (hbel q hq).2.2 _ hy; have := I.ge; omega
    · obtain ⟨j, hj, h1, -, -⟩ := hR y _ hxy
      rw [← h1]
      exact hnames _ (by simp)

end Merge

end Verification.TolerantFrames
