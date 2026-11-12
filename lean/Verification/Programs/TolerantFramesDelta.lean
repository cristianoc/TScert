import Verification.Programs.TolerantFramesState

/-! # Tolerant frames: a step's delta on the named state

After a step, the pass folds the rule's output back into its store
(`SinglePass.applyDelta`): the handed facts the output lost are removed, the
output's facts not among the handed ones added, renamed from the pushed slots
to names, and a linear fact over a read's name restated over the read's path.
This module proves that, where the store's facts hold after the step at the
valuation naming the result, the output holds at the pushed slots and the
renaming sends each slot to a name holding its value, every fact of the
resulting store holds; and that the state after a preserving step or a copy
holds (`StateHolds`) at the pushed environment. -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations
open Verification.SinglePass (Atom Store State)

/-! ## `applyDelta` in three loops -/

/-- A handed fact's image over the pushed slots. -/
def deltaImage (shift : Bool) (a : Atom) : Atom := if shift then (a.rename fun i => some (i + 1)).getD a else a

/-- `applyDelta`'s first loop: each handed fact whose image the output lost
removed. -/
def deltaRemove (s : Store) (pairs : List (Atom × Atom)) (out : HeapKnowledge.Knowledge) (shift : Bool) : Store :=
  Id.run do
  let outSet : Std.HashSet Atom := (SinglePass.atomsOf out).foldl (·.insert ·) {}
  let mut s := s
  for (a, b) in pairs do
    if !outSet.contains (deltaImage shift b) then s := s.remove a
  return s

/-- `applyDelta`'s second loop: each output fact not among the images added,
renamed by `back`; and the index facts added. -/
def deltaAdd (s : Store) (pairs : List (Atom × Atom)) (out : HeapKnowledge.Knowledge) (shift : Bool)
    (back : Nat → Option Nat) : Store × List HeapKnowledge.IndexAtom := Id.run do
  let inSet : Std.HashSet Atom := pairs.foldl (fun acc (_, b) => acc.insert (deltaImage shift b)) {}
  let mut s := s
  let mut added : List HeapKnowledge.IndexAtom := []
  for o in SinglePass.atomsOf out do
    if !inSet.contains o then
      if let some a := o.rename back then
        let trivial := match a with | .link g => g.alias && g.cell == g.value | _ => false
        if !trivial then s := s.add a
        if let .index x := a then added := x :: added
  return (s, added)

/-- `applyDelta`'s third loop: each added linear fact over a read's name also
over the read's path. -/
def deltaRestate (s : Store) (added : List HeapKnowledge.IndexAtom) : Store := Id.run do
  let mut s := s
  for x in added do
    for v in x.fact.slots do
      let reads := (s.about v).filterMap fun b => match b with
        | .link g => if !g.alias && g.value == v then some g else none
        | _ => none
      if !reads.isEmpty then
        for y in HeapKnowledge.restateReads reads (· == v) [x] do s := s.add (.index y)
  return s

/-- `applyDelta` is its three loops in order. -/
theorem applyDelta_eq (s : Store) (pairs : List (Atom × Atom)) (out : HeapKnowledge.Knowledge) (shift : Bool)
    (back : Nat → Option Nat) : SinglePass.applyDelta s pairs out shift back =
      deltaRestate (deltaAdd (deltaRemove s pairs out shift) pairs out shift back).1
        (deltaAdd (deltaRemove s pairs out shift) pairs out shift back).2 := rfl

/-- `forIn_inv` before a continuation. -/
theorem forIn_inv_bind {α β γ : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β)) (P : β → Prop)
    (k : β → Id γ) (R : γ → Prop) (h0 : P init) (hf : ∀ a ∈ l, ∀ b, P b → P (f a b).value)
    (hk : ∀ b, P b → R (k b)) : R (forIn l init f >>= k) :=
  hk _ (forIn_inv l init f P h0 hf)

/-! ## Each loop keeps the store's facts holding -/

/-- **The removal loop keeps only facts the store held.** -/
theorem deltaRemove_sub (L : StoreLaws) {s : Store} {pairs : List (Atom × Atom)} {out : HeapKnowledge.Knowledge}
    {shift : Bool} : ∀ x ∈ storeAll (deltaRemove s pairs out shift), x ∈ storeAll s := by
  unfold deltaRemove
  simp only [Id.run]
  refine forIn_inv_bind (R := fun (t : Store) => ∀ x ∈ storeAll t, x ∈ storeAll s) pairs s _
    (fun t => ∀ x ∈ storeAll t, x ∈ storeAll s) _ (fun _ h => h) ?_ (fun _ h => h)
  intro ab _ t ht
  split
  · intro x hx
    apply ht
    unfold Store.remove at hx
    dsimp only at hx
    split at hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ (L.keys_erase _ _ _ hx)
      · refine vals_foldl (fun x => x ∈ storeAll t) _ (fun m n hm y hy => ?_) _ _
          (fun y hy => List.mem_append_right _ hy) x hx
        rcases L.vals_insert _ _ _ _ hy with hy | hy
        · exact hm y (L.findD_vals _ _ _ (List.mem_of_mem_erase hy))
        · exact hm y hy
    · exact hx
  · exact ht

/-- The removal loop keeps the store's facts holding. -/
theorem deltaRemove_ok (L : StoreLaws) {s : Store} {pairs : List (Atom × Atom)} {out : HeapKnowledge.Knowledge}
    {shift : Bool} {η : Env} {h : Heap} (hs : StoreOk s η h) : StoreOk (deltaRemove s pairs out shift) η h :=
  fun x hx => hs x (deltaRemove_sub L x hx)

/-- **The addition loop adds holding facts**: each output fact holds at the
pushed slots `ρ'`, and `back` sends each slot to a name holding its value;
the index facts it records hold too. -/
theorem deltaAdd_ok (L : StoreLaws) {s : Store} {pairs : List (Atom × Atom)} {out : HeapKnowledge.Knowledge}
    {shift : Bool} {back : Nat → Option Nat} {η ρ' : Env} {h : Heap} (hs : StoreOk s η h)
    (hout : ∀ o ∈ SinglePass.atomsOf out, AtomHolds o ρ' h) (hback : ∀ i x, back i = some x → η x = ρ' i) :
    StoreOk (deltaAdd s pairs out shift back).1 η h ∧
      HeapKnowledge.IndexHolds (deltaAdd s pairs out shift back).2 η h := by
  unfold deltaAdd
  simp only [Id.run]
  refine forIn_inv_bind (R := fun (r : Store × List HeapKnowledge.IndexAtom) =>
      StoreOk r.1 η h ∧ HeapKnowledge.IndexHolds r.2 η h) (SinglePass.atomsOf out) (s, []) _
    (fun r => StoreOk r.1 η h ∧ HeapKnowledge.IndexHolds r.2 η h) _ ⟨hs, HeapKnowledge.indexHolds_nil η h⟩ ?_
    (fun _ h => h)
  intro o ho r ⟨hr, hi⟩
  have hidx : ∀ x a, AtomHolds a η h → a = .index x → HeapKnowledge.IndexHolds (x :: r.2) η h := by
    intro x a ha hax y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · subst hax; exact ha y (List.mem_singleton_self _)
    · exact hi y hy
  split
  · split
    · rename_i a hra
      have ha : AtomHolds a η h := atomHolds_rename (η := ρ') (ρ := η) (fun i x hx => hback i x hx) hra (hout o ho)
      have hadd := add_ok L hr ha
      cases a with
      | index x => exact ⟨hadd, hidx x _ ha rfl⟩
      | link g =>
        by_cases ht : (g.alias && g.cell == g.value) = true
        · simp only [ht, Bool.not_true, Bool.false_eq_true, if_false]
          exact ⟨hr, hi⟩
        · simp only [Bool.not_eq_true] at ht
          simp only [ht, Bool.not_false, if_true]
          exact ⟨hadd, hi⟩
      | cell _ | value _ | elem _ | sep _ => exact ⟨hadd, hi⟩
    · exact ⟨hr, hi⟩
  · exact ⟨hr, hi⟩

/-- **The restatement loop adds holding facts**: a linear fact restated over
a read's path (`HeapKnowledge.restateReads_holds`), the read links being the
store's. -/
theorem deltaRestate_ok (L : StoreLaws) {s : Store} {added : List HeapKnowledge.IndexAtom} {η : Env} {h : Heap}
    (hs : StoreOk s η h) (hadd : HeapKnowledge.IndexHolds added η h) : StoreOk (deltaRestate s added) η h := by
  unfold deltaRestate
  simp only [Id.run]
  refine forIn_inv_bind (R := fun (t : Store) => StoreOk t η h) added s _ (fun t => StoreOk t η h) _ hs ?_
    (fun _ h => h)
  intro x hx t ht
  show StoreOk (forIn (m := Id) x.fact.slots t _) η h
  refine forIn_inv _ _ _ (fun t => StoreOk t η h) ht ?_
  intro v _ u hu
  split
  · rename_i hne
    show StoreOk (forIn (m := Id) _ u _) η h
    have hl : HeapLinks.Holds ((u.about v).filterMap fun b => match b with
        | .link g => if (!g.alias && g.value == v) = true then some g else none
        | _ => none) η h := by
      intro g hg
      obtain ⟨b, hb, hbg⟩ := List.mem_filterMap.mp hg
      split at hbg
      · split at hbg
        · cases hbg; exact hu _ (about_storeAll L hb) g (List.mem_singleton_self _)
        · cases hbg
      · cases hbg
    have hx1 : HeapKnowledge.IndexHolds [x] η h := fun y hy hc => by
      simp only [List.mem_singleton] at hy; subst hy; exact hadd y hx hc
    have hy := HeapKnowledge.restateReads_holds (dropped := (· == v)) hl hx1
    refine forIn_inv _ _ _ (fun t => StoreOk t η h) hu ?_
    intro y hyl w hw
    exact add_ok L hw fun z hz hc => by simp only [List.mem_singleton] at hz; subst hz; exact hy z hyl hc
  · exact hu

/-- **A step's delta keeps the store's facts holding**: where the facts the
removal loop keeps hold at `η`, the output holds at the pushed slots `ρ'`
and `back` sends each slot to a name holding its value. -/
theorem applyDelta_ok (L : StoreLaws) {s : Store} {pairs : List (Atom × Atom)} {out : HeapKnowledge.Knowledge}
    {shift : Bool} {back : Nat → Option Nat} {η ρ' : Env} {h : Heap}
    (hrem : StoreOk (deltaRemove s pairs out shift) η h) (hout : HeapKnowledge.Holds out ρ' h)
    (hback : ∀ i x, back i = some x → η x = ρ' i) :
    StoreOk (SinglePass.applyDelta s pairs out shift back) η h := by
  rw [applyDelta_eq]
  obtain ⟨h1, h2⟩ := deltaAdd_ok (pairs := pairs) (shift := shift) L hrem (atomsOf_holds hout) hback
  exact deltaRestate_ok L h1 h2

/-- **(Preserving) A step's delta keeps the store's facts holding** where
every fact of the store holds after the step. -/
theorem applyDelta_preserving (L : StoreLaws) {s : Store} {pairs : List (Atom × Atom)}
    {out : HeapKnowledge.Knowledge} {shift : Bool} {back : Nat → Option Nat} {η ρ' : Env} {h : Heap}
    (hs : StoreOk s η h) (hout : HeapKnowledge.Holds out ρ' h) (hback : ∀ i x, back i = some x → η x = ρ' i) :
    StoreOk (SinglePass.applyDelta s pairs out shift back) η h :=
  applyDelta_ok L (deltaRemove_ok L hs) hout hback

/-! ## The renaming back to names -/

/-- The pass's renaming of a step's output from the pushed slots to names
(`SinglePass.lean` lines 1316–1317, 1331–1332): slot 0 the result's name, a
slot the table's inverse gives its name, else the slot's name. -/
def passBack (table : Std.HashMap Nat Nat) (names : List Nat) (result : Nat) : Nat → Option Nat :=
  let inverse : Std.HashMap Nat Nat := table.fold (fun acc nm s => acc.insert s nm) {}
  fun i => if i == 0 then some result else (inverse.get? (i - 1)).orElse fun _ => names[i - 1]?

theorem inverse_foldl {table : Std.HashMap Nat Nat} :
    ∀ (l : List (Nat × Nat)) (m : Std.HashMap Nat Nat), (∀ j x, m.get? j = some x → table.get? x = some j) →
      (∀ p ∈ l, table.get? p.1 = some p.2) →
      ∀ j x, (l.foldl (fun acc b => acc.insert b.2 b.1) m).get? j = some x → table.get? x = some j
  | [], _, hm, _ => hm
  | p :: l, m, hm, hl => inverse_foldl l _ (fun j x hj => by
      rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hj
      split at hj
      · rename_i he
        simp only [beq_iff_eq] at he
        cases hj; subst he; exact hl p (List.mem_cons_self ..)
      · exact hm j x (by rw [Std.HashMap.get?_eq_getElem?]; exact hj))
    fun q hq => hl q (List.mem_cons_of_mem _ hq)

/-- The table's inverse sends a slot to a name the table sends to it. -/
theorem inverse_get {table : Std.HashMap Nat Nat} {j x : Nat}
    (hj : (table.fold (fun acc nm s => acc.insert s nm) ({} : Std.HashMap Nat Nat)).get? j = some x) :
    table.get? x = some j := by
  rw [Std.HashMap.fold_eq_foldl_toList] at hj
  refine inverse_foldl _ _ (fun j x h => by simp at h) (fun p hp => ?_) j x hj
  rw [Std.HashMap.get?_eq_getElem?]
  exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hp

/-- **The pass's renaming sends each pushed slot to a name holding its
value**, the result's name holding `v` and the slots' names their values. -/
theorem passBack_ok {names : List Nat} {want : Std.HashSet Nat} {whole : Bool} {r : Nat} {v : Tm} {ρ η η' : Env}
    (hs : SlotsNamed names ρ η) (h0 : η' r = v) (hagree : ∀ x ∈ names, η' x = η x) :
    ∀ i x, passBack (SinglePass.slotTable names want whole) names r i = some x → η' x = push v ρ i := by
  intro i x hb
  simp only [passBack] at hb
  cases i with
  | zero => simp only [beq_self_eq_true, ite_true, Option.some.injEq] at hb; subst hb; exact h0
  | succ j =>
    simp only [Nat.add_one_ne_zero, beq_iff_eq, ite_false, Nat.add_sub_cancel] at hb
    have hn : names[j]? = some x := by
      cases hi : (Std.HashMap.fold (fun acc nm s => acc.insert s nm) ({} : Std.HashMap Nat Nat)
          (SinglePass.slotTable names want whole)).get? j with
      | none => rw [hi] at hb; simpa using hb
      | some y =>
        rw [hi] at hb
        simp only [Option.orElse_some, Option.some.injEq] at hb; subst hb
        exact slotTable_get (inverse_get hi)
    rw [hagree x (List.mem_of_getElem? hn)]
    exact (hs j x hn).symm

/-! ## The state after a step -/

section After
variable {ι : Type}
open ProgramTyping PositiveGraphs

/-- Implications hold along an admissible transition: each type's meaning is
admissible. -/
theorem impliesOk_admissible {G : NormalGraph ι} {I : List (PromiseCalls.Implication ι)} {η : Env}
    {s s' : IndexedHeap} (ha : Admissible s s') (hI : PromiseCalls.ImpliesOk G I η s.n s.W) :
    PromiseCalls.ImpliesOk G I η s'.n s'.W := by
  obtain ⟨hle, hx⟩ := ha
  intro y hy ht
  exact (ProgramTyping.meaning_adm G y.type).transfer (hI y hy ht) s'.n hle s'.W hx

/-- **The state after a step holds** at the pushed environment: given the
state's valuation `η` before the step, a valuation `η'` after it agreeing
with `η` on every name the slots, the fresh names, the start names and the
implications mention and naming the result `r` with the value `v`, where the
store's facts the removal loop keeps hold at `η'` after the step and the
rule's output at the pushed slots, the pushed state holds. -/
theorem stateHolds_after (L : StoreLaws) {G : NormalGraph ι} {st : State} {I : List (PromiseCalls.Implication ι)}
    {start : List Nat} {entry ρ η η' : Env} {m : Nat} {s s' : IndexedHeap} {r : Nat} {v : Tm}
    {pairs : List (Atom × Atom)} {out : HeapKnowledge.Knowledge} {want : Std.HashSet Nat} {whole : Bool}
    (hn : SlotsNamed st.names ρ η) (hI : PromiseCalls.ImpliesOk G I η s.n s.W) (hF : ∀ x ∈ st.fresh, FreshAt m (η x))
    (hst : ∀ q x, start[q]? = some x → η x = entry q) (ha : Admissible s s')
    (h0 : η' r = v) (hagree : ∀ x ∈ st.names, η' x = η x) (hfa : ∀ x ∈ st.fresh, η' x = η x)
    (hsa : ∀ (q x : Nat), start[q]? = some x → η' x = η x) (hia : ∀ y ∈ I, η' y.test = η y.test ∧ η' y.target = η y.target)
    (hrem : StoreOk (deltaRemove st.store pairs out true) η' s'.h) (hout : HeapKnowledge.Holds out (push v ρ) s'.h) :
    StateHolds G ⟨r :: st.names, SinglePass.applyDelta st.store pairs out true
        (passBack (SinglePass.slotTable st.names want whole) st.names r), st.fresh⟩
      I start entry (push v ρ) m s' := by
  refine ⟨η', fun i x hx => ?_, applyDelta_ok L hrem hout (passBack_ok hn h0 hagree), ?_, ?_, ?_⟩
  · cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hx; subst hx; exact h0.symm
    | succ j =>
      simp only [List.getElem?_cons_succ] at hx
      rw [hagree x (List.mem_of_getElem? hx)]; exact hn j x hx
  · intro y hy ht
    obtain ⟨e1, e2⟩ := hia y hy
    rw [e2]; rw [e1] at ht
    exact impliesOk_admissible ha hI y hy ht
  · intro x hx; rw [hfa x hx]; exact hF x hx
  · intro q x hq; rw [hsa q x hq]; exact hst q x hq

/-- The result's name is new: no slot, fresh name, start name or
implication mentions it. -/
def ResultFresh (st : State) (I : List (PromiseCalls.Implication ι)) (start : List Nat) (r : Nat) : Prop :=
  r ∉ st.names ∧ r ∉ st.fresh ∧ r ∉ start ∧ ∀ y ∈ I, y.test ≠ r ∧ y.target ≠ r

/-- **The state after a preserving step whose result takes a fresh name**
(line 1309): the frame's facts at `Env.set η r v` (`named_keep_box`,
`pass_preserving_frame_select`) and the rule's output at the pushed slots
give the pushed state. -/
theorem stateHolds_fresh_result (L : StoreLaws) {G : NormalGraph ι} {st : State}
    {I : List (PromiseCalls.Implication ι)} {start : List Nat} {entry ρ η : Env} {m : Nat} {s s' : IndexedHeap}
    {r : Nat} {v : Tm} {pairs : List (Atom × Atom)} {out : HeapKnowledge.Knowledge} {want : Std.HashSet Nat}
    {whole : Bool} (hn : SlotsNamed st.names ρ η) (hI : PromiseCalls.ImpliesOk G I η s.n s.W)
    (hF : ∀ x ∈ st.fresh, FreshAt m (η x)) (hst : ∀ q x, start[q]? = some x → η x = entry q)
    (ha : Admissible s s') (hr : ResultFresh st I start r)
    (hS : Named (storeAll st.store) (Env.set η r v) ρ m s') (hout : HeapKnowledge.Holds out (push v ρ) s'.h) :
    StateHolds G ⟨r :: st.names, SinglePass.applyDelta st.store pairs out true
        (passBack (SinglePass.slotTable st.names want whole) st.names r), st.fresh⟩
      I start entry (push v ρ) m s' := by
  obtain ⟨hrn, hrf, hrs, hri⟩ := hr
  have ne : ∀ {x}, x ≠ r → Env.set η r v x = η x := fun hx => by simp [Env.set, hx]
  exact stateHolds_after L hn hI hF hst ha (by simp [Env.set])
    (fun x hx => ne fun e => hrn (e ▸ hx)) (fun x hx => ne fun e => hrf (e ▸ hx))
    (fun q x hq => ne fun e => hrs (e ▸ List.mem_of_getElem? hq))
    (fun y hy => ⟨ne (hri y hy).1, ne (hri y hy).2⟩) (deltaRemove_ok L hS) hout

/-- **The state after a preserving read of a slot** (line 1307): the result
keeps the slot's name `x`, whose value `v` it is; every name keeps its value. -/
theorem stateHolds_reused_name (L : StoreLaws) {G : NormalGraph ι} {st : State}
    {I : List (PromiseCalls.Implication ι)} {start : List Nat} {entry ρ η : Env} {m : Nat} {s s' : IndexedHeap}
    {i x : Nat} {pairs : List (Atom × Atom)} {out : HeapKnowledge.Knowledge} {want : Std.HashSet Nat}
    {whole : Bool} (hn : SlotsNamed st.names ρ η) (hI : PromiseCalls.ImpliesOk G I η s.n s.W)
    (hF : ∀ x ∈ st.fresh, FreshAt m (η x)) (hst : ∀ q x, start[q]? = some x → η x = entry q)
    (ha : Admissible s s') (hx : st.names[i]? = some x)
    (hS : Named (storeAll st.store) η ρ m s') (hout : HeapKnowledge.Holds out (push (ρ i) ρ) s'.h) :
    StateHolds G ⟨x :: st.names, SinglePass.applyDelta st.store pairs out true
        (passBack (SinglePass.slotTable st.names want whole) st.names x), st.fresh⟩
      I start entry (push (ρ i) ρ) m s' :=
  stateHolds_after L hn hI hF hst ha (hn i x hx).symm (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ => ⟨rfl, rfl⟩) (deltaRemove_ok L hS) hout

/-- **A copy (lines 1203–1220) keeps the state**: the result is slot `i`'s
value, named as it; the store and the heap are unchanged. -/
theorem stateHolds_copy {G : NormalGraph ι} {st : State} {I : List (PromiseCalls.Implication ι)}
    {start : List Nat} {entry ρ : Env} {m : Nat} {s : IndexedHeap} {i x : Nat} (hx : st.names[i]? = some x)
    (hS : StateHolds G st I start entry ρ m s) :
    StateHolds G { st with names := x :: st.names } I start entry (push (ρ i) ρ) m s := by
  obtain ⟨η, hn, hst, hI, hF, hs⟩ := hS
  refine ⟨η, fun k y hy => ?_, hst, hI, hF, hs⟩
  cases k with
  | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hy; subst hy; exact hn i _ hx
  | succ j => simp only [List.getElem?_cons_succ] at hy; exact hn j y hy

end After

/-! ## The writing case -/

theorem mapM_mem_fwd {α β : Type} {g : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM g = some l' → ∀ a ∈ l, ∃ b ∈ l', g a = some b
  | [], _, _, a, ha => by cases ha
  | a :: l, l', h, x, hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨c, hc, cs, hcs, rfl⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨c, List.mem_cons_self .., hc⟩
    · obtain ⟨b, hb, hg⟩ := mapM_mem_fwd hcs x hx
      exact ⟨b, List.mem_cons_of_mem _ hb, hg⟩

/-- **A renamed fact holding gives the fact**: where `f` maps a name to a
slot, the slot holds the name's value. -/
theorem atomHolds_rename_rev {a b : Atom} {f : Nat → Option Nat} {η ρ : Env} {h : Heap}
    (hf : ∀ x i, f x = some i → ρ i = η x) (hr : a.rename f = some b) (hb : AtomHolds b ρ h) :
    AtomHolds a η h := by
  cases a with
  | cell x =>
    simp only [Atom.rename, Option.map_eq_some_iff] at hr
    obtain ⟨s, hs, rfl⟩ := hr
    intro g hg; simp only [List.mem_singleton] at hg; rw [hg]
    have := hb _ (List.mem_singleton_self _)
    simpa only [hf _ _ hs] using this
  | value x =>
    simp only [Atom.rename, Option.map_eq_some_iff] at hr
    obtain ⟨s, hs, rfl⟩ := hr
    intro g hg; simp only [List.mem_singleton] at hg; rw [hg]
    have := hb _ (List.mem_singleton_self _)
    simpa only [hf _ _ hs] using this
  | link g =>
    simp only [Atom.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hr
    obtain ⟨c, hc, v, hv, rfl⟩ := hr
    intro g' hg; simp only [List.mem_singleton] at hg; rw [hg]
    have := hb _ (List.mem_singleton_self _)
    simpa only [hf _ _ hc, hf _ _ hv] using this
  | elem e =>
    simp only [Atom.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hr
    obtain ⟨s, hs, c, hc, rfl⟩ := hr
    intro e' he hcond; simp only [List.mem_singleton] at he; subst he
    have := hb _ (List.mem_singleton_self _) (fun b' hb' => by
      cases hcb : e'.cond with
      | none =>
        rw [hcb] at hc
        have hc0 : c = none := (Option.some.inj hc).symm
        subst hc0; cases hb'
      | some b =>
        rw [hcb] at hc
        cases hfb : f b with
        | none => rw [Option.mapM_some, hfb] at hc; simp at hc
        | some b'' =>
          rw [Option.mapM_some, hfb] at hc
          have hc' : c = some b'' := (Option.some.inj hc).symm
          subst hc'
          simp only [Option.some.injEq] at hb'; subst hb'
          rw [hf _ _ hfb]; exact hcond b hcb)
    simpa only [hf _ _ hs] using this
  | index x =>
    simp only [Atom.rename, Option.map_eq_some_iff] at hr
    obtain ⟨y, hy, rfl⟩ := hr
    intro x' hx' hc
    simp only [List.mem_singleton] at hx'; subst hx'
    unfold HeapKnowledge.mapIndex at hy
    split at hy
    · rename_i F hF hcn
      cases hy
      exact (HeapKnowledge.IndexFact.holdsAt_mapM hF (fun s _ t ht => hf s t ht)).mp
        (hb _ (List.mem_singleton_self _) (fun b hb' => by simp only at hb'; rw [hcn] at hb'; cases hb'))
    · rename_i F c hF hcn
      simp only [Option.map_eq_some_iff] at hy
      obtain ⟨t, ht, rfl⟩ := hy
      refine (HeapKnowledge.IndexFact.holdsAt_mapM hF (fun s _ t ht => hf s t ht)).mp (hb _ (List.mem_singleton_self _) ?_)
      intro d hd
      cases hd
      rw [hf c _ ht]; exact hc c hcn
    · cases hy
  | sep x =>
    simp only [Atom.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hr
    obtain ⟨s, hs, ps, hps, rfl⟩ := hr
    intro p hp g hg
    obtain ⟨q, hq, hqp⟩ := mapM_mem_fwd hps p hp
    simp only [Option.map_eq_some_iff] at hqp
    obtain ⟨t, ht, rfl⟩ := hqp
    exact (hb _ hq g hg).congr (hf _ _ hs).symm (hf _ _ ht).symm

/-- **(Obstacle) A fact the removal loop removes leaves the store**: each
fact the loop keeps is the store's and none of the handed facts whose image
the output lost. `Store.remove` erases a fact from the live set and from its
names' lists (`List.erase`, the first copy); that it leaves the store needs
exact erasure laws of `Lean.PersistentHashMap`, lists without duplicates and
every listed fact under its own names only. A named hypothesis of the
writing case. -/
def RemovedLeave (s : Store) (pairs : List (Atom × Atom)) (out : HeapKnowledge.Knowledge) (shift : Bool) : Prop :=
  ∀ x ∈ storeAll (deltaRemove s pairs out shift),
    x ∈ storeAll s ∧ ∀ ab ∈ pairs, deltaImage shift ab.2 ∉ SinglePass.atomsOf out → x ≠ ab.1

/-- A total renaming renames every fact. -/
theorem rename_succ_total (b : Atom) : ∃ c, b.rename (fun i => some (i + 1)) = some c := by
  cases b with
  | index x =>
    obtain ⟨G, hG⟩ := HeapKnowledge.IndexFact.mapM_total (· + 1) x.fact
    have hG' : x.fact.mapM (fun i => some (i + 1)) = some G := hG
    simp only [Atom.rename, HeapKnowledge.mapIndex, hG']
    cases x.cond <;> simp
  | cell _ | value _ | link _ => exact ⟨_, rfl⟩
  | elem e => cases hc : e.cond <;> simp [Atom.rename, hc]
  | sep x =>
    have : ∀ (l : List (Nat × List PropKey)), ∃ l', l.mapM (fun (p, fs) => (some (p + 1)).map (·, fs)) = some l' := by
      intro l
      induction l with
      | nil => exact ⟨[], rfl⟩
      | cons p l ih => obtain ⟨l', hl⟩ := ih; exact ⟨_, by rw [List.mapM_cons, hl]; rfl⟩
    obtain ⟨l', hl⟩ := this x.partners
    exact ⟨_, by simp only [Atom.rename]; rw [hl]; rfl⟩

/-- **(Writing) A step's delta keeps the store's facts holding** where every
stored fact either holds after the step (the facts its effect keeps) or is
handed to the rule (a pair), and the removal loop removes the handed facts
whose image the output lost (`RemovedLeave`): a kept handed fact holds by the
output, read back through the pushed slots and the table. -/
theorem applyDelta_writing (L : StoreLaws) {s : Store} {pairs : List (Atom × Atom)}
    {out : HeapKnowledge.Knowledge} {back f : Nat → Option Nat} {η ρ : Env} {v : Tm} {h : Heap}
    (hgone : RemovedLeave s pairs out true)
    (hcov : ∀ x ∈ storeAll s, AtomHolds x η h ∨ ∃ b, (x, b) ∈ pairs ∧ x.rename f = some b)
    (hf : ∀ x i, f x = some i → ρ i = η x) (hout : HeapKnowledge.Holds out (push v ρ) h)
    (hback : ∀ i x, back i = some x → η x = push v ρ i) :
    StoreOk (SinglePass.applyDelta s pairs out true back) η h := by
  refine applyDelta_ok L (fun x hx => ?_) hout hback
  obtain ⟨hxs, hne⟩ := hgone x hx
  rcases hcov x hxs with hh | ⟨b, hp, hr⟩
  · exact hh
  · have himg : deltaImage true b ∈ SinglePass.atomsOf out :=
      Classical.byContradiction fun hn => hne (x, b) hp hn rfl
    obtain ⟨c, hc⟩ := rename_succ_total b
    have hci : deltaImage true b = c := by simp [deltaImage, hc]
    have hcb : AtomHolds c (push v ρ) h := hci ▸ atomsOf_holds hout _ himg
    have hb : AtomHolds b ρ h := atomHolds_rename_rev (f := fun i => some (i + 1))
      (fun x i hx => by simp only [Option.some.injEq] at hx; subst hx; rfl) hc hcb
    exact atomHolds_rename_rev hf hr hb

end Verification.TolerantFrames
