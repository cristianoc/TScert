import Verification.Programs.TolerantFramesNamed

/-! # Tolerant frames: the pass's named state

The single pass's state at a program point (`SinglePass.State`) is a list of
names, one per slot, a store of facts over names (`SinglePass.Store`) and the
names holding stores the invocation allocated; beside it the walk keeps the
implications over names. This module states what such a state means
(`StateHolds`): there is a valuation `η` of the names under which each slot
holds its name's value, every stored fact holds, every implication holds,
every fresh name holds a store allocated at or after the invocation's mark,
and the start's names hold the invocation's entry values. The valuation is
existential per state: a loop head's names denote new values on each visit.

The store's well-formedness, separate from its meaning, is `StateWF`; the
laws of the store's maps its operations need follow from the lemmas of
`Std.HashSet` and `Std.HashMap` (`keys_insert`, `keys_erase`, `vals_insert`,
`findD_vals`). -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations
open Verification.SinglePass (Atom Store State)

/-! ## The store's facts and the laws of its maps -/

/-- The store's live facts, as `Store.toList` lists them. -/
def keysOf (m : Std.HashSet Atom) : List Atom := m.toList

/-- The facts the store's index by name lists, over every name. -/
def valsOf (m : Std.HashMap Nat (List Atom)) : List Atom := m.toList.flatMap (·.2)

theorem mem_keysOf {m : Std.HashSet Atom} {x : Atom} : x ∈ keysOf m ↔ x ∈ m := Std.HashSet.mem_toList

/-- A fact the index lists is listed under some name. -/
theorem mem_valsOf {m : Std.HashMap Nat (List Atom)} {x : Atom} : x ∈ valsOf m ↔ ∃ n, x ∈ m.getD n [] := by
  simp only [valsOf, List.mem_flatMap]
  constructor
  · rintro ⟨⟨n, l⟩, hp, hx⟩
    rw [Std.HashMap.mem_toList_iff_getElem?_eq_some] at hp
    exact ⟨n, by rw [Std.HashMap.getD_eq_getD_getElem?, hp]; exact hx⟩
  · rintro ⟨n, hx⟩
    rw [Std.HashMap.getD_eq_getD_getElem?] at hx
    cases h : m[n]? with
    | none => rw [h] at hx; simp at hx
    | some l => rw [h] at hx; exact ⟨(n, l), Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr h, hx⟩

/-! The store's laws: each an upper bound on what an operation's result
holds, from `Std.HashSet`'s and `Std.HashMap`'s lemmas. -/

theorem keys_insert (m : Std.HashSet Atom) (a x : Atom) (hx : x ∈ keysOf (m.insert a)) : x = a ∨ x ∈ keysOf m := by
  rw [mem_keysOf, Std.HashSet.mem_insert] at hx
  rw [mem_keysOf]
  rcases hx with h | h
  · exact .inl (beq_iff_eq.mp h).symm
  · exact .inr h

theorem keys_erase (m : Std.HashSet Atom) (a x : Atom) (hx : x ∈ keysOf (m.erase a)) : x ∈ keysOf m := by
  rw [mem_keysOf, Std.HashSet.mem_erase] at hx
  exact mem_keysOf.mpr hx.2

theorem vals_insert (m : Std.HashMap Nat (List Atom)) (n : Nat) (l : List Atom) (x : Atom)
    (hx : x ∈ valsOf (m.insert n l)) : x ∈ l ∨ x ∈ valsOf m := by
  obtain ⟨k, hk⟩ := mem_valsOf.mp hx
  rw [Std.HashMap.getD_insert] at hk
  split at hk
  · exact .inl hk
  · exact .inr (mem_valsOf.mpr ⟨k, hk⟩)

theorem findD_vals (m : Std.HashMap Nat (List Atom)) (n : Nat) (x : Atom) (hx : x ∈ m.getD n []) :
    x ∈ valsOf m := mem_valsOf.mpr ⟨n, hx⟩

/-- Every fact the store holds: its live facts and the facts its index by
name lists. -/
def storeAll (s : Store) : List Atom := s.toList ++ valsOf s.byName

theorem toList_eq (s : Store) : s.toList = keysOf s.live := rfl

theorem about_storeAll {s : Store} {n : Nat} {a : Atom} (ha : a ∈ s.about n) : a ∈ storeAll s :=
  List.mem_append_right _ (findD_vals _ _ _ ha)

theorem toList_storeAll {s : Store} {a : Atom} (ha : a ∈ s.toList) : a ∈ storeAll s := List.mem_append_left _ ha

/-! ## The state's meaning -/

section State
variable {ι : Type} [DecidableEq ι]
open ProgramTyping PositiveGraphs

/-- Each slot holds its name's value. -/
def SlotsNamed (names : List Nat) (ρ η : Env) : Prop := ∀ i x, names[i]? = some x → ρ i = η x

/-- **The pass's state holds** at the slot environment `ρ`, the invocation's
mark `m` and the state `s`: there is a valuation `η` of the names under which
each slot holds its name's value, every fact the store holds holds
(`Named`), every implication holds (`PromiseCalls.ImpliesOk`: where the
test's name holds `true`, the target's value has the type), every name of
`st.fresh` holds a store at or past the mark, and each start name `start[q]`
holds the invocation's entry value `entry q`. -/
def StateHolds (G : NormalGraph ι) (st : State) (implies : List (PromiseCalls.Implication ι)) (start : List Nat)
    (entry : Env) : Assertion := fun ρ m s =>
  ∃ η : Env, SlotsNamed st.names ρ η ∧ Named (storeAll st.store) η ρ m s ∧
    PromiseCalls.ImpliesOk G implies η s.n s.W ∧ (∀ x ∈ st.fresh, FreshAt m (η x)) ∧
    ∀ q x, start[q]? = some x → η x = entry q

/-- **The store's well-formedness**: its live facts are canonical
(`Atom.canon`), and each fact its index lists under a name is live, mentions
that name, and is listed there once. -/
structure StoreWF (s : Store) : Prop where
  canonical : ∀ a ∈ s.live, a.canon = a
  indexed : ∀ n, ∀ a ∈ s.byName.getD n [], a ∈ s.live
  named : ∀ n, ∀ a ∈ s.byName.getD n [], n ∈ a.names
  nodup : ∀ n, (s.byName.getD n []).Nodup

/-- **The state's well-formedness** relative to the pass's next fresh name
`next`, separate from its meaning:

- `store`: the store's well-formedness (`StoreWF`);
- `slotted`: every name a stored fact reading the heap mentions is held by a
  slot;
- `below`: every name of the slots, of the stored facts and of `fresh` is
  below `next`, so the next result name is fresh;
- `freshHeld`: every fresh name is held by a slot. -/
structure StateWF (st : State) (next : Nat) : Prop where
  store : StoreWF st.store
  slotted : ∀ a ∈ storeAll st.store, a.heapFree = false → ∀ x ∈ a.names, x ∈ st.names
  below : (∀ x ∈ st.names, x < next) ∧ (∀ a ∈ storeAll st.store, ∀ x ∈ a.names, x < next) ∧ ∀ x ∈ st.fresh, x < next
  freshHeld : ∀ x ∈ st.fresh, x ∈ st.names

/-- The next name is fresh for every stored fact. -/
theorem StateWF.fresh_result {st : State} {next : Nat} (w : StateWF st next) :
    ∀ a ∈ storeAll st.store, next ∉ a.names :=
  fun a ha hx => Nat.lt_irrefl _ (w.below.2.1 a ha next hx)

end State

/-! ## Loops over lists

The pass's operations are written with `for` over lists in `Id`; an invariant
indexed by the position read carries through them. -/

theorem forIn_idx {α β : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β)) (P : Nat → β → Prop)
    (Q : β → Prop) (h0 : P 0 init)
    (hy : ∀ k a b b', l[k]? = some a → P k b → f a b = .yield b' → P (k + 1) b')
    (hd : ∀ k a b b', l[k]? = some a → P k b → f a b = .done b' → Q b')
    (hend : ∀ b, P l.length b → Q b) : Q (forIn l init f) := by
  induction l generalizing init P with
  | nil => exact hend init h0
  | cons a l ih =>
    rw [List.forIn_cons]
    cases hfa : f a init with
    | done b' => exact hd 0 a init b' rfl h0 hfa
    | yield b' =>
      exact ih b' (fun k => P (k + 1)) (hy 0 a init b' rfl h0 hfa)
        (fun k a b b' hk hp hf => hy (k + 1) a b b' hk hp hf)
        (fun k a b b' hk hp hf => hd (k + 1) a b b' hk hp hf) (fun b hb => hend b hb)

/-- `forIn_idx` before a continuation, as `do` notation places a loop. -/
theorem forIn_idx_bind {α β γ : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β)) (P : Nat → β → Prop)
    (Q : β → Prop) (k : β → Id γ) (R : γ → Prop) (h0 : P 0 init)
    (hy : ∀ k a b b', l[k]? = some a → P k b → f a b = .yield b' → P (k + 1) b')
    (hd : ∀ k a b b', l[k]? = some a → P k b → f a b = .done b' → Q b')
    (hend : ∀ b, P l.length b → Q b) (hk : ∀ b, Q b → R (k b)) : R (forIn l init f >>= k) :=
  hk _ (forIn_idx l init f P Q h0 hy hd hend)

/-- A loop whose every step keeps an invariant keeps it. -/
theorem forIn_inv {α β : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β)) (P : β → Prop)
    (h0 : P init) (hf : ∀ a ∈ l, ∀ b, P b → P (f a b).value) : P (forIn l init f) := by
  induction l generalizing init with
  | nil => exact h0
  | cons a l ih =>
    rw [List.forIn_cons]
    have := hf a (List.mem_cons_self ..) init h0
    cases hfa : f a init with
    | done b' => rw [hfa] at this; exact this
    | yield b' =>
      rw [hfa] at this
      exact ih b' this fun a ha b hb => hf a (List.mem_cons_of_mem _ ha) b hb

/-! ## One fact: canonical form and renaming -/

theorem mapM_mem {α β : Type} {g : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM g = some l' → ∀ b ∈ l', ∃ a ∈ l, g a = some b
  | [], l', h, b, hb => by simp at h; subst h; cases hb
  | a :: l, l', h, b, hb => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨c, hc, cs, hcs, rfl⟩ := h
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, List.mem_cons_self .., hc⟩
    · obtain ⟨a', ha', hg⟩ := mapM_mem hcs b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', hg⟩

/-- **A fact's canonical form holds where the fact does**: clearing an
unconditional fact's `negated` changes nothing a condition reads. -/
theorem atomHolds_canon {a : Atom} {η : Env} {h : Heap} : AtomHolds a.canon η h ↔ AtomHolds a η h := by
  cases a with
  | index x =>
    rcases x with ⟨f, c, neg⟩
    cases c <;> cases neg <;> simp [Atom.canon, AtomHolds, HeapKnowledge.IndexHolds]
  | elem e =>
    rcases e with ⟨sl, p, c, neg⟩
    cases c <;> cases neg <;> simp [Atom.canon, AtomHolds, HeapKnowledge.ElemsHolds]
  | cell _ | value _ | link _ | sep _ => rfl

/-- **A fact renamed holds at the renamed valuation**: where `f` maps a name
to a slot, the slot holds the name's value. -/
theorem atomHolds_rename {a b : Atom} {f : Nat → Option Nat} {η ρ : Env} {h : Heap}
    (hf : ∀ x i, f x = some i → ρ i = η x) (hr : a.rename f = some b) (ha : AtomHolds a η h) :
    AtomHolds b ρ h := by
  cases a with
  | cell x =>
    simp only [Atom.rename, Option.map_eq_some_iff] at hr
    obtain ⟨s, hs, rfl⟩ := hr
    intro g hg; simp only [List.mem_singleton] at hg; subst hg
    simpa only [hf _ _ hs] using ha x (List.mem_singleton_self _)
  | value x =>
    simp only [Atom.rename, Option.map_eq_some_iff] at hr
    obtain ⟨s, hs, rfl⟩ := hr
    intro g hg; simp only [List.mem_singleton] at hg; subst hg
    simpa only [hf _ _ hs] using ha x (List.mem_singleton_self _)
  | link g =>
    simp only [Atom.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hr
    obtain ⟨c, hc, v, hv, rfl⟩ := hr
    intro g' hg; simp only [List.mem_singleton] at hg; subst hg
    have := ha g (List.mem_singleton_self _)
    simpa only [hf _ _ hc, hf _ _ hv] using this
  | elem e =>
    simp only [Atom.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hr
    obtain ⟨s, hs, c, hc, rfl⟩ := hr
    intro e' he hcond; simp only [List.mem_singleton] at he; subst he
    have := ha e (List.mem_singleton_self _) (fun b hb => by
      cases hcb : e.cond with
      | none => rw [hcb] at hb; cases hb
      | some b' =>
        rw [hcb] at hb hc
        simp only [Option.some.injEq] at hb; subst hb
        cases hfb : f b' with
        | none => rw [Option.mapM_some, hfb] at hc; simp at hc
        | some b'' =>
          rw [Option.mapM_some, hfb] at hc
          have hc' : c = some b'' := (Option.some.inj hc).symm
          subst hc'
          rw [← hf _ _ hfb]; exact hcond b'' rfl)
    simpa only [hf _ _ hs] using this
  | index x =>
    simp only [Atom.rename, Option.map_eq_some_iff] at hr
    obtain ⟨y, hy, rfl⟩ := hr
    have hm : HeapKnowledge.mapIndices f [x] = [y] := by simp [HeapKnowledge.mapIndices, hy]
    have := HeapKnowledge.mapIndices_holds (ρ := η) (ρ' := ρ) (fun s t ht => hf s t ht) ha
    rw [hm] at this
    exact this
  | sep x =>
    simp only [Atom.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hr
    obtain ⟨s, hs, ps, hps, rfl⟩ := hr
    intro p hp g hg
    obtain ⟨q, hq, hqp⟩ := mapM_mem hps p hp
    simp only [Option.map_eq_some_iff] at hqp
    obtain ⟨t, ht, rfl⟩ := hqp
    exact (ha q hq g hg).congr (hf _ _ hs) (hf _ _ ht)

/-! ## The store's operations -/

/-- The facts of a store hold at `η` and `h`. -/
def StoreOk (s : Store) (η : Env) (h : Heap) : Prop := ∀ a ∈ storeAll s, AtomHolds a η h

theorem vals_foldl {β : Type} (P : Atom → Prop) (g : Std.HashMap Nat (List Atom) → β → Std.HashMap Nat (List Atom))
    (hg : ∀ m n, (∀ y ∈ valsOf m, P y) → ∀ x ∈ valsOf (g m n), P x) :
    ∀ (l : List β) m, (∀ y ∈ valsOf m, P y) → ∀ x ∈ valsOf (l.foldl g m), P x
  | [], _, hm => hm
  | n :: l, m, hm => vals_foldl P g hg l (g m n) (hg m n hm)

theorem storeOk_of {s' : Store} {η : Env} {h : Heap}
    (hk : ∀ x ∈ s'.toList, AtomHolds x η h) (hv : ∀ x ∈ valsOf s'.byName, AtomHolds x η h) : StoreOk s' η h := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hk x hx
  · exact hv x hx

/-- A fact added raw keeps the store's facts holding, where it holds. -/
theorem addRaw_ok {s : Store} {a : Atom} {η : Env} {h : Heap} (hs : StoreOk s η h)
    (ha : AtomHolds a η h) : StoreOk (s.addRaw a) η h := by
  have hc : AtomHolds a.canon η h := atomHolds_canon.mpr ha
  unfold Store.addRaw
  dsimp only
  split
  · exact hs
  · refine storeOk_of (fun x hx => ?_) (vals_foldl _ _ (fun m n hm x hx => ?_) _ _
      (fun y hy => hs y (List.mem_append_right _ hy)))
    · rcases keys_insert _ _ _ hx with rfl | hx
      · exact hc
      · exact hs x (List.mem_append_left _ hx)
    · rcases vals_insert _ _ _ _ hx with hx | hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact hc
        · exact hm x (findD_vals _ _ _ hx)
      · exact hm x hx

/-- A fact removed keeps the store's facts holding. -/
theorem remove_ok {s : Store} {a : Atom} {η : Env} {h : Heap} (hs : StoreOk s η h) :
    StoreOk (s.remove a) η h := by
  unfold Store.remove
  dsimp only
  split
  · refine storeOk_of (fun x hx => hs x (List.mem_append_left _ (keys_erase _ _ _ hx)))
      (vals_foldl _ _ (fun m n hm x hx => ?_) _ _ (fun y hy => hs y (List.mem_append_right _ hy)))
    rcases vals_insert _ _ _ _ hx with hx | hx
    · exact hm x (findD_vals _ _ _ (List.mem_of_mem_erase hx))
    · exact hm x hx
  · exact hs

theorem foldl_remove_ok {η : Env} {h : Heap} :
    ∀ (as : List Atom) (s : Store), StoreOk s η h → StoreOk (as.foldl Store.remove s) η h
  | [], _, hs => hs
  | _ :: as, _, hs => foldl_remove_ok as _ (remove_ok hs)

/-- **A bound added keeps the store's facts holding**, a stronger bound
replacing weaker ones. -/
theorem addBound_ok {s : Store} {a : Atom} {η : Env} {h : Heap} (hs : StoreOk s η h)
    (ha : AtomHolds a η h) : StoreOk (s.addBound a) η h := by
  have hc : AtomHolds a.canon η h := atomHolds_canon.mpr ha
  unfold Store.addBound
  dsimp only
  split
  · exact hs
  · split
    · split
      · exact hs
      · exact addRaw_ok (foldl_remove_ok _ _ hs) hc
    · exact addRaw_ok hs hc

theorem foldl_addBound_ok {η : Env} {h : Heap} {c : Option Nat} {neg : Bool} :
    ∀ (Fs : List (Linear.Fact HeapKnowledge.Term)) (s : Store), StoreOk s η h →
      (∀ F ∈ Fs, AtomHolds (.index ⟨.linear F, c, neg⟩) η h) →
      StoreOk (Fs.foldl (fun (s : Store) F => s.addBound (.index ⟨.linear F, c, neg⟩)) s) η h
  | [], _, hs, _ => hs
  | F :: Fs, _, hs, hx => foldl_addBound_ok Fs _ (addBound_ok hs (hx F (List.mem_cons_self ..)))
      fun G hG => hx G (List.mem_cons_of_mem _ hG)

/-- **A fact added (`Store.add`) keeps the store's facts holding**: a length
fact also as the linear facts it means (`HeapKnowledge.atomLinear_holds`). -/
theorem add_ok {s : Store} {a : Atom} {η : Env} {h : Heap} (hs : StoreOk s η h)
    (ha : AtomHolds a η h) : StoreOk (s.add a) η h := by
  have hc : AtomHolds a.canon η h := atomHolds_canon.mpr ha
  unfold Store.add
  dsimp only
  split
  · exact hs
  · refine addBound_ok ?_ hc
    split
    · rename_i _ x n c neg heq
      have hx : ∀ F ∈ HeapKnowledge.atomLinear (.length x n), AtomHolds (.index ⟨.linear F, c, neg⟩) η h := by
        intro F hF y hy hcond
        simp only [List.mem_singleton] at hy; subst hy
        rw [heq] at hc
        exact HeapKnowledge.atomLinear_holds (hc _ (List.mem_singleton_self _) hcond) F hF
      exact foldl_addBound_ok _ _ hs hx
    · exact hs

/-! ## Materialization -/

open SinglePass in
/-- The facts `materialize` reads (its `atoms`): every fact of the store with
`whole`, else the facts its worklist collects from the index by name. -/
def selectedAtoms (st : State) (slots : List Nat) (whole : Bool) (chain : Bool) : List Atom :=
  let given := slots.filterMap fun s => st.names[s]?
  if whole then st.store.toList else Id.run do
    let mut seen : Std.HashSet Nat := given.foldl (·.insert ·) {}
    let mut frontier := given
    let mut kept : Std.HashSet Atom := {}
    let mut out : Array Atom := #[]
    while !frontier.isEmpty do
      let mut next := []
      for x in frontier do
        for a in st.store.about x do
          if !kept.contains a then
            kept := kept.insert a
            out := out.push a
            let through := match a with
              | .link g => [g.cell, g.value]
              | .index x => match x.fact with
                | .linear _ => if chain then a.names else []
                | _ => []
              | _ => []
            for y in through do
              if !seen.contains y then
                seen := seen.insert y
                next := y :: next
      frontier := next
    return out.toList

/-- `materialize`'s alias links: each slot below `d` holding a name a slot
before it holds, related to that first slot. -/
def aliasLinksOf (names : List Nat) (d : Nat) (table : Std.HashMap Nat Nat) : List Atom := Id.run do
  let mut out := []
  let mut i := 0
  for n in names do
    if i ≥ d then break
    if let some first := table.get? n then
      if first != i then out := Atom.link { cell := first, value := i, alias := true } :: out
    i := i + 1
  return out

/-- `materialize`'s derived facts: the index facts with the names `out`, held
by no slot, restated through read links and eliminated. -/
def derivedOf (indices : List HeapKnowledge.IndexAtom) (links : HeapLinks.Links) (table : Std.HashMap Nat Nat)
    (out : List Nat) : List HeapKnowledge.IndexAtom :=
  if out.isEmpty || indices.isEmpty then [] else
    let isOut := fun s => !table.contains s
    let restated := indices ++ HeapKnowledge.restateReads links isOut indices ++
      HeapKnowledge.restateStores links isOut indices
    (HeapKnowledge.eliminateIndices out restated).drop indices.length

open SinglePass HeapKnowledge in
/-- `materialize`'s computation from its facts `atoms` on. -/
def materializeFrom (st : State) (d : Nat) (given : List Nat) (atoms : List Atom) (whole : Bool) :
    Knowledge × List (Atom × Atom) × Std.HashMap Nat Nat :=
  let want : Std.HashSet Nat := atoms.foldl (fun acc a => a.names.foldl (·.insert ·) acc)
    (given.foldl (·.insert ·) {})
  let table := slotTable st.names want whole
  let out := want.fold (fun acc n => if table.contains n then acc else n :: acc) []
  let indices := atoms.filterMap fun a => match a with | .index x => some x | _ => none
  let links := atoms.filterMap fun a => match a with | .link g => some g | _ => none
  let derived := derivedOf indices links table out
  let f := fun n => table.get? n
  let pairs := atoms.filterMap fun a => (a.rename f).map (a, ·)
  let extra := derived.filterMap fun x => (Atom.index x).rename f
  let aliasLinks : List Atom := aliasLinksOf st.names d table
  (ofAtoms (pairs.map (·.2) ++ extra ++ aliasLinks) d, pairs, table)

/-- `materialize` is `materializeFrom` at its selected facts. -/
theorem materialize_eq (st : State) (d : Nat) (slots : List Nat) (whole chain : Bool) :
    SinglePass.materialize st d slots whole chain =
      materializeFrom st d (slots.filterMap fun s => st.names[s]?) (selectedAtoms st slots whole chain) whole := rfl

theorem selectedAtoms_whole (st : State) (slots : List Nat) (chain : Bool) :
    selectedAtoms st slots true chain = st.store.toList := rfl

/-- **The slot table gives, for each name, a slot holding it.** -/
theorem slotTable_get {names : List Nat} {want : Std.HashSet Nat} {whole : Bool} {n i : Nat}
    (hg : (SinglePass.slotTable names want whole).get? n = some i) : names[i]? = some n := by
  let TOk : Std.HashMap Nat Nat → Prop := fun t => ∀ n i, t.get? n = some i → names[i]? = some n
  have hins : ∀ t k x, TOk t → names[k]? = some x → TOk (t.insert x k) := by
    intro t k x ht hk n' i' hg'
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hg'
    split at hg'
    · rename_i he
      simp only [beq_iff_eq] at he
      cases hg'; subst he; exact hk
    · exact ht n' i' (by rw [Std.HashMap.get?_eq_getElem?]; exact hg')
  have hemp : TOk ∅ := fun n i h => by simp at h
  unfold SinglePass.slotTable at hg
  simp only [Id.run] at hg
  revert hg
  refine forIn_idx_bind (R := fun (t : Std.HashMap Nat Nat) => t.get? n = some i → names[i]? = some n) (Q := fun (b : Option (Std.HashMap Nat Nat) × Std.HashMap Nat Nat × Nat × Nat) =>
      TOk (match b.1 with | some r => r | none => b.2.1)) names _ _
    (fun k b => b.2.2.1 = k ∧ TOk b.2.1 ∧ ∀ r, b.1 = some r → TOk r) _ ⟨rfl, hemp, fun _ h => by cases h⟩
    ?_ ?_ ?_ ?_
  · intro k a b b' hk ⟨hi, ht, hr⟩ hf
    split at hf
    · split at hf
      · split at hf
        · cases hf
        · cases hf
          exact ⟨by simp [hi], hins _ _ _ ht (hi ▸ hk), fun _ h => by cases h⟩
      · cases hf; exact ⟨by simp [hi], ht, fun _ h => by cases h⟩
    · cases hf; exact ⟨by simp [hi], ht, fun _ h => by cases h⟩
  · intro k a b b' hk ⟨hi, ht, hr⟩ hf
    split at hf
    · split at hf
      · split at hf
        · cases hf
          exact hins _ _ _ ht (hi ▸ hk)
        · cases hf
      · cases hf
    · cases hf
  · intro b ⟨_, ht, hr⟩
    cases hb : b.1 with
    | none => simpa [hb] using ht
    | some r => simpa [hb] using hr r hb
  · intro b hb
    cases hb1 : b.1 with
    | none => simp only [hb1] at hb ⊢; exact hb n i
    | some r => simp only [hb1] at hb ⊢; exact hb n i

/-- **The alias links `materialize` adds hold**: each relates two slots
holding one name. -/
theorem aliasLinksOf_holds {names : List Nat} {d : Nat} {want : Std.HashSet Nat} {whole : Bool} {ρ η : Env}
    {h : Heap} (hs : SlotsNamed names ρ η) :
    ∀ a ∈ aliasLinksOf names d (SinglePass.slotTable names want whole), AtomHolds a ρ h := by
  unfold aliasLinksOf
  simp only [Id.run]
  refine forIn_idx_bind (R := fun (t : List Atom) => ∀ a ∈ t, AtomHolds a ρ h)
    (Q := fun (b : List Atom × Nat) => ∀ a ∈ b.1, AtomHolds a ρ h) names _ _
    (fun k b => b.2 = k ∧ ∀ a ∈ b.1, AtomHolds a ρ h) _ ⟨rfl, fun _ h => by cases h⟩ ?_ ?_ ?_ ?_
  · intro k n b b' hk ⟨hi, hb⟩ hf
    split at hf
    · cases hf
    · split at hf
      · rename_i first hfirst
        split at hf
        · cases hf
          refine ⟨by simp [hi], fun a ha => ?_⟩
          rcases List.mem_cons.mp ha with rfl | ha
          · intro g hg
            simp only [List.mem_singleton] at hg; subst hg
            simp only [ite_true]
            rw [hs _ _ (slotTable_get hfirst), hs _ _ (hi ▸ hk)]
          · exact hb a ha
        · cases hf; exact ⟨by simp [hi], hb⟩
      · cases hf; exact ⟨by simp [hi], hb⟩
  · intro k n b b' _ ⟨_, hb⟩ hf
    split at hf
    · cases hf; exact hb
    · split at hf
      · split at hf <;> cases hf
      · cases hf
  · intro b ⟨_, hb⟩; exact hb
  · intro b hb; exact hb

/-- The derived facts hold where the index facts and links they are derived
from do. -/
theorem derivedOf_holds {indices : List HeapKnowledge.IndexAtom} {links : HeapLinks.Links}
    {table : Std.HashMap Nat Nat} {out : List Nat} {η : Env} {h : Heap}
    (hi : HeapKnowledge.IndexHolds indices η h) (hl : HeapLinks.Holds links η h) :
    HeapKnowledge.IndexHolds (derivedOf indices links table out) η h := by
  unfold derivedOf
  split
  · exact HeapKnowledge.indexHolds_nil η h
  · have hr : HeapKnowledge.IndexHolds (indices ++ HeapKnowledge.restateReads links (fun s => !table.contains s) indices ++
        HeapKnowledge.restateStores links (fun s => !table.contains s) indices) η h := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · rcases List.mem_append.mp ha with ha | ha
        · exact hi a ha
        · exact HeapKnowledge.restateReads_holds hl hi a ha
      · exact HeapKnowledge.restateStores_holds hl hi a ha
    intro a ha
    exact HeapKnowledge.eliminateIndices_holds hr a (List.mem_of_mem_drop ha)

/-- `ofAtoms`'s fold, one fact into the knowledge. -/
def ofStep (a : Atom) (k : HeapKnowledge.Knowledge) : HeapKnowledge.Knowledge := match a with
  | .cell f => { k with cells := f :: k.cells }
  | .value f => { k with values := f :: k.values }
  | .link g => { k with links := g :: k.links }
  | .elem e => { k with elems := e :: k.elems }
  | .index i => { k with indices := i :: k.indices }
  | .sep f => { k with separation := { k.separation with facts := f :: k.separation.facts } }

theorem ofAtoms_eq (as : List Atom) (d : Nat) : SinglePass.ofAtoms as d =
    let k := as.foldr ofStep {}
    { k with separation := HeapSeparation.norm d ((k.separation.facts.filter fun f =>
        f.slot < d && f.partners.all (·.1 < d)).map (SinglePass.flip d)) } := rfl

theorem ofStep_mem : ∀ (as : List Atom),
    (∀ f ∈ (as.foldr ofStep {}).cells, Atom.cell f ∈ as) ∧ (∀ f ∈ (as.foldr ofStep {}).values, Atom.value f ∈ as) ∧
    (∀ g ∈ (as.foldr ofStep {}).links, Atom.link g ∈ as) ∧ (∀ e ∈ (as.foldr ofStep {}).elems, Atom.elem e ∈ as) ∧
    (∀ x ∈ (as.foldr ofStep {}).indices, Atom.index x ∈ as) ∧
    (∀ f ∈ (as.foldr ofStep {}).separation.facts, Atom.sep f ∈ as)
  | [] => by simp
  | a :: as => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ofStep_mem as
    simp only [List.foldr_cons]
    cases a <;> simp only [ofStep, List.mem_cons, reduceCtorEq, Atom.cell.injEq, Atom.value.injEq,
      Atom.link.injEq, Atom.elem.injEq, Atom.index.injEq, Atom.sep.injEq, false_or] <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
        | exact fun x hx => h1 x hx | exact fun x hx => h2 x hx | exact fun x hx => h3 x hx
        | exact fun x hx => h4 x hx | exact fun x hx => h5 x hx | exact fun x hx => h6 x hx
        | exact fun x hx => Or.imp_right (h1 x) hx | exact fun x hx => Or.imp_right (h2 x) hx
        | exact fun x hx => Or.imp_right (h3 x) hx | exact fun x hx => Or.imp_right (h4 x) hx
        | exact fun x hx => Or.imp_right (h5 x) hx | exact fun x hx => Or.imp_right (h6 x) hx

/-- **Facts at slots holding make the knowledge `ofAtoms` builds hold**, its
separation read at depth `d`. -/
theorem ofAtoms_holds {as : List Atom} {d : Nat} {ρ : Env} {h : Heap} (ha : ∀ b ∈ as, AtomHolds b ρ h) :
    HeapKnowledge.Holds (SinglePass.ofAtoms as d) ρ h := by
  rw [ofAtoms_eq]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ofStep_mem as
  refine ⟨fun f hf => ha _ (h1 f hf) f (List.mem_singleton_self _), fun f hf => ha _ (h2 f hf) f (List.mem_singleton_self _),
    fun g hg => ha _ (h3 g hg) g (List.mem_singleton_self _), ?_,
    fun e he => ha _ (h4 e he) e (List.mem_singleton_self _), fun x hx => ha _ (h5 x hx) x (List.mem_singleton_self _)⟩
  apply HeapSeparation.norm_holds
  intro a ham
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ham
  obtain ⟨hf, hlt⟩ := List.mem_filter.mp hf
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hlt
  obtain ⟨hsl, hps⟩ := hlt
  have hsep := ha _ (h6 f hf)
  refine ⟨by simp only [SinglePass.flip]; omega, fun p' hp' => ?_⟩
  simp only [SinglePass.flip, List.mem_map] at hp'
  obtain ⟨p, hp, rfl⟩ := hp'
  have hpl := hps p hp
  refine ⟨by omega, fun g hg => ?_⟩
  have e1 : d - 1 - (d - 1 - f.slot) = f.slot := by omega
  have e2 : d - 1 - (d - 1 - p.1) = p.1 := by omega
  simp only [SinglePass.flip, e1, e2]
  exact hsep p hp g hg

/-- **A knowledge's facts hold as named facts at its slots** (`atomsOf`, its
separation read from levels to slots). -/
theorem atomsOf_holds {k : HeapKnowledge.Knowledge} {ρ : Env} {h : Heap} (hk : HeapKnowledge.Holds k ρ h) :
    ∀ a ∈ SinglePass.atomsOf k, AtomHolds a ρ h := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hk
  intro a ha
  simp only [SinglePass.atomsOf, List.mem_append, List.mem_map] at ha
  rcases ha with (((((⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩) | ⟨g, hg, rfl⟩) | ⟨e, he, rfl⟩) | ⟨x, hx, rfl⟩) | ⟨f, hf, rfl⟩)
  · intro f' hf'; simp only [List.mem_singleton] at hf'; rw [hf']; exact h1 f hf
  · intro f' hf'; simp only [List.mem_singleton] at hf'; rw [hf']; exact h2 f hf
  · intro g' hg'; simp only [List.mem_singleton] at hg'; rw [hg']; exact h3 g hg
  · intro e' he'; simp only [List.mem_singleton] at he'; rw [he']; exact h5 e he
  · intro x' hx'; simp only [List.mem_singleton] at hx'; rw [hx']; exact h6 x hx
  · intro p' hp' g hg
    simp only [SinglePass.flip, List.mem_map] at hp'
    obtain ⟨p, hp, rfl⟩ := hp'
    exact ((h4 f hf).2 p hp).2 g hg

/-- The slot table maps each name to a slot holding its value. -/
theorem table_named {names : List Nat} {want : Std.HashSet Nat} {whole : Bool} {ρ η : Env}
    (hs : SlotsNamed names ρ η) :
    ∀ x i, (SinglePass.slotTable names want whole).get? x = some i → ρ i = η x :=
  fun _ _ hg => hs _ _ (slotTable_get hg)

/-- **Materialization from holding facts is sound**: where every fact
`atoms` lists holds at `η` and each slot holds its name's value, the
knowledge `materializeFrom` builds holds at the slots. -/
theorem materializeFrom_holds {st : State} {d : Nat} {given : List Nat} {atoms : List Atom} {whole : Bool}
    {ρ η : Env} {h : Heap} (hs : SlotsNamed st.names ρ η) (ha : ∀ a ∈ atoms, AtomHolds a η h) :
    HeapKnowledge.Holds (materializeFrom st d given atoms whole).1 ρ h := by
  simp only [materializeFrom]
  apply ofAtoms_holds
  intro b hb
  have hf := table_named (want := atoms.foldl (fun acc a => a.names.foldl (·.insert ·) acc)
    (given.foldl (·.insert ·) {})) (whole := whole) hs
  rcases List.mem_append.mp hb with hb | hb
  · rcases List.mem_append.mp hb with hb | hb
    · obtain ⟨⟨a, b'⟩, hp, rfl⟩ := List.mem_map.mp hb
      obtain ⟨a', ha', hab⟩ := List.mem_filterMap.mp hp
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hab
      obtain ⟨b'', hr, rfl, rfl⟩ := hab
      exact atomHolds_rename hf hr (ha _ ha')
    · obtain ⟨x, hx, hr⟩ := List.mem_filterMap.mp hb
      refine atomHolds_rename hf hr ?_
      have hi : HeapKnowledge.IndexHolds (atoms.filterMap fun a => match a with | .index x => some x | _ => none) η h := by
        intro y hy
        obtain ⟨a, haa, hay⟩ := List.mem_filterMap.mp hy
        split at hay
        · cases hay; exact ha _ haa y (List.mem_singleton_self _)
        · cases hay
      have hl : HeapLinks.Holds (atoms.filterMap fun a => match a with | .link g => some g | _ => none) η h := by
        intro g hg
        obtain ⟨a, haa, hag⟩ := List.mem_filterMap.mp hg
        split at hag
        · cases hag; exact ha _ haa g (List.mem_singleton_self _)
        · cases hag
      intro y hy
      simp only [List.mem_singleton] at hy; subst hy
      exact derivedOf_holds hi hl y hx
  · exact aliasLinksOf_holds hs b hb

/-- The pairs `materializeFrom` returns: each a fact of `atoms` and its image
under the table. -/
theorem materializeFrom_pairs {st : State} {d : Nat} {given : List Nat} {atoms : List Atom} {whole : Bool}
    {a b : Atom} (hp : (a, b) ∈ (materializeFrom st d given atoms whole).2.1) :
    a ∈ atoms ∧ a.rename (fun n => (materializeFrom st d given atoms whole).2.2.get? n) = some b := by
  simp only [materializeFrom] at hp ⊢
  obtain ⟨a', ha', hab⟩ := List.mem_filterMap.mp hp
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hab
  obtain ⟨b', hr, rfl, rfl⟩ := hab
  exact ⟨ha', hr⟩

/-- The table `materializeFrom` returns is the slot table. -/
theorem materializeFrom_table {st : State} {d : Nat} {given : List Nat} {atoms : List Atom} {whole : Bool} :
    ∃ want, (materializeFrom st d given atoms whole).2.2 = SinglePass.slotTable st.names want whole := ⟨_, rfl⟩

/-! ## Materialization from the state -/

/-- **(Obstacle) The selective facts are drawn from the index by name.** The
worklist of `materialize` collects each fact it returns from `Store.about` of
some name; the worklist is a `while` loop (`Lean.Loop.forIn`, implemented by
`repeatM`, opaque to proof), so no theorem reaches its result. A named
hypothesis of the selective case. -/
def SelectedFromIndex (st : State) (slots : List Nat) (chain : Bool) : Prop :=
  ∀ a ∈ selectedAtoms st slots false chain, ∃ n, a ∈ st.store.about n

section Materialize
variable {ι : Type}
open ProgramTyping PositiveGraphs

/-- **The whole materialization holds at the slots**: from the state's
meaning, the knowledge `materialize … true` hands a writing step holds at the
node's environment and heap. -/
theorem stateHolds_materialize_whole {G : NormalGraph ι} {st : State} {implies : List (PromiseCalls.Implication ι)}
    {start : List Nat} {entry ρ : Env} {m : Nat} {s : IndexedHeap} (hS : StateHolds G st implies start entry ρ m s)
    (d : Nat) (slots : List Nat) (chain : Bool) :
    HeapKnowledge.Holds (SinglePass.materialize st d slots true chain).1 ρ s.h := by
  obtain ⟨η, hn, hst, -⟩ := hS
  rw [materialize_eq, selectedAtoms_whole]
  exact materializeFrom_holds hn fun a ha => hst a (toList_storeAll ha)

/-- **The selective materialization holds at the slots**, its facts drawn
from the index by name (`SelectedFromIndex`, the obstacle of the `while`
loop). -/
theorem stateHolds_materialize {G : NormalGraph ι} {st : State} {implies : List (PromiseCalls.Implication ι)}
    {start : List Nat} {entry ρ : Env} {m : Nat} {s : IndexedHeap} 
    (hS : StateHolds G st implies start entry ρ m s) (d : Nat) (slots : List Nat) (chain : Bool)
    (hsel : SelectedFromIndex st slots chain) :
    HeapKnowledge.Holds (SinglePass.materialize st d slots false chain).1 ρ s.h := by
  obtain ⟨η, hn, hst, -⟩ := hS
  rw [materialize_eq]
  refine materializeFrom_holds hn fun a ha => ?_
  obtain ⟨n, hn⟩ := hsel a ha
  exact hst a (about_storeAll hn)

/-- **The knowledge a step's rule reads holds** (`kE`, line 1229, and `kE'`,
line 1321): `KnowledgeExpand.expandLinks` of either materialization at the
node's context, where the environment meets that context. Both hold at
once; so a precondition decided at `kE` holds where the step reads `kE'`. -/
theorem stateHolds_stepKnowledge {G : NormalGraph ι} {Γ : List (Ty ι)} {st : State}
    {implies : List (PromiseCalls.Implication ι)} {start : List Nat} {entry ρ : Env} {m : Nat} {s : IndexedHeap}
    (hS : StateHolds G st implies start entry ρ m s) (he : EnvOk G Γ ρ s.n s.W)
    (d : Nat) (ms : List Nat) (wholeStep : Bool) (hsel : wholeStep = false → SelectedFromIndex st ms true) :
    HeapKnowledge.Holds (KnowledgeExpand.expandLinks (KnowledgeExpand.ctxOf G Γ)
        (SinglePass.materialize st d ms wholeStep).1) ρ s.h ∧
      HeapKnowledge.Holds (KnowledgeExpand.expandLinks (KnowledgeExpand.ctxOf G Γ)
        (SinglePass.materialize st d ms true).1) ρ s.h := by
  have hc := KnowledgeExpand.ctxOf_ok he
  refine ⟨KnowledgeExpand.expandLinks_holds hc ?_,
    KnowledgeExpand.expandLinks_holds hc (stateHolds_materialize_whole hS d ms true)⟩
  cases wholeStep with
  | true => exact stateHolds_materialize_whole hS d ms true
  | false => exact stateHolds_materialize hS d ms true (hsel rfl)

end Materialize

end Verification.TolerantFrames
