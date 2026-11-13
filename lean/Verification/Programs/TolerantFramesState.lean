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
holds the invocation's entry value `ε.env q`, its facts read at the
invocation's entry state `ε`. -/
def StateHolds (G : NormalGraph ι) (st : State) (implies : List (PromiseCalls.Implication ι)) (start : List Nat)
    (ε : HeapKnowledge.EntryState) : Assertion := fun ρ m s =>
  ∃ η : Env, SlotsNamed st.names ρ η ∧ Named ε (storeAll st.store) η ρ m s ∧
    PromiseCalls.ImpliesOk G implies η s.n s.W ∧ (∀ x ∈ st.fresh, FreshAt m (η x)) ∧
    ∀ q x, start[q]? = some x → η x = ε.env q

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
- `below`: every name of the slots, of the stored facts and of `fresh` is
  below `next`, so the next result name is fresh. A fresh name need not be
  held by a slot: a merge keeps a predecessor's fresh name beside its renames. -/
structure StateWF (st : State) (next : Nat) : Prop where
  store : StoreWF st.store
  below : (∀ x ∈ st.names, x < next) ∧ (∀ a ∈ storeAll st.store, ∀ x ∈ a.names, x < next) ∧ ∀ x ∈ st.fresh, x < next

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
theorem atomHolds_canon {a : Atom} {η : Env} {h : Heap} : AtomHolds ε a.canon η h ↔ AtomHolds ε a η h := by
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
    (hf : ∀ x i, f x = some i → ρ i = η x) (hr : a.rename f = some b) (ha : AtomHolds ε a η h) :
    AtomHolds ε b ρ h := by
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
def StoreOk (ε : HeapKnowledge.EntryState) (s : Store) (η : Env) (h : Heap) : Prop := ∀ a ∈ storeAll s, AtomHolds ε a η h

theorem vals_foldl {β : Type} (P : Atom → Prop) (g : Std.HashMap Nat (List Atom) → β → Std.HashMap Nat (List Atom))
    (hg : ∀ m n, (∀ y ∈ valsOf m, P y) → ∀ x ∈ valsOf (g m n), P x) :
    ∀ (l : List β) m, (∀ y ∈ valsOf m, P y) → ∀ x ∈ valsOf (l.foldl g m), P x
  | [], _, hm => hm
  | n :: l, m, hm => vals_foldl P g hg l (g m n) (hg m n hm)

theorem storeOk_of {s' : Store} {η : Env} {h : Heap}
    (hk : ∀ x ∈ s'.toList, AtomHolds ε x η h) (hv : ∀ x ∈ valsOf s'.byName, AtomHolds ε x η h) : StoreOk ε s' η h := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hk x hx
  · exact hv x hx

/-- A fact added raw keeps the store's facts holding, where it holds. -/
theorem addRaw_ok {s : Store} {a : Atom} {η : Env} {h : Heap} (hs : StoreOk ε s η h)
    (ha : AtomHolds ε a η h) : StoreOk ε (s.addRaw a) η h := by
  have hc : AtomHolds ε a.canon η h := atomHolds_canon.mpr ha
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
theorem remove_ok {s : Store} {a : Atom} {η : Env} {h : Heap} (hs : StoreOk ε s η h) :
    StoreOk ε (s.remove a) η h := by
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
    ∀ (as : List Atom) (s : Store), StoreOk ε s η h → StoreOk ε (as.foldl Store.remove s) η h
  | [], _, hs => hs
  | _ :: as, _, hs => foldl_remove_ok as _ (remove_ok hs)

/-- **A bound added keeps the store's facts holding**, a stronger bound
replacing weaker ones. -/
theorem addBound_ok {s : Store} {a : Atom} {η : Env} {h : Heap} (hs : StoreOk ε s η h)
    (ha : AtomHolds ε a η h) : StoreOk ε (s.addBound a) η h := by
  have hc : AtomHolds ε a.canon η h := atomHolds_canon.mpr ha
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
    ∀ (Fs : List (Linear.Fact HeapKnowledge.Term)) (s : Store), StoreOk ε s η h →
      (∀ F ∈ Fs, AtomHolds ε (.index ⟨.linear F, c, neg⟩) η h) →
      StoreOk ε (Fs.foldl (fun (s : Store) F => s.addBound (.index ⟨.linear F, c, neg⟩)) s) η h
  | [], _, hs, _ => hs
  | F :: Fs, _, hs, hx => foldl_addBound_ok Fs _ (addBound_ok hs (hx F (List.mem_cons_self ..)))
      fun G hG => hx G (List.mem_cons_of_mem _ hG)

/-- **A fact added (`Store.add`) keeps the store's facts holding**: a length
fact also as the linear facts it means (`HeapKnowledge.atomLinear_holds`). -/
theorem add_ok {s : Store} {a : Atom} {η : Env} {h : Heap} (hs : StoreOk ε s η h)
    (ha : AtomHolds ε a η h) : StoreOk ε (s.add a) η h := by
  have hc : AtomHolds ε a.canon η h := atomHolds_canon.mpr ha
  unfold Store.add
  dsimp only
  split
  · exact hs
  · refine addBound_ok ?_ hc
    split
    · rename_i _ x n c neg heq
      have hx : ∀ F ∈ HeapKnowledge.atomLinear (.length x n), AtomHolds ε (.index ⟨.linear F, c, neg⟩) η h := by
        intro F hF y hy hcond
        simp only [List.mem_singleton] at hy; subst hy
        rw [heq] at hc
        exact HeapKnowledge.atomLinear_holds (hc _ (List.mem_singleton_self _) hcond) F hF
      exact foldl_addBound_ok _ _ hs hx
    · exact hs

end Verification.TolerantFrames
