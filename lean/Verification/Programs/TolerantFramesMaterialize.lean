import Verification.Programs.TolerantFramesState

/-! # Tolerant frames: materialization from the named state

`SinglePass.materialize` hands a step the positional knowledge it reads: the
facts over the names its expression mentions (or every fact), renamed to the
slots holding their names, with the alias links between slots holding one
name and the facts derived for names no slot holds. This module proves that
knowledge holds at the node's environment wherever the state holds
(`StateHolds`). -/
namespace Verification.TolerantFrames
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification Footprints HeapObservations
open Verification.SinglePass (Atom Store State)

/-! ## Materialization -/

open SinglePass in
/-- The facts `materialize` reads (its `atoms`): every fact of the store with
`whole`, else the facts its worklist collects from the index by name
(`SinglePass.selectFrom`). -/
def selectedAtoms (st : State) (slots : List Nat) (whole : Bool) (chain : Bool) : List Atom :=
  let given := slots.filterMap fun s => st.names[s]?
  if whole then st.store.toList else
    (selectFrom st.store chain (st.store.size + 2) given (given.foldl (·.insert ·) {}) {} #[]).toList

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
    ∀ a ∈ aliasLinksOf names d (SinglePass.slotTable names want whole), AtomHolds ε a ρ h := by
  unfold aliasLinksOf
  simp only [Id.run]
  refine forIn_idx_bind (R := fun (t : List Atom) => ∀ a ∈ t, AtomHolds ε a ρ h)
    (Q := fun (b : List Atom × Nat) => ∀ a ∈ b.1, AtomHolds ε a ρ h) names _ _
    (fun k b => b.2 = k ∧ ∀ a ∈ b.1, AtomHolds ε a ρ h) _ ⟨rfl, fun _ h => by cases h⟩ ?_ ?_ ?_ ?_
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
    (hi : HeapKnowledge.IndexHolds ε indices η h) (hl : HeapLinks.Holds links η h) :
    HeapKnowledge.IndexHolds ε (derivedOf indices links table out) η h := by
  unfold derivedOf
  split
  · exact HeapKnowledge.indexHolds_nil η h
  · have hr : HeapKnowledge.IndexHolds ε (indices ++ HeapKnowledge.restateReads links (fun s => !table.contains s) indices ++
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
theorem ofAtoms_holds {as : List Atom} {d : Nat} {ρ : Env} {h : Heap} (ha : ∀ b ∈ as, AtomHolds ε b ρ h) :
    HeapKnowledge.Holds (SinglePass.ofAtoms as d) ε ρ h := by
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
theorem atomsOf_holds {k : HeapKnowledge.Knowledge} {ρ : Env} {h : Heap} (hk : HeapKnowledge.Holds k ε ρ h) :
    ∀ a ∈ SinglePass.atomsOf k, AtomHolds ε a ρ h := by
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
    {ρ η : Env} {h : Heap} (hs : SlotsNamed st.names ρ η) (ha : ∀ a ∈ atoms, AtomHolds ε a η h) :
    HeapKnowledge.Holds (materializeFrom st d given atoms whole).1 ε ρ h := by
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
      have hi : HeapKnowledge.IndexHolds ε (atoms.filterMap fun a => match a with | .index x => some x | _ => none) η h := by
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

/-- The selective facts are drawn from the index by name: each fact
`selectedAtoms` returns without `whole` is listed by `Store.about` of some
name. -/
def SelectedFromIndex (st : State) (slots : List Nat) (chain : Bool) : Prop :=
  ∀ a ∈ selectedAtoms st slots false chain, ∃ n, a ∈ st.store.about n

theorem foldl_inv {α β : Type} (P : β → Prop) (f : β → α → β) :
    ∀ (l : List α) (b : β), P b → (∀ a ∈ l, ∀ b, P b → P (f b a)) → P (l.foldl f b)
  | [], _, h, _ => h
  | a :: l, b, h, hf => foldl_inv P f l (f b a) (hf a (List.mem_cons_self ..) b h)
      fun a' ha' => hf a' (List.mem_cons_of_mem _ ha')

/-- **One round keeps only facts the index lists**: a fact a round keeps is
listed under a frontier name. -/
theorem selectRound_about (s : Store) (chain : Bool) (frontier : List Nat) (seen : Std.HashSet Nat)
    (kept : Std.HashSet Atom) (out : Array Atom) (h : ∀ a ∈ out.toList, ∃ n, a ∈ s.about n) :
    ∀ a ∈ (SinglePass.selectRound s chain frontier seen kept out).2.2.2.toList, ∃ n, a ∈ s.about n := by
  let P : List Nat × Std.HashSet Nat × Std.HashSet Atom × Array Atom → Prop :=
    fun b => ∀ a ∈ b.2.2.2.toList, ∃ n, a ∈ s.about n
  refine foldl_inv P _ frontier _ h fun x _ acc hacc => foldl_inv P _ (s.about x) acc hacc fun a ha b hb => ?_
  obtain ⟨nx, sn, kp, o⟩ := b
  dsimp only
  split
  · exact hb
  · refine foldl_inv P _ _ _ ?_ fun y _ c hc => ?_
    · intro a' ha'
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at ha'
      rcases ha' with ha' | rfl
      · exact hb a' ha'
      · exact ⟨x, ha⟩
    · obtain ⟨nx', sn', kp', o'⟩ := c
      dsimp only
      split
      · exact hc
      · exact hc

/-- **The selective worklist keeps only facts the index lists.** -/
theorem selectFrom_about (s : Store) (chain : Bool) :
    ∀ (fuel : Nat) (frontier : List Nat) (seen : Std.HashSet Nat) (kept : Std.HashSet Atom) (out : Array Atom),
      (∀ a ∈ out.toList, ∃ n, a ∈ s.about n) →
      ∀ a ∈ (SinglePass.selectFrom s chain fuel frontier seen kept out).toList, ∃ n, a ∈ s.about n
  | 0, _, _, _, _, h => h
  | fuel + 1, frontier, seen, kept, out, h => by
    unfold SinglePass.selectFrom
    split
    · exact h
    · exact selectFrom_about s chain fuel _ _ _ _ (selectRound_about s chain frontier seen kept out h)

/-- **Every fact the selective worklist returns is listed by the index**
(`SelectedFromIndex`). -/
theorem selectedFromIndex (st : State) (slots : List Nat) (chain : Bool) : SelectedFromIndex st slots chain :=
  selectFrom_about st.store chain _ _ _ _ _ (fun a h => by simp at h)

section Materialize
variable {ι : Type}
open ProgramTyping PositiveGraphs

/-- **The whole materialization holds at the slots**: from the state's
meaning, the knowledge `materialize … true` hands a writing step holds at the
node's environment and heap. -/
theorem stateHolds_materialize_whole {G : NormalGraph ι} {st : State} {implies : List (PromiseCalls.Implication ι)}
    {start : List Nat} {ρ : Env} {m : Nat} {s : IndexedHeap} (hS : StateHolds G st implies start ε ρ m s)
    (d : Nat) (slots : List Nat) (chain : Bool) :
    HeapKnowledge.Holds (SinglePass.materialize st d slots true chain).1 ε ρ s.h := by
  obtain ⟨η, hn, hst, -⟩ := hS
  rw [materialize_eq, selectedAtoms_whole]
  exact materializeFrom_holds hn fun a ha => hst a (toList_storeAll ha)

/-- **The selective materialization holds at the slots**: its facts are
drawn from the index by name (`selectedFromIndex`). -/
theorem stateHolds_materialize {G : NormalGraph ι} {st : State} {implies : List (PromiseCalls.Implication ι)}
    {start : List Nat} {ρ : Env} {m : Nat} {s : IndexedHeap} 
    (hS : StateHolds G st implies start ε ρ m s) (d : Nat) (slots : List Nat) (chain : Bool) :
    HeapKnowledge.Holds (SinglePass.materialize st d slots false chain).1 ε ρ s.h := by
  obtain ⟨η, hn, hst, -⟩ := hS
  rw [materialize_eq]
  refine materializeFrom_holds hn fun a ha => ?_
  obtain ⟨n, hn⟩ := selectedFromIndex st slots chain a ha
  exact hst a (about_storeAll hn)

/-- **The knowledge a step's rule reads holds** (`kE` and, over every fact, `kE'` in
`SinglePass.run`): `KnowledgeExpand.expandLinks` of either materialization at the
node's context, where the environment meets that context. Both hold at
once; so a precondition decided at `kE` holds where the step reads `kE'`. -/
theorem stateHolds_stepKnowledge {G : NormalGraph ι} {Γ : List (Ty ι)} {st : State}
    {implies : List (PromiseCalls.Implication ι)} {start : List Nat} {ρ : Env} {m : Nat} {s : IndexedHeap}
    (hS : StateHolds G st implies start ε ρ m s) (he : EnvOk G Γ ρ s.n s.W)
    (d : Nat) (ms : List Nat) (wholeStep : Bool) :
    HeapKnowledge.Holds (KnowledgeExpand.expandLinks (KnowledgeExpand.ctxOf G Γ)
        (SinglePass.materialize st d ms wholeStep).1) ε ρ s.h ∧
      HeapKnowledge.Holds (KnowledgeExpand.expandLinks (KnowledgeExpand.ctxOf G Γ)
        (SinglePass.materialize st d ms true).1) ε ρ s.h := by
  have hc := KnowledgeExpand.ctxOf_ok he
  refine ⟨KnowledgeExpand.expandLinks_holds hc ?_,
    KnowledgeExpand.expandLinks_holds hc (stateHolds_materialize_whole hS d ms true)⟩
  cases wholeStep with
  | true => exact stateHolds_materialize_whole hS d ms true
  | false => exact stateHolds_materialize hS d ms true

end Materialize

end Verification.TolerantFrames
