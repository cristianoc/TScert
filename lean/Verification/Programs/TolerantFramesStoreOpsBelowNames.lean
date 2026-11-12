import Verification.Programs.TolerantFramesStoreOpsNames

/-! # Tolerant frames: the store operations keep the facts' names below the counter

`Store.drop`, the delta, an edge's store and transfer and a head's entry keep
every stored fact's names below the pass's counter where their inputs' are:
the facts they add are renamed by maps into names below it, or derived by
the eliminations, which name their inputs' names
(`TolerantFramesStoreOpsNames`). -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations HeapKnowledge PositiveGraphs
open Verification.SinglePass (Atom Store State)

/-! ## Forgetting names keeps the facts' names below the counter -/

/-- Every name a fact states is below `next`. -/
def AtomBelow (next : Nat) (a : Atom) : Prop := ∀ x ∈ a.names, x < next

theorem linkNamed_below {ls : HeapLinks.Links} {next : Nat} (hl : ∀ g ∈ ls, AtomBelow next (.link g)) {x : Nat}
    (hx : LinkNamed ls x) : x < next := by
  obtain ⟨g, hg, rfl | rfl⟩ := hx
  · exact hl g hg _ (by simp [Atom.names])
  · exact hl g hg _ (by simp [Atom.names])

theorem namedIn_below {as : List IndexAtom} {next : Nat} (ha : ∀ a ∈ as, AtomBelow next (.index a)) {x : Nat}
    (hx : NamedIn as x) : x < next := by
  obtain ⟨a, ha', hx⟩ := hx
  exact ha a ha' x hx

/-- **The facts `drop` derives name below the counter** where its index
facts and links do: the eliminations name their inputs' names
(`eliminateIndices_named`) and the restatements their inputs' names or a
link's (`restateReads_named`, `restateStores_named`). -/
theorem dropDerived_below {indices : List IndexAtom} {links : HeapLinks.Links} {isOut : Nat → Bool} {D : List Nat}
    {next : Nat} (hi : ∀ a ∈ indices, AtomBelow next (.index a)) (hl : ∀ g ∈ links, AtomBelow next (.link g)) :
    ∀ b ∈ (eliminateIndices D (indices ++ restateReads links isOut indices ++
      restateStores links isOut indices)).drop indices.length, AtomBelow next (.index b) := by
  intro b hb x hx
  have hr := eliminateIndices_named (List.mem_of_mem_drop hb) hx
  rcases namedIn_append.mp hr with hr | ⟨c, hc, hxc⟩
  · rcases namedIn_append.mp hr with hr | ⟨c, hc, hxc⟩
    · exact namedIn_below hi hr
    · rcases restateReads_named hc hxc with h | h
      · exact namedIn_below hi h
      · exact linkNamed_below hl h
  · rcases restateStores_named hc hxc with h | h
    · exact namedIn_below hi h
    · exact linkNamed_below hl h

/-- **The alias map sends a name to a name its links state.** -/
theorem keptAliasOf_named {isOut : Nat → Bool} {links : HeapLinks.Links} (x : Nat) :
    (keptAliasOf isOut links).getD x x = x ∨ LinkNamed links ((keptAliasOf isOut links).getD x x) := by
  suffices H : ∀ (l : HeapLinks.Links) (acc : Std.HashMap Nat Nat), (∀ x y, acc[x]? = some y → LinkNamed links y) →
      (∀ g ∈ l, g ∈ links) → ∀ x y, (l.foldl (fun acc g =>
        if !g.alias then acc
        else if isOut g.cell && !isOut g.value && !acc.contains g.cell then acc.insert g.cell g.value
        else if isOut g.value && !isOut g.cell && !acc.contains g.value then acc.insert g.value g.cell
        else acc) acc)[x]? = some y → LinkNamed links y by
    rw [Std.HashMap.getD_eq_getD_getElem?]
    cases hx : (keptAliasOf isOut links)[x]? with
    | none => exact .inl rfl
    | some y => exact .inr (H links ∅ (fun x y hy => by rw [Std.HashMap.getElem?_empty] at hy; cases hy) (fun _ h => h) x y hx)
  intro l
  induction l with
  | nil => intro acc hacc _; exact hacc
  | cons g l ih =>
    intro acc hacc hsub
    have hg := hsub g (List.mem_cons_self ..)
    refine ih _ ?_ (fun g' hg' => hsub g' (List.mem_cons_of_mem _ hg'))
    intro x y hxy
    dsimp only at hxy
    split at hxy
    · exact hacc x y hxy
    · split at hxy
      · rw [Std.HashMap.getElem?_insert] at hxy
        split at hxy
        · cases hxy; exact ⟨g, hg, .inr rfl⟩
        · exact hacc x y hxy
      · split at hxy
        · rw [Std.HashMap.getElem?_insert] at hxy
          split at hxy
          · cases hxy; exact ⟨g, hg, .inl rfl⟩
          · exact hacc x y hxy
        · exact hacc x y hxy

/-- **Forgetting names keeps every fact's names below the counter**
(`Store.drop`): the removed facts leave; a separation fact keeps fewer
partners; a fact restated at an alias names a link's names; the derived
facts name the names of the store's facts (`dropDerived_below`). -/
theorem drop_below {s : Store} {D : List Nat} {next : Nat} (hs : FactsBelow s next) :
    FactsBelow (s.drop D) next := by
  unfold Store.drop SinglePass.timedKind
  simp only [Id.run]
  have habout : ∀ (L : List Nat), ∀ a ∈ (CertificateProducer.keepFirst ∅ (L.flatMap s.about)).2.toList,
      AtomBelow next a := by
    intro L a ha
    obtain ⟨n, -, ha⟩ := List.mem_flatMap.mp (keepFirst_sub ha)
    exact hs a (about_storeAll ha)
  generalize (List.foldl (fun x1 x2 => x1.insert x2) (∅ : Std.HashSet Nat) D) = dset
  have hnear := habout
  generalize hA : (CertificateProducer.keepFirst ∅ (List.flatMap s.about D)).snd.toList = atoms
  have hatoms : ∀ a ∈ atoms, AtomBelow next a := hA ▸ habout D
  clear hA habout
  generalize (CertificateProducer.keepFirst ∅ (List.filter (fun x => !dset.contains x)
    (List.flatMap Atom.names atoms))).snd.toList = others
  generalize hN : List.filter _ (CertificateProducer.keepFirst ∅ (List.flatMap s.about others)).snd.toList = near
  have hnear : ∀ a ∈ near, AtomBelow next a := by
    intro a ha; rw [← hN] at ha; exact hnear others a ((List.mem_filter.mp ha).1)
  clear hN
  have hboth : ∀ a ∈ atoms ++ near, AtomBelow next a := fun a ha => by
    rcases List.mem_append.mp ha with ha | ha
    · exact hatoms a ha
    · exact hnear a ha
  have hi : ∀ x ∈ ((atoms ++ near).filterMap fun a => match a with
      | .index x => some x | _ => none), AtomBelow next (.index x) := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := List.mem_filterMap.mp hx
    rcases a with _ | _ | _ | _ | y | _ <;> simp at hax
    subst hax
    exact hboth _ ha
  have hl : ∀ g ∈ ((atoms ++ near).filterMap fun a => match a with
      | .link g => some g | _ => none), AtomBelow next (.link g) := by
    intro g hg
    obtain ⟨a, ha, hag⟩ := List.mem_filterMap.mp hg
    rcases a with _ | _ | y | _ | _ | _ <;> simp at hag
    subst hag
    exact hboth _ ha
  generalize ((atoms ++ near).filterMap fun a => match a with | .index x => some x | _ => none) = indices at hi ⊢
  generalize ((atoms ++ near).filterMap fun a => match a with | .link g => some g | _ => none) = links at hl ⊢
  have hd := dropDerived_below (D := D) (isOut := fun n => dset.contains n) hi hl
  generalize (List.drop indices.length (HeapKnowledge.eliminateIndices D (indices ++
    HeapKnowledge.restateReads links (fun n => dset.contains n) indices ++
      HeapKnowledge.restateStores links (fun n => dset.contains n) indices))) = derived at hd ⊢
  have hk := keptAliasOf_named (isOut := fun n => dset.contains n) (links := links)
  unfold keptAliasOf at hk
  generalize (List.foldl _ (∅ : Std.HashMap Nat Nat) links) = keptAlias at hk ⊢
  split
  · exact hs
  split
  · exact hs
  have h0 := foldl_remove_below (next := next) atoms s hs
  refine id_bind_inv _ _ (fun st => FactsBelow st next) (fun st => FactsBelow st next)
    (forIn_inv (P := fun st => FactsBelow st next) _ _ _ h0 ?_) ?_
  · intro a ha b hb
    split
    · rename_i f
      split
      · split
        · refine add_below hb fun x hx => hatoms _ ha x ?_
          simp only [Atom.names, List.mem_cons, List.mem_map] at hx ⊢
          rcases hx with rfl | ⟨p, hp, rfl⟩
          · exact .inl rfl
          · exact .inr ⟨p, (List.mem_filter.mp hp).1, rfl⟩
        · exact hb
      · exact hb
    · exact hb
  intro b hb
  have hlast : ∀ b, FactsBelow b next → FactsBelow (forIn derived b fun x r =>
      if (Atom.index x).names.all (fun x => !dset.contains x) = true then ForInStep.yield (r.add (Atom.index x))
      else ForInStep.yield r : Id Store) next := by
    intro b hb
    refine forIn_inv (P := fun st => FactsBelow st next) _ _ _ hb fun x hx b hb => ?_
    split
    · exact add_below hb (hd x hx)
    · exact hb
  split
  · refine id_bind_inv _ _ (fun st => FactsBelow st next) (fun st => FactsBelow st next)
      (forIn_inv (P := fun st => FactsBelow st next) _ _ _ hb ?_) (fun b hb => hlast b hb)
    intro a ha b hb
    split
    · rename_i b' hb'
      split
      · refine add_below hb fun y hy => ?_
        obtain ⟨x, hx, e⟩ := atom_rename_names hb' y hy
        cases e
        rcases hk x with e | e
        · rw [e]; exact hatoms a ha x hx
        · exact linkNamed_below hl e
      · exact hb
    · exact hb
  · exact hlast b hb

/-! ## The delta keeps the facts' names below the counter -/

/-- `back` renames into names below `next`. -/
def BackBelow (back : Nat → Option Nat) (next : Nat) : Prop := ∀ i j, back i = some j → j < next

theorem deltaRemove_below {s : Store} {next : Nat} (hs : FactsBelow s next) (pairs : List (Atom × Atom))
    (out : HeapKnowledge.Knowledge) (shift : Bool) : FactsBelow (deltaRemove s pairs out shift) next :=
  fun a ha => hs a (deltaRemove_sub a ha)

theorem deltaAdd_below {s : Store} {next : Nat} (hs : FactsBelow s next) (pairs : List (Atom × Atom))
    (out : HeapKnowledge.Knowledge) (shift : Bool) {back : Nat → Option Nat} (hb : BackBelow back next) :
    FactsBelow (deltaAdd s pairs out shift back).1 next ∧
      ∀ x ∈ (deltaAdd s pairs out shift back).2, AtomBelow next (.index x) := by
  unfold deltaAdd
  simp only [Id.run]
  refine forIn_inv_bind (R := fun (r : Store × List HeapKnowledge.IndexAtom) =>
      FactsBelow r.1 next ∧ ∀ x ∈ r.2, AtomBelow next (.index x))
    (SinglePass.atomsOf out) (s, []) _ (fun r => FactsBelow r.1 next ∧ ∀ x ∈ r.2, AtomBelow next (.index x)) _
    ⟨hs, by simp⟩ ?_ (fun _ h => h)
  intro o _ r hr
  have hab : ∀ a, o.rename back = some a → AtomBelow next a := fun a ha y hy => by
    obtain ⟨x, -, e⟩ := atom_rename_names ha y hy; exact hb x y e
  repeat' split
  all_goals first
    | contradiction
    | exact hr
    | refine ⟨?_, ?_⟩
  all_goals first
    | contradiction
    | exact hr.1
    | exact hr.2
    | exact add_below hr.1 (hab _ (by assumption))
    | (intro x hx
       rcases List.mem_cons.mp hx with rfl | hx
       · exact hab _ (by assumption)
       · exact hr.2 x hx)

theorem deltaRestate_below {s : Store} {next : Nat} (hs : FactsBelow s next) {added : List HeapKnowledge.IndexAtom}
    (ha : ∀ x ∈ added, AtomBelow next (.index x)) : FactsBelow (deltaRestate s added) next := by
  unfold deltaRestate
  simp only [Id.run]
  refine forIn_inv_bind (R := fun t => FactsBelow t next) added s _ (fun t => FactsBelow t next) _ hs ?_ (fun _ h => h)
  intro x hx t ht
  show FactsBelow (forIn (m := Id) x.fact.slots t _) next
  refine forIn_inv _ _ _ (fun t => FactsBelow t next) ht ?_
  intro v _ u hu
  split
  · show FactsBelow (forIn (m := Id) _ u _) next
    have hl : ∀ g ∈ (u.about v).filterMap (fun b => match b with
        | .link g => if !g.alias && g.value == v then some g else none
        | _ => none), AtomBelow next (.link g) := by
      intro g hg
      obtain ⟨b, hb, hbg⟩ := List.mem_filterMap.mp hg
      split at hbg
      · split at hbg
        · cases hbg; exact hu _ (about_storeAll hb)
        · cases hbg
      · cases hbg
    refine forIn_inv _ _ _ (fun t => FactsBelow t next) hu fun y hy w' hw => add_below hw fun z hz => ?_
    rcases restateReads_named hy hz with h | h
    · exact namedIn_below (fun a ha' => by rw [List.mem_singleton.mp ha']; exact ha x hx) h
    · exact linkNamed_below hl h
  · exact hu

/-- **The delta keeps every fact's names below the counter** where `back`
renames into names below it: the removal loop removes, the additions name
`back`'s images, the restatements those and a stored link's names. -/
theorem applyDelta_below {s : Store} {next : Nat} (hs : FactsBelow s next) (pairs : List (Atom × Atom))
    (out : HeapKnowledge.Knowledge) (shift : Bool) {back : Nat → Option Nat} (hb : BackBelow back next) :
    FactsBelow (SinglePass.applyDelta s pairs out shift back) next := by
  rw [applyDelta_eq]
  have h := deltaAdd_below (deltaRemove_below hs pairs out shift) pairs out shift hb
  exact deltaRestate_below h.1 h.2

/-! ## An edge's store and transfer keep the names below the counter -/

/-- The keys of a table are among `names`. -/
def KeysIn (names : List Nat) (t : Std.HashMap Nat Nat) : Prop := ∀ n i, t[n]? = some i → n ∈ names
theorem keysIn_insert {names : List Nat} {t : Std.HashMap Nat Nat} {x : Nat} (j : Nat) (ht : KeysIn names t)
    (hx : x ∈ names) : KeysIn names (t.insert x j) := by
  intro m k hm
  rw [Std.HashMap.getElem?_insert] at hm
  split at hm
  · rename_i e; simp only [beq_iff_eq] at e; exact e ▸ hx
  · exact ht m k hm
theorem slotTable_keys {names : List Nat} {want : Std.HashSet Nat} {whole : Bool} :
    KeysIn names (SinglePass.slotTable names want whole) := by
  unfold SinglePass.slotTable
  simp only [Id.run]
  refine forIn_inv_bind (R := KeysIn names) names
    ((none, ∅, 0, 0) : Option (Std.HashMap Nat Nat) × Std.HashMap Nat Nat × Nat × Nat) _
    (fun (st : Option (Std.HashMap Nat Nat) × Std.HashMap Nat Nat × Nat × Nat) =>
      (∀ r, st.1 = some r → KeysIn names r) ∧ KeysIn names st.2.1) _ ?_ ?_ ?_
  · refine ⟨fun r h => (by simp at h), fun m k hm => ?_⟩
    rw [Std.HashMap.getElem?_empty] at hm; cases hm
  · intro x hx st hst
    repeat' split
    all_goals refine ⟨fun r h => ?_, ?_⟩
    all_goals simp only [pure, ForInStep.value, Option.some.injEq, reduceCtorEq] at *
    all_goals first
      | exact hst.2
      | exact keysIn_insert _ hst.2 hx
      | exact h ▸ keysIn_insert _ hst.2 hx
  · intro st hst
    split
    · rename_i r hr; exact hst.1 r hr
    · exact hst.2

/-- **`materialize`'s table names the state's slot names.** -/
theorem materialize_table_keys (st : State) (d : Nat) (slots : List Nat) (whole chain : Bool) :
    KeysIn st.names (SinglePass.materialize st d slots whole chain).2.2 := by
  unfold SinglePass.materialize SinglePass.timedKind
  exact slotTable_keys

/-- The inverse of a table sends a slot to a key of the table. -/
theorem inverse_keys {names : List Nat} {table : Std.HashMap Nat Nat} (ht : KeysIn names table) :
    ∀ i nm, (table.fold (fun acc nm s => acc.insert s nm) (∅ : Std.HashMap Nat Nat)).get? i = some nm →
      nm ∈ names := by
  rw [Std.HashMap.fold_eq_foldl_toList]
  suffices H : ∀ (l : List (Nat × Nat)) (acc : Std.HashMap Nat Nat), (∀ p ∈ l, p ∈ table.toList) →
      (∀ i nm, acc[i]? = some nm → nm ∈ names) →
      ∀ i nm, (l.foldl (fun acc p => acc.insert p.2 p.1) acc)[i]? = some nm → nm ∈ names by
    intro i nm h
    rw [Std.HashMap.get?_eq_getElem?] at h
    exact H _ ∅ (fun _ h => h) (fun i nm h => by rw [Std.HashMap.getElem?_empty] at h; cases h) i nm h
  intro l
  induction l with
  | nil => intro acc _ hacc; exact hacc
  | cons p l ih =>
    intro acc hl hacc
    refine ih _ (fun q hq => hl q (List.mem_cons_of_mem _ hq)) ?_
    intro i nm h
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · cases h
      have hp := hl p (List.mem_cons_self ..)
      exact ht p.1 p.2 (Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hp)
    · exact hacc i nm h

theorem dropHeap_below {s : Store} {next : Nat} (w : StoreWF s) (hs : FactsBelow s next) (keep : Atom → Bool) :
    FactsBelow (s.dropHeap keep) next :=
  fun a ha => hs a ((dropHeap_cover w keep).2 a ha).1

theorem back_below {names : List Nat} {next : Nat} (hn : ∀ x ∈ names, x < next) {table : Std.HashMap Nat Nat}
    (ht : KeysIn names table) :
    BackBelow (fun i => ((table.fold (fun acc nm s => acc.insert s nm) (∅ : Std.HashMap Nat Nat)).get? i).orElse
      fun _ => names[i]?) next := by
  intro i j h
  dsimp only at h
  cases hi : (table.fold (fun acc nm s => acc.insert s nm) (∅ : Std.HashMap Nat Nat)).get? i with
  | some nm =>
    rw [hi] at h; cases h
    exact hn _ (inverse_keys ht i _ hi)
  | none =>
    rw [hi] at h
    exact hn _ (List.mem_of_getElem? h)

variable {ι : Type}

/-- **An edge's store keeps the facts' names below the counter** where the
entry store, the output store and the source's slot names are below it. -/
theorem edgeStoreOf_below {G : NormalGraph ι} {Γ : List (ProgramTyping.Ty ι)} {entryStore store : Store}
    {next : Nat} (we : StoreWF entryStore) (he : FactsBelow entryStore next) (hs : FactsBelow store next)
    {names pushedNames : List Nat} (hn : ∀ x ∈ names, x < next) (hp : ∀ x ∈ pushedNames, x < next) (width : Nat)
    (pushed isHandler : Bool) (observed : Option BranchRefinement.Observation) (promote : Option Bool) :
    FactsBelow (SinglePass.edgeStoreOf G Γ entryStore store names pushedNames width pushed isHandler observed promote)
      next := by
  unfold SinglePass.edgeStoreOf
  split
  · exact dropHeap_below we he _
  · split
    · have ht := materialize_table_keys { names, store } (if pushed then width + 1 else width) [0] false true
      generalize SinglePass.materialize { names, store } (if pushed then width + 1 else width) [0] false = M at ht ⊢
      obtain ⟨k, pairs, table⟩ := M
      exact applyDelta_below hs _ _ _ (back_below hn ht)
    · have ht := materialize_table_keys { names := pushedNames, store } (width + 1) [0] false true
      generalize SinglePass.materialize { names := pushedNames, store } (width + 1) [0] false = M at ht ⊢
      obtain ⟨k, pairs, table⟩ := M
      exact applyDelta_below hs _ _ _ (back_below hp ht)
    · exact hs

/-- A cursor reads only elements of its list. -/
theorem cursor_get_mem {α : Type} {c : SinglePass.Cursor α} (hc : ∀ x ∈ c.rest, x ∈ c.all) (i : Nat) :
    (∀ x, (c.get i).1 = some x → x ∈ c.all) ∧ (c.get i).2.all = c.all ∧ ∀ x ∈ (c.get i).2.rest, x ∈ c.all := by
  unfold SinglePass.Cursor.get
  split
  · refine ⟨fun x hx => hc x (List.mem_of_mem_drop (List.mem_of_mem_head? hx)), rfl,
      fun x hx => hc x (List.mem_of_mem_drop hx)⟩
  · exact ⟨fun x hx => List.mem_of_mem_drop (List.mem_of_mem_head? hx), rfl, fun x hx => List.mem_of_mem_drop hx⟩

/-- **A target's names are the source's or 0** (`mapNames`): each read slot
gives a source name, an unread one 0. -/
theorem mapNames_mem {names : List Nat} {m : PointClaims.Mapping} {x : Nat} (hx : x ∈ SinglePass.mapNames names m) :
    x ∈ names ∨ x = 0 := by
  cases m with
  | none => exact .inl hx
  | some slots =>
    unfold SinglePass.mapNames at hx
    simp only [Id.run] at hx
    revert hx
    refine forIn_inv_bind (R := fun (l : List Nat) => x ∈ l → x ∈ names ∨ x = 0)
      (List.take (SinglePass.orderedSuffix slots names.length) slots)
      ((SinglePass.Cursor.of names, Array.mkEmpty (SinglePass.orderedSuffix slots names.length)) :
        SinglePass.Cursor Nat × Array Nat) _
      (fun (r : SinglePass.Cursor Nat × Array Nat) => r.1.all = names ∧ (∀ y ∈ r.1.rest, y ∈ r.1.all) ∧
        ∀ y ∈ r.2.toList, y ∈ names ∨ y = 0) _
      ⟨rfl, fun y hy => hy, by simp⟩ ?_ ?_
    · intro s _ r hr
      obtain ⟨hall, hrest, hout⟩ := hr
      obtain ⟨h1, h2, h3⟩ := cursor_get_mem hrest s
      refine ⟨h2.trans hall, fun y hy => (show y ∈ (r.fst.get s).snd.all from h2 ▸ h3 y hy), fun y hy => ?_⟩
      simp only [pure, ForInStep.value, Array.toList_push, List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · exact hout y hy
      · cases hg : (r.1.get s).1 with
        | none => exact .inr rfl
        | some z => exact .inl (hall ▸ h1 z hg)
    · intro r hr hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hr.2.2 x hx
      · split at hx
        · exact .inl (List.mem_of_mem_drop hx)
        · cases hx

/-- **An edge's transfer keeps the state below the counter** where the
source's names, the edge's store, the entry's fresh names and the result
are, and the counter is positive (an unread target slot is named 0). -/
theorem edgeTransfer_below [DecidableEq ι] [Hashable ι] {names : List Nat} {m : PointClaims.Mapping}
    {pushed isHandler outFresh : Bool} {entry : State} {result : Nat} {edgeStore : Store}
    {implies : List (PromiseCalls.Implication ι)} {next : Nat} (hpos : 0 < next) (hn : ∀ x ∈ names, x < next)
    (hs : FactsBelow edgeStore next) (hf : ∀ x ∈ entry.fresh, x < next) (hr : result < next) :
    StateBelow (SinglePass.edgeTransfer names m pushed isHandler outFresh entry result edgeStore implies).1 next := by
  refine ⟨fun x hx => ?_, drop_below hs, fun x hx => ?_⟩
  · rcases mapNames_mem hx with hx | rfl
    · exact hn x hx
    · exact hpos
  · simp only [SinglePass.edgeTransfer, SinglePass.timedKind, List.mem_filter] at hx
    have hx := hx.1
    split at hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hr
      · exact hf x hx
    · exact hf x hx

theorem empty_below (next : Nat) : FactsBelow ({} : Store) next := by
  intro a ha
  simp [storeAll, Store.toList, valsOf] at ha

/-- **A head's entry state is below its counter** where the start names, the
promised input's name and the slots' own names `i + base` are: its store's
facts are renamed to the slots' names. -/
theorem headEntry_below {g : HeapKnowledge.Knowledge} {isStart : Bool} {width fresh : Nat} {startNames : List Nat}
    {argName : Option Nat} {argSlots : List Nat} {inputSlots : List (Nat × Nat)}
    {implies : List (PromiseCalls.Implication ι)} {N : Nat}
    (hN : N = (SinglePass.headEntry g isStart width fresh startNames argName argSlots inputSlots implies).2.2)
    (hstart : ∀ x ∈ startNames, x < N) (harg : ∀ a, argName = some a → a < N)
    (hbase : ∀ i < width, i + (if isStart then startNames.headD 0 else fresh) < N) :
    StateBelow (SinglePass.headEntry g isStart width fresh startNames argName argSlots inputSlots implies).1 N := by
  have hnames : ∀ x ∈ (SinglePass.headEntry g isStart width fresh startNames argName argSlots inputSlots implies).1.names,
      x < N := by
    intro x hx
    simp only [SinglePass.headEntry, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, hx⟩ := hx
    split at hx
    · rename_i y hy
      subst hx
      obtain ⟨⟨j, q⟩, -, hq⟩ := Option.bind_eq_some_iff.mp hy
      exact hstart _ (List.mem_of_getElem? hq)
    · split at hx
      · split at hx
        · subst hx; exact harg _ rfl
        · subst hx; exact hbase i hi
      · subst hx; exact hbase i hi
  refine ⟨hnames, ?_, fun x hx => by simp [SinglePass.headEntry] at hx⟩
  have key : ∀ (l : List Atom) (st : Store), FactsBelow st N → FactsBelow (l.foldl (fun s a =>
      match a.rename fun i => (SinglePass.headEntry g isStart width fresh startNames argName argSlots
        inputSlots implies).1.names[i]? with
      | some b => s.add b | none => s) st) N := by
    intro l
    induction l with
    | nil => intro st h; exact h
    | cons a l ih =>
      intro st h
      refine ih _ ?_
      dsimp only
      split
      · rename_i b hb
        refine add_below h fun y hy => ?_
        obtain ⟨x, -, e⟩ := atom_rename_names hb y hy
        exact hnames y (List.mem_of_getElem? e)
      · exact h
  exact key _ _ (empty_below N)

end Verification.TolerantFrames
