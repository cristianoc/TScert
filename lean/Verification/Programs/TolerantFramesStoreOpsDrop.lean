import Verification.Programs.TolerantFramesMergeMirror

/-! # Tolerant frames: forgetting names

`SinglePass.Store.drop s D` forgets the names `D` no slot holds any longer:
it removes the facts naming them, keeps a separation fact's partners outside
`D`, restates a fact of a dropped name an alias link relates to a kept name
at that name, and adds the linear facts the elimination of `D` derives from
the facts over `D` and their neighbours, restated through read links. This
module proves that every fact of the result holds wherever every fact of `s`
holds (`drop_holds`): each added fact is derived from facts of `s`. -/
namespace Verification.TolerantFrames
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification Footprints HeapObservations
open Verification.SinglePass (Atom Store State)

/-! ## Lists without repeats and loops in `Id` -/

theorem keepFirst_foldl_mem {α : Type} [BEq α] [Hashable α] :
    ∀ (l : List α) (acc : Std.HashSet α × Array α) (x : α),
      x ∈ (l.foldl (fun (p : Std.HashSet α × Array α) a =>
        if p.1.contains a then (p.1, p.2) else (p.1.insert a, p.2.push a)) acc).2.toList →
        x ∈ acc.2.toList ∨ x ∈ l
  | [], _, _, hx => .inl hx
  | a :: l, acc, x, hx => by
    rcases keepFirst_foldl_mem l _ x hx with hx | hx
    · dsimp only at hx
      split at hx
      · exact .inl hx
      · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact .inl hx
        · exact .inr (List.mem_cons_self ..)
    · exact .inr (List.mem_cons_of_mem _ hx)

/-- **`keepFirst` keeps only elements of its list.** -/
theorem keepFirst_sub {α : Type} [BEq α] [Hashable α] {seen : Std.HashSet α} {l : List α} {x : α}
    (hx : x ∈ (CertificateProducer.keepFirst seen l).2.toList) : x ∈ l := by
  unfold CertificateProducer.keepFirst at hx
  rcases keepFirst_foldl_mem l (seen, #[]) x (by simpa using hx) with hx | hx
  · simp at hx
  · exact hx

/-- An invariant of a loop's state carried into its continuation (`Id`'s
bind). -/
theorem id_bind_inv {α β : Type} (x : Id α) (f : α → Id β) (P : α → Prop) (Q : β → Prop) (hx : P x)
    (hf : ∀ a, P a → Q (f a)) : Q (x >>= f) := hf x hx

/-! ## The alias map -/

/-- The alias map `drop` builds from its links: each dropped name an alias
link relates to a kept one, sent to that name. -/
def keptAliasOf (isOut : Nat → Bool) (links : HeapLinks.Links) : Std.HashMap Nat Nat :=
  links.foldl (fun acc g =>
    if !g.alias then acc
    else if isOut g.cell && !isOut g.value && !acc.contains g.cell then acc.insert g.cell g.value
    else if isOut g.value && !isOut g.cell && !acc.contains g.value then acc.insert g.value g.cell
    else acc) {}

/-- **The alias map relates names holding one value**, where its links hold. -/
theorem keptAliasOf_eq {isOut : Nat → Bool} {links : HeapLinks.Links} {η : Env} {h : Heap}
    (hl : HeapLinks.Holds links η h) (x : Nat) : η ((keptAliasOf isOut links).getD x x) = η x := by
  suffices H : ∀ (l : HeapLinks.Links) (acc : Std.HashMap Nat Nat), HeapLinks.Holds l η h →
      (∀ x y, acc[x]? = some y → η y = η x) → ∀ x y, (l.foldl (fun acc g =>
        if !g.alias then acc
        else if isOut g.cell && !isOut g.value && !acc.contains g.cell then acc.insert g.cell g.value
        else if isOut g.value && !isOut g.cell && !acc.contains g.value then acc.insert g.value g.cell
        else acc) acc)[x]? = some y → η y = η x by
    rw [Std.HashMap.getD_eq_getD_getElem?]
    cases hx : (keptAliasOf isOut links)[x]? with
    | none => rfl
    | some y => exact H links {} hl (fun x y hy => by simp at hy) x y hx
  intro l
  induction l with
  | nil => intro acc _ hacc; exact hacc
  | cons g l ih =>
    intro acc hl hacc
    have hg := hl g (List.mem_cons_self ..)
    refine ih _ (fun g' hg' => hl g' (List.mem_cons_of_mem _ hg')) ?_
    intro x y hxy
    by_cases ha : g.alias = true
    · simp only [ha, if_true] at hg
      simp only [ha, Bool.not_true, Bool.false_eq_true, if_false] at hxy
      split at hxy
      · rw [Std.HashMap.getElem?_insert] at hxy
        split at hxy
        · rename_i hc; simp only [beq_iff_eq] at hc; subst hc; cases hxy; exact hg.symm
        · exact hacc x y hxy
      · split at hxy
        · rw [Std.HashMap.getElem?_insert] at hxy
          split at hxy
          · rename_i hc; simp only [beq_iff_eq] at hc; subst hc; cases hxy; exact hg
          · exact hacc x y hxy
        · exact hacc x y hxy
    · simp only [Bool.not_eq_true] at ha
      simp only [ha, Bool.not_false, if_true] at hxy
      exact hacc x y hxy

/-! ## The facts `drop` adds -/

/-- The derived facts of `drop`: the elimination of the dropped names from
its index facts restated through its read links, past the index facts
themselves. -/
theorem dropDerived_holds {indices : List HeapKnowledge.IndexAtom} {links : HeapLinks.Links}
    {isOut : Nat → Bool} {D : List Nat} {η : Env} {h : Heap}
    (hi : HeapKnowledge.IndexHolds ε indices η h) (hl : HeapLinks.Holds links η h) :
    HeapKnowledge.IndexHolds ε ((HeapKnowledge.eliminateIndices D (indices ++
      HeapKnowledge.restateReads links isOut indices ++ HeapKnowledge.restateStores links isOut indices)).drop
        indices.length) η h := by
  have hr : HeapKnowledge.IndexHolds ε (indices ++ HeapKnowledge.restateReads links isOut indices ++
      HeapKnowledge.restateStores links isOut indices) η h := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · exact hi a ha
      · exact HeapKnowledge.restateReads_holds hl hi a ha
    · exact HeapKnowledge.restateStores_holds hl hi a ha
  intro a ha
  exact HeapKnowledge.eliminateIndices_holds hr a (List.mem_of_mem_drop ha)

/-- A separation fact with fewer partners holds where the fact does. -/
theorem sep_filter_holds {f : HeapSeparation.Fact} {keep : Nat × List PropKey → Bool} {η : Env} {h : Heap}
    (hf : AtomHolds ε (.sep f) η h) : AtomHolds ε (.sep { f with partners := f.partners.filter keep }) η h :=
  fun p hp g hg => hf p ((List.mem_filter.mp hp).1) g hg

/-- **Forgetting names keeps every fact holding** (`Store.drop`): where every
fact of `s` holds at `η` and `h`, every fact of `s.drop D` does. The removed
facts leave; a separation fact keeps the partners outside `D`; a fact over a
dropped name restated at the name an alias link relates it to holds by the
link; the derived facts hold by `eliminateIndices_holds`, `restateReads_holds`
and `restateStores_holds` over the facts naming `D` and their linear and link
neighbours, all facts of `s`. -/
theorem drop_holds {s : Store} {D : List Nat} {η : Env} {h : Heap} (hs : StoreOk ε s η h) :
    StoreOk ε (s.drop D) η h := by
  unfold Store.drop SinglePass.timedKind
  simp only [Id.run]
  have habout : ∀ (L : List Nat), ∀ a ∈ (CertificateProducer.keepFirst ∅ (L.flatMap s.about)).2.toList,
      AtomHolds ε a η h := by
    intro L a ha
    obtain ⟨n, -, ha⟩ := List.mem_flatMap.mp (keepFirst_sub ha)
    exact hs a (about_storeAll ha)
  generalize (List.foldl (fun x1 x2 => x1.insert x2) (∅ : Std.HashSet Nat) D) = dset
  have hnear := habout
  generalize hA : (CertificateProducer.keepFirst ∅ (List.flatMap s.about D)).snd.toList = atoms
  have hatoms : ∀ a ∈ atoms, AtomHolds ε a η h := hA ▸ habout D
  clear hA habout
  generalize (CertificateProducer.keepFirst ∅ (List.filter (fun x => !dset.contains x)
    (List.flatMap Atom.names atoms))).snd.toList = others
  generalize hN : List.filter _ (CertificateProducer.keepFirst ∅ (List.flatMap s.about others)).snd.toList = near
  have hnear : ∀ a ∈ near, AtomHolds ε a η h := by
    intro a ha; rw [← hN] at ha; exact hnear others a ((List.mem_filter.mp ha).1)
  clear hN
  have hboth : ∀ a ∈ atoms ++ near, AtomHolds ε a η h := fun a ha => by
    rcases List.mem_append.mp ha with ha | ha
    · exact hatoms a ha
    · exact hnear a ha
  have hi : HeapKnowledge.IndexHolds ε ((atoms ++ near).filterMap fun a => match a with
      | .index x => some x | _ => none) η h := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := List.mem_filterMap.mp hx
    rcases a with _ | _ | _ | _ | y | _ <;> simp at hax
    subst hax
    exact hboth _ ha _ (List.mem_singleton_self _)
  have hl : HeapLinks.Holds ((atoms ++ near).filterMap fun a => match a with
      | .link g => some g | _ => none) η h := by
    intro g hg
    obtain ⟨a, ha, hag⟩ := List.mem_filterMap.mp hg
    rcases a with _ | _ | y | _ | _ | _ <;> simp at hag
    subst hag
    exact hboth _ ha _ (List.mem_singleton_self _)
  generalize ((atoms ++ near).filterMap fun a => match a with | .index x => some x | _ => none) = indices at hi ⊢
  generalize ((atoms ++ near).filterMap fun a => match a with | .link g => some g | _ => none) = links at hl ⊢
  have hd := dropDerived_holds (D := D) (isOut := fun n => dset.contains n) hi hl
  generalize (List.drop indices.length (HeapKnowledge.eliminateIndices D (indices ++
    HeapKnowledge.restateReads links (fun n => dset.contains n) indices ++
      HeapKnowledge.restateStores links (fun n => dset.contains n) indices))) = derived at hd ⊢
  have hk := keptAliasOf_eq (isOut := fun n => dset.contains n) hl
  unfold keptAliasOf at hk
  generalize (List.foldl _ (∅ : Std.HashMap Nat Nat) links) = keptAlias at hk ⊢
  split
  · exact hs
  split
  · exact hs
  have h0 := foldl_remove_ok atoms s hs
  refine id_bind_inv _ _ (fun st => StoreOk ε st η h) (fun st => StoreOk ε st η h) (forIn_inv (P := fun st => StoreOk ε st η h) _ _ _ h0 ?_) ?_
  · intro a ha b hb
    split
    · rename_i f
      split
      · split
        · exact add_ok hb (sep_filter_holds (hatoms _ ha))
        · exact hb
      · exact hb
    · exact hb
  intro b hb
  have hlast : ∀ b, StoreOk ε b η h → StoreOk ε (forIn derived b fun x r =>
      if (Atom.index x).names.all (fun x => !dset.contains x) = true then ForInStep.yield (r.add (Atom.index x))
      else ForInStep.yield r : Id Store) η h := by
    intro b hb
    refine forIn_inv (P := fun st => StoreOk ε st η h) _ _ _ hb fun x hx b hb => ?_
    split
    · exact add_ok hb (fun y hy => (List.mem_singleton.mp hy) ▸ hd x hx)
    · exact hb
  split
  · refine id_bind_inv _ _ (fun st => StoreOk ε st η h) (fun st => StoreOk ε st η h) (forIn_inv (P := fun st => StoreOk ε st η h) _ _ _ hb ?_) (fun b hb => hlast b hb)
    intro a ha b hb
    split
    · rename_i b' hb'
      split
      · exact add_ok hb (atomHolds_rename (fun x i hxi => by cases hxi; exact hk x) hb' (hatoms a ha))
      · exact hb
    · exact hb
  · exact hlast b hb

/-- **Forgetting names keeps the store well-formed** (`Store.drop`): it
only removes and adds (`remove_wf`, `add_wf`). -/
theorem drop_wf {s : Store} (w : StoreWF s) (D : List Nat) : StoreWF (s.drop D) := by
  unfold Store.drop SinglePass.timedKind
  simp only [Id.run]
  split
  · exact w
  split
  · exact w
  refine id_bind_inv _ _ StoreWF StoreWF (forIn_inv (P := StoreWF) _ _ _ (foldl_remove_wf _ _ w) ?_) ?_
  · intro a _ b hb
    split
    · split
      · split
        · exact add_wf hb _
        · exact hb
      · exact hb
    · exact hb
  intro b hb
  have hlast : ∀ b, StoreWF b → ∀ x (b' : Store), StoreWF b' →
      StoreWF ((if ((Atom.index x).names.all fun y => !(List.foldl (fun x1 x2 => x1.insert x2)
        (∅ : Std.HashSet Nat) D).contains y) = true then
        pure (ForInStep.yield (b'.add (Atom.index x))) else pure (ForInStep.yield b') : Id (ForInStep Store))).value :=
    fun _ _ x b' hb => by split; exact add_wf hb _; exact hb
  split
  · refine id_bind_inv _ _ StoreWF StoreWF (forIn_inv (P := StoreWF) _ _ _ hb ?_) (fun b hb => id_bind_inv _ _ StoreWF StoreWF (forIn_inv (P := StoreWF) _ _ _ hb fun x _ b' hb' => hlast b hb x b' hb') (fun _ h => h))
    intro a _ b hb
    split
    · split
      · exact add_wf hb _
      · exact hb
    · exact hb
  · exact id_bind_inv _ _ StoreWF StoreWF (forIn_inv (P := StoreWF) _ _ _ hb fun x _ b' hb' => hlast b hb x b' hb') (fun _ h => h)

end Verification.TolerantFrames
