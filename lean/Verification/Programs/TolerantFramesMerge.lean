import Verification.Programs.TolerantFramesEntry

/-! # Tolerant frames: a merge's equalities

At a merge (`SinglePass.mergeState`) a slot whose predecessors' names differ
takes a fresh name `φ`, and each predecessor renames its name `x` there to
`φ`. Restating a predecessor's facts at the fresh names, the merge states
`φ` equal to `x` where a slot keeps `x`, and one name's fresh names equal:
by an alias link always, and by two linear facts `k(φ) - k(x) ≤ 0`,
`k(x) - k(φ) ≤ 0` for every root term kind `k` the predecessor's unconditional
facts witness as defined on `x` (`Store.definedKinds`). This module proves
those facts hold at a predecessor's valuation extended to the fresh names by
its own names' values. -/
namespace Verification.TolerantFrames
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification Footprints HeapObservations
open Verification.SinglePass (Atom Store State)

theorem index_int {x : UInt64} {i : Nat} (h : indexOfBits x = some i) : (HeapKnowledge.intValue (.num x)).isSome := by
  rw [HeapKnowledge.intValue_num (IndexWrites.index_safeInt h)]; rfl

/-! ## The store's defined term kinds -/

/-- **`Store.definedKinds` is sound**: where every fact of the store holds at
`η`, every root term kind the store's unconditional facts witness on `x`
denotes an integer at `η x` (`HeapKnowledge.kindValue`). -/
theorem definedKinds_some {s : Store} {η : Env} {h : Heap} (hS : StoreOk ε s η h) {x : Nat}
    {k : HeapKnowledge.Term.Kind} (hk : k ∈ s.definedKinds x) :
    (HeapKnowledge.kindValue h k (η x)).isSome := by
  have hk' := List.mem_eraseDups.mp hk
  obtain ⟨a, ha, hp⟩ := List.mem_flatMap.mp hk'
  have hh := hS a (about_storeAll ha)
  cases a with
  | index ia =>
    obtain ⟨f, c, neg⟩ := ia
    cases c with
    | some _ => simp at hp
    | none =>
      have hf : f.HoldsAt ε η h := hh _ (List.mem_singleton_self _) (fun b hb => by cases hb)
      cases f with
      | int y =>
        dsimp only at hp
        split at hp
        · rename_i hy
          simp only [beq_iff_eq] at hy; subst hy
          simp only [List.mem_singleton] at hp; subst hp
          exact hf
        · cases hp
      | index y =>
        dsimp only at hp
        split at hp
        · rename_i hy
          simp only [beq_iff_eq] at hy; subst hy
          simp only [List.mem_singleton] at hp; subst hp
          obtain ⟨b, i, hb, hib⟩ := hf
          rw [HeapKnowledge.kindValue, hb]; exact index_int hib
        · cases hp
      | bound y yk st =>
        dsimp only at hp
        split at hp
        · rename_i hyk
          simp only [beq_iff_eq] at hyk; subst hyk
          simp only [List.mem_singleton] at hp; subst hp
          obtain ⟨_, _, b, i, _, _, hb, hib, _⟩ := hf
          rw [HeapKnowledge.kindValue, hb]; exact index_int hib
        · cases hp
      | length y yk =>
        dsimp only at hp
        rcases List.mem_append.mp hp with hp1 | hp2
        · split at hp1
          · rename_i hy
            simp only [beq_iff_eq] at hy; subst hy
            simp only [List.mem_singleton] at hp1; subst hp1
            obtain ⟨sp, ls, hsp, hls, _, hm⟩ := hf
            rw [HeapKnowledge.kindValue, HeapKnowledge.lengthOf_of_spine hsp hls hm]; rfl
          · cases hp1
        · split at hp2
          · rename_i hyk
            simp only [beq_iff_eq] at hyk; subst hyk
            simp only [List.mem_singleton] at hp2; subst hp2
            obtain ⟨_, ls, _, _, hk', hm⟩ := hf
            rw [HeapKnowledge.kindValue, hk', HeapKnowledge.intValue_length hm]; rfl
          · cases hp2
      | linear F =>
        obtain ⟨t, ht, htk⟩ := List.mem_filterMap.mp hp
        split at htk
        · rename_i hcond
          cases htk
          simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.isEmpty_iff] at hcond
          obtain ⟨⟨he, hs⟩, hpath⟩ := hcond
          have hdef := hf.1 t ht
          have ht_eq : t = HeapKnowledge.Term.now t.kind x [] := by
            rw [HeapKnowledge.Term.eq_now he, hs, hpath]
          rw [ht_eq, HeapKnowledge.termValue_nil] at hdef
          exact hdef
        · cases htk
      | _ => simp at hp
  | cell _ | value _ | link _ | elem _ | sep _ => simp at hp

/-! ## The merge's equalities -/

/-- A merge's facts stating the fresh name `φ` equal to `x`
(`SinglePass.mergeState`'s `eqAtoms`): the alias link, and for each kind
`k ∈ kinds` the two linear facts stating `k(φ) = k(x)`. -/
def mergeEqAtoms (kinds : List HeapKnowledge.Term.Kind) (φ x : Nat) : List Atom :=
  Atom.link { cell := φ, value := x, alias := true } ::
    kinds.flatMap fun k =>
      [.index ⟨.linear (.le [(HeapKnowledge.Term.now k φ [], 1), (HeapKnowledge.Term.now k x [], -1)] 0), none, false⟩,
       .index ⟨.linear (.le [(HeapKnowledge.Term.now k φ [], -1), (HeapKnowledge.Term.now k x [], 1)] 0), none, false⟩]

/-- **A merge's equality holds**: at a valuation under which `φ` and `x`
hold one value, the alias link holds, and for every kind `k ∈ kinds` defined
at `η x` the two linear facts for `k` too. -/
theorem mergeEqAtoms_holds {kinds : List HeapKnowledge.Term.Kind} {φ x : Nat} {η : Env} {h : Heap}
    (heq : η φ = η x)
    (hkinds : ∀ k ∈ kinds, (HeapKnowledge.kindValue h k (η x)).isSome) :
    ∀ a ∈ mergeEqAtoms kinds φ x, AtomHolds ε a η h := by
  intro a ha
  simp only [mergeEqAtoms, List.mem_cons] at ha
  rcases ha with rfl | ha
  · intro g hg
    simp only [List.mem_singleton] at hg; subst hg
    simpa using heq
  · obtain ⟨k, hk, ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hkinds k hk)
    have htv : ∀ y, η y = η x → HeapKnowledge.termValue ε η h (.now k y []) = some v := by
      intro y hy; rw [HeapKnowledge.termValue_nil, hy, hv]
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl <;>
    · intro y hy _
      simp only [List.mem_singleton] at hy; subst hy
      refine ⟨fun t ht => ?_, ?_⟩
      · simp only [Linear.Fact.vars, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff,
          or_false] at ht
        rcases ht with rfl | rfl
        · rw [htv φ heq]; rfl
        · rw [htv x rfl]; rfl
      · simp only [Linear.Fact.Holds, Linear.Form.eval, HeapKnowledge.termValuation, htv φ heq, htv x rfl,
          Option.getD_some]
        omega

/-- A predecessor's equalities at a merge (`equal` in
`SinglePass.mergeState`): for each name `x` it renames to the fresh names
`φs`, `φ` equal to `x` for each `φ` where a slot of the merge keeps `x`,
and consecutive fresh names equal, each with the linear facts for the root
term kinds the predecessor's store witnesses on `x` (`Store.definedKinds`). -/
def mergeEqual (st : State) (names : Array Nat) (m : Std.HashMap Nat (List Nat)) : List Atom :=
  m.fold (fun (acc : List Atom) x φs =>
    let kinds := st.store.definedKinds x
    (if names.contains x then φs.flatMap (mergeEqAtoms kinds · x) else []) ++
    (φs.zip φs.tail).flatMap (fun (φ, ψ) => mergeEqAtoms kinds ψ φ) ++ acc) []

theorem zip_tail_eq {α : Type} {P : α → Prop} : ∀ (l : List α), (∀ a ∈ l, P a) → ∀ p ∈ l.zip l.tail, P p.1 ∧ P p.2
  | [], _, _, hp => by simp at hp
  | [_], _, _, hp => by simp at hp
  | a :: b :: l, hl, p, hp => by
    simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨hl a (by simp), hl b (by simp)⟩
    · exact zip_tail_eq (b :: l) (fun c hc => hl c (List.mem_cons_of_mem _ hc)) p hp

/-- **(Merge) A predecessor's equalities hold at its valuation extended to
the fresh names**: where every fact of the predecessor's store holds at `η`,
and `η'` holds at each fresh name `φ` of `x` the value `η` holds at `x`, and
agrees with `η` at every renamed name, every equality the merge states for
that predecessor holds at `η'`. -/
theorem mergeEqual_holds {st : State} {names : Array Nat} {m : Std.HashMap Nat (List Nat)} {η η' : Env}
    {h : Heap} (hS : StoreOk ε st.store η h)
    (hφ : ∀ x φs, m[x]? = some φs → ∀ φ ∈ φs, η' φ = η x)
    (hx : ∀ x φs, m[x]? = some φs → η' x = η x) :
    ∀ a ∈ mergeEqual st names m, AtomHolds ε a η' h := by
  unfold mergeEqual
  rw [Std.HashMap.fold_eq_foldl_toList]
  refine foldl_inv (fun (acc : List Atom) => ∀ a ∈ acc, AtomHolds ε a η' h) _ _ _ (fun _ h => by cases h) ?_
  intro ⟨x, φs⟩ hp acc hacc a ha
  have hm : m[x]? = some φs := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hp
  have hkinds : ∀ k ∈ st.store.definedKinds x, (HeapKnowledge.kindValue h k (η' x)).isSome := fun k hk => by
    rw [hx x φs hm]; exact definedKinds_some hS hk
  simp only [List.mem_append, List.mem_flatMap] at ha
  rcases ha with (ha | ⟨⟨φ, ψ⟩, hpair, ha⟩) | ha
  · split at ha
    · obtain ⟨φ, hφs, ha⟩ := List.mem_flatMap.mp ha
      exact mergeEqAtoms_holds (by rw [hφ x φs hm φ hφs, hx x φs hm]) hkinds a ha
    · cases ha
  · obtain ⟨hφ1, hψ1⟩ := zip_tail_eq (P := fun y => y ∈ φs) φs (fun _ h => h) _ hpair
    refine mergeEqAtoms_holds (by rw [hφ x φs hm ψ hψ1, hφ x φs hm φ hφ1]) (fun k hk => ?_) a ha
    rw [hφ x φs hm φ hφ1]; exact definedKinds_some hS hk
  · exact hacc a ha

end Verification.TolerantFrames
