import Verification.Programs.TolerantFramesEntry

/-! # Tolerant frames: a merge's equalities

At a merge (`SinglePass.mergeState`) a slot whose predecessors' names differ
takes a fresh name `φ`, and each predecessor renames its name `x` there to
`φ`. Restating a predecessor's facts at the fresh names, the merge states
`φ` equal to `x` where a slot keeps `x`, and one name's fresh names equal:
by an alias link always, and by two linear facts `φ - x ≤ 0`, `x - φ ≤ 0`
only where the predecessor's unconditional facts make `x` an integer
(`Store.integral`). This module proves those facts hold at a predecessor's
valuation extended to the fresh names by its own names' values. -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations
open Verification.SinglePass (Atom Store State)

theorem index_int {x : UInt64} {i : Nat} (h : indexOfBits x = some i) : (HeapKnowledge.intValue (.num x)).isSome := by
  rw [HeapKnowledge.intValue_num (IndexWrites.index_safeInt h)]; rfl

/-! ## The store's integers -/

/-- **`Store.integral` is sound**: where every fact of the store holds at
`η`, a name the store's unconditional facts make an integer holds a safe
integer. -/
theorem integral_int {s : Store} {η : Env} {h : Heap} (hS : StoreOk s η h) {x : Nat}
    (hi : s.integral x = true) : (HeapKnowledge.intValue (η x)).isSome := by
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp hi
  have hh := hS a (about_storeAll ha)
  cases a with
  | index ia =>
    obtain ⟨f, c, neg⟩ := ia
    cases c with
    | some _ => simp at hp
    | none =>
      have hf : f.HoldsAt η h := hh _ (List.mem_singleton_self _) (fun b hb => by cases hb)
      cases f with
      | int k =>
        simp only [beq_iff_eq] at hp; subst hp; exact hf
      | index k =>
        simp only [beq_iff_eq] at hp; subst hp
        obtain ⟨b, i, hb, hib⟩ := hf
        rw [hb]; exact index_int hib
      | length y k =>
        simp only [beq_iff_eq] at hp; subst hp
        obtain ⟨_, ls, _, _, hk, hm⟩ := hf
        rw [hk, HeapKnowledge.intValue_length hm]; rfl
      | bound y k st =>
        simp only [beq_iff_eq] at hp; subst hp
        obtain ⟨_, _, b, i, _, _, hb, hib, _⟩ := hf
        rw [hb]; exact index_int hib
      | linear F =>
        simp only [List.contains_iff_mem] at hp
        exact hf.1 _ hp
      | _ => simp at hp
  | cell _ | value _ | link _ | elem _ | sep _ => simp at hp

/-! ## The merge's equalities -/

/-- A merge's facts stating the fresh name `φ` equal to `x`
(`SinglePass.mergeState`'s `eqAtoms`): the alias link, and with `int` the
two linear facts of their values. -/
def mergeEqAtoms (int : Bool) (φ x : Nat) : List Atom :=
  Atom.link { cell := φ, value := x, alias := true } ::
    (if !int then [] else
    [.index ⟨.linear (.le [(HeapKnowledge.Term.value φ, 1), (HeapKnowledge.Term.value x, -1)] 0), none, false⟩,
    .index ⟨.linear (.le [(HeapKnowledge.Term.value φ, -1), (HeapKnowledge.Term.value x, 1)] 0), none, false⟩])

/-- **A merge's equality holds**: at a valuation under which `φ` and `x`
hold one value, the alias link holds, and where `x` holds a safe integer the
two linear facts too. -/
theorem mergeEqAtoms_holds {int : Bool} {φ x : Nat} {η : Env} {h : Heap} (heq : η φ = η x)
    (hint : int = true → (HeapKnowledge.intValue (η x)).isSome) : ∀ a ∈ mergeEqAtoms int φ x, AtomHolds a η h := by
  intro a ha
  simp only [mergeEqAtoms, List.mem_cons] at ha
  rcases ha with rfl | ha
  · intro g hg
    simp only [List.mem_singleton] at hg; subst hg
    simpa using heq
  · cases int with
    | false => simp at ha
    | true =>
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (hint rfl)
      have hv : ∀ y, η y = η x → HeapKnowledge.termValue η h (.value y) = some k := by
        intro y hy; simp [hy, hk]
      simp only [Bool.not_true, Bool.false_eq_true, if_false, List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl <;>
      · intro y hy _
        simp only [List.mem_singleton] at hy; subst hy
        refine ⟨fun t ht => ?_, ?_⟩
        · simp only [Linear.Fact.vars, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff,
            or_false] at ht
          rcases ht with rfl | rfl
          · rw [hv φ heq]; rfl
          · rw [hv x rfl]; rfl
        · simp only [Linear.Fact.Holds, Linear.Form.eval, HeapKnowledge.termValuation, hv φ heq, hv x rfl,
            Option.getD_some]
          omega

/-- A predecessor's equalities at a merge (`equal` in
`SinglePass.mergeState`): for each name `x` it renames to the fresh names
`φs`, `φ` equal to `x` for each `φ` where a slot of the merge keeps `x`,
and consecutive fresh names equal, each with the linear facts where the
predecessor's store makes `x` an integer. -/
def mergeEqual (st : State) (names : Array Nat) (m : Std.HashMap Nat (List Nat)) : List Atom :=
  m.fold (fun (acc : List Atom) x φs =>
    let int := st.store.integral x
    (if names.contains x then φs.flatMap (mergeEqAtoms int · x) else []) ++
    (φs.zip φs.tail).flatMap (fun (φ, ψ) => mergeEqAtoms int ψ φ) ++ acc) []

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
    {h : Heap} (hS : StoreOk st.store η h)
    (hφ : ∀ x φs, m[x]? = some φs → ∀ φ ∈ φs, η' φ = η x)
    (hx : ∀ x φs, m[x]? = some φs → η' x = η x) :
    ∀ a ∈ mergeEqual st names m, AtomHolds a η' h := by
  unfold mergeEqual
  rw [Std.HashMap.fold_eq_foldl_toList]
  refine foldl_inv (fun (acc : List Atom) => ∀ a ∈ acc, AtomHolds a η' h) _ _ _ (fun _ h => by cases h) ?_
  intro ⟨x, φs⟩ hp acc hacc a ha
  have hm : m[x]? = some φs := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hp
  have hint : st.store.integral x = true → (HeapKnowledge.intValue (η' x)).isSome := fun hi => by
    rw [hx x φs hm]; exact integral_int hS hi
  simp only [List.mem_append, List.mem_flatMap] at ha
  rcases ha with (ha | ⟨⟨φ, ψ⟩, hpair, ha⟩) | ha
  · split at ha
    · obtain ⟨φ, hφs, ha⟩ := List.mem_flatMap.mp ha
      exact mergeEqAtoms_holds (by rw [hφ x φs hm φ hφs, hx x φs hm]) hint a ha
    · cases ha
  · obtain ⟨hφ1, hψ1⟩ := zip_tail_eq (P := fun y => y ∈ φs) φs (fun _ h => h) _ hpair
    refine mergeEqAtoms_holds (by rw [hφ x φs hm ψ hψ1, hφ x φs hm φ hφ1]) (fun hi => ?_) a ha
    rw [hφ x φs hm φ hφ1]; exact integral_int hS hi
  · exact hacc a ha

end Verification.TolerantFrames
