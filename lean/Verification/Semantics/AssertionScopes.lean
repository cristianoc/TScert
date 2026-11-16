import Verification.Semantics.TwoStateFormulas

/-! # Substitution and scope of assertions

Capture-avoiding substitution of slots by paths in the assertions of the
note "Tolerant frames" and its semantic equivalence (I5, "Substitution and
marks"; the note, §6, rules Call and (Rigid): "the substitution of the
witness is capture-avoiding"), and the scope of a two-state formula: the
runtime slots of its entry and exit valuations it reads (`FormulaF.scoped`).
These read only the assertion semantics and the effect action
(`TwoStateFormulas`), so callable and body typing state scoped guarantees
with them. -/
namespace Verification.Footprints

/-! ## Renaming the roots of an effect -/

/-- A region with its slots renamed by `σ`: a callee's position `i` read as
the caller's slot `σ i`. -/
def Region.rename (σ : Nat → Nat) : Region → Region
  | .field x k => .field (σ x) k
  | .fields x => .fields (σ x)
  | .cells x => .cells (σ x)
  | .cls c => .cls c
  | .all => .all
  | .path x p k => .path (σ x) p k
  | .pathFields x p => .pathFields (σ x) p
  | .pathCells x p => .pathCells (σ x) p
  | .inCls r c => .inCls (r.rename σ) c
  | .spine x p => .spine (σ x) p

theorem Region.mem_rename (σ : Nat → Nat) (ρ : Env) (h : Heap) (l : Nat) :
    ∀ r : Region, (r.rename σ).mem ρ h l = r.mem (fun i => ρ (σ i)) h l := by
  intro r
  induction r with
  | inCls r c ih => simp only [Region.rename, Region.mem, ih]
  | _ => rfl

def Footprint.rename (σ : Nat → Nat) (Φ : Footprint) : Footprint := Φ.map fun e => (e.1.rename σ, e.2)

end Verification.Footprints

namespace Verification.Parity
open Verification Footprints HeapKnowledge TolerantFrames

/-- The variable `x`: the empty path at slot `x`. -/
def Path.var (x : Nat) : Path := ⟨x, []⟩

/-! ## The roots of an effect -/

/-- The slots a region reads its roots at. -/
def regionRoots : Region → List Nat
  | .field x _ | .fields x | .cells x | .path x _ _ | .pathFields x _ | .pathCells x _ | .spine x _ => [x]
  | .cls _ | .all => []
  | .inCls r _ => regionRoots r

/-- An effect reading runtime slots below `n` alone. -/
def effectScoped (n : Nat) (Φ : Footprint) : Bool := Φ.all fun e => (regionRoots e.1).all (· < n)

section Action
variable {Φ : Footprint} {η η' : Env} {s s' : IndexedHeap}

theorem EffectAction.admissible (h : EffectAction Φ η s s') : Admissible s s' := h.1
/-- **An effect with its roots renamed acts as the effect at the renamed
valuation** (`Footprints.Region.mem_rename`). -/
theorem EffectAction.rename_iff (σ : Nat → Nat) :
    EffectAction (Footprint.rename σ Φ) η s s' ↔ EffectAction Φ (fun i => η (σ i)) s s' := by
  have hm : ∀ (r : Region) l, (r.rename σ).mem η s.h l = r.mem (fun i => η (σ i)) s.h l :=
    fun r l => Region.mem_rename σ η s.h l r
  constructor
  · rintro ⟨ha, hl, hp⟩
    refine ⟨ha, hl, fun l v hv => ?_⟩
    obtain ⟨v', hv', hal⟩ := hp l v hv
    refine ⟨v', hv', hal.imp_right fun ⟨e, he, hme, hc⟩ => ?_⟩
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    exact ⟨e0, he0, by rw [← hm]; exact hme, hc⟩
  · rintro ⟨ha, hl, hp⟩
    refine ⟨ha, hl, fun l v hv => ?_⟩
    obtain ⟨v', hv', hal⟩ := hp l v hv
    refine ⟨v', hv', hal.imp_right fun ⟨e, he, hme, hc⟩ => ?_⟩
    exact ⟨(e.1.rename σ, e.2), List.mem_map.mpr ⟨e, he, rfl⟩, by rw [hm]; exact hme, hc⟩

private theorem region_mem_congr {r : Region} {η η' : Env} (he : ∀ x ∈ regionRoots r, η x = η' x) (hp : Heap)
    (l : Nat) : r.mem η hp l = r.mem η' hp l := by
  induction r with
  | inCls r _ ih => simp only [Region.mem, ih (by simpa [regionRoots] using he)]
  | cls _ | all => rfl
  | _ => simp only [regionRoots, List.mem_singleton, forall_eq] at he; simp only [Region.mem, he]

/-- **An effect acts alike at valuations agreeing on its roots.** -/
theorem EffectAction.congr_roots {η' : Env} (he : ∀ x, (∃ e ∈ Φ, x ∈ regionRoots e.1) → η' x = η x) :
    EffectAction Φ η' s s' ↔ EffectAction Φ η s s' := by
  have hm : ∀ e ∈ Φ, ∀ l, e.1.mem η' s.h l = e.1.mem η s.h l :=
    fun e he' l => region_mem_congr (fun x hx => he x ⟨e, he', hx⟩) s.h l
  constructor
  · rintro ⟨ha, hl, hp⟩
    refine ⟨ha, hl, fun l v hv => ?_⟩
    obtain ⟨v', hv', hal⟩ := hp l v hv
    exact ⟨v', hv', hal.imp_right fun ⟨e, he', hme, hc⟩ => ⟨e, he', by rw [← hm e he']; exact hme, hc⟩⟩
  · rintro ⟨ha, hl, hp⟩
    refine ⟨ha, hl, fun l v hv => ?_⟩
    obtain ⟨v', hv', hal⟩ := hp l v hv
    exact ⟨v', hv', hal.imp_right fun ⟨e, he', hme, hc⟩ => ⟨e, he', by rw [hm e he']; exact hme, hc⟩⟩

/-- **Entrywise coverage includes the actions**: where every location an
entry of `Φ` selects at the first state is selected by an entry of `Ψ` with
a larger change, an action of `Φ` is one of `Ψ`. -/
theorem EffectAction.mono_entries {Ψ : Footprint}
    (hcov : ∀ e ∈ Φ, ∀ l, e.1.mem η s.h l = true → ∃ e' ∈ Ψ, e'.1.mem η s.h l = true ∧ e.2.le e'.2 = true)
    (ha : EffectAction Φ η s s') : EffectAction Ψ η s s' := by
  refine ⟨ha.1, ha.2.1, fun l v hv => ?_⟩
  obtain ⟨v', hv', hal⟩ := ha.2.2 l v hv
  refine ⟨v', hv', hal.imp_right fun ⟨e, he, hm, hc⟩ => ?_⟩
  obtain ⟨e', he', hm', hle⟩ := hcov e he l hm
  exact ⟨e', he', hm', hc.mono hle⟩

end Action

/-! ## Paths -/

private theorem readPath_append (h : Heap) (x : Val) (p q : List String) :
    readPath h x (p ++ q) = (readPath h x p).bind (fun v => readPath h v q) := by
  induction p generalizing x with
  | nil => rfl
  | cons f p ih =>
    cases x <;> simp only [List.cons_append, readPath, Option.bind_none]
    split
    · split
      · exact ih _
      · rfl
    · rfl

/-! ## Substitutions -/

/-- A witness read one binder further. -/
def Witness.shift : Witness → Witness
  | .path p => .path ⟨p.root + 1, p.fields⟩
  | .literal v => .literal v

theorem Witness.value_shift (w : Witness) (v : Val) (η : Env) (h : Heap) :
    w.shift.value (push v η) h = w.value η h := by
  cases w <;> rfl

namespace Substitution

/-- The path image of slot `i`, where its image is a path. -/
def pathAt (θ : Substitution) (i : Nat) : Option Path :=
  match θ.image i with
  | some (.path p) => some p
  | _ => none

theorem Holds.path {θ : Substitution} {target source : Env} {h : Heap} (hθ : θ.Holds target source h) {i : Nat}
    {q : Path} (hq : θ.pathAt i = some q) : q.read source h = some (target i) := by
  unfold pathAt at hq
  split at hq
  · rename_i p hp; cases hq; exact hθ i _ hp
  · cases hq

/-- The substitution under one more logical binder: slot `0` stays, slot
`i + 1` goes to the image of `i`, one slot further. -/
def lift (θ : Substitution) : Substitution :=
  ⟨(.path (Path.var 0) :: θ.images.toList.map Witness.shift).toArray, θ.boxed, θ.stable.map (· + 1)⟩

theorem heapFree_shift (w : Witness) : w.shift.heapFree = w.heapFree := by cases w <;> rfl

/-- **The lifted substitution holds under the binder.** -/
theorem Holds.lift {θ : Substitution} {target source : Env} {h : Heap} (hθ : θ.Holds target source h) (v : Val) :
    θ.lift.Holds (push v target) (push v source) h := by
  intro i w hi
  simp only [Substitution.lift, image, List.getElem?_toArray] at hi
  cases i with
  | zero =>
    simp [Witness.heapFree, Path.var] at hi
    subst hi; rfl
  | succ i =>
    simp only [List.getElem?_cons_succ, List.getElem?_map] at hi
    cases hq : θ.images.toList[i]? with
    | none => rw [hq] at hi; simp at hi
    | some q =>
      rw [hq] at hi
      have hc : (θ.stable.map (· + 1)).contains (i + 1) = θ.stable.contains i := by
        cases h1 : θ.stable.contains i <;> cases h2 : (θ.stable.map (· + 1)).contains (i + 1) <;>
          simp_all
      simp only [Option.map_some, heapFree_shift, hc] at hi
      have hcond : ¬ (θ.boxed && !q.heapFree && !θ.stable.contains i) = true := by
        intro hcd; rw [if_pos hcd] at hi; cases hi
      rw [if_neg hcond, Option.some.injEq] at hi
      subst hi
      rw [Witness.value_shift]
      apply hθ i q
      unfold image; rw [← Array.getElem?_toList, hq]; simp only [if_neg hcond]

theorem HoldsAt.of_holds {θ : Substitution} (hst : θ.stable = []) {target source : Env}
    {s : TolerantFrames.IndexedHeap} (hθ : θ.Holds target source s.h) : θ.HoldsAt target source s :=
  ⟨hθ, fun s' _ => hθ.box hst s'.h⟩

theorem box_box (θ : Substitution) : θ.box.box = θ.box := rfl

/-- An image under a box is an image reading no heap or a certified one. -/
theorem image_box {θ : Substitution} {i : Nat} {w : Witness} (h : θ.box.image i = some w) :
    θ.images[i]? = some w ∧ (w.heapFree = true ∨ θ.stable.contains i = true) := by
  unfold image at h
  have hi : θ.box.images = θ.images := rfl
  rw [hi] at h
  cases hw : θ.images[i]? with
  | none => rw [hw] at h; cases h
  | some w0 =>
    rw [hw] at h
    dsimp only at h
    by_cases hc : (θ.box.boxed && !w0.heapFree && !θ.box.stable.contains i) = true
    · rw [if_pos hc] at h; cases h
    · rw [if_neg hc] at h; cases h
      refine ⟨rfl, ?_⟩
      simp only [box, Bool.true_and, Bool.and_eq_true, Bool.not_eq_true', not_and] at hc
      cases hf : w.heapFree <;> cases hs : θ.stable.contains i <;> simp_all

/-- **Under a box at a state an action reaches, the substitution still holds.** -/
theorem HoldsAt.under {θ : Substitution} {target source : Env} {s s' : TolerantFrames.IndexedHeap}
    (hθ : θ.HoldsAt target source s) (ha : TolerantFrames.Admissible s s') : θ.box.HoldsAt target source s' :=
  ⟨hθ.2 s' ha, fun s'' ha' => by rw [box_box]; exact hθ.2 s'' (ha.trans ha')⟩

theorem lift_box (θ : Substitution) : θ.lift.box = θ.box.lift := rfl

theorem HoldsAt.lift {θ : Substitution} {target source : Env} {s : TolerantFrames.IndexedHeap}
    (hθ : θ.HoldsAt target source s) (v : Val) : θ.lift.HoldsAt (push v target) (push v source) s :=
  ⟨hθ.1.lift v, fun s' ha => by rw [lift_box]; exact (hθ.2 s' ha).lift v⟩

/-- The substitution sending each of the slots below `n` one slot further:
reading an assertion under one more binder. -/
def shift (n : Nat) : Substitution := ⟨((List.range n).map fun i => .path (Path.var (i + 1))).toArray, false, []⟩

/-- The substitution sending slot `0` to a witness and slot `i + 1`, below
`n + 1`, to slot `i`: instantiating a logical binder. -/
def instantiate (w : Witness) (n : Nat) : Substitution :=
  ⟨(w :: (List.range n).map fun i => .path (Path.var i)).toArray, false, []⟩

/-- The identity on the slots below `n`: the scope of `n` runtime slots. -/
def ident (n : Nat) : Substitution := ⟨((List.range n).map fun i => .path (Path.var i)).toArray, false, []⟩

private theorem range_image {n i j : Nat} (hj : (List.range n)[i]? = some j) : j = i ∧ i < n := by
  obtain ⟨hlt, hj'⟩ := List.getElem?_eq_some_iff.mp hj
  simp only [List.getElem_range] at hj'
  simp only [List.length_range] at hlt
  exact ⟨hj'.symm, hlt⟩

theorem shift_holds (n : Nat) (η : Env) (v : Val) (h : Heap) : (shift n).Holds η (push v η) h := by
  intro i w hi
  rw [image_of_unboxed rfl] at hi
  simp only [shift, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at hi
  obtain ⟨j, hj, rfl⟩ := hi
  obtain ⟨rfl, -⟩ := range_image hj
  rfl

/-- The identity holds between two valuations agreeing below `n`. -/
theorem ident_holds {n : Nat} {η η' : Env} (he : ∀ i < n, η' i = η i) (h : Heap) : (ident n).Holds η η' h := by
  intro i w hi
  rw [image_of_unboxed rfl] at hi
  simp only [ident, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at hi
  obtain ⟨j, hj, rfl⟩ := hi
  obtain ⟨rfl, hlt⟩ := range_image hj
  show some (η' j) = some (η j)
  rw [he j hlt]

/-- **Instantiating a binder with a witness's value.** -/
theorem instantiate_holds {w : Witness} {n : Nat} {η : Env} {h : Heap} {v : Val} (hw : w.value η h = some v) :
    (instantiate w n).Holds (push v η) η h := by
  intro i w' hi
  rw [image_of_unboxed rfl] at hi
  simp only [instantiate, List.getElem?_toArray] at hi
  cases i with
  | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi; exact hw
  | succ i =>
    simp only [List.getElem?_cons_succ, List.getElem?_map, Option.map_eq_some_iff] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    obtain ⟨rfl, -⟩ := range_image hj
    rfl

end Substitution

/-! ## Substituting into atoms -/

/-- A path with its root replaced by its image. -/
def substPath (θ : Substitution) (p : Path) : Option Path :=
  (θ.pathAt p.root).map fun q => ⟨q.root, q.fields ++ p.fields⟩

/-- A current term with its slot replaced by its image. -/
def substTerm (θ : Substitution) (t : Term) : Option Term :=
  if t.atEntry then none else (θ.pathAt t.slot).map fun q => Term.now t.kind q.root (q.fields ++ t.path)

/-- A scalar parameter with its slot renamed: its image is a variable, so
it stays a scalar. -/
def substScalar (θ : Substitution) (t : Term) : Option Term :=
  if t.atEntry then none else match θ.pathAt t.slot with
    | some q => if q.fields.isEmpty then some (Term.now t.kind q.root t.path) else none
    | none => none

/-- A variable of a scalar body with its parameter renamed. -/
def substBound (θ : Substitution) : Bound → Option Bound
  | .free t => (substScalar θ t).map .free
  | b => some b

/-- A witness substituted: a path rooted at a slot whose image is a literal
is that literal where it reads no field. -/
def substWitness (θ : Substitution) : Witness → Option Witness
  | .path p => match θ.image p.root with
    | some (.literal v) => if p.fields.isEmpty then some (.literal v) else none
    | _ => (substPath θ p).map .path
  | .literal v => some (.literal v)

/-- An atom with every slot replaced by its image. -/
def substAtom (θ : Substitution) : Atom → Option Atom
  | .linear F => (F.mapVars (substTerm θ)).map .linear
  | .equal p w => do pure (.equal (← substPath θ p) (← substWitness θ w))
  | .dense p n => do pure (.dense (← substPath θ p) (← substTerm θ n))
  | .contents p R => (substPath θ p).map (.contents · R)
  | .every p n body => do
    pure (.every (← substPath θ p) (← substTerm θ n) (← IndexFact.mapBodyWith (substBound θ) body))
  | .element p t w => do pure (.element (← substPath θ p) (← substTerm θ t) (← substWitness θ w))
  | .defined t => (substTerm θ t).map .defined
  | .safeInt p => (substPath θ p).map .safeInt
  | .pastSafe p => (substPath θ p).map .pastSafe

section AtomSubst
variable {θ : Substitution} {target source : Env} {h : Heap}

theorem substPath_read (hθ : θ.Holds target source h) {p p' : Path} (hs : substPath θ p = some p') :
    p'.read source h = p.read target h := by
  simp only [substPath, Option.map_eq_some_iff] at hs
  obtain ⟨q, hq, rfl⟩ := hs
  simp only [Path.read]
  rw [readPath_append]
  have := hθ.path hq
  simp only [Path.read] at this
  rw [this]; rfl

theorem substTerm_termAt (hθ : θ.Holds target source h) {t t' : Term} (hs : substTerm θ t = some t') :
    termAt source h t' = termAt target h t := by
  unfold substTerm at hs
  split at hs
  · cases hs
  · obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hs
    have := hθ.path hq
    simp only [Path.read] at this
    simp only [termAt, readPath_append, this, Option.bind_some]

theorem substScalar_termAt (hθ : θ.Holds target source h) {t t' : Term} (hs : substScalar θ t = some t') :
    termAt source h t' = termAt target h t ∧ t'.kind = t.kind ∧ t'.path = t.path ∧ t'.atEntry = false := by
  unfold substScalar at hs
  split at hs
  · cases hs
  · split at hs
    · rename_i q hq
      split at hs
      · rename_i he
        cases hs
        have hf : q.fields = [] := by simpa using he
        have := hθ.path hq
        rw [Path.read_nil hf] at this
        have he' : source q.root = target t.slot := Option.some.inj this
        refine ⟨?_, rfl, rfl, rfl⟩
        unfold termAt
        simp only [he']
      · cases hs
    · cases hs

theorem substWitness_value (hθ : θ.Holds target source h) {w w' : Witness} (hs : substWitness θ w = some w') :
    w'.value source h = w.value target h := by
  cases w with
  | path p =>
    simp only [substWitness] at hs
    cases hi : θ.image p.root with
    | none =>
      rw [hi] at hs
      obtain ⟨p', hp, rfl⟩ := Option.map_eq_some_iff.mp hs
      exact substPath_read hθ hp
    | some w0 =>
      rw [hi] at hs
      cases w0 with
      | path q =>
        obtain ⟨p', hp, rfl⟩ := Option.map_eq_some_iff.mp hs
        exact substPath_read hθ hp
      | literal v =>
        by_cases he : p.fields.isEmpty
        · simp only [he, if_true, Option.some.injEq] at hs
          subst hs
          have := hθ p.root _ hi
          simp only [Witness.value] at this ⊢
          rw [Path.read_nil (by simpa using he)]
          exact this
        · simp [he] at hs
  | literal v => cases hs; rfl

theorem substBound_value (hθ : θ.Holds target source h) {b b' : Bound} (hs : substBound θ b = some b')
    (ls : List (Option Nat)) (i : Nat) : scalarValue source h ls i b' = scalarValue target h ls i b := by
  cases b with
  | free t =>
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp hs
    exact (substScalar_termAt hθ ht).1
  | project k p =>
    cases hs
    cases k <;> cases p <;> rfl
  | _ => cases hs; rfl

private theorem bind_some_eq {α β : Type} {o : Option α} {f : α → Option β} {b : β} (h : o.bind f = some b) :
    ∃ a, o = some a ∧ f a = some b := Option.bind_eq_some_iff.mp h

/-- **Substitution of an atom is semantic** (I5, `substAssertion_sound` on
atoms): the substituted atom holds at the source valuation where the atom
holds at the target one. -/
theorem substAtom_holds (hθ : θ.Holds target source h) {a a' : Atom} (hs : substAtom θ a = some a') :
    a'.Holds source h ↔ a.Holds target h := by
  cases a with
  | linear F =>
    obtain ⟨F', hF, rfl⟩ := Option.map_eq_some_iff.mp hs
    exact factAt_mapVars hF fun x _ y hy => substTerm_termAt hθ hy
  | equal p w =>
    simp only [substAtom, Option.bind_eq_bind, Option.pure_def] at hs
    obtain ⟨p', hp, hs⟩ := bind_some_eq hs
    obtain ⟨w', hw, hs⟩ := bind_some_eq hs
    cases hs
    simp only [Atom.Holds, substPath_read hθ hp, substWitness_value hθ hw]
  | dense p n =>
    simp only [substAtom, Option.bind_eq_bind, Option.pure_def] at hs
    obtain ⟨p', hp, hs⟩ := bind_some_eq hs
    obtain ⟨n', hn, hs⟩ := bind_some_eq hs
    cases hs
    simp only [Atom.Holds, substPath_read hθ hp, substTerm_termAt hθ hn]
  | contents p R =>
    obtain ⟨p', hp, rfl⟩ := Option.map_eq_some_iff.mp hs
    simp only [Atom.Holds, substPath_read hθ hp]
  | every p n body =>
    simp only [substAtom, Option.bind_eq_bind, Option.pure_def] at hs
    obtain ⟨p', hp, hs⟩ := bind_some_eq hs
    obtain ⟨n', hn, hs⟩ := bind_some_eq hs
    obtain ⟨body', hb, hs⟩ := bind_some_eq hs
    cases hs
    obtain ⟨hb1, hb2⟩ := IndexFact.mapBodyWith_pairs hb
    have hval : ∀ ls i, ∀ F ∈ body, ∀ F', F.mapVars (substBound θ) = some F' →
        (F'.HoldsAt (scalarValue source h ls i) ↔ F.HoldsAt (scalarValue target h ls i)) := fun ls i F _ F' hm =>
      LinearClause.holdsAt_mapVars hm fun _ _ y hy => substBound_value hθ hy ls i
    simp only [Atom.Holds, substPath_read hθ hp, substTerm_termAt hθ hn]
    constructor
    · rintro ⟨w, s, ls, k, hw, hs, hls, hk, hall⟩
      refine ⟨w, s, ls, k, hw, hs, hls, hk, fun i hi => ⟨(hall i hi).1, fun F hF => ?_⟩⟩
      obtain ⟨F', hF', hm⟩ := hb2 F hF
      exact (hval ls i F hF F' hm).mp ((hall i hi).2 F' hF')
    · rintro ⟨w, s, ls, k, hw, hs, hls, hk, hall⟩
      refine ⟨w, s, ls, k, hw, hs, hls, hk, fun i hi => ⟨(hall i hi).1, fun F' hF' => ?_⟩⟩
      obtain ⟨F, hF, hm⟩ := hb1 F' hF'
      exact (hval ls i F hF F' hm).mpr ((hall i hi).2 F hF)
  | element p t w =>
    simp only [substAtom, Option.bind_eq_bind, Option.pure_def] at hs
    obtain ⟨p', hp, hs⟩ := bind_some_eq hs
    obtain ⟨t', ht, hs⟩ := bind_some_eq hs
    obtain ⟨w', hw, hs⟩ := bind_some_eq hs
    cases hs
    simp only [Atom.Holds, substPath_read hθ hp, substTerm_termAt hθ ht, substWitness_value hθ hw]
  | defined t =>
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp hs
    simp only [Atom.Holds, substTerm_termAt hθ ht]
  | safeInt p =>
    obtain ⟨p', hp, rfl⟩ := Option.map_eq_some_iff.mp hs
    simp only [Atom.Holds, substPath_read hθ hp]
  | pastSafe p =>
    obtain ⟨p', hp, rfl⟩ := Option.map_eq_some_iff.mp hs
    simp only [Atom.Holds, substPath_read hθ hp]

theorem separated_subst (hθ : θ.Holds target source h) {p q p' q' : Path} (hp : substPath θ p = some p')
    (hq : substPath θ q = some q') : Separated source h p' q' ↔ Separated target h p q := by
  simp only [Separated, substPath_read hθ hp, substPath_read hθ hq]

theorem apart_subst (hθ : θ.Holds target source h) {p q p' q' : Path} (hp : substPath θ p = some p')
    (hq : substPath θ q = some q') : Apart source h p' q' ↔ Apart target h p q := by
  simp only [Apart, substPath_read hθ hp, substPath_read hθ hq]

theorem fresh_subst (hθ : θ.Holds target source h) {m : Nat} {p p' : Path} (hp : substPath θ p = some p') :
    FreshPath source m h p' ↔ FreshPath target m h p := by
  simp only [FreshPath, substPath_read hθ hp]

end AtomSubst

/-! ## Substituting into assertions -/

/-- The slot a root is renamed to: its image, where that is a variable. -/
def rootImage (θ : Substitution) (r : Nat) : Option Nat :=
  match θ.image r with
  | some (.path ⟨r', []⟩) => some r'
  | _ => none

/-- **An effect under a substitution**: its regions' roots renamed to their
variable images (`Footprints.Footprint.rename`); refused where a root's image
is no variable. -/
def renameEffect (θ : Substitution) (Φ : Footprint) : Option Footprint :=
  if Φ.all fun e => (regionRoots e.1).all fun r => (rootImage θ r).isSome then
    some (Footprint.rename (fun r => (rootImage θ r).getD r) Φ)
  else none

theorem renameEffect_action {θ : Substitution} {target source : Env} {h : Heap} (hθ : θ.Holds target source h)
    {Φ Ψ : Footprint} (hr : renameEffect θ Φ = some Ψ) {s s' : IndexedHeap} :
    EffectAction Ψ source s s' ↔ EffectAction Φ target s s' := by
  unfold renameEffect at hr
  split at hr
  · rename_i hall
    cases hr
    rw [EffectAction.rename_iff]
    refine EffectAction.congr_roots fun r hr => ?_
    obtain ⟨e, he, hre⟩ := hr
    have := List.all_eq_true.mp (List.all_eq_true.mp hall e he) r hre
    obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp this
    rw [hr', Option.getD_some]
    unfold rootImage at hr'
    split at hr'
    · rename_i w hw
      cases hr'
      have := hθ r _ hw
      simpa [Witness.value, Path.read, readPath] using this
    · cases hr'
  · cases hr

/-- **Node `b` is node `a` under the substitution `θ`** (I5,
`substAssertion`, as a check of two arena nodes): the same connective, atoms
and paths substituted, the substitution lifted under a logical binder.
Under a box the effect's roots are renamed to their variable images, and the
body is substituted by the heap-free images alone, which mean the same at
every state an action reaches. -/
def substCheck (nodes : Array AssertionNode) (θ : Substitution) (a b : Nat) : Bool :=
  match nodes[a]?, nodes[b]? with
  | some .truth, some .truth => true
  | some .falsity, some .falsity => true
  | some (.atom x), some (.atom y) => substAtom θ x == some y
  | some (.and l r), some (.and l' r') =>
    if _ : l.index < a ∧ r.index < a ∧ l'.index < b ∧ r'.index < b then
      substCheck nodes θ l.index l'.index && substCheck nodes θ r.index r'.index
    else false
  | some (.guarded l r), some (.guarded l' r') =>
    if _ : l.index < a ∧ r.index < a ∧ l'.index < b ∧ r'.index < b then
      substCheck nodes θ l.index l'.index && substCheck nodes θ r.index r'.index
    else false
  | some (.existsValue x), some (.existsValue y) =>
    if _ : x.index < a ∧ y.index < b then substCheck nodes θ.lift x.index y.index else false
  | some (.separated p q), some (.separated p' q') => substPath θ p == some p' && substPath θ q == some q'
  | some (.apart p q), some (.apart p' q') => substPath θ p == some p' && substPath θ q == some q'
  | some (.fresh p), some (.fresh p') => substPath θ p == some p'
  | some (.box Φ x), some (.box Ψ y) =>
    if _ : x.index < a ∧ y.index < b then
      renameEffect θ Φ == some Ψ && substCheck nodes θ.box x.index y.index
    else false
  | _, _ => false
termination_by a + b

set_option maxHeartbeats 1000000 in
/-- **Checked substitution is semantic** (I5, `substAssertion_sound`):
where the images read at `source` give the target values, the substituted
node holds at `source` exactly where the node holds at `target`. -/
theorem substCheck_sound (nodes : Array AssertionNode) :
    ∀ (n a b : Nat), a + b = n → ∀ (θ : Substitution) (target source : Env) (m : Nat) (s : IndexedHeap),
      substCheck nodes θ a b = true → θ.HoldsAt target source s →
      (satNode nodes b source m s ↔ satNode nodes a target m s) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro a b hab θ target source m s hc hθ
  rw [substCheck] at hc
  rw [satNode, satNode]
  cases ha : nodes[a]? with
  | none => simp [ha] at hc
  | some na =>
  cases hb : nodes[b]? with
  | none => rw [ha, hb] at hc; cases na <;> simp at hc
  | some nb =>
  rw [ha, hb] at hc
  cases na <;> cases nb <;> (try (simp at hc; done)) <;> dsimp only at hc ⊢
  · exact Iff.rfl
  · exact Iff.rfl
  · rename_i x y
    simp only [beq_iff_eq] at hc
    exact substAtom_holds hθ.1 hc
  · rename_i l r l' r'
    split at hc
    · rename_i hi
      obtain ⟨h1, h2, h3, h4⟩ := hi
      simp only [Bool.and_eq_true] at hc
      simp only [h1, h2, h3, h4, dite_true]
      exact and_congr (ih _ (by omega) _ _ rfl θ target source m s hc.1 hθ)
        (ih _ (by omega) _ _ rfl θ target source m s hc.2 hθ)
    · cases hc
  · rename_i l r l' r'
    split at hc
    · rename_i hi
      obtain ⟨h1, h2, h3, h4⟩ := hi
      simp only [Bool.and_eq_true] at hc
      simp only [h1, h2, h3, h4, dite_true]
      exact or_congr (ih _ (by omega) _ _ rfl θ target source m s hc.1 hθ)
        (ih _ (by omega) _ _ rfl θ target source m s hc.2 hθ)
    · cases hc
  · rename_i x y
    split at hc
    · rename_i hi
      simp only [hi.1, hi.2, dite_true]
      exact exists_congr fun v => ih _ (by omega) _ _ rfl θ.lift (push v target) (push v source) m s hc (hθ.lift v)
    · cases hc
  · rename_i p q p' q'
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact separated_subst hθ.1 hc.1 hc.2
  · rename_i p q p' q'
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact apart_subst hθ.1 hc.1 hc.2
  · rename_i p p'
    simp only [beq_iff_eq] at hc
    exact fresh_subst hθ.1 hc
  · rename_i Φ x Ψ y
    split at hc
    · rename_i hi
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨hren, hrec⟩ := hc
      simp only [hi.1, hi.2, dite_true]
      constructor
      · intro hs s' ha'
        exact (ih _ (by omega) _ _ rfl θ.box target source m s' hrec (hθ.under ha'.admissible)).mp
          (hs s' ((renameEffect_action hθ.1 hren).mpr ha'))
      · intro hs s' ha'
        exact (ih _ (by omega) _ _ rfl θ.box target source m s' hrec
          (hθ.under ((renameEffect_action hθ.1 hren).mp ha').admissible)).mpr
          (hs s' ((renameEffect_action hθ.1 hren).mp ha'))
    · cases hc

/-- **Substitution at the arena level**: `b` is `a[θ]`. -/
theorem sat_subst {arena : AssertionArena} {θ : Substitution} {a b : AssertionRef}
    (hc : substCheck arena.nodes θ a.index b.index = true) {target source : Env} {m : Nat} {s : IndexedHeap}
    (hθ : θ.HoldsAt target source s) : Sat arena source m s b ↔ Sat arena target m s a :=
  substCheck_sound arena.nodes _ a.index b.index rfl θ target source m s hc hθ

/-- **Reading an assertion under one more binder** (the note's `∃`
elimination, I4 `existsElim`): where `b` is `a` with each slot below `n`
shifted, `b` holds under any value pushed exactly where `a` holds. -/
theorem sat_shift {arena : AssertionArena} {n : Nat} {a b : AssertionRef}
    (hc : substCheck arena.nodes (Substitution.shift n) a.index b.index = true) {η : Env} {m : Nat}
    {s : IndexedHeap} (v : Val) : Sat arena (push v η) m s b ↔ Sat arena η m s a :=
  sat_subst hc (.of_holds rfl (Substitution.shift_holds n η v s.h))

/-- **Instantiating a binder** (I4 `existsIntro`): where `b` is the body `a`
with slot `0` read as the path `w`, `b` holds where `a` holds of the value
`w` reads. -/
theorem sat_instantiate {arena : AssertionArena} {w : Witness} {n : Nat} {a b : AssertionRef}
    (hc : substCheck arena.nodes (Substitution.instantiate w n) a.index b.index = true) {η : Env} {m : Nat}
    {s : IndexedHeap} {v : Val} (hw : w.value η s.h = some v) : Sat arena η m s b ↔ Sat arena (push v η) m s a :=
  sat_subst hc (.of_holds rfl (Substitution.instantiate_holds hw))

/-! ## Scopes

An assertion is scoped at `n` runtime slots when it is itself under the
identity on the slots below `n`: every slot it reads outside its own
binders is below `n`. The slots a binder of the assertion introduces are its
eigenvariables, kept by the lifted identity. -/

/-- Node `a` reads no runtime slot at or above `n`. -/
def scopedAt (nodes : Array AssertionNode) (n : Nat) (a : Nat) : Bool := substCheck nodes (Substitution.ident n) a a

/-- **An assertion reads its runtime slots alone**: two valuations agreeing
below its scope satisfy it alike. -/
theorem sat_scoped_congr {arena : AssertionArena} {n : Nat} {a : AssertionRef}
    (hc : scopedAt arena.nodes n a.index = true) {η η' : Env} (he : ∀ i < n, η' i = η i) {m : Nat}
    {s : IndexedHeap} : Sat arena η' m s a ↔ Sat arena η m s a :=
  sat_subst hc (.of_holds rfl (Substitution.ident_holds he s.h))

/-! ## Scopes of formulas -/

/-- The runtime slots of the entry and of the exit environment. -/
structure Scope where
  before : Nat
  after : Nat
  deriving DecidableEq, Repr

def Scope.count (sc : Scope) : Phase → Nat
  | .before => sc.before
  | .after => sc.after

/-- A path reading runtime slots below `n`. -/
def Path.scoped (n : Nat) (p : Path) : Bool := decide (p.root < n)

def Witness.scoped (n : Nat) : Witness → Bool
  | .path p => p.scoped n
  | .literal _ => true

def StepVar.scoped (sc : Scope) : StepVar → Bool
  | .before t => !t.atEntry && decide (t.slot < sc.before)
  | .after t => !t.atEntry && decide (t.slot < sc.after)

/-- A post reads its operands in their phases' scopes: the exit's operands
below the exit count, the entry's below the entry count. -/
def OperationPostF.scoped (sc : Scope) : OperationPost → Bool
  | .arith _ l r y => l.scoped sc.after && r.scoped sc.after && y.scoped sc.after
  | .stringLength x y => x.scoped sc.after && y.scoped sc.after
  | .stringRead x i y => x.scoped sc.after && i.scoped sc.after && y.scoped sc.after
  | .lengthsKept x x' => decide (x < sc.before) && decide (x' < sc.after)
  | .boundedWrite x i x' => decide (x < sc.before) && decide (i < sc.before) && decide (x' < sc.after)
  | .push x x' args => decide (x < sc.before) && decide (x' < sc.after) && args.all (Witness.scoped sc.before)
  | .fact p l F => F.slots.all (fun i => decide (i + l < sc.count p)) && F.entrySlots.all (fun i => decide (i < sc.before))
  | .freshSpine x | .freshObject x => decide (x < sc.after)
  | .elementsWhen x _ y _ => decide (x < sc.after) && decide (y < sc.after)
  | .spineExtends x => decide (x < sc.before)
  | .viewWrite x i v _ => decide (x < sc.before) && decide (i < sc.before) && decide (v < sc.before)

/-- **A formula reads runtime slots within its scope**: assertions by the
identity check (their binders' eigenvariables apart), linear facts by their
terms' slots, a transition by its effect read at the entry, a transport by
an image for every entry slot read at the exit. -/
def FormulaF.scoped (arena : AssertionArena) (sc : Scope) : Formula → Bool
  | .at p a => scopedAt arena.nodes (sc.count p) a.index
  | .transition Φ => effectScoped sc.before Φ
  | .operation q => q.scoped sc
  | .linear F => F.vars.all (StepVar.scoped sc)
  | .defined v => StepVar.scoped sc v
  | .transport θ => decide (θ.images.size = sc.before) && θ.images.toList.all (Witness.scoped sc.after)
  | .and F G => F.scoped arena sc && G.scoped arena sc
  | .truth | .falsity => true
end Verification.Parity
