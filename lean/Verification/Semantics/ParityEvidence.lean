import Verification.Semantics.ParityAssertions

/-! # Parity evidence: substitution, marks and support contexts

The semantic evidence of the design `docs/drafts/parity-interfaces.md`, I5,
that reads no region membership: capture-avoiding substitution of slots by
paths and its semantic equivalence (I5, "Substitution and marks"; the note
"Tolerant frames", §6, rules Call and (Rigid): "the substitution of the
witness is capture-avoiding"), the transport of freshness between marks, the
meaning of a rigid path (the note, §4, `rigid(π) ≜ ∃v. □_⊤ (π ≐ v)`), and
support contexts throughout a modality (I5, "Support contexts throughout a
modality"; the note, §5, "Support", "Respect", Theorem "Tolerant frame"). -/
namespace Verification.Parity
open Verification Footprints HeapKnowledge TolerantFrames

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

/-- **A substitution of slots by paths** (I5, `Substitution`): slot `i` of
the substituted assertion is replaced by the path `images[i]`. Slots past
the images are outside its domain. -/
structure Substitution where
  images : Array Path

namespace Substitution

/-- **The interpretation of names** (I5, `Substitution.Holds`): each image,
read at `source`, gives the value slot `i` has at `target`. -/
def Holds (θ : Substitution) (target source : Env) (h : Heap) : Prop :=
  ∀ (i : Nat) (p : Path), θ.images[i]? = some p → p.read source h = some (target i)

/-- A substitution of slots by slots: every image is a variable. -/
def isRenaming (θ : Substitution) : Bool := θ.images.toList.all fun p => p.fields.isEmpty

/-- The substitution under one more logical binder: slot `0` stays, slot
`i + 1` goes to the image of `i`, one slot further. -/
def lift (θ : Substitution) : Substitution :=
  ⟨(Path.var 0 :: θ.images.toList.map fun p => ⟨p.root + 1, p.fields⟩).toArray⟩

/-- The substitution sending each of the slots below `n` one slot further:
reading an assertion under one more binder. -/
def shift (n : Nat) : Substitution := ⟨((List.range n).map fun i => Path.var (i + 1)).toArray⟩

/-- The substitution sending slot `0` to a witness path and slot `i + 1`,
below `n + 1`, to slot `i`: instantiating a logical binder. -/
def instantiate (w : Path) (n : Nat) : Substitution :=
  ⟨(w :: (List.range n).map Path.var).toArray⟩

theorem image_mem {θ : Substitution} {i : Nat} {p : Path} (hi : θ.images[i]? = some p) : p ∈ θ.images.toList := by
  rw [← Array.getElem?_toList] at hi
  exact List.mem_of_getElem? hi

theorem renaming_fields {θ : Substitution} (hr : θ.isRenaming = true) {i : Nat} {p : Path}
    (hi : θ.images[i]? = some p) : p.fields = [] := by
  have := List.all_eq_true.mp hr p (image_mem hi)
  simpa using this

/-- A renaming holds at every heap where it holds at one. -/
theorem Holds.heap {θ : Substitution} (hr : θ.isRenaming = true) {target source : Env} {h : Heap}
    (hθ : θ.Holds target source h) (h' : Heap) : θ.Holds target source h' := by
  intro i p hi
  rw [Path.read_heap (renaming_fields hr hi)]; exact hθ i p hi

theorem lift_renaming {θ : Substitution} (hr : θ.isRenaming = true) : θ.lift.isRenaming = true := by
  simp only [isRenaming, lift, List.all_cons, List.all_map, Bool.and_eq_true, List.all_eq_true,
    Function.comp_def] at hr ⊢
  exact ⟨rfl, fun p hp => hr p hp⟩

/-- **The lifted substitution holds under the binder.** -/
theorem Holds.lift {θ : Substitution} {target source : Env} {h : Heap} (hθ : θ.Holds target source h) (v : Val) :
    θ.lift.Holds (push v target) (push v source) h := by
  intro i p hi
  simp only [Substitution.lift, List.getElem?_toArray] at hi
  cases i with
  | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi; rfl
  | succ i =>
    simp only [List.getElem?_cons_succ, List.getElem?_map, Option.map_eq_some_iff] at hi
    obtain ⟨q, hq, rfl⟩ := hi
    exact hθ i q (by rw [← Array.getElem?_toList]; exact hq)

theorem shift_holds (n : Nat) (η : Env) (v : Val) (h : Heap) : (shift n).Holds η (push v η) h := by
  intro i p hi
  simp only [shift, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at hi
  obtain ⟨j, hj, rfl⟩ := hi
  obtain ⟨_, hj'⟩ := List.getElem?_eq_some_iff.mp hj
  simp only [List.getElem_range] at hj'
  subst hj'; rfl

theorem shift_renaming (n : Nat) : (shift n).isRenaming = true := by
  simp [isRenaming, shift, Path.var]

/-- **Instantiating a binder with a witness the path reads.** -/
theorem instantiate_holds {w : Path} {n : Nat} {η : Env} {h : Heap} {v : Val} (hw : w.read η h = some v) :
    (instantiate w n).Holds (push v η) η h := by
  intro i p hi
  simp only [instantiate, List.getElem?_toArray] at hi
  cases i with
  | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi; exact hw
  | succ i =>
    simp only [List.getElem?_cons_succ, List.getElem?_map, Option.map_eq_some_iff] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    obtain ⟨_, hj'⟩ := List.getElem?_eq_some_iff.mp hj
    simp only [List.getElem_range] at hj'
    subst hj'; rfl

end Substitution

/-! ## Substituting into atoms -/

/-- A path with its root replaced by its image. -/
def substPath (θ : Substitution) (p : Path) : Option Path :=
  θ.images[p.root]?.map fun q => ⟨q.root, q.fields ++ p.fields⟩

/-- A current term with its slot replaced by its image. -/
def substTerm (θ : Substitution) (t : Term) : Option Term :=
  if t.atEntry then none else θ.images[t.slot]?.map fun q => Term.now t.kind q.root (q.fields ++ t.path)

/-- A scalar parameter with its slot renamed: its image is a variable, so
it stays a scalar. -/
def substScalar (θ : Substitution) (t : Term) : Option Term :=
  if t.atEntry then none else match θ.images[t.slot]? with
    | some q => if q.fields.isEmpty then some (Term.now t.kind q.root t.path) else none
    | none => none

/-- A variable of a scalar body with its parameter renamed. -/
def substBound (θ : Substitution) : Bound → Option Bound
  | .free t => (substScalar θ t).map .free
  | b => some b

def substWitness (θ : Substitution) : Witness → Option Witness
  | .path p => (substPath θ p).map .path
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
  have := hθ p.root q hq
  simp only [Path.read] at this
  rw [this]; rfl

theorem substTerm_termAt (hθ : θ.Holds target source h) {t t' : Term} (hs : substTerm θ t = some t') :
    termAt source h t' = termAt target h t := by
  unfold substTerm at hs
  split at hs
  · cases hs
  · obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hs
    have := hθ t.slot q hq
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
        have := hθ t.slot q hq
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
    obtain ⟨p', hp, rfl⟩ := Option.map_eq_some_iff.mp hs
    exact substPath_read hθ hp
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

/-- **Node `b` is node `a` under the substitution `θ`** (I5,
`substAssertion`, as a check of two arena nodes): the same connective, atoms
and paths substituted, the substitution lifted under a logical binder.
Under a box the substitution is a renaming and the effect reads no slot, so
the substituted assertion means the same at every state an action reaches. -/
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
      (Φ == Ψ && effectEnvFree Φ && θ.isRenaming) && substCheck nodes θ x.index y.index
    else false
  | _, _ => false
termination_by a + b

set_option maxHeartbeats 1000000 in
/-- **Checked substitution is semantic** (I5, `substAssertion_sound`):
where the images read at `source` give the target values, the substituted
node holds at `source` exactly where the node holds at `target`. -/
theorem substCheck_sound (nodes : Array AssertionNode) :
    ∀ (n a b : Nat), a + b = n → ∀ (θ : Substitution) (target source : Env) (m : Nat) (s : IndexedHeap),
      substCheck nodes θ a b = true → θ.Holds target source s.h →
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
    exact substAtom_holds hθ hc
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
    exact separated_subst hθ hc.1 hc.2
  · rename_i p q p' q'
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact apart_subst hθ hc.1 hc.2
  · rename_i p p'
    simp only [beq_iff_eq] at hc
    exact fresh_subst hθ hc
  · rename_i Φ x Ψ y
    split at hc
    · rename_i hi
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨rfl, henv⟩, hren⟩, hrec⟩ := hc
      simp only [hi.1, hi.2, dite_true]
      constructor
      · intro hs s' ha'
        exact (ih _ (by omega) _ _ rfl θ target source m s' hrec (hθ.heap hren s'.h)).mp
          (hs s' (ha'.envFree henv))
      · intro hs s' ha'
        exact (ih _ (by omega) _ _ rfl θ target source m s' hrec (hθ.heap hren s'.h)).mpr
          (hs s' (ha'.envFree henv))
    · cases hc

/-- **Substitution at the arena level**: `b` is `a[θ]`. -/
theorem sat_subst {arena : AssertionArena} {θ : Substitution} {a b : AssertionRef}
    (hc : substCheck arena.nodes θ a.index b.index = true) {target source : Env} {m : Nat} {s : IndexedHeap}
    (hθ : θ.Holds target source s.h) : Sat arena source m s b ↔ Sat arena target m s a :=
  substCheck_sound arena.nodes _ a.index b.index rfl θ target source m s hc hθ

/-- **Reading an assertion under one more binder** (the note's `∃`
elimination, I4 `existsElim`): where `b` is `a` with each slot below `n`
shifted, `b` holds under any value pushed exactly where `a` holds. -/
theorem sat_shift {arena : AssertionArena} {n : Nat} {a b : AssertionRef}
    (hc : substCheck arena.nodes (Substitution.shift n) a.index b.index = true) {η : Env} {m : Nat}
    {s : IndexedHeap} (v : Val) : Sat arena (push v η) m s b ↔ Sat arena η m s a :=
  sat_subst hc (Substitution.shift_holds n η v s.h)

/-- **Instantiating a binder** (I4 `existsIntro`): where `b` is the body `a`
with slot `0` read as the path `w`, `b` holds where `a` holds of the value
`w` reads. -/
theorem sat_instantiate {arena : AssertionArena} {w : Path} {n : Nat} {a b : AssertionRef}
    (hc : substCheck arena.nodes (Substitution.instantiate w n) a.index b.index = true) {η : Env} {m : Nat}
    {s : IndexedHeap} {v : Val} (hw : w.read η s.h = some v) : Sat arena η m s b ↔ Sat arena (push v η) m s a :=
  sat_subst hc (Substitution.instantiate_holds hw)

/-! ## Building a substituted assertion -/

/-- Node `i` of `src` under `θ`, its nodes appended to `acc`: the reference
of the new node. Shared subterms are rebuilt where they occur. -/
def substBuild (src : Array AssertionNode) (θ : Substitution) (i : Nat) (acc : Array AssertionNode) :
    Option (Array AssertionNode × Nat) :=
  let push := fun (acc : Array AssertionNode) (n : AssertionNode) => some (acc.push n, acc.size)
  match src[i]? with
  | some .truth => push acc .truth
  | some .falsity => push acc .falsity
  | some (.atom x) => (substAtom θ x).bind fun y => push acc (.atom y)
  | some (.and l r) =>
    if _ : l.index < i ∧ r.index < i then do
      let (acc, l') ← substBuild src θ l.index acc
      let (acc, r') ← substBuild src θ r.index acc
      push acc (.and ⟨l'⟩ ⟨r'⟩)
    else none
  | some (.guarded l r) =>
    if _ : l.index < i ∧ r.index < i then do
      let (acc, l') ← substBuild src θ l.index acc
      let (acc, r') ← substBuild src θ r.index acc
      push acc (.guarded ⟨l'⟩ ⟨r'⟩)
    else none
  | some (.existsValue b) =>
    if _ : b.index < i then do
      let (acc, b') ← substBuild src θ.lift b.index acc
      push acc (.existsValue ⟨b'⟩)
    else none
  | some (.separated p q) => do push acc (.separated (← substPath θ p) (← substPath θ q))
  | some (.apart p q) => do push acc (.apart (← substPath θ p) (← substPath θ q))
  | some (.fresh p) => do push acc (.fresh (← substPath θ p))
  | some (.box Φ b) =>
    if _ : b.index < i then do
      let (acc, b') ← substBuild src θ b.index acc
      push acc (.box Φ ⟨b'⟩)
    else none
  | none => none
termination_by i

/-- `nodes'` extends `nodes`: it has every node of `nodes` at its index. -/
def AssertionArena.extends (nodes' nodes : Array AssertionNode) : Bool :=
  decide (nodes.size ≤ nodes'.size) && (List.range nodes.size).all fun j => nodes'[j]? == nodes[j]?

/-- **An extended arena satisfies its old nodes as they were.** -/
theorem satNode_extend {nodes nodes' : Array AssertionNode} (he : AssertionArena.extends nodes' nodes = true) :
    ∀ i, i < nodes.size → ∀ η m s, satNode nodes' i η m s ↔ satNode nodes i η m s := by
  have hj : ∀ j, j < nodes.size → nodes'[j]? = nodes[j]? := by
    intro j hjs
    simp only [AssertionArena.extends, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at he
    exact he.2 j hjs
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
  intro hi η m s
  rw [satNode, satNode, hj i hi]
  cases hn : nodes[i]? with
  | none => exact Iff.rfl
  | some n =>
    cases n with
    | and l r =>
      dsimp only
      apply and_congr
      · by_cases hl : l.index < i
        · simp only [hl, dite_true]; exact ih _ hl (by omega) η m s
        · simp only [hl, dite_false]
      · by_cases hr : r.index < i
        · simp only [hr, dite_true]; exact ih _ hr (by omega) η m s
        · simp only [hr, dite_false]
    | guarded l r =>
      dsimp only
      apply or_congr
      · by_cases hl : l.index < i
        · simp only [hl, dite_true]; exact ih _ hl (by omega) η m s
        · simp only [hl, dite_false]
      · by_cases hr : r.index < i
        · simp only [hr, dite_true]; exact ih _ hr (by omega) η m s
        · simp only [hr, dite_false]
    | existsValue b =>
      dsimp only
      by_cases hb : b.index < i
      · simp only [hb, dite_true]; exact exists_congr fun v => ih _ hb (by omega) _ m s
      · simp only [hb, dite_false]
    | box Φ b =>
      dsimp only
      by_cases hb : b.index < i
      · simp only [hb, dite_true]; exact forall_congr' fun s' => imp_congr_right fun _ => ih _ hb (by omega) η m s'
      · simp only [hb, dite_false]
    | _ => exact Iff.rfl

/-- **Substitution into an assertion** (I5, `substAssertion`): the arena
extended by `A` under `θ`, and the new node's reference. The result is
checked: it extends the arena, it is valid, and its node is `A[θ]`. -/
def substAssertion (arena : AssertionArena) (θ : Substitution) (A : AssertionRef) :
    Except String (AssertionArena × AssertionRef) :=
  match substBuild arena.nodes θ A.index arena.nodes with
  | some (nodes', r) =>
    if A.index < arena.nodes.size && AssertionArena.extends nodes' arena.nodes &&
        substCheck nodes' θ A.index r && AssertionArena.check ⟨nodes'⟩ then
      .ok (⟨nodes'⟩, ⟨r⟩)
    else .error "substAssertion: the substituted assertion is not well formed"
  | none => .error "substAssertion: a slot is outside the substitution"

/-- **Substitution into an assertion is semantic** (I5,
`substAssertion_sound`): the result is a valid extension in which the new
node holds at `source` exactly where `A` holds at `target`. -/
theorem substAssertion_sound {arena arena' : AssertionArena} {θ : Substitution} {A A' : AssertionRef}
    (hc : substAssertion arena θ A = .ok (arena', A')) {target source : Env} {m : Nat} {s : IndexedHeap}
    (hθ : θ.Holds target source s.h) :
    arena'.Valid ∧ (Sat arena' source m s A' ↔ Sat arena target m s A) := by
  unfold substAssertion at hc
  split at hc
  · rename_i nodes' r _
    split at hc
    · rename_i hok
      cases hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨⟨hA, hext⟩, hsub⟩, hvalid⟩ := hok
      refine ⟨AssertionArena.check_valid hvalid, ?_⟩
      have h1 := substCheck_sound nodes' _ A.index r rfl θ target source m s hsub hθ
      exact h1.trans (satNode_extend hext A.index hA target m s)
    · cases hc
  · cases hc

/-! ## Marks -/

/-- **Caller and callee marks** (I5, `MarkEvidence`): the callee's entry
mark is at or above its caller's. -/
structure MarkEvidence where
  caller : Nat
  callee : Nat
  ordered : caller ≤ callee

/-- **Freshness transport is directional** (I5, `fresh_mark_mono`): a store
fresh for a later callee mark is fresh for the caller. -/
theorem fresh_mark_mono {caller callee : Nat} (hm : caller ≤ callee) {v : Val} (hf : FreshAt callee v) :
    FreshAt caller v :=
  hf.lower hm

theorem freshPath_mark_mono (e : MarkEvidence) {η : Env} {h : Heap} {p : Path}
    (hf : FreshPath η e.callee h p) : FreshPath η e.caller h p := by
  obtain ⟨v, hv, hfv⟩ := hf
  exact ⟨v, hv, fresh_mark_mono e.ordered hfv⟩

/-! ## Rigid paths -/

/-- **The meaning of a rigid path** (I5, `PathRigid`; the note, §4,
`rigid(π)`): the path reads one value after every admissible transition. -/
def PathRigid (p : Path) (η : Env) (s : IndexedHeap) : Prop :=
  ∃ v, ∀ s', Admissible s s' → p.read η s'.h = some v

/-- **The note's `rigid(π) ≜ ∃v. □_⊤ (π ≐ v)` is `PathRigid`**: for an arena
whose node `a` is `∃v. □_⊤ (π' ≐ v)`, `π'` being `π` read under the binder. -/
theorem sat_rigid_iff {arena : AssertionArena} (hv : arena.Valid) {a b c : AssertionRef} {p : Path}
    (ha : arena.nodes[a.index]? = some (.existsValue b)) (hb : arena.nodes[b.index]? = some (.box topEffect c))
    (hc : arena.nodes[c.index]? = some (.atom (.equal ⟨p.root + 1, p.fields⟩ (.path (Path.var 0)))))
    {η : Env} {m : Nat} {s : IndexedHeap} : Sat arena η m s a ↔ PathRigid p η s := by
  rw [sat_exists hv ha]
  have hread : ∀ (v : Val) (h : Heap), (⟨p.root + 1, p.fields⟩ : Path).read (push v η) h = p.read η h :=
    fun _ _ => rfl
  constructor
  · rintro ⟨v, hv'⟩
    refine ⟨v, fun s' hs' => ?_⟩
    have := (sat_atom hc).mp ((sat_box hv hb).mp hv' s' (EffectAction.top hs'))
    obtain ⟨u, hu, hw⟩ := this
    rw [hread] at hu
    simp only [Witness.value, Path.read, Path.var, readPath] at hw
    cases hw
    exact hu
  · rintro ⟨v, hv'⟩
    refine ⟨v, (sat_box hv hb).mpr fun s' hs' => (sat_atom hc).mpr ⟨v, ?_, rfl⟩⟩
    rw [hread]; exact hv' s' hs'.admissible

/-! ## Support contexts throughout a modality -/

/-- **A contextual support** (I5, `SupportContext`): a condition on both
endpoints of a transition. -/
abbrev SupportContext := Env → Nat → IndexedHeap → IndexedHeap → Prop

/-- **`S` supports `A` in the context `C`** (the note, §5, Definition
"Support", read in a context; I5, `Supports`): every admissible transition in
the context and within `S` keeps `A`. -/
def Supports (arena : AssertionArena) (C : SupportContext) (S : Footprint) (A : AssertionRef) : Prop :=
  ∀ η m s s', Admissible s s' → C η m s s' → Sat arena η m s A → SupportedBy S η s s' → Sat arena η m s' A

/-- **`Φ` respects `S` under `K`, semantically** (the note, §5, Definition
"Respect", read as what its proof uses): every action of `Φ` from a state of
`K` stays within `S`. -/
def Respects (arena : AssertionArena) (K : AssertionRef) (Φ S : Footprint) : Prop :=
  ∀ η m s s', Sat arena η m s K → EffectAction Φ η s s' → SupportedBy S η s s'

/-- **Context evidence valid over the entire modal domain** (I5,
`ContextThroughout`): from a state reached by an action from a state of `K`,
every further action of `Φ` is in the context. -/
def ContextThroughout (arena : AssertionArena) (K : AssertionRef) (Φ : Footprint) (C : SupportContext) : Prop :=
  ∀ η m anchor s s', Sat arena η m anchor K → EffectAction Φ η anchor s → EffectAction Φ η s s' → C η m s s'

/-- **A context of one transition gives that transition's consequence**:
the one use of actual-step evidence. Box introduction (`tolerant_frame`)
asks the context throughout the modal domain instead. -/
theorem supports_step {arena : AssertionArena} {C : SupportContext} {S : Footprint} {A : AssertionRef}
    (hs : Supports arena C S A) {η : Env} {m : Nat} {s s' : IndexedHeap} (ha : Admissible s s')
    (hc : C η m s s') (hA : Sat arena η m s A) (hS : SupportedBy S η s s') : Sat arena η m s' A :=
  hs η m s s' ha hc hA hS

/-- **The tolerant frame theorem** (the note, §5, Theorem "Tolerant frame";
I5, `tolerant_frame`): `K ∧ A ⊢ □_Φ A` where `S` supports `A` in a context
holding throughout the modal domain of `K` and `Φ`, and `Φ` respects `S`
under `K`. -/
theorem tolerant_frame {arena : AssertionArena} {C : SupportContext} {S Φ : Footprint} {K A : AssertionRef}
    (hs : Supports arena C S A) (hc : ContextThroughout arena K Φ C) (hr : Respects arena K Φ S) :
    ∀ η m s, Sat arena η m s K → Sat arena η m s A → ∀ s', EffectAction Φ η s s' → Sat arena η m s' A :=
  fun η m s hK hA s' ha =>
    hs η m s s' ha.admissible (hc η m s s s' hK (EffectAction.refl Φ η s) ha) hA (hr η m s s' hK ha)

/-- The references whose nodes are conjuncts of node `k`: `k` itself and,
through `∧`, those of its two sides. -/
def conjuncts (nodes : Array AssertionNode) (k : Nat) : List Nat :=
  k :: match nodes[k]? with
    | some (.and l r) =>
      (if _ : l.index < k then conjuncts nodes l.index else []) ++
        (if _ : r.index < k then conjuncts nodes r.index else [])
    | _ => []
termination_by k

/-- Each conjunct of a node holds where the node does. -/
theorem conjuncts_sat (nodes : Array AssertionNode) :
    ∀ k, ∀ g ∈ conjuncts nodes k, ∀ η m s, satNode nodes k η m s → satNode nodes g η m s := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro g hg η m s hk
  rw [conjuncts] at hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact hk
  · split at hg
    · rename_i l r hn
      rw [satNode, hn] at hk
      rcases List.mem_append.mp hg with hg | hg
      · split at hg
        · rename_i hl; simp only [hl, dite_true] at hk; exact ih _ hl g hg η m s hk.1
        · cases hg
      · split at hg
        · rename_i hr; simp only [hr, dite_true] at hk; exact ih _ hr g hg η m s hk.2
        · cases hg
    · cases hg

/-- **Finite context evidence** (I5, `ContextEvidence`): the context `true`,
an invariant conjunct of `K`, and conjunctions. -/
inductive ContextEvidence where
  | truth
  | invariant (g : AssertionRef)
  | conj (a b : ContextEvidence)
  deriving DecidableEq, Repr

/-- The context the evidence denotes: an invariant conjunct holds at both
endpoints. -/
def ContextEvidence.ctx (arena : AssertionArena) : ContextEvidence → SupportContext
  | .truth => fun _ _ _ _ => True
  | .invariant g => fun η m s s' => Sat arena η m s g ∧ Sat arena η m s' g
  | .conj a b => fun η m s s' => a.ctx arena η m s s' ∧ b.ctx arena η m s s'

/-- The check of context evidence against `K`: an invariant conjunct is a
conjunct of `K` with checked invariance. -/
def ContextEvidence.check (arena : AssertionArena) (K : AssertionRef) : ContextEvidence → Bool
  | .truth => true
  | .invariant g => (conjuncts arena.nodes K.index).contains g.index && invNode arena.nodes g.index
  | .conj a b => a.check arena K && b.check arena K

/-- **Checked context evidence holds throughout the modal domain.** -/
theorem ContextEvidence.sound {arena : AssertionArena} {K : AssertionRef} {Φ : Footprint} :
    ∀ ev : ContextEvidence, ev.check arena K = true → ContextThroughout arena K Φ (ev.ctx arena)
  | .truth, _ => fun _ _ _ _ _ _ _ _ => trivial
  | .invariant g, hc => by
    simp only [ContextEvidence.check, Bool.and_eq_true, List.contains_iff_mem] at hc
    intro η m anchor s s' hK ha ha'
    have hg : Sat arena η m anchor g := conjuncts_sat arena.nodes K.index g.index hc.1 η m anchor hK
    have hinv := invNode_sound arena.nodes g.index hc.2
    have h1 : Sat arena η m s g := hinv η m anchor s ha.admissible hg
    exact ⟨h1, hinv η m s s' ha'.admissible h1⟩
  | .conj a b, hc => by
    simp only [ContextEvidence.check, Bool.and_eq_true] at hc
    intro η m anchor s s' hK ha ha'
    exact ⟨a.sound hc.1 η m anchor s s' hK ha ha', b.sound hc.2 η m anchor s s' hK ha ha'⟩

end Verification.Parity
