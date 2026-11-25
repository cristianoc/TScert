import Verification.Semantics.AssertionScopes
import Verification.Semantics.ExitSchemas

/-! # A scoped formula reads its scope alone

A two-state formula scoped at `sc` (`FormulaF.scoped`) reads the entry
valuation below `sc.before` and the exit valuation below `sc.after`, besides
the two states and the mark. Two two-states agreeing on those
(`TwoState.AgreeBelow`) satisfy it alike (`FormulaF.holds_scoped_congr`),
and so an exit specification whose frame and postconditions are scoped
(`ExitSpec.holds_scoped_congr`). Each kind of formula reads its scope by
its own congruence: an assertion by `sat_scoped_congr`, a transition by
`EffectAction.congr_roots`, a linear fact and definedness by the slots
their terms read (`stepValue_scoped_congr`), a transport by its images'
roots and its domain (`Substitution.holdsAt_scoped_congr`), and an
operational post by the slots each constructor reads
(`OperationPostF.holds_scoped_congr`). -/
namespace Verification.Parity
open Verification Footprints HeapKnowledge TolerantFrames

/-- **Two two-states agreeing below a scope**: the same states and mark, the
entry valuations agreeing below `sc.before` and the exit valuations below
`sc.after`. -/
structure TwoState.AgreeBelow (sc : Scope) (s s' : TwoState) : Prop where
  beforeEnv : ∀ i < sc.before, s'.beforeEnv i = s.beforeEnv i
  afterEnv : ∀ i < sc.after, s'.afterEnv i = s.afterEnv i
  mark : s'.mark = s.mark
  before : s'.before = s.before
  after : s'.after = s.after

/-! ## Paths, witnesses and terms -/

/-- A path reads its root's value alone. -/
theorem Path.read_scoped_congr {n : Nat} {p : Path} (hp : p.scoped n = true) {η η' : Env}
    (he : ∀ i < n, η' i = η i) (h : Heap) : p.read η' h = p.read η h := by
  simp only [Path.scoped, decide_eq_true_eq] at hp
  simp only [Path.read, he p.root hp]

/-- A witness reads its path's root alone. -/
theorem Witness.value_scoped_congr {n : Nat} {w : Witness} (hw : w.scoped n = true) {η η' : Env}
    (he : ∀ i < n, η' i = η i) (h : Heap) : w.value η' h = w.value η h := by
  cases w with
  | path p => exact Path.read_scoped_congr hw he h
  | literal _ => rfl

/-- **A term reads its slot's value alone** (`termAt`). -/
theorem termAt_congr {ρ ρ' : Env} {t : Term} (he : ρ' t.slot = ρ t.slot) (h : Heap) :
    termAt ρ' h t = termAt ρ h t := by
  simp only [termAt, he]

/-- **A scoped two-state variable reads its scope alone.** -/
theorem stepValue_scoped_congr {sc : Scope} {s s' : TwoState} (hs : s.AgreeBelow sc s') {v : StepVar}
    (hv : StepVar.scoped sc v = true) : stepValue s' v = stepValue s v := by
  cases v with
  | before t =>
    simp only [StepVar.scoped, Bool.and_eq_true, decide_eq_true_eq] at hv
    simp only [stepValue, hs.before]; exact termAt_congr (hs.beforeEnv _ hv.2) _
  | after t =>
    simp only [StepVar.scoped, Bool.and_eq_true, decide_eq_true_eq] at hv
    simp only [stepValue, hs.after]; exact termAt_congr (hs.afterEnv _ hv.2) _

/-! ## Transports -/

/-- An image of a substitution is one of its images, at a position in its
domain. -/
theorem Substitution.image_mem {θ : Substitution} {i : Nat} {w : Witness} (h : θ.image i = some w) :
    i < θ.images.size ∧ w ∈ θ.images.toList := by
  unfold Substitution.image at h
  cases hw : θ.images[i]? with
  | none => rw [hw] at h; cases h
  | some w0 =>
    rw [hw] at h
    dsimp only at h
    split at h
    · cases h
    · cases h
      obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.mp hw
      exact ⟨hi, by rw [← he]; exact Array.getElem_mem_toList hi⟩

/-- **A substitution reads its domain of the target and its images' roots
of the source alone.** -/
theorem Substitution.holds_scoped_congr {θ : Substitution} {n : Nat}
    (hw : θ.images.toList.all (Witness.scoped n) = true) {target target' source source' : Env}
    (ht : ∀ i < θ.images.size, target' i = target i) (hs : ∀ i < n, source' i = source i) (h : Heap) :
    θ.Holds target' source' h ↔ θ.Holds target source h := by
  have hv : ∀ i w, θ.image i = some w → (w.value source' h = some (target' i) ↔ w.value source h = some (target i)) := by
    intro i w hi
    obtain ⟨hlt, hmem⟩ := Substitution.image_mem hi
    rw [Witness.value_scoped_congr (List.all_eq_true.mp hw w hmem) hs h, ht i hlt]
  exact ⟨fun hθ i w hi => (hv i w hi).mp (hθ i w hi), fun hθ i w hi => (hv i w hi).mpr (hθ i w hi)⟩

/-- **A transport reads its domain of the target and its images' roots of
the source alone**, at the state and under a box (`Substitution.HoldsAt`). -/
theorem Substitution.holdsAt_scoped_congr {θ : Substitution} {n : Nat}
    (hw : θ.images.toList.all (Witness.scoped n) = true) {target target' source source' : Env}
    (ht : ∀ i < θ.images.size, target' i = target i) (hs : ∀ i < n, source' i = source i)
    (s : IndexedHeap) : θ.HoldsAt target' source' s ↔ θ.HoldsAt target source s := by
  have hbw : θ.box.images.toList.all (Witness.scoped n) = true := hw
  simp only [Substitution.HoldsAt, Substitution.holds_scoped_congr hw ht hs,
    Substitution.holds_scoped_congr hbw ht hs]

/-! ## Operational posts -/

private theorem mapM_congr {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.mapM f = l.mapM g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.mapM_cons, h a (List.mem_cons_self ..), mapM_congr fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- **An operational post reads its scope alone**, for every constructor. -/
theorem OperationPostF.holds_scoped_congr {sc : Scope} {s s' : TwoState} (hs : s.AgreeBelow sc s')
    {q : OperationPost} (hq : q.scoped sc = true) : q.Holds s' ↔ q.Holds s := by
  have hb := hs.beforeEnv
  have ha := hs.afterEnv
  obtain ⟨b, a, m, B, A⟩ := s
  obtain ⟨b', a', m', B', A'⟩ := s'
  obtain ⟨-, -, -, hB, hA⟩ := hs
  dsimp only at hb ha hB hA
  subst hB hA
  cases q with
  | arith op l r y =>
    simp only [OperationPostF.scoped, Bool.and_eq_true] at hq
    simp only [OperationPostF.Holds, Witness.value_scoped_congr hq.1.1 ha, Witness.value_scoped_congr hq.1.2 ha,
      Path.read_scoped_congr hq.2 ha]
  | stringLength x y =>
    simp only [OperationPostF.scoped, Bool.and_eq_true] at hq
    simp only [OperationPostF.Holds, Path.read_scoped_congr hq.1 ha, Path.read_scoped_congr hq.2 ha]
  | stringRead x i y =>
    simp only [OperationPostF.scoped, Bool.and_eq_true] at hq
    simp only [OperationPostF.Holds, Path.read_scoped_congr hq.1.1 ha, Witness.value_scoped_congr hq.1.2 ha,
      Path.read_scoped_congr hq.2 ha]
  | lengthsKept x x' =>
    simp only [OperationPostF.scoped, Bool.and_eq_true, decide_eq_true_eq] at hq
    simp only [OperationPostF.Holds, hb x hq.1, ha x' hq.2]
  | boundedWrite x i x' =>
    simp only [OperationPostF.scoped, Bool.and_eq_true, decide_eq_true_eq] at hq
    simp only [OperationPostF.Holds, hb x hq.1.1, hb i hq.1.2, ha x' hq.2]
  | push x x' args =>
    simp only [OperationPostF.scoped, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hq
    have hm : args.mapM (·.value b' B'.h) = args.mapM (·.value b B'.h) :=
      mapM_congr fun w hw => Witness.value_scoped_congr (hq.2 w hw) hb B'.h
    simp only [OperationPostF.Holds, hm, hb x hq.1.1, ha x' hq.1.2]
  | fact p l F =>
    simp only [OperationPostF.scoped, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hq
    cases p
    · simp only [OperationPostF.Holds, TwoState.env, TwoState.state]
      exact (IndexFact.holdsAt_congr (ε := ⟨b', B'.h⟩) (h := B'.h) fun i hi => hb _ (hq.1 i hi)).trans
        (IndexFact.holdsAt_congr_entry rfl fun i hi => hb i (hq.2 i hi))
    · simp only [OperationPostF.Holds, TwoState.env, TwoState.state]
      exact (IndexFact.holdsAt_congr (ε := ⟨b', B'.h⟩) (h := A'.h) fun i hi => ha _ (hq.1 i hi)).trans
        (IndexFact.holdsAt_congr_entry rfl fun i hi => hb i (hq.2 i hi))
  | freshSpine x =>
    simp only [OperationPostF.scoped, decide_eq_true_eq] at hq
    simp only [OperationPostF.Holds, ha x hq]
  | freshObject x =>
    simp only [OperationPostF.scoped, decide_eq_true_eq] at hq
    simp only [OperationPostF.Holds, ha x hq]
  | freshRegion x =>
    simp only [OperationPostF.scoped, decide_eq_true_eq] at hq
    simp only [OperationPostF.Holds, ha x hq]
  | elementsWhen x v y R =>
    simp only [OperationPostF.scoped, Bool.and_eq_true, decide_eq_true_eq] at hq
    simp only [OperationPostF.Holds, ha x hq.1, ha y hq.2]
  | spineExtends x =>
    simp only [OperationPostF.scoped, decide_eq_true_eq] at hq
    simp only [OperationPostF.Holds, hb x hq]
  | viewWrite x i v f =>
    simp only [OperationPostF.scoped, Bool.and_eq_true, decide_eq_true_eq] at hq
    simp only [OperationPostF.Holds, hb x hq.1.1, hb i hq.1.2, hb v hq.2]
  | shallowCopy x x' =>
    simp only [OperationPostF.scoped, Bool.and_eq_true, decide_eq_true_eq] at hq
    simp only [OperationPostF.Holds, hb x hq.1, ha x' hq.2]

/-! ## Formulas -/

/-- **The scope transfer**: a formula scoped at `sc` holds alike at two
two-states with the same states and mark whose valuations agree below the
scope. -/
theorem FormulaF.holds_scoped_congr {arena : AssertionArena} {sc : Scope} {s s' : TwoState}
    (hs : s.AgreeBelow sc s') : ∀ {F : Formula}, F.scoped arena sc = true → (Holds arena s' F ↔ Holds arena s F)
  | .at p a, hF => by
    simp only [FormulaF.scoped] at hF
    cases p
    · simp only [Holds, TwoState.env, TwoState.state, hs.mark, hs.before]
      exact sat_scoped_congr hF hs.beforeEnv
    · simp only [Holds, TwoState.env, TwoState.state, hs.mark, hs.after]
      exact sat_scoped_congr hF hs.afterEnv
  | .transition Φ, hF => by
    simp only [FormulaF.scoped, effectScoped, List.all_eq_true, decide_eq_true_eq] at hF
    simp only [Holds, hs.before, hs.after]
    exact EffectAction.congr_roots fun x ⟨e, he, hx⟩ => hs.beforeEnv x (hF e he x hx)
  | .operation q, hF => OperationPostF.holds_scoped_congr hs hF
  | .linear F, hF => by
    simp only [FormulaF.scoped, List.all_eq_true] at hF
    simp only [Holds]
    exact ⟨factAt_congr fun x hx => (stepValue_scoped_congr hs (hF x hx)).symm,
      factAt_congr fun x hx => stepValue_scoped_congr hs (hF x hx)⟩
  | .defined v, hF => by
    simp only [FormulaF.scoped] at hF
    simp only [Holds]
    rw [stepValue_scoped_congr hs hF]
  | .transport θ, hF => by
    simp only [FormulaF.scoped, Bool.and_eq_true, decide_eq_true_eq] at hF
    simp only [Holds, hs.after]
    exact Substitution.holdsAt_scoped_congr hF.2 (fun i hi => hs.beforeEnv i (hF.1 ▸ hi)) hs.afterEnv _
  | .and F G, hF => by
    simp only [FormulaF.scoped, Bool.and_eq_true] at hF
    simp only [Holds, FormulaF.holds_scoped_congr hs hF.1, FormulaF.holds_scoped_congr hs hF.2]
  | .truth, _ => Iff.rfl
  | .falsity, _ => Iff.rfl

/-- **An exit specification scoped at `sc`** (its frame read at entry slots
below `sc.before`, its postconditions scoped) holds alike at two two-states
agreeing below the scope. -/
theorem ExitSpec.holds_scoped_congr {arena : AssertionArena} {sc : Scope} {q : CallEffects.ExitSpec}
    (hf : effectScoped sc.before q.frame = true) (he : q.ensures.all (FormulaF.scoped arena sc) = true)
    {s s' : TwoState} (hs : s.AgreeBelow sc s') : q.Holds arena s' ↔ q.Holds arena s := by
  have hT := FormulaF.holds_scoped_congr (arena := arena) (F := .transition q.frame) hs hf
  simp only [Holds] at hT
  simp only [CallEffects.ExitSpec.Holds, hT]
  refine and_congr_right fun _ => forall₂_congr fun F hF => ?_
  exact FormulaF.holds_scoped_congr hs (List.all_eq_true.mp he F hF)

end Verification.Parity
