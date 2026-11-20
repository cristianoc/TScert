import Verification.Semantics.FormulaScopes
import Verification.Semantics.ExitConjunction

/-! # The scope of a schema

A schema reads a call's values below a position (the note *Tolerant
frames*, §6, rule Call, a specification over its parameters): code of arity
`n` binds the receiver and its first `n` parameters, so its specification
reads entry positions below `n + 1` and exit positions below `n + 2`.
`Exits.belowRow n` checks this of a schema: its frames and its formulas
instantiated at the code's arity scoped there, no append of the actuals from
a position on (a sequence whose length is the call's), and transports
completed by the next exit slot whose replacements are in scope. Such a
schema states, at every call, one specification scoped at the code's arity
(`Exits.belowRow_sound`), so actuals past the first `n` do not change its
exits (`Exits.exitPost_take`).

Scope is not certification: whether a body establishes a postcondition is
decided by body certification, which states no postcondition it has not
proved. -/
namespace Verification.CallEffects
open Verification Footprints Parity TolerantFrames

/-- A sequence of a call's values of the same length at every call: no
actuals from a position on. -/
def _root_.Verification.Parity.WitnessSeq.fixedLength : WitnessSeq → Bool
  | .fixed _ => true
  | .restFrom _ => false
  | .append a b => a.fixedLength && b.fixedLength

theorem _root_.Verification.Parity.WitnessSeq.instantiate_fixedLength {a : WitnessSeq} (h : a.fixedLength = true) (m n : Nat) :
    a.instantiate m = a.instantiate n := by
  induction a with
  | fixed _ => rfl
  | restFrom _ => cases h
  | append a b iha ihb =>
    simp only [WitnessSeq.fixedLength, Bool.and_eq_true] at h
    simp only [WitnessSeq.instantiate, iha h.1, ihb h.2]

/-- A schema formula whose appends' arguments have the same length at every
call. -/
def _root_.Verification.Parity.FormulaF.fixedLength {T : Type} : FormulaF WitnessSeq T → Bool
  | .operation (.push _ _ a) => a.fixedLength
  | .and F G => F.fixedLength && G.fixedLength
  | _ => true

theorem instantiateFormula_fixedLength {F : FormulaSchema} (h : F.fixedLength = true) (m N : Nat) (hm : m + 1 ≤ N)
    (n : Nat) (hn : n + 1 ≤ N) : instantiateFormula ⟨m, N, hm⟩ F = instantiateFormula ⟨n, N, hn⟩ F := by
  unfold instantiateFormula
  induction F with
  | operation q =>
    cases q with
    | push x x' a =>
      simp only [FormulaF.fixedLength] at h
      simp only [FormulaF.map, OperationPostF.map, WitnessSeq.instantiate_fixedLength h m n]
    | _ => rfl
  | and F G ihF ihG =>
    simp only [FormulaF.fixedLength, Bool.and_eq_true] at h
    simp only [FormulaF.map] at ihF ihG ⊢
    rw [ihF h.1, ihG h.2]
  | _ => rfl

/-- The instantiation at code of arity `n`: `n` actuals, the receiver and
the actuals in scope. -/
def arityInstantiation (n : Nat) : CallInstantiation := ⟨n, n + 1, Nat.le_refl _⟩

/-- Whether one exit schema reads entry positions below `n + 1` and exit
positions below `n + 2`. -/
def ExitSchema.belowRow (n : Nat) (q : ExitSchema) : Bool :=
  effectScoped (n + 1) q.frame && q.ensures.all (·.fixedLength) &&
    q.ensures.all fun F => (instantiateFormula (arityInstantiation n) F).scoped AssertionArena.empty ⟨n + 1, n + 2⟩

/-- **A schema scoped at code of arity `n`**: its transports completed by
the next exit slot and their replacements below `n + 1`, and both exits
scoped. -/
def Exits.belowRow (n : Nat) (x : Exits ExitSchema) : Bool :=
  x.canonicalTransports && decide (x.slots ≤ n + 1) && x.normal.belowRow n && x.exceptional.belowRow n

/-- The scope of a function's schema at arity `n`: `Exits.belowRow`. -/
def Exits.below (n : Nat) (x : Exits ExitSchema) : Bool := x.belowRow n

/-- **A scoped schema states one specification at every call**, scoped at
code of arity `n` (the note's Call: the specification at the call's arity
is the one at the code's arity). -/
theorem Exits.belowRow_sound {n : Nat} {x : Exits ExitSchema} (h : x.belowRow n = true) :
    ∃ q : Exits ExitSpec,
      (∀ c, effectScoped (n + 1) (q.get c).frame = true ∧
        (q.get c).ensures.all (FormulaF.scoped AssertionArena.empty ⟨n + 1, n + 2⟩) = true) ∧
      ∀ c r args s s' v, x.exitPost c r args s s' v ↔
        (q.get c).Holds AssertionArena.empty (callState r args v s.h.length s s') := by
  simp only [Exits.belowRow, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hcan, hslots⟩, hnorm⟩, hexc⟩ := h
  have hget : ∀ c, (x.get c).belowRow n = true := fun c => by cases c <;> assumption
  refine ⟨x.map (ExitSchema.instantiate (arityInstantiation n)), fun c => ?_, fun c r args s s' v => ?_⟩
  · have hq := hget c
    simp only [ExitSchema.belowRow, Bool.and_eq_true] at hq
    rw [Exits.get_map]
    refine ⟨hq.1.1, ?_⟩
    simp only [ExitSchema.instantiate, List.all_map]
    exact hq.2
  · have hq := hget c
    simp only [ExitSchema.belowRow, Bool.and_eq_true] at hq
    let N := max (args.length + 1) (n + 1)
    unfold Exits.exitPost
    rw [← instantiate_completion hcan (N := N) (by omega), Exits.get_map]
    rw [← ExitSchema.holds_widen (ι := arityInstantiation n) (ι' := ⟨n, N, by omega⟩)
      (Exits.canonicalTransports_get hcan c) rfl (Nat.le_trans (Exits.slots_get x c) hslots)
      (by show n + 1 ≤ N; omega) _ (callState_shifted r args v s.h.length s s')]
    simp only [ExitSchema.instantiate]
    rw [List.map_congr_left fun F hF =>
      instantiateFormula_fixedLength (List.all_eq_true.mp hq.1.2 F hF) args.length N _ n _]

/-- **A call and the call of its first `m ≥ n` actuals agree below the
scope of the receiver and the first `n` parameters**: the same entry
values at positions up to `n`, the same exit values at positions up to
`n + 1`. -/
theorem callState_agreeBelow_take {n m : Nat} (hm : n ≤ m) (r : Tm) (args : List Tm) (v : Tm) (k : Nat)
    (s s' : IndexedHeap) :
    (callState r args v k s s').AgreeBelow ⟨n + 1, n + 2⟩ (callState r (args.take m) v k s s') := by
  have hc : ∀ i < n + 1, callEnv r (args.take m) i = callEnv r args i := by
    intro i hi
    unfold callEnv
    split
    · rfl
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
      rw [ite_eq_left (by omega)]
  refine ⟨hc, fun i hi => ?_, rfl, rfl, rfl⟩
  change i < n + 2 at hi
  show ensuresEnv v r (args.take m) i = ensuresEnv v r args i
  unfold ensuresEnv
  split
  · rfl
  · exact hc _ (by omega)

/-- **Arity independence**: a schema scoped at code of arity `n` has the
same exits at the first `m ≥ n` actuals of a call as at all of them. -/
theorem Exits.exitPost_take {n m : Nat} {x : Exits ExitSchema} (h : x.belowRow n = true) (hm : n ≤ m)
    {c : Completion} {r : Tm} {args : List Tm} {s s' : IndexedHeap} {v : Tm} :
    x.exitPost c r (args.take m) s s' v ↔ x.exitPost c r args s s' v := by
  obtain ⟨q, hq, hx⟩ := Exits.belowRow_sound h
  rw [hx, hx]
  exact ExitSpec.holds_scoped_congr (hq c).1 (hq c).2 (callState_agreeBelow_take hm r args v s.h.length s s')

end Verification.CallEffects
