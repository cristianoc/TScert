import Verification.Paper.TolerantFrames.AllSupport
import Verification.Paper.TolerantFrames.Renaming
import Verification.Paper.TolerantFrames.Consequences

/-! # Logical witnesses at their own state

An existential in the current assertion is witnessed at the exit state. Its
witness may have been allocated after the command entry, so opening the binder
extends only the current environment. Old assertions keep their environment.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge
open Verification.TolerantFrames

/-- Remove a fresh logical binder from the current environment only. This
leaves old assertions and their entry valuation unchanged. -/
def ExitLift (Q : Postcondition) : Postcondition :=
  fun ρ ρ' m s t => Q ρ (fun i => ρ' (i + 1)) m s t

/-- An instance of the body at a particular syntactic value. This is not an
arbitrary semantic witness: its evaluation must succeed in this environment.
Variable instances are actual capture-avoiding Formula renamings below. -/
def ValueInstantiation (F : Formula) (v : Value) : Assertion :=
  fun ρ m s => ∃ u, v.eval ρ = some u ∧ F.Holds (push u ρ) m s

theorem ScalarLiteral.source (v : ScalarLiteral) : isSourceVal v.eval = true := by
  cases v <;> try rfl
  case boolean b => cases b <;> rfl

theorem ScalarLiteral.refs {n : Nat} {W : WorldT n} (v : ScalarLiteral) : RefsOk W v.eval := by
  apply RefsOk_of_nil
  cases v <;> try rfl
  case boolean b => cases b <;> rfl

theorem BaseValue.valid {ρ m s} (hv : HeapContext ρ m s) (v : BaseValue) :
    isSourceVal (v.eval ρ) = true ∧ HeapRefs s.h (v.eval ρ) := by
  cases v with
  | «variable» x => exact ⟨hv.2.1 x, hv.1 x⟩
  | literal v => exact ⟨v.source, HeapRefs.of_world (v.refs (W := s.W))⟩

/-- Conversion returns a numeric source value, with no references. -/
theorem Value.valid {ρ m s} (hv : HeapContext ρ m s) {v : Value} {u : Val}
    (he : v.eval ρ = some u) : isSourceVal u = true ∧ HeapRefs s.h u := by
  cases v with
  | base v => cases he; exact v.valid hv
  | converted f v =>
    simp only [Value.eval] at he
    split at he <;> try cases he
    exact ⟨rfl, HeapRefs.of_nil rfl⟩

/-- The usual existential introduction, for an evaluated source value. -/
theorem exists_intro {F : Formula} {v : Value} {ρ m s} (hv : HeapContext ρ m s)
    (hi : ValueInstantiation F v ρ m s) : (Formula.existsValue F).Holds ρ m s := by
  obtain ⟨u, hu, hF⟩ := hi
  have hvalid := Value.valid hv hu
  exact ⟨u, hvalid.1, hvalid.2, hF⟩

/-- Definedness of a syntactic value at its actual current phase. -/
def ValueDefined (v : Value) : Assertion := fun ρ _ _ => ∃ u, v.eval ρ = some u

/-- Freeze the successfully evaluated current value throughout the whole
postcondition, including its old components. This is not textual substitution. -/
def EvaluatedValueInstance (Q : Val → Postcondition) (v : Value) : Postcondition :=
  fun ρ ρ' m s t => ∃ u, v.eval ρ' = some u ∧ Q u ρ ρ' m s t

theorem value_instance {Q : Val → Postcondition} {v : Value} {ρ ρ' m s t}
    (hv : HeapContext ρ' m t) (hq : ForallValue Q ρ ρ' m s t)
    (hd : ValueDefined v ρ' m t) : EvaluatedValueInstance Q v ρ ρ' m s t := by
  obtain ⟨u, hu⟩ := hd
  have hvalid := Value.valid hv hu
  exact ⟨u, hu, hq u hvalid.1 hvalid.2⟩

/-- Variable instantiation has a total syntactic representative. Other
values require literal substitution, which is a separate syntax obligation. -/
theorem ValueInstantiation.variable {F : Formula} {x : Nat} {ρ m s} :
    ValueInstantiation F (.base (.variable x)) ρ m s ↔
      (F.rename (fun | 0 => x | i + 1 => i)).Holds ρ m s := by
  rw [Formula.holds_rename]
  have he : (fun i => ρ ((fun | 0 => x | i + 1 => i) i)) = push (ρ x) ρ := by
    funext i; cases i <;> rfl
  simp [ValueInstantiation, Value.eval, BaseValue.eval, he]

end Verification.Paper.TolerantFrames
