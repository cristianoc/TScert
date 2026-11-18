import Verification.Paper.TolerantFrames.Assertions

/-! # Precise correspondence obstructions

These are proved countermodels to a claimed bridge, not new inference rules.
The displayed paper mathematics is left unchanged pending an owner decision.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge
open Verification.TolerantFrames

/-- A single variable holding -0, with no heap references. -/
def negativeZeroEnv : Env := fun _ => .num 0x8000000000000000

def zeroTermEquality : Formula :=
  .and (.atom (.le (.scale 1 (.path .value ⟨0, []⟩)) (.constant 0)))
    (.atom (.le (.constant 0) (.scale 1 (.path .value ⟨0, []⟩))))

def positiveZeroValueEquality : Formula :=
  .atom (.equal ⟨0, []⟩ (.base (.literal (.number 0))))

/-- Definition 23's reverse literal-equality bridge cannot hold under raw
stored-value equality. This uses one numeric variable and no heap locations,
and works in every indexed heap, at the valid invocation mark zero. -/
theorem negative_zero_obstruction (s : IndexedHeap) :
    ValidContext negativeZeroEnv 0 s ∧ zeroTermEquality.Holds negativeZeroEnv 0 s ∧
      ¬ positiveZeroValueEquality.Holds negativeZeroEnv 0 s := by
  have hi : intValue (.num 0x8000000000000000) = some 0 := by decide
  refine ⟨⟨fun _ => RefsOk_of_nil rfl, fun _ => rfl, Nat.zero_le _⟩, ?_, ?_⟩
  · simp [zeroTermEquality, Formula.Holds, Atom.Holds, Expression.eval, Term.eval,
      Parity.Path.read, readPath, negativeZeroEnv, kindValue, hi]
  · simp [positiveZeroValueEquality, Formula.Holds, Atom.Holds, Value.eval, BaseValue.eval,
      ScalarLiteral.eval, Parity.Path.read, readPath, negativeZeroEnv]

end Verification.Paper.TolerantFrames
