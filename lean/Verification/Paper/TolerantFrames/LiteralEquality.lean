import Verification.Paper.TolerantFrames.Arithmetic

/-! # Safe-integer literal equality, with both stored zeros

This states the owner's correction to Definition 23. Stored value equality
implies integer term equality. The reverse recovers the unique stored value
at a nonzero integer; at zero it gives the disjunction of +0 and -0. Raw value
equality and shared integer/float meanings remain unchanged.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge TolerantFrames
open Verification.Parity (Path)

def NumberEquality (p : Path) (bits : UInt64) : Formula :=
  .atom (.equal p (.base (.literal (.number bits))))

def IntegerEquality (p : Path) (n : Int) : Formula :=
  .and (.atom (.le (.scale 1 (.path .value p)) (.constant n)))
    (.atom (.le (.constant n) (.scale 1 (.path .value p))))

def ZeroValueEquality (p : Path) : Formula :=
  .or (NumberEquality p 0) (NumberEquality p 0x8000000000000000)

/-- Nonzero safe integers have one stored IEEE representation. -/
theorem safeInt_unique_nonzero {a b : UInt64} {n : Int}
    (ha : SafeIntegers.SafeInt a n) (hb : SafeIntegers.SafeInt b n) (hn : n ≠ 0) : a = b := by
  apply UInt64.toNat_inj.mp
  rcases ha.2 with ⟨hap, ha⟩ | ⟨han, ha⟩ <;>
    rcases hb.2 with ⟨hbp, hb⟩ | ⟨hbn, hb⟩ <;> omega

/-- Zero has exactly the two stored representations, not one. -/
theorem safeInt_zero_values {bits : UInt64} (h : SafeIntegers.SafeInt bits 0) :
    bits = 0 ∨ bits = 0x8000000000000000 := by
  rcases h.2 with ⟨_, he⟩ | ⟨_, he⟩
  · left
    apply UInt64.toNat_inj.mp
    change bits.toNat = 0
    simpa only [Int.natAbs_zero, SafeIntegers.bitsOfNat_zero] using he
  · right
    apply UInt64.toNat_inj.mp
    change bits.toNat = 2 ^ 63
    simpa only [Int.natAbs_zero, SafeIntegers.bitsOfNat_zero, Nat.zero_add] using he

theorem NumberEquality.holds_iff {ρ m s p bits} :
    (NumberEquality p bits).Holds ρ m s ↔ p.read ρ s.h = some (.num bits) := by
  simp [NumberEquality, Formula.Holds, Atom.Holds, Value.eval, BaseValue.eval, ScalarLiteral.eval]

theorem IntegerEquality.holds_iff {ρ m s p n} :
    (IntegerEquality p n).Holds ρ m s ↔ (Term.path .value p).eval ρ s.h = some n := by
  cases he : (Term.path .value p).eval ρ s.h <;>
    simp [IntegerEquality, Formula.Holds, Atom.Holds, Expression.eval, he] <;> omega

/-- The unrestricted forward direction of the corrected paper clause. -/
theorem value_equality_to_integer {p : Path} {bits : UInt64} {n : Int}
    (hlit : SafeIntegers.SafeInt bits n) {ρ m s}
    (he : (NumberEquality p bits).Holds ρ m s) : (IntegerEquality p n).Holds ρ m s := by
  apply IntegerEquality.holds_iff.mpr
  simp only [Term.eval, NumberEquality.holds_iff.mp he, Option.bind_some, kindValue]
  exact intValue_num hlit

/-- The reverse direction for a nonzero safe-integer literal. -/
theorem integer_equality_to_value {p : Path} {bits : UInt64} {n : Int}
    (hlit : SafeIntegers.SafeInt bits n) (hn : n ≠ 0) {ρ m s}
    (he : (IntegerEquality p n).Holds ρ m s) : (NumberEquality p bits).Holds ρ m s := by
  have hi := IntegerEquality.holds_iff.mp he
  simp only [Term.eval, Option.bind_eq_some_iff] at hi
  obtain ⟨v, hp, hi⟩ := hi
  obtain ⟨actual, rfl, ha⟩ := intValue_safe hi
  have hab := safeInt_unique_nonzero ha hlit hn
  subst actual
  exact NumberEquality.holds_iff.mpr hp

/-- At integer zero the exact reverse conclusion is the two-value disjunction. -/
theorem integer_zero_to_values {p : Path} {ρ m s}
    (he : (IntegerEquality p 0).Holds ρ m s) : (ZeroValueEquality p).Holds ρ m s := by
  have hi := IntegerEquality.holds_iff.mp he
  simp only [Term.eval, Option.bind_eq_some_iff] at hi
  obtain ⟨v, hp, hi⟩ := hi
  obtain ⟨actual, rfl, ha⟩ := intValue_safe hi
  rcases safeInt_zero_values ha with rfl | rfl
  · exact .inl (NumberEquality.holds_iff.mpr hp)
  · exact .inr (NumberEquality.holds_iff.mpr hp)

end Verification.Paper.TolerantFrames
