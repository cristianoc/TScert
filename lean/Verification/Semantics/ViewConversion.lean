import Verification.Semantics.Worlds
/-!
# The conversion of a typed array's format

A write through a typed array of format `t` stores the format's total
conversion of the number written (the note *Tolerant frames*, "The typed
array's steps"; ECMA-262, NumericToRawBytes then RawBytesToNumeric):
`Uint8`, `Uint16` and `Int32` send a number that is not finite to `0` and any
other to its integer part modulo `2^8`, `2^16` and `2^32`, the last taken in
`[-2^31, 2^31)`; `Float64` stores the number itself (`ViewFormat.conv`, over
the bits of a double), a NaN read back as a NaN whose bits the host chooses
(`SameNumber`: the element's bits equal the conversion's, or both are NaNs).

- **Its result is a number the format stores** (`ViewFormat.conv_stored`,
  `ViewFormat.Stored`).
- **On the integers the format stores it is the identity on the integer**
  (`ViewFormat.conv_safeInt`): an integer format keeps a safe integer of its
  range, `+0` of `-0`; `Float64` keeps every safe integer's bits.
-/
namespace Verification
open SafeIntegers

/-- A double's bits denote NaN: its biased exponent all ones, its fraction
not zero. -/
def isNaNBits (x : UInt64) : Bool :=
  ((x >>> 52) &&& 0x7ff) == 0x7ff && (x &&& 0xfffffffffffff) != 0

/-- **The total conversion of a format** on the bits of a double: the
integer formats through `ToInt32` (`toInt32`: a number that is not finite
is `0`, any other its integer part modulo `2^32`, read as signed), modulo
`2^8` and `2^16` for the unsigned ones; `Float64` the number itself. -/
def ViewFormat.conv : ViewFormat → UInt64 → UInt64
  | .uint8, x => int32Bits (toInt32 x % 2 ^ 8)
  | .uint16, x => int32Bits (toInt32 x % 2 ^ 16)
  | .int32, x => int32Bits (toInt32 x)
  | .float64, x => x

#guard ViewFormat.conv .uint8 (300.0 : Float).toBits == (44.0 : Float).toBits
#guard ViewFormat.conv .uint8 (-1.0 : Float).toBits == (255.0 : Float).toBits
#guard ViewFormat.conv .uint8 (0.0 / 0.0 : Float).toBits == (0.0 : Float).toBits
#guard ViewFormat.conv .uint8 (1.0 / 0.0 : Float).toBits == (0.0 : Float).toBits
#guard ViewFormat.conv .uint8 (-1.5 : Float).toBits == (255.0 : Float).toBits
#guard ViewFormat.conv .uint8 (2.75 : Float).toBits == (2.0 : Float).toBits
#guard ViewFormat.conv .uint16 (65537.0 : Float).toBits == (1.0 : Float).toBits
#guard ViewFormat.conv .int32 (2147483648.0 : Float).toBits == (-2147483648.0 : Float).toBits
#guard ViewFormat.conv .int32 (-0.0 : Float).toBits == (0.0 : Float).toBits
#guard ViewFormat.conv .float64 (-0.0 : Float).toBits == (-0.0 : Float).toBits
#guard ViewFormat.conv .float64 (0.5 : Float).toBits == (0.5 : Float).toBits
#guard isNaNBits (ViewFormat.conv .float64 0xfff0000000000001)

/-- **The number an element reads after a write of the conversion `z`**: `z`
itself, or a NaN where `z` is one, the host choosing a NaN's bits
(ECMA-262, NumericToRawBytes). -/
def SameNumber (y z : UInt64) : Prop := y = z ∨ (isNaNBits y = true ∧ isNaNBits z = true)

theorem SameNumber.refl (z : UInt64) : SameNumber z z := .inl rfl

/-- Of a conversion that is no NaN, the number read is the conversion. -/
theorem SameNumber.eq_of_not_nan {y z : UInt64} (h : SameNumber y z) (hz : isNaNBits z = false) : y = z := by
  rcases h with h | ⟨-, h⟩
  · exact h
  · rw [hz] at h; cases h

/-- An integer of a 32-bit result is a safe integer its bits denote. -/
private theorem stored_int32Bits {i lo hi : Int} (hlo : lo ≤ i) (hhi : i ≤ hi) (hl : -2 ^ 31 ≤ lo)
    (hh : hi < 2 ^ 31) : ∃ j, SafeInt (int32Bits i) j ∧ lo ≤ j ∧ j ≤ hi :=
  ⟨i, safeInt_int32Bits (by omega), hlo, hhi⟩

/-- **The conversion's result is a number the format stores.** -/
theorem ViewFormat.conv_stored (f : ViewFormat) (x : UInt64) : f.Stored (.num (f.conv x)) := by
  have hr := toInt32_range x
  refine ⟨_, rfl, fun lo hi he => ?_⟩
  cases f with
  | uint8 =>
    simp only [ViewFormat.range, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact stored_int32Bits (Int.emod_nonneg _ (by decide)) (by have := Int.emod_lt_of_pos (toInt32 x) (show (0 : Int) < 2 ^ 8 by decide); omega) (by decide) (by decide)
  | uint16 =>
    simp only [ViewFormat.range, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact stored_int32Bits (Int.emod_nonneg _ (by decide)) (by have := Int.emod_lt_of_pos (toInt32 x) (show (0 : Int) < 2 ^ 16 by decide); omega) (by decide) (by decide)
  | int32 =>
    simp only [ViewFormat.range, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact stored_int32Bits (by omega) (by omega) (by decide) (by decide)
  | float64 => simp [ViewFormat.range] at he

/-- A safe integer is no NaN. -/
theorem isNaNBits_safeInt {x : UInt64} {i : Int} (hx : SafeInt x i) : isNaNBits x = false := by
  have he := hx.expo_lt
  have hne : ((x >>> 52) &&& 0x7ff) ≠ 0x7ff := fun h => by
    have := congrArg UInt64.toNat h
    rw [IndexNumbers.expo_toNat] at this
    have h7 : (0x7ff : UInt64).toNat = 2047 := rfl
    omega
  simp [isNaNBits, hne]

/-- **On the integers a format stores, the conversion keeps the integer**:
a safe integer `i` within the format's range converts to the bits of `i`
(`+0` of `-0`) in an integer format, and to itself in `Float64`. -/
theorem ViewFormat.conv_safeInt {f : ViewFormat} {x : UInt64} {i : Int} (hx : SafeInt x i)
    (hr : ∀ lo hi, f.range = some (lo, hi) → lo ≤ i ∧ i ≤ hi) :
    f.conv x = if f = .float64 then x else int32Bits i := by
  cases f with
  | uint8 =>
    obtain ⟨h0, h1⟩ := hr 0 255 rfl
    simp only [ViewFormat.conv, toInt32_small hx (by omega) (by omega), reduceCtorEq, ite_false]
    congr 1; omega
  | uint16 =>
    obtain ⟨h0, h1⟩ := hr 0 65535 rfl
    simp only [ViewFormat.conv, toInt32_small hx (by omega) (by omega), reduceCtorEq, ite_false]
    congr 1; omega
  | int32 =>
    obtain ⟨h0, h1⟩ := hr _ _ rfl
    simp only [ViewFormat.conv, reduceCtorEq, ite_false]
    rw [toInt32_small hx (by omega) (by omega)]
  | float64 => simp [ViewFormat.conv]

end Verification
