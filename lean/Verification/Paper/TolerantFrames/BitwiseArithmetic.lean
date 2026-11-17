import Verification.Semantics.SafeIntegers

/-! # General Mask and Or arithmetic

The current paper admits arbitrary safe first operands for Mask and bounded
nonnegative operands for Or. These proofs use the existing shared IEEE integer
conversion and bitwise definitions. Command execution is connected separately.
-/
namespace Verification.Paper.TolerantFrames
open SafeIntegers

theorem xor_mask_le (a b : Nat) : b ^^^ (a &&& b) ≤ b := by
  apply Nat.le_of_testBit
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_and]
  cases b.testBit i <;> simp

theorem intAnd_nonneg_mask {a m : Int} (hm : 0 ≤ m) :
    0 ≤ intAnd a m ∧ intAnd a m ≤ m := by
  cases m with
  | negSucc _ => omega
  | ofNat b =>
    cases a with
    | ofNat c => exact ⟨by simp [intAnd], by simpa [intAnd] using Nat.and_le_right (n := c) (m := b)⟩
    | negSucc c => exact ⟨by simp [intAnd], by simpa [intAnd] using xor_mask_le c b⟩

theorem mask_general {x y : UInt64} {m : Int} (hy : SafeInt y m)
    (hm : 0 ≤ m) (hmlt : m < 2 ^ 31) :
    ∃ r, SafeInt (arithBits .bitAnd x y) r ∧ 0 ≤ r ∧ r ≤ m := by
  have hy32 := toInt32_safe_nonneg hy hm hmlt
  let r := intAnd (toInt32 x) m
  have hr := intAnd_nonneg_mask (a := toInt32 x) hm
  refine ⟨r, ?_, hr⟩
  simp only [arithBits, hy32]
  exact safeInt_int32Bits (by dsimp [r]; omega)

theorem mask_nonneg {x y : UInt64} {i m : Int} (hx : SafeInt x i) (hy : SafeInt y m)
    (hi : 0 ≤ i) (hm : 0 ≤ m) (hmlt : m < 2 ^ 31) :
    ∃ r, SafeInt (arithBits .bitAnd x y) r ∧ 0 ≤ r ∧ r ≤ m ∧ r ≤ i := by
  by_cases hsmall : i < 2 ^ 31
  · obtain ⟨r, hs, h0, hi, hm⟩ := bitAnd_safe hx hy hi hsmall hm hmlt
    exact ⟨r, hs, h0, hm, hi⟩
  · obtain ⟨r, hs, h0, hr⟩ := mask_general (x := x) hy hm hmlt
    exact ⟨r, hs, h0, hr, by omega⟩
end Verification.Paper.TolerantFrames
namespace Verification.Paper.TolerantFrames
open SafeIntegers

theorem nat_or_le_add (a b : Nat) : a ||| b ≤ a + b := by
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    by_cases ha : a = 0
    · simp [ha]
    have half := ih (a / 2) (Nat.div_lt_self (by omega) (by decide)) (b / 2)
    have modBound : (a % 2) ||| (b % 2) ≤ a % 2 + b % 2 := by
      have h₁ : a % 2 = 0 ∨ a % 2 = 1 := by omega
      have h₂ : b % 2 = 0 ∨ b % 2 = 1 := by omega
      rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> simp [h₁, h₂]
    have hd := Nat.div_add_mod (a ||| b) 2
    rw [Nat.or_div_two] at hd
    have hm : (a ||| b) % 2 = a % 2 ||| b % 2 := by
      simpa using (Nat.or_mod_two_pow (a := a) (b := b) (n := 1))
    rw [hm] at hd
    omega

theorem or_general {x y : UInt64} {i j : Int} (hx : SafeInt x i) (hy : SafeInt y j)
    (hi : 0 ≤ i) (hlt : i < 2 ^ 31) (hj : 0 ≤ j) (hjlt : j < 2 ^ 31) :
    ∃ r, SafeInt (arithBits .bitOr x y) r ∧ i ≤ r ∧ j ≤ r ∧ r ≤ i + j := by
  have hx32 := toInt32_safe_nonneg hx hi hlt
  have hy32 := toInt32_safe_nonneg hy hj hjlt
  have hl := Nat.left_le_or (n := i.toNat) (m := j.toNat)
  have hr := Nat.right_le_or (n := i.toNat) (m := j.toNat)
  have hu := nat_or_le_add i.toNat j.toNat
  have hb := Nat.or_lt_two_pow (n := 31) (x := i.toNat) (y := j.toNat) (by omega) (by omega)
  have he : intOr i j = ((i.toNat ||| j.toNat : Nat) : Int) := by
    cases i <;> cases j <;> simp_all [intOr]
  refine ⟨(i.toNat ||| j.toNat : Nat), ?_, by omega, by omega, by omega⟩
  simp only [arithBits, hx32, hy32, he]
  exact safeInt_int32Bits (by omega)
end Verification.Paper.TolerantFrames
