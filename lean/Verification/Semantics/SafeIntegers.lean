import Verification.Semantics.IndexNumbers

/-! # Safe integers against the float model

The safe-integer fact of the numeric foundation (TScert #104, decision N):
a double denotes a **safe integer** `i`, `|i| ≤ 2^53 - 1`, where its bits are
those of `i`'s magnitude (`bitsOfNat`), with the sign bit set for a negative
`i`; both zeros denote `0`. Proved against Lean's logical float model
(`Float.Model`): where two doubles denote safe integers `i` and `j` and the
mathematical result is a safe integer, `+`, `-` and `*` compute it exactly
(`add_safe`, `sub_safe`, `mul_safe`), and the order of the doubles is the
order of the integers (`doubleOrder_safe`). -/
namespace Verification.SafeIntegers
open Float.Model Float.Model.UnpackedFloat Verification.IndexNumbers

/-! ## The fact -/

/-- The double `x` denotes the safe integer `i`: `|i| < 2^53`, and `x`'s bits
are the bits of `|i|`, its sign bit set where `i ≤ 0` admits it (so `-0`
denotes `0`). -/
def SafeInt (x : UInt64) (i : Int) : Prop :=
  i.natAbs < 2 ^ 53 ∧
    ((0 ≤ i ∧ x.toNat = (bitsOfNat i.natAbs).toNat) ∨ (i ≤ 0 ∧ x.toNat = (bitsOfNat i.natAbs).toNat + 2 ^ 63))

/-- The magnitude a double's bits would denote as a safe integer: the
quotient of its normal mantissa by the weight of its fractional bits, `0` for
a zero. -/
def magnitudeOfBits (x : UInt64) : Nat :=
  let mag := x.toNat % 2 ^ 63
  if mag = 0 then 0 else (mag % 2 ^ 52 + 2 ^ 52) / 2 ^ (1075 - mag / 2 ^ 52)

/-- The safe integer a double denotes, decided from its bits: the candidate
magnitude, kept where encoding it again gives the bits. -/
def safeIntOfBits (x : UInt64) : Option Int :=
  let n := magnitudeOfBits x
  let neg := decide (2 ^ 63 ≤ x.toNat)
  if n < 2 ^ 53 ∧ x.toNat = (bitsOfNat n).toNat + (if neg then 2 ^ 63 else 0) then
    some (if neg then -(n : Int) else n)
  else none

/-! ## The bits of a natural below `2^53` -/

theorem bitsOfNat_lt {L : Nat} (hL : L < 2 ^ 53) : (bitsOfNat L).toNat < 2 ^ 63 := by
  rcases Nat.eq_zero_or_pos L with rfl | h0
  · show (encodeBits 0 1075).toNat < _
    decide
  · obtain ⟨ht, -, hhi, hlen⟩ := bitsOfNat_toNat h0 hL
    rw [ht]
    have : (1022 + (L.log2 + 1)) * 2 ^ 52 ≤ 1075 * 2 ^ 52 := Nat.mul_le_mul_right _ (by omega)
    omega

theorem bitsOfNat_zero : (bitsOfNat 0).toNat = 0 := by decide

/-- The canonical unpacked form of a positive natural below `2^53`: its
mantissa shifted to 53 bits, at the matching exponent. -/
theorem canon_pos {N : Nat} (h0 : 0 < N) (_hN : N < 2 ^ 53) : 0 < N * 2 ^ (52 - N.log2) :=
  Nat.mul_pos h0 (Nat.two_pow_pos _)

theorem log2_lt53 {N : Nat} (h0 : 0 < N) (hN : N < 2 ^ 53) : N.log2 < 53 :=
  (Nat.log2_lt (by omega)).mpr hN

theorem log2_mul_pow {m : Nat} (hm : 0 < m) (a : Nat) : (m * 2 ^ a).log2 = m.log2 + a := by
  apply (Nat.log2_eq_iff (Nat.mul_ne_zero (by omega) (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)))).mpr
  have h1 : 2 ^ m.log2 ≤ m := Nat.log2_self_le (by omega)
  have h2 : m < 2 ^ (m.log2 + 1) := Nat.lt_log2_self
  constructor
  · rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ h1
  · rw [show m.log2 + a + 1 = (m.log2 + 1) + a by omega, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos _)

/-! ## Exact rounding -/

theorem shiftRight_zero (em : ExtendedMantissa) : em >>> (0 : Nat) = em := rfl

theorem shiftRight_succ (em : ExtendedMantissa) (d : Nat) :
    em >>> (d + 1) = (em >>> d).shiftRightOne := rfl

/-- Shifting out zero bits is exact. -/
theorem shiftRight_exact (q d : Nat) :
    (⟨q * 2 ^ d, false, false⟩ : ExtendedMantissa) >>> d = ⟨q, false, false⟩ := by
  induction d generalizing q with
  | zero => simp [shiftRight_zero]
  | succ d ih =>
    rw [shiftRight_succ, show q * 2 ^ (d + 1) = (q * 2) * 2 ^ d by rw [Nat.pow_succ]; ac_rfl, ih]
    simp [ExtendedMantissa.shiftRightOne]

theorem total_eq {m N : Nat} {e : Int} (hm : 0 < m) (hN0 : 0 < N)
    (hv : m * 2 ^ e.toNat = N * 2 ^ (-e).toNat) : (m.log2 : Int) + e = N.log2 := by
  have := congrArg Nat.log2 hv
  rw [log2_mul_pow hm, log2_mul_pow hN0] at this
  omega

/-- Rounding a 53-bit mantissa, given with `d` zero bits below it, at an
exponent no smaller than the least is exact. -/
theorem roundWithAccuracy_exact (s : Sign) {M d : Nat} {E e : Int} (hM : 0 < M) (hMl : M.log2 = 52)
    (hE : -1074 ≤ E) (hed : e + d = E) :
    roundWithAccuracy .binary64 s (M * 2 ^ d) e .exact = .finite s M E hM := by
  have h1 : totalExponent (M * 2 ^ d) e = E + 53 := by
    simp only [totalExponent]; rw [log2_mul_pow hM, hMl]; omega
  have h2 : Format.targetExponent .binary64 (E + 53) = E := by
    simp only [Format.targetExponent, Format.mantissaBits, Format.minExponent]; omega
  have h3 : (E - e).toNat = d := by omega
  have h5 : totalExponent M E = E + 53 := by simp only [totalExponent, hMl]; omega
  have h6 : e + ((d : Nat) : Int) = E := hed
  have hr : ExtendedMantissa.roundedMantissa ⟨M, false, false⟩ = M := rfl
  have h0 : ExtendedMantissa.ofMantissaAndAccuracy (M * 2 ^ d) .exact = ⟨M * 2 ^ d, false, false⟩ := rfl
  have h0' : ExtendedMantissa.ofMantissaAndAccuracy M .exact = ⟨M, false, false⟩ := rfl
  simp only [roundWithAccuracy, shiftToTargetExponent, shiftToExponent, h1, h2, h3, h0, shiftRight_exact,
    hr, h6, h5, h0', Int.sub_self, Int.toNat_zero, shiftRight_zero, Int.natCast_zero, Int.add_zero]
  rw [dif_neg (by omega)]

theorem canon_log2 {N : Nat} (h0 : 0 < N) (hN : N < 2 ^ 53) : (N * 2 ^ (52 - N.log2)).log2 = 52 := by
  rw [log2_mul_pow h0]; have := log2_lt53 h0 hN; omega

/-- Rounding a value that is a natural below `2^53` gives its canonical form. -/
theorem round_exact (s : Sign) {m N : Nat} {e : Int} (hm : 0 < m) (hN0 : 0 < N) (hN : N < 2 ^ 53)
    (hv : m * 2 ^ e.toNat = N * 2 ^ (-e).toNat) :
    round .binary64 s m e = .finite s (N * 2 ^ (52 - N.log2)) ((N.log2 : Int) - 52) (canon_pos hN0 hN) := by
  have hl := log2_lt53 hN0 hN
  have ht := total_eq hm hN0 hv
  have htarget : Format.targetExponent .binary64 (totalExponent m e) = (N.log2 : Int) - 52 := by
    simp only [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]
    omega
  simp only [round, htarget, decreaseExponent]
  have hcl := canon_log2 hN0 hN
  by_cases he : (N.log2 : Int) - 52 ≤ e
  · -- the exponent is decreased to the target: the mantissa grows
    obtain ⟨d, hd⟩ : ∃ d, d = (e - ((N.log2 : Int) - 52)).toNat := ⟨_, rfl⟩
    rw [← hd]
    have hm' : m <<< d = N * 2 ^ (52 - N.log2) * 2 ^ 0 := by
      rw [Nat.shiftLeft_eq, Nat.pow_zero, Nat.mul_one]
      rcases Int.le_total 0 e with h0 | h0
      · have hne : (-e).toNat = 0 := by omega
        rw [hne, Nat.pow_zero, Nat.mul_one] at hv
        have : d = e.toNat + (52 - N.log2) := by omega
        rw [this, Nat.pow_add, ← Nat.mul_assoc, hv]
      · have hne : e.toNat = 0 := by omega
        rw [hne, Nat.pow_zero, Nat.mul_one] at hv
        have : (-e).toNat + d = 52 - N.log2 := by omega
        rw [hv, Nat.mul_assoc, ← Nat.pow_add, this]
    rw [hm']
    exact roundWithAccuracy_exact s (canon_pos hN0 hN) hcl (by omega) (by omega)
  · -- the exponent is below the target: zero bits are shifted out
    have hd0 : (e - ((N.log2 : Int) - 52)).toNat = 0 := by omega
    rw [hd0, Nat.shiftLeft_zero]
    obtain ⟨d, hd⟩ : ∃ d, d = ((N.log2 : Int) - 52 - e).toNat := ⟨_, rfl⟩
    have hne : e.toNat = 0 := by omega
    rw [hne, Nat.pow_zero, Nat.mul_one] at hv
    have hmq : m = (N * 2 ^ (52 - N.log2)) * 2 ^ d := by
      rw [hv, Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
    rw [hmq]
    exact roundWithAccuracy_exact s (canon_pos hN0 hN) hcl (by omega) (by omega)

/-! ## Unpacking and packing the doubles of safe integers -/

/-- The sign a double's sign bit gives. -/
def signOfBit (neg : Bool) : Sign := if neg then .negative else .positive

theorem unpack_finite (b : BitVec 64)
    (he1 : 1 ≤ b.toNat / 2 ^ 52 % 2 ^ 11) (he2 : b.toNat / 2 ^ 52 % 2 ^ 11 ≤ 2046) :
    ∃ h, UnpackedFloat.unpack .binary64 b =
      .finite (signOfBit (decide (2 ^ 63 ≤ b.toNat))) (b.toNat % 2 ^ 52 + 2 ^ 52)
        ((b.toNat / 2 ^ 52 % 2 ^ 11 : Nat) - 1075) h := by
  refine ⟨by omega, ?_⟩
  have hb := b.isLt
  have hsign : Sign.ofBitVec (unpackSign (spec := Format.binary64) b) = signOfBit (decide (2 ^ 63 ≤ b.toNat)) := by
    simp only [Sign.ofBitVec, signOfBit]
    by_cases hs : 2 ^ 63 ≤ b.toNat
    · rw [if_neg (by rw [← BitVec.toNat_inj, unpackSign_toNat]; simp; omega)]; simp [hs]
    · rw [if_pos (by rw [← BitVec.toNat_inj, unpackSign_toNat]; simp; omega)]; simp [hs]
  simp only [UnpackedFloat.unpack, hsign]
  rw [if_neg (by rw [exp_allOnes]; omega), if_neg (by rw [exp_zero]; omega)]
  congr 1
  · rw [BitVec.toNat_append, unpackMantissa_toNat]
    have hm : b.toNat % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (Nat.two_pow_pos 52)
    rw [← Nat.shiftLeft_add_eq_or_of_lt hm, Nat.shiftLeft_eq]
    simp; omega
  · simp [unpackExponent_toNat, Format.exponentBias]

theorem pack_finite (s : Sign) (m : Nat) (e : Int) (h : 0 < m) (hm1 : 2 ^ 52 ≤ m) (hm2 : m < 2 ^ 53)
    (he1 : 1 ≤ e + 1075) (he2 : e + 1075 ≤ 2046) :
    (UnpackedFloat.pack .binary64 (.finite s m e h)).toNat =
      s.toBitVec.toNat * 2 ^ 63 + (e + 1075).toNat * 2 ^ 52 + (m - 2 ^ 52) := by
  have hl : m.log2 = 52 := (Nat.log2_eq_iff (by omega)).mpr ⟨hm1, hm2⟩
  simp only [UnpackedFloat.pack, hl, Format.exponentBias]
  rw [if_neg (by simp; omega), if_pos (by simp [Format.mantissaBits])]
  rw [packComponents_toNat]
  simp
  omega

theorem signOfBit_toNat (q : Bool) : (signOfBit q).toBitVec.toNat = if q then 1 else 0 := by
  cases q <;> rfl

/-- The fields of the bits of a natural below `2^53`, a sign bit added or not. -/
theorem bitsOfNat_fields {N : Nat} (h0 : 0 < N) (hN : N < 2 ^ 53) (q : Bool) :
    let t := (bitsOfNat N).toNat + (if q then 2 ^ 63 else 0)
    t / 2 ^ 52 % 2 ^ 11 = 1023 + N.log2 ∧ t % 2 ^ 52 + 2 ^ 52 = N * 2 ^ (52 - N.log2) ∧
      (2 ^ 63 ≤ t ↔ q = true) ∧ t < 2 ^ 64 := by
  obtain ⟨ht, hlo, hhi, hlen⟩ := bitsOfNat_toNat h0 hN
  have hk : 53 - (N.log2 + 1) = 52 - N.log2 := by omega
  rw [hk] at ht hlo hhi
  intro t
  generalize hb : N * 2 ^ (52 - N.log2) = b at ht hlo hhi ⊢
  generalize hL : N.log2 = L at ht hlen ⊢
  have hL' : L ≤ 52 := by omega
  have ht' : t = (1023 + L) * 2 ^ 52 + (b - 2 ^ 52) + (if q then 2 ^ 63 else 0) := by
    simp only [t, ht]; omega
  rw [ht']
  cases q <;> simp only [if_true, if_false, Bool.false_eq_true, iff_false, iff_true] <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem finite_eq {s : Sign} {m m' : Nat} {e e' : Int} {h : 0 < m} {h' : 0 < m'} (hm : m = m') (he : e = e') :
    UnpackedFloat.finite s m e h = .finite s m' e' h' := by
  subst hm; subst he; rfl

/-- The canonical unpacked form of a nonzero safe integer. -/
def canonical (i : Int) (h : i ≠ 0) (hi : i.natAbs < 2 ^ 53) : UnpackedFloat :=
  .finite (signOfBit (decide (i < 0))) (i.natAbs * 2 ^ (52 - i.natAbs.log2)) ((i.natAbs.log2 : Int) - 52)
    (canon_pos (by omega) hi)

theorem model_safe {x : UInt64} {i : Int} (hx : SafeInt x i) (h : i ≠ 0) :
    (Float.ofBits x).toModel.unpack = canonical i h hx.1 := by
  have h0 : 0 < i.natAbs := by omega
  have hq : ∃ q : Bool, x.toNat = (bitsOfNat i.natAbs).toNat + (if q then 2 ^ 63 else 0) ∧ (q = true ↔ i < 0) := by
    rcases hx.2 with ⟨hi, he⟩ | ⟨hi, he⟩
    · exact ⟨false, by simpa using he, by simp; omega⟩
    · exact ⟨true, by simpa using he, by simp; omega⟩
  obtain ⟨q, hxq, hqi⟩ := hq
  obtain ⟨hE, hM, hS, -⟩ := bitsOfNat_fields h0 hx.1 q
  rw [← hxq] at hE hM hS
  have hl := log2_lt53 h0 hx.1
  obtain ⟨hpos, hu⟩ := unpack_finite x.toBitVec (by simp; omega) (by simp; omega)
  simp only [UInt64.toNat_toBitVec] at hu
  rw [model_unpack, hu]
  have hdec : decide (2 ^ 63 ≤ x.toNat) = decide (i < 0) := by
    by_cases hneg : i < 0
    · simp only [hneg, decide_true, decide_eq_true_eq]; exact hS.mpr (hqi.mpr hneg)
    · simp only [hneg, decide_false, decide_eq_false_iff_not]; exact fun hc => hneg (hqi.mp (hS.mp hc))
  rw [hdec]
  have hp := pack_finite (signOfBit (decide (i < 0))) (x.toNat % 2 ^ 52 + 2 ^ 52)
    ((x.toNat / 2 ^ 52 % 2 ^ 11 : Nat) - 1075) hpos (by omega) (by omega) (by omega) (by omega)
  have hE' : ((x.toNat / 2 ^ 52 % 2 ^ 11 : Nat) - 1075 + 1075 : Int).toNat = x.toNat / 2 ^ 52 % 2 ^ 11 := by omega
  rw [hE'] at hp
  have hsb : (signOfBit (decide (i < 0))).toBitVec.toNat ≤ 1 := by rw [signOfBit_toNat]; split <;> omega
  obtain ⟨h', hu'⟩ := unpack_finite (UnpackedFloat.pack .binary64
    (.finite (signOfBit (decide (i < 0))) (x.toNat % 2 ^ 52 + 2 ^ 52) ((x.toNat / 2 ^ 52 % 2 ^ 11 : Nat) - 1075) hpos))
    (by rw [hp]; omega) (by rw [hp]; omega)
  rw [hu']
  have hf : ((signOfBit (decide (i < 0))).toBitVec.toNat * 2 ^ 63 + x.toNat / 2 ^ 52 % 2 ^ 11 * 2 ^ 52 +
      (x.toNat % 2 ^ 52 + 2 ^ 52 - 2 ^ 52)) / 2 ^ 52 % 2 ^ 11 = x.toNat / 2 ^ 52 % 2 ^ 11 := by omega
  have hm : ((signOfBit (decide (i < 0))).toBitVec.toNat * 2 ^ 63 + x.toNat / 2 ^ 52 % 2 ^ 11 * 2 ^ 52 +
      (x.toNat % 2 ^ 52 + 2 ^ 52 - 2 ^ 52)) % 2 ^ 52 = x.toNat % 2 ^ 52 := by omega
  have hs : decide (2 ^ 63 ≤ (signOfBit (decide (i < 0))).toBitVec.toNat * 2 ^ 63 + x.toNat / 2 ^ 52 % 2 ^ 11 * 2 ^ 52 +
      (x.toNat % 2 ^ 52 + 2 ^ 52 - 2 ^ 52)) = decide (i < 0) := by
    rw [signOfBit_toNat]; by_cases hneg : i < 0 <;> simp [hneg] <;> omega
  simp only [hp, hf, hm, hs, canonical]
  exact finite_eq (by omega) (by omega)

theorem model_safe_zero {x : UInt64} (hx : SafeInt x 0) : ∃ s, (Float.ofBits x).toModel.unpack = .zero s := by
  apply model_zero
  rcases hx.2 with ⟨-, he⟩ | ⟨-, he⟩ <;> simp [bitsOfNat_zero] at he <;> omega

theorem pack_canonical (i : Int) (h : i ≠ 0) (hi : i.natAbs < 2 ^ 53) :
    SafeInt (UInt64.ofBitVec (UnpackedFloat.pack .binary64 (canonical i h hi))) i := by
  have h0 : 0 < i.natAbs := by omega
  have hl := log2_lt53 h0 hi
  have hlo : 2 ^ 52 ≤ i.natAbs * 2 ^ (52 - i.natAbs.log2) := by
    have := (canon_log2 h0 hi); have := Nat.log2_self_le (n := i.natAbs * 2 ^ (52 - i.natAbs.log2)) (by
      have := canon_pos h0 hi; omega)
    simp_all
  have hhi : i.natAbs * 2 ^ (52 - i.natAbs.log2) < 2 ^ 53 := by
    have := canon_log2 h0 hi
    have := (Nat.log2_lt (n := i.natAbs * 2 ^ (52 - i.natAbs.log2)) (k := 53) (by have := canon_pos h0 hi; omega)).mp
      (by omega)
    exact this
  have hp := pack_finite (signOfBit (decide (i < 0))) _ ((i.natAbs.log2 : Int) - 52) (canon_pos h0 hi) hlo hhi
    (by omega) (by omega)
  refine ⟨hi, ?_⟩
  obtain ⟨ht, -, -, -⟩ := bitsOfNat_toNat h0 hi
  have hk : 53 - (i.natAbs.log2 + 1) = 52 - i.natAbs.log2 := by omega
  rw [hk] at ht
  have hE : ((i.natAbs.log2 : Int) - 52 + 1075).toNat = 1022 + (i.natAbs.log2 + 1) := by omega
  simp only [canonical, UInt64.toNat_ofBitVec]
  rw [hp, hE, signOfBit_toNat]
  by_cases hneg : i < 0
  · right; simp [hneg]; omega
  · left; simp [hneg]; omega

theorem pack_zero_safe (s : Sign) : SafeInt (UInt64.ofBitVec (UnpackedFloat.pack .binary64 (.zero s))) 0 := by
  refine ⟨by decide, ?_⟩
  simp only [UnpackedFloat.pack, packedZero, UInt64.toNat_ofBitVec, packComponents_toNat]
  rw [show (Int.natAbs 0) = 0 from rfl, bitsOfNat_zero]
  cases s
  · right; simp [Sign.toBitVec]
  · left; simp [Sign.toBitVec]

/-! ## Exact sums and differences -/

/-- The unpacked form of a safe integer's double: a zero, or its canonical form. -/
theorem model_safe_cases {x : UInt64} {i : Int} (hx : SafeInt x i) :
    (i = 0 ∧ ∃ s, (Float.ofBits x).toModel.unpack = .zero s) ∨
      ∃ h, (Float.ofBits x).toModel.unpack = canonical i h hx.1 := by
  by_cases h : i = 0
  · subst h; exact .inl ⟨rfl, model_safe_zero hx⟩
  · exact .inr ⟨h, model_safe hx h⟩

theorem signOfBit_apply (i : Int) (n : Nat) :
    (signOfBit (decide (i < 0))).apply ((i.natAbs * n : Nat) : Int) = i * n := by
  by_cases hn : i < 0
  · simp only [hn, decide_true, signOfBit, if_true, Sign.apply]
    rw [Int.natCast_mul, Int.ofNat_natAbs_of_nonpos (by omega), Int.neg_mul, Int.neg_neg]
  · simp only [hn, decide_false, signOfBit, Bool.false_eq_true, if_false, Sign.apply]
    rw [Int.natCast_mul, Int.natAbs_of_nonneg (by omega)]

/-- A canonical mantissa decreased to a smaller exponent `-K` is the integer
times `2^K`. -/
theorem shift_canonical (i : Int) (h : i ≠ 0) (hi : i.natAbs < 2 ^ 53) {K : Nat}
    (hK : (i.natAbs.log2 : Int) - 52 ≥ -(K : Int)) :
    (signOfBit (decide (i < 0))).apply
        (((i.natAbs * 2 ^ (52 - i.natAbs.log2)) <<< ((i.natAbs.log2 : Int) - 52 - -(K : Int)).toNat : Nat) : Int) =
      i * 2 ^ K := by
  have hl := log2_lt53 (by omega) hi
  rw [Nat.shiftLeft_eq, Nat.mul_assoc, ← Nat.pow_add, signOfBit_apply i _]
  have : 52 - i.natAbs.log2 + ((i.natAbs.log2 : Int) - 52 - -(K : Int)).toNat = K := by omega
  rw [this, Int.natCast_pow]; rfl

/-- Normalizing `k * 2^K` at exponent `-K` gives `k`'s double, for a safe `k`. -/
theorem normalize_safe {S k : Int} {K : Nat} (hS : S = k * 2 ^ K) (hk : k.natAbs < 2 ^ 53) :
    SafeInt (UInt64.ofBitVec (UnpackedFloat.pack .binary64 (normalize .binary64 S (-(K : Int)) .positive))) k := by
  have hP : (0 : Int) < 2 ^ K := Int.pow_pos (by decide)
  simp only [normalize]
  rcases Int.lt_trichotomy k 0 with hn | rfl | hp
  · have hSn : S < 0 := by rw [hS]; exact Int.mul_neg_of_neg_of_pos hn hP
    rw [show compare S 0 = .lt from Int.compare_eq_lt.mpr hSn]
    simp only
    have hv : (-S).toNat * 2 ^ (-(K : Int)).toNat = k.natAbs * 2 ^ (- -(K : Int)).toNat := by
      have : (- -(K : Int)).toNat = K := by omega
      rw [this, show (-(K : Int)).toNat = 0 by omega, Nat.pow_zero, Nat.mul_one]
      have : -S = ((k.natAbs * 2 ^ K : Nat) : Int) := by
        rw [hS, Int.natCast_mul, Int.ofNat_natAbs_of_nonpos (by omega), Int.natCast_pow, Int.neg_mul]; rfl
      rw [this, Int.toNat_natCast]
    rw [round_exact .negative (by omega) (by omega) hk hv]
    have := pack_canonical k (by omega) hk
    simp only [canonical, show decide (k < 0) = true by simp [hn], signOfBit, if_true] at this
    exact this
  · have hS0 : S = 0 := by rw [hS]; simp
    rw [show compare S 0 = .eq from Int.compare_eq_eq.mpr hS0]
    exact pack_zero_safe .positive
  · have hSp : 0 < S := by rw [hS]; exact Int.mul_pos hp hP
    rw [show compare S 0 = .gt from Int.compare_eq_gt.mpr hSp]
    simp only
    have hv : S.toNat * 2 ^ (-(K : Int)).toNat = k.natAbs * 2 ^ (- -(K : Int)).toNat := by
      have : (- -(K : Int)).toNat = K := by omega
      rw [this, show (-(K : Int)).toNat = 0 by omega, Nat.pow_zero, Nat.mul_one]
      have : S = ((k.natAbs * 2 ^ K : Nat) : Int) := by
        rw [hS, Int.natCast_mul, Int.natAbs_of_nonneg (by omega), Int.natCast_pow]; rfl
      rw [this, Int.toNat_natCast]
    rw [round_exact .positive (by omega) (by omega) hk hv]
    have := pack_canonical k (by omega) hk
    simp only [canonical, show decide (k < 0) = false by simp; omega, signOfBit, Bool.false_eq_true,
      if_false] at this
    exact this

theorem arithBits_add (x y : UInt64) :
    arithBits .add x y = UInt64.ofBitVec (UnpackedFloat.pack .binary64
      (UnpackedFloat.add .binary64 (Float.ofBits x).toModel.unpack (Float.ofBits y).toModel.unpack)) := rfl

theorem arithBits_sub (x y : UInt64) :
    arithBits .sub x y = UInt64.ofBitVec (UnpackedFloat.pack .binary64
      (UnpackedFloat.sub .binary64 (Float.ofBits x).toModel.unpack (Float.ofBits y).toModel.unpack)) := rfl

theorem arithBits_mul (x y : UInt64) :
    arithBits .mul x y = UInt64.ofBitVec (UnpackedFloat.pack .binary64
      (UnpackedFloat.mul .binary64 (Float.ofBits x).toModel.unpack (Float.ofBits y).toModel.unpack)) := rfl

/-- **Exact addition.** Doubles of safe integers add to the double of their
sum where the sum is a safe integer. -/
theorem add_safe {x y : UInt64} {i j : Int} (hx : SafeInt x i) (hy : SafeInt y j)
    (hr : (i + j).natAbs < 2 ^ 53) : SafeInt (arithBits .add x y) (i + j) := by
  rw [arithBits_add]
  rcases model_safe_cases hx with ⟨rfl, s, hu⟩ | ⟨h, hu⟩ <;>
    rcases model_safe_cases hy with ⟨rfl, t, hv⟩ | ⟨h', hv⟩ <;> rw [hu, hv]
  · simp only [UnpackedFloat.add]; split <;> exact pack_zero_safe _
  · simp only [Int.zero_add, canonical, UnpackedFloat.add]
    exact pack_canonical j h' hy.1
  · simp only [Int.add_zero, canonical, UnpackedFloat.add]
    exact pack_canonical i h hx.1
  · simp only [canonical, UnpackedFloat.add]
    have hl := log2_lt53 (by omega) hx.1
    have hl' := log2_lt53 (by omega) hy.1
    obtain ⟨K, hK⟩ : ∃ K : Nat, min ((i.natAbs.log2 : Int) - 52) ((j.natAbs.log2 : Int) - 52) = -(K : Int) :=
      ⟨(-(min ((i.natAbs.log2 : Int) - 52) ((j.natAbs.log2 : Int) - 52))).toNat, by omega⟩
    simp only [decreaseExponent, hK]
    rw [shift_canonical i h hx.1 (by omega), shift_canonical j h' hy.1 (by omega)]
    exact normalize_safe (by rw [Int.add_mul]) hr

/-- **Exact subtraction.** Doubles of safe integers subtract to the double of
their difference where it is a safe integer. -/
theorem sub_safe {x y : UInt64} {i j : Int} (hx : SafeInt x i) (hy : SafeInt y j)
    (hr : (i - j).natAbs < 2 ^ 53) : SafeInt (arithBits .sub x y) (i - j) := by
  rw [arithBits_sub]
  rcases model_safe_cases hx with ⟨rfl, s, hu⟩ | ⟨h, hu⟩ <;>
    rcases model_safe_cases hy with ⟨rfl, t, hv⟩ | ⟨h', hv⟩ <;> rw [hu, hv]
  · simp only [UnpackedFloat.sub]; split <;> exact pack_zero_safe _
  · simp only [Int.zero_sub, canonical, UnpackedFloat.sub]
    have hn := pack_canonical (-j) (by omega) (by simpa using hy.1)
    simp only [canonical, Int.natAbs_neg] at hn
    have hs : -signOfBit (decide (j < 0)) = signOfBit (decide (-j < 0)) := by
      by_cases hj : j < 0
      · simp only [hj, decide_true, show ¬ -j < 0 by omega, decide_false, signOfBit]; rfl
      · simp only [hj, decide_false, show -j < 0 by omega, decide_true, signOfBit]; rfl
    rw [hs]; exact hn
  · simp only [Int.sub_zero, canonical, UnpackedFloat.sub]
    exact pack_canonical i h hx.1
  · simp only [canonical, UnpackedFloat.sub]
    have hl := log2_lt53 (by omega) hx.1
    have hl' := log2_lt53 (by omega) hy.1
    obtain ⟨K, hK⟩ : ∃ K : Nat, min ((i.natAbs.log2 : Int) - 52) ((j.natAbs.log2 : Int) - 52) = -(K : Int) :=
      ⟨(-(min ((i.natAbs.log2 : Int) - 52) ((j.natAbs.log2 : Int) - 52))).toNat, by omega⟩
    simp only [decreaseExponent, hK]
    rw [shift_canonical i h hx.1 (by omega), shift_canonical j h' hy.1 (by omega)]
    exact normalize_safe (by rw [Int.sub_mul]) hr

/-! ## Decoding -/

/-- **Decoding.** The safe integer `safeIntOfBits` decodes is the one the
double denotes. -/
theorem safeIntOfBits_sound {x : UInt64} {i : Int} (h : safeIntOfBits x = some i) : SafeInt x i := by
  simp only [safeIntOfBits] at h
  by_cases hc : magnitudeOfBits x < 2 ^ 53 ∧
      x.toNat = (bitsOfNat (magnitudeOfBits x)).toNat + (if decide (2 ^ 63 ≤ x.toNat) then 2 ^ 63 else 0)
  · rw [if_pos hc] at h
    cases h
    by_cases hn : 2 ^ 63 ≤ x.toNat
    · simp only [hn, decide_true, if_true] at hc ⊢
      refine ⟨by simpa using hc.1, .inr ⟨by omega, by simpa using hc.2⟩⟩
    · simp only [hn, decide_false, Bool.false_eq_true, if_false, Nat.add_zero] at hc ⊢
      refine ⟨by simpa using hc.1, .inl ⟨by omega, by simpa using hc.2⟩⟩
  · rw [if_neg hc] at h; cases h

/-! ## Order and equality -/

/-- The canonical forms of two positive safe integers compare as they do. -/
theorem compare_canonical_pos {i j : Int} (hi : 0 < i) (hj : 0 < j) (h : i ≠ 0) (h' : j ≠ 0)
    (ha : i.natAbs < 2 ^ 53) (hb : j.natAbs < 2 ^ 53) :
    (canonical i h ha).compare (canonical j h' hb) = some (compare i j) := by
  have hx : SafeInt (bitsOfNat i.natAbs) i := ⟨ha, .inl ⟨by omega, rfl⟩⟩
  have hy : SafeInt (bitsOfNat j.natAbs) j := ⟨hb, .inl ⟨by omega, rfl⟩⟩
  have hc := compare_denotes (denotes_bitsOfNat ha) (denotes_bitsOfNat hb)
  rw [model_safe hx h, model_safe hy h'] at hc
  rw [hc]
  congr 1
  rcases Int.lt_trichotomy i j with hl | rfl | hl
  · rw [Int.compare_eq_lt.mpr hl, Nat.compare_eq_lt.mpr (by omega)]
  · rw [Int.compare_eq_eq.mpr rfl, Nat.compare_eq_eq.mpr rfl]
  · rw [Int.compare_eq_gt.mpr hl, Nat.compare_eq_gt.mpr (by omega)]

theorem canonical_neg {i : Int} (hi : i < 0) (h : i ≠ 0) (ha : i.natAbs < 2 ^ 53) :
    ∃ m e hm, canonical i h ha = .finite .negative m e hm ∧
      canonical (-i) (by omega) (by simpa using ha) = .finite .positive m e hm := by
  refine ⟨i.natAbs * 2 ^ (52 - i.natAbs.log2), (i.natAbs.log2 : Int) - 52, canon_pos (by omega) ha, ?_, ?_⟩
  · simp [canonical, hi, signOfBit]
  · simp only [canonical, Int.natAbs_neg, show ¬ -i < 0 by omega, decide_false, signOfBit,
      Bool.false_eq_true, if_false]

theorem canonical_pos' {i : Int} (hi : 0 < i) (h : i ≠ 0) (ha : i.natAbs < 2 ^ 53) :
    ∃ m e hm, canonical i h ha = .finite .positive m e hm :=
  ⟨i.natAbs * 2 ^ (52 - i.natAbs.log2), (i.natAbs.log2 : Int) - 52, canon_pos (by omega) ha,
    by simp [canonical, show ¬ i < 0 by omega, signOfBit]⟩

/-- The unpacked forms of two safe integers' doubles compare as the integers. -/
theorem compare_safe {x y : UInt64} {i j : Int} (hx : SafeInt x i) (hy : SafeInt y j) :
    (Float.ofBits x).toModel.unpack.compare (Float.ofBits y).toModel.unpack = some (compare i j) := by
  rcases model_safe_cases hx with ⟨rfl, s, hu⟩ | ⟨h, hu⟩ <;>
    rcases model_safe_cases hy with ⟨rfl, t, hv⟩ | ⟨h', hv⟩ <;> rw [hu, hv]
  · rfl
  · rcases Int.lt_or_gt_of_ne h' with hn | hp
    · obtain ⟨m, e, hm, he, -⟩ := canonical_neg hn h' hy.1
      rw [he, Int.compare_eq_gt.mpr hn]; rfl
    · obtain ⟨m, e, hm, he⟩ := canonical_pos' hp h' hy.1
      rw [he, Int.compare_eq_lt.mpr hp]; rfl
  · rcases Int.lt_or_gt_of_ne h with hn | hp
    · obtain ⟨m, e, hm, he, -⟩ := canonical_neg hn h hx.1
      rw [he, Int.compare_eq_lt.mpr hn]; rfl
    · obtain ⟨m, e, hm, he⟩ := canonical_pos' hp h hx.1
      rw [he, Int.compare_eq_gt.mpr hp]; rfl
  · rcases Int.lt_or_gt_of_ne h with hn | hp <;> rcases Int.lt_or_gt_of_ne h' with hn' | hp'
    · obtain ⟨m, e, hm, he, hpe⟩ := canonical_neg hn h hx.1
      obtain ⟨m', e', hm', he', hpe'⟩ := canonical_neg hn' h' hy.1
      have hc := compare_canonical_pos (i := -i) (j := -j) (by omega) (by omega) (by omega) (by omega)
        (by simpa using hx.1) (by simpa using hy.1)
      rw [hpe, hpe'] at hc
      rw [he, he']
      simp only [UnpackedFloat.compare] at hc ⊢
      rw [Option.some.injEq] at hc
      rw [hc]
      congr 1
      rcases Int.lt_trichotomy i j with hl | rfl | hl
      · rw [Int.compare_eq_lt.mpr hl, Int.compare_eq_gt.mpr (by omega)]; rfl
      · rw [Int.compare_eq_eq.mpr rfl, Int.compare_eq_eq.mpr rfl]; rfl
      · rw [Int.compare_eq_gt.mpr hl, Int.compare_eq_lt.mpr (by omega)]; rfl
    · obtain ⟨m, e, hm, he, -⟩ := canonical_neg hn h hx.1
      obtain ⟨m', e', hm', he'⟩ := canonical_pos' hp' h' hy.1
      rw [he, he', Int.compare_eq_lt.mpr (by omega)]; rfl
    · obtain ⟨m, e, hm, he⟩ := canonical_pos' hp h hx.1
      obtain ⟨m', e', hm', he', -⟩ := canonical_neg hn' h' hy.1
      rw [he, he', Int.compare_eq_gt.mpr (by omega)]; rfl
    · exact compare_canonical_pos hp hp' h h' hx.1 hy.1

/-- **Order.** Two doubles of safe integers are ordered as the integers. -/
theorem doubleOrder_safe {x y : UInt64} {i j : Int} (hx : SafeInt x i) (hy : SafeInt y j) :
    doubleOrder x y = some (compare i j) := by
  have hxy := compare_safe hx hy
  have hyx := compare_safe hy hx
  simp only [doubleOrder]
  rcases Int.lt_trichotomy i j with h | rfl | h
  · rw [if_pos ((float_lt_iff _ _).mpr (by rw [hxy, Int.compare_eq_lt.mpr h])), Int.compare_eq_lt.mpr h]
  · rw [if_neg (by rw [float_lt_iff, hxy, Int.compare_eq_eq.mpr rfl]; simp),
      if_pos ((float_beq_iff _ _).mpr (by rw [hxy, Int.compare_eq_eq.mpr rfl])), Int.compare_eq_eq.mpr rfl]
  · rw [if_neg (by rw [float_lt_iff, hxy, Int.compare_eq_gt.mpr h]; simp),
      if_neg (by rw [float_beq_iff, hxy, Int.compare_eq_gt.mpr h]; simp),
      if_pos ((float_lt_iff _ _).mpr (by rw [hyx, Int.compare_eq_lt.mpr h])), Int.compare_eq_gt.mpr h]

/-! ## Witnesses against JavaScript

Each line states what Node v26 computes for the same doubles: `5`, `-0`,
`-7`, `0.5`, `2 ** 53`, NaN and `Infinity` decode as `Number.isSafeInteger`
answers, and `(2 ** 53 - 1) + 2` is `2 ** 53`, no safe integer, so no atom
states that sum. -/

#guard safeIntOfBits (bitsOfNat 5) = some 5
#guard safeIntOfBits 0x8000000000000000 = some 0
#guard safeIntOfBits ((7.0 : Float).neg.toBits) = some (-7)
#guard safeIntOfBits ((0.5 : Float).toBits) = none
#guard safeIntOfBits (bitsOfNat (2 ^ 53)) = none
#guard safeIntOfBits (bitsOfNat (2 ^ 53 - 1)) = some (2 ^ 53 - 1)
#guard safeIntOfBits ((0.0 / 0.0 : Float).toBits) = none
#guard safeIntOfBits ((1.0 / 0.0 : Float).toBits) = none
#guard safeIntOfBits (arithBits .add (bitsOfNat (2 ^ 53 - 1)) (bitsOfNat 2)) = none
#guard safeIntOfBits (arithBits .sub (bitsOfNat 3) (bitsOfNat 10)) = some (-7)

end Verification.SafeIntegers
