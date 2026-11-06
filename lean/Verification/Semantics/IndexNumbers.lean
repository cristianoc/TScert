import Verification.Semantics.Calculus

/-! # Index numbers against the float model

What the index facts (`HeapKnowledge.IndexAtom`) read of a double, proved
against Lean's logical float model (`Float.Model`): a double `indexOfBits`
decodes to an index, and a natural's bits (`bitsOfNat` below `2^53`),
compare as their naturals do; strict equality keeps the index a double
decodes to; and a conjunction with a mask that is a non-negative 32-bit
integer is an index. The fields of a double are read as its bits' natural:
the biased exponent `x.toNat / 2^52 % 2^11`, the fraction `x.toNat % 2^52`
and the sign `x.toNat / 2^63`. -/
namespace Verification.IndexNumbers
open Float.Model Float.Model.UnpackedFloat

/-! ## The fields of a double -/

theorem expo_toNat (x : UInt64) : ((x >>> 52) &&& 0x7ff).toNat = x.toNat / 2 ^ 52 % 2 ^ 11 := by
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
  have : (0x7ff : UInt64).toNat = 2 ^ 11 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  rfl

theorem frac_toNat (x : UInt64) : (x &&& 0xfffffffffffff).toNat = x.toNat % 2 ^ 52 := by
  rw [UInt64.toNat_and]
  have : (0xfffffffffffff : UInt64).toNat = 2 ^ 52 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem sign_toNat (x : UInt64) : (x >>> 63 == 1) = decide (2 ^ 63 ≤ x.toNat) := by
  have hx := x.toNat_lt
  have h : (x >>> 63).toNat = x.toNat / 2 ^ 63 := by
    rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl
  by_cases hs : 2 ^ 63 ≤ x.toNat
  · have : x >>> 63 = 1 := UInt64.toNat_inj.mp (by rw [h]; show _ = 1; omega)
    simp [this, hs]
  · have : x >>> 63 ≠ 1 := fun he => by
      have := congrArg UInt64.toNat he; rw [h] at this; change _ = 1 at this; omega
    simp [this, hs]

/-- The scaled value of a double with its sign clear and a biased exponent
neither `0` nor all ones: `(m + 2^52) * 2^(e - 1)`, its value times `2^1074`. -/
def scaled (x : UInt64) : Nat := (x.toNat % 2 ^ 52 + 2 ^ 52) * 2 ^ (x.toNat / 2 ^ 52 % 2 ^ 11 - 1)

/-- The double `x` denotes the natural `n` exactly: a zero denoting `0`, or a
normal double, its sign clear, whose value is `n`. -/
def Denotes (x : UInt64) (n : Nat) : Prop :=
  ((x.toNat = 0 ∨ x.toNat = 2 ^ 63) ∧ n = 0) ∨
  (x.toNat < 2 ^ 63 ∧ 1 ≤ x.toNat / 2 ^ 52 % 2 ^ 11 ∧ x.toNat / 2 ^ 52 % 2 ^ 11 ≤ 2046 ∧
    scaled x = n * 2 ^ 1074)

theorem indexOfBits_denotes {x : UInt64} {i : Nat} (h : indexOfBits x = some i) :
    Denotes x i ∧ i < 4294967295 := by
  have hx := x.toNat_lt
  simp only [indexOfBits, expo_toNat, frac_toNat, sign_toNat] at h
  by_cases hz : x.toNat % 2 ^ 52 = 0 ∧ x.toNat / 2 ^ 52 % 2 ^ 11 = 0
  · rw [if_pos (by simp [hz.1, hz.2])] at h
    cases h
    refine ⟨.inl ⟨?_, rfl⟩, by omega⟩
    have h1 := Nat.div_add_mod x.toNat (2 ^ 52)
    have h2 := Nat.div_add_mod (x.toNat / 2 ^ 52) (2 ^ 11)
    have : x.toNat / 2 ^ 52 / 2 ^ 11 ≤ 1 := by
      rw [Nat.div_div_eq_div_mul]; exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega))
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with h3 | h3 <;> omega
  · rw [if_neg (by simpa [Bool.and_eq_true, beq_iff_eq] using hz)] at h
    split at h
    · cases h
    · rename_i hn
      simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, not_or] at hn
      split at h
      · rename_i hd
        cases h
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hd
        refine ⟨.inr ⟨by omega, by omega, by omega, ?_⟩, hd.2⟩
        unfold scaled
        exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hd.1)).symm
      · cases h

theorem denotes_indexOfBits {x : UInt64} {i : Nat} (hd : Denotes x i) (hi : i < 4294967295) :
    indexOfBits x = some i := by
  simp only [indexOfBits, expo_toNat, frac_toNat, sign_toNat]
  rcases hd with ⟨hz, rfl⟩ | ⟨hs, he1, he2, hsc⟩
  · rcases hz with hz | hz <;> simp [hz]
  · have hnz : ¬ (x.toNat % 2 ^ 52 = 0 ∧ x.toNat / 2 ^ 52 % 2 ^ 11 = 0) := by omega
    rw [if_neg (by simpa [Bool.and_eq_true, beq_iff_eq] using hnz)]
    rw [if_neg (by simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, not_or]; omega)]
    have hs' : (x.toNat % 2 ^ 52 + 2 ^ 52) * 2 ^ (x.toNat / 2 ^ 52 % 2 ^ 11 - 1) = i * 2 ^ 1074 := hsc
    rw [hs']
    have hP : 0 < 2 ^ 1074 := Nat.two_pow_pos 1074
    generalize 2 ^ 1074 = P at hP ⊢
    rw [Nat.mul_mod_left, Nat.mul_div_cancel _ hP, if_pos (by simp [hi])]

/-! ## The float model of such doubles -/

theorem unpackExponent_toNat (b : BitVec 64) :
    (unpackExponent (spec := Format.binary64) b).toNat = b.toNat / 2 ^ 52 % 2 ^ 11 := by
  simp [unpackExponent, BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow]

theorem unpackMantissa_toNat (b : BitVec 64) :
    (unpackMantissa (spec := Format.binary64) b).toNat = b.toNat % 2 ^ 52 := by
  simp [unpackMantissa, BitVec.extractLsb_toNat]

theorem unpackSign_toNat (b : BitVec 64) :
    (unpackSign (spec := Format.binary64) b).toNat = b.toNat / 2 ^ 63 := by
  have := b.isLt
  simp [unpackSign, BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow]
  omega


theorem exp_allOnes (b : BitVec 64) :
    unpackExponent (spec := Format.binary64) b = -1#_ ↔ b.toNat / 2 ^ 52 % 2 ^ 11 = 2047 := by
  rw [← BitVec.toNat_inj, unpackExponent_toNat]; simp

theorem exp_zero (b : BitVec 64) :
    unpackExponent (spec := Format.binary64) b = 0#_ ↔ b.toNat / 2 ^ 52 % 2 ^ 11 = 0 := by
  rw [← BitVec.toNat_inj, unpackExponent_toNat]; simp

theorem mant_zero (b : BitVec 64) :
    unpackMantissa (spec := Format.binary64) b = 0#_ ↔ b.toNat % 2 ^ 52 = 0 := by
  rw [← BitVec.toNat_inj, unpackMantissa_toNat]; simp

theorem unpack_finitePos (b : BitVec 64) (hs : b.toNat < 2 ^ 63)
    (he1 : 1 ≤ b.toNat / 2 ^ 52 % 2 ^ 11) (he2 : b.toNat / 2 ^ 52 % 2 ^ 11 ≤ 2046) :
    ∃ h, UnpackedFloat.unpack .binary64 b =
      .finite .positive (b.toNat % 2 ^ 52 + 2 ^ 52) ((b.toNat / 2 ^ 52 % 2 ^ 11 : Nat) - 1075) h := by
  refine ⟨by omega, ?_⟩
  have hsign : unpackSign (spec := Format.binary64) b = 0#1 := by
    rw [← BitVec.toNat_inj, unpackSign_toNat]; simp; omega
  simp only [UnpackedFloat.unpack, hsign, Sign.ofBitVec, if_true]
  rw [if_neg (by rw [exp_allOnes]; omega), if_neg (by rw [exp_zero]; omega)]
  congr 1
  · rw [BitVec.toNat_append, unpackMantissa_toNat]
    have hm : b.toNat % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (Nat.two_pow_pos 52)
    rw [← Nat.shiftLeft_add_eq_or_of_lt hm, Nat.shiftLeft_eq]
    simp; omega
  · simp [unpackExponent_toNat, Format.exponentBias]

theorem unpack_zero (b : BitVec 64) (hz : b.toNat % 2 ^ 63 = 0) :
    ∃ s, UnpackedFloat.unpack .binary64 b = .zero s := by
  refine ⟨Sign.ofBitVec (unpackSign (spec := .binary64) b), ?_⟩
  have he : b.toNat / 2 ^ 52 % 2 ^ 11 = 0 := by omega
  have hm : b.toNat % 2 ^ 52 = 0 := by omega
  simp only [UnpackedFloat.unpack]
  rw [if_neg (by rw [exp_allOnes]; omega), if_pos ((exp_zero b).mpr he), dif_pos ((mant_zero b).mpr hm)]

theorem packComponents_toNat (s : Sign) (e : BitVec 11) (m : BitVec 52) :
    (packComponents .binary64 s e m).toNat = s.toBitVec.toNat * 2 ^ 63 + e.toNat * 2 ^ 52 + m.toNat := by
  simp only [packComponents, BitVec.toNat_append]
  have hm := m.isLt
  have he := e.isLt
  rw [← Nat.shiftLeft_add_eq_or_of_lt hm, ← Nat.shiftLeft_add_eq_or_of_lt he, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  simp only [Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add]

theorem pack_finitePos (m : Nat) (e : Int) (h : 0 < m) (hm1 : 2 ^ 52 ≤ m) (hm2 : m < 2 ^ 53)
    (he1 : 1 ≤ e + 1075) (he2 : e + 1075 ≤ 2046) :
    (UnpackedFloat.pack .binary64 (.finite .positive m e h)).toNat = (e + 1075).toNat * 2 ^ 52 + (m - 2 ^ 52) := by
  have hl : m.log2 = 52 := (Nat.log2_eq_iff (by omega)).mpr ⟨hm1, hm2⟩
  simp only [UnpackedFloat.pack, hl, Format.exponentBias]
  rw [if_neg (by simp; omega), if_pos (by simp [Format.mantissaBits])]
  rw [packComponents_toNat]
  simp [Sign.toBitVec]
  omega

theorem model_unpack (x : UInt64) :
    (Float.ofBits x).toModel.unpack =
      UnpackedFloat.unpack .binary64 (UnpackedFloat.pack .binary64 (UnpackedFloat.unpack .binary64 x.toBitVec)) := rfl

theorem model_finitePos (x : UInt64) (hs : x.toNat < 2 ^ 63)
    (he1 : 1 ≤ x.toNat / 2 ^ 52 % 2 ^ 11) (he2 : x.toNat / 2 ^ 52 % 2 ^ 11 ≤ 2046) :
    ∃ h, (Float.ofBits x).toModel.unpack =
      .finite .positive (x.toNat % 2 ^ 52 + 2 ^ 52) ((x.toNat / 2 ^ 52 % 2 ^ 11 : Nat) - 1075) h := by
  obtain ⟨h, hu⟩ := unpack_finitePos x.toBitVec (by simpa using hs) (by simpa using he1) (by simpa using he2)
  simp only [UInt64.toNat_toBitVec] at hu
  rw [model_unpack, hu]
  have hp := pack_finitePos (x.toNat % 2 ^ 52 + 2 ^ 52) ((x.toNat / 2 ^ 52 % 2 ^ 11 : Nat) - 1075) h
    (by omega) (by omega) (by omega) (by omega)
  have hE : ((x.toNat / 2 ^ 52 % 2 ^ 11 : Nat) - 1075 + 1075 : Int).toNat = x.toNat / 2 ^ 52 % 2 ^ 11 := by omega
  rw [hE] at hp
  obtain ⟨h', hu'⟩ := unpack_finitePos (UnpackedFloat.pack .binary64
    (.finite .positive (x.toNat % 2 ^ 52 + 2 ^ 52) ((x.toNat / 2 ^ 52 % 2 ^ 11 : Nat) - 1075) h))
    (by rw [hp]; omega) (by rw [hp]; omega) (by rw [hp]; omega)
  refine ⟨h, ?_⟩
  rw [hu']
  have hf : (x.toNat / 2 ^ 52 % 2 ^ 11 * 2 ^ 52 + (x.toNat % 2 ^ 52 + 2 ^ 52 - 2 ^ 52)) / 2 ^ 52 % 2 ^ 11 =
      x.toNat / 2 ^ 52 % 2 ^ 11 := by omega
  have hm : (x.toNat / 2 ^ 52 % 2 ^ 11 * 2 ^ 52 + (x.toNat % 2 ^ 52 + 2 ^ 52 - 2 ^ 52)) % 2 ^ 52 =
      x.toNat % 2 ^ 52 := by omega
  simp only [hp, hf, hm]

theorem model_zero (x : UInt64) (hz : x.toNat % 2 ^ 63 = 0) :
    ∃ s, (Float.ofBits x).toModel.unpack = .zero s := by
  obtain ⟨s, hu⟩ := unpack_zero x.toBitVec (by simpa using hz)
  rw [model_unpack, hu]
  apply unpack_zero
  simp only [UnpackedFloat.pack, packedZero, packComponents_toNat]
  simp

theorem lex_scaled {m1 m2 E1 E2 : Nat} (hm1 : 2 ^ 52 ≤ m1 ∧ m1 < 2 ^ 53) (hm2 : 2 ^ 52 ≤ m2 ∧ m2 < 2 ^ 53)
    (hE1 : 1 ≤ E1) (hE2 : 1 ≤ E2) :
    (compare ((E1 : Int) - 1075) ((E2 : Int) - 1075)).then (compare m1 m2) =
      compare (m1 * 2 ^ (E1 - 1)) (m2 * 2 ^ (E2 - 1)) := by
  rcases Nat.lt_trichotomy E1 E2 with h | rfl | h
  · have hc : compare ((E1 : Int) - 1075) ((E2 : Int) - 1075) = .lt := Int.compare_eq_lt.mpr (by omega)
    rw [hc]
    symm; apply Nat.compare_eq_lt.mpr
    have h1 : m1 * 2 ^ (E1 - 1) < 2 ^ 53 * 2 ^ (E1 - 1) := Nat.mul_lt_mul_of_pos_right hm1.2 (Nat.two_pow_pos _)
    have h2 : 2 ^ 53 * 2 ^ (E1 - 1) ≤ 2 ^ 52 * 2 ^ (E2 - 1) := by
      rw [← Nat.pow_add, ← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : 2 ^ 52 * 2 ^ (E2 - 1) ≤ m2 * 2 ^ (E2 - 1) := Nat.mul_le_mul_right _ hm2.1
    omega
  · have hc : compare ((E1 : Int) - 1075) ((E1 : Int) - 1075) = .eq := Int.compare_eq_eq.mpr rfl
    rw [hc]
    simp only [Ordering.then]
    rcases Nat.lt_trichotomy m1 m2 with hm | rfl | hm
    · rw [Nat.compare_eq_lt.mpr hm, Nat.compare_eq_lt.mpr (Nat.mul_lt_mul_of_pos_right hm (Nat.two_pow_pos _))]
    · rw [Nat.compare_eq_eq.mpr rfl, Nat.compare_eq_eq.mpr rfl]
    · rw [Nat.compare_eq_gt.mpr hm, Nat.compare_eq_gt.mpr (Nat.mul_lt_mul_of_pos_right hm (Nat.two_pow_pos _))]
  · have hc : compare ((E1 : Int) - 1075) ((E2 : Int) - 1075) = .gt := Int.compare_eq_gt.mpr (by omega)
    rw [hc]
    symm; apply Nat.compare_eq_gt.mpr
    have h1 : m2 * 2 ^ (E2 - 1) < 2 ^ 53 * 2 ^ (E2 - 1) := Nat.mul_lt_mul_of_pos_right hm2.2 (Nat.two_pow_pos _)
    have h2 : 2 ^ 53 * 2 ^ (E2 - 1) ≤ 2 ^ 52 * 2 ^ (E1 - 1) := by
      rw [← Nat.pow_add, ← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : 2 ^ 52 * 2 ^ (E1 - 1) ≤ m1 * 2 ^ (E1 - 1) := Nat.mul_le_mul_right _ hm1.1
    omega


theorem denotes_pos {x : UInt64} {n : Nat} (hs : scaled x = n * 2 ^ 1074) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · have : 0 < scaled x := Nat.mul_pos (by omega) (Nat.two_pow_pos _)
    omega
  · exact h

theorem compare_mul_right {p q P : Nat} (hP : 0 < P) : compare (p * P) (q * P) = compare p q := by
  rcases Nat.lt_trichotomy p q with h | rfl | h
  · rw [Nat.compare_eq_lt.mpr h, Nat.compare_eq_lt.mpr (Nat.mul_lt_mul_of_pos_right h hP)]
  · rw [Nat.compare_eq_eq.mpr rfl, Nat.compare_eq_eq.mpr rfl]
  · rw [Nat.compare_eq_gt.mpr h, Nat.compare_eq_gt.mpr (Nat.mul_lt_mul_of_pos_right h hP)]

theorem compare_denotes {x y : UInt64} {p q : Nat} (hx : Denotes x p) (hy : Denotes y q) :
    (Float.ofBits x).toModel.unpack.compare (Float.ofBits y).toModel.unpack = some (compare p q) := by
  rcases hx with ⟨hx, rfl⟩ | ⟨hxs, hx1, hx2, hxv⟩ <;> rcases hy with ⟨hy, rfl⟩ | ⟨hys, hy1, hy2, hyv⟩
  · obtain ⟨s, hs⟩ := model_zero x (by omega)
    obtain ⟨s', hs'⟩ := model_zero y (by omega)
    rw [hs, hs']; rfl
  · obtain ⟨s, hs⟩ := model_zero x (by omega)
    obtain ⟨h, hu⟩ := model_finitePos y hys hy1 hy2
    rw [hs, hu, Nat.compare_eq_lt.mpr (denotes_pos hyv)]; rfl
  · obtain ⟨h, hu⟩ := model_finitePos x hxs hx1 hx2
    obtain ⟨s, hs⟩ := model_zero y (by omega)
    rw [hs, hu, Nat.compare_eq_gt.mpr (denotes_pos hxv)]; rfl
  · obtain ⟨h, hu⟩ := model_finitePos x hxs hx1 hx2
    obtain ⟨h', hu'⟩ := model_finitePos y hys hy1 hy2
    rw [hu, hu']
    show some (_ : Ordering) = _
    congr 1
    rw [lex_scaled (by omega) (by omega) hx1 hy1]
    change compare (scaled x) (scaled y) = _
    rw [hxv, hyv, compare_mul_right (Nat.two_pow_pos 1074)]

theorem float_lt_iff (a b : Float) : a < b ↔ a.toModel.unpack.compare b.toModel.unpack = some .lt := by
  show a.lt b = true ↔ _
  simp [Float.lt, LT.lt, Float.Model.lt, UnpackedFloat.lt]

theorem float_beq_iff (a b : Float) : (a == b) = true ↔ a.toModel.unpack.compare b.toModel.unpack = some .eq := by
  show (a.toModel.unpack.compare b.toModel.unpack == some Ordering.eq) = true ↔ _
  exact beq_iff_eq

theorem doubleOrder_denotes {x y : UInt64} {p q : Nat} (hx : Denotes x p) (hy : Denotes y q) :
    doubleOrder x y = some (compare p q) := by
  have hxy := compare_denotes hx hy
  have hyx := compare_denotes hy hx
  simp only [doubleOrder]
  rcases Nat.lt_trichotomy p q with h | rfl | h
  · rw [if_pos ((float_lt_iff _ _).mpr (by rw [hxy, Nat.compare_eq_lt.mpr h])), Nat.compare_eq_lt.mpr h]
  · rw [if_neg (by rw [float_lt_iff, hxy, Nat.compare_eq_eq.mpr rfl]; simp),
      if_pos ((float_beq_iff _ _).mpr (by rw [hxy, Nat.compare_eq_eq.mpr rfl])), Nat.compare_eq_eq.mpr rfl]
  · rw [if_neg (by rw [float_lt_iff, hxy, Nat.compare_eq_gt.mpr h]; simp),
      if_neg (by rw [float_beq_iff, hxy, Nat.compare_eq_gt.mpr h]; simp),
      if_pos ((float_lt_iff _ _).mpr (by rw [hyx, Nat.compare_eq_lt.mpr h])), Nat.compare_eq_gt.mpr h]

theorem bitsOfNat_toNat {L : Nat} (h0 : 0 < L) (hL : L < 2 ^ 53) :
    (bitsOfNat L).toNat = (1022 + (L.log2 + 1)) * 2 ^ 52 + (L * 2 ^ (53 - (L.log2 + 1)) - 2 ^ 52) ∧
      2 ^ 52 ≤ L * 2 ^ (53 - (L.log2 + 1)) ∧ L * 2 ^ (53 - (L.log2 + 1)) < 2 ^ 53 ∧ L.log2 + 1 ≤ 53 := by
  have hl1 : 2 ^ L.log2 ≤ L := Nat.log2_self_le (by omega)
  have hl2 : L < 2 ^ (L.log2 + 1) := Nat.lt_log2_self
  have hlen : L.log2 < 53 := (Nat.log2_lt (by omega)).mpr hL
  have hlo : 2 ^ 52 ≤ L * 2 ^ (53 - (L.log2 + 1)) := by
    calc 2 ^ 52 = 2 ^ L.log2 * 2 ^ (53 - (L.log2 + 1)) := by rw [← Nat.pow_add]; congr 1; omega
      _ ≤ L * 2 ^ (53 - (L.log2 + 1)) := Nat.mul_le_mul_right _ hl1
  have hhi : L * 2 ^ (53 - (L.log2 + 1)) < 2 ^ 53 := by
    calc L * 2 ^ (53 - (L.log2 + 1)) < 2 ^ (L.log2 + 1) * 2 ^ (53 - (L.log2 + 1)) :=
          Nat.mul_lt_mul_of_pos_right hl2 (Nat.two_pow_pos _)
      _ = 2 ^ 53 := by rw [← Nat.pow_add]; congr 1; omega
  refine ⟨?_, hlo, hhi, by omega⟩
  simp only [bitsOfNat, if_pos hL, encodeBits]
  rw [if_neg (by simp; omega), if_pos (by omega), if_pos (by omega)]
  rw [UInt64.toNat_ofNat', Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  have hm : L * 2 ^ (53 - (L.log2 + 1)) - 2 ^ 52 < 2 ^ 52 := by omega
  have he : 1075 - (53 - (L.log2 + 1)) = 1022 + (L.log2 + 1) := by omega
  rw [he, Nat.mul_comm _ (2 ^ 52), ← Nat.two_pow_add_eq_or_of_lt hm, Nat.mul_comm (2 ^ 52)]
  apply Nat.mod_eq_of_lt
  have : 1022 + (L.log2 + 1) ≤ 1075 := by omega
  have : (1022 + (L.log2 + 1)) * 2 ^ 52 ≤ 1075 * 2 ^ 52 := Nat.mul_le_mul_right _ this
  omega

theorem denotes_bitsOfNat {L : Nat} (hL : L < 2 ^ 53) : Denotes (bitsOfNat L) L := by
  rcases Nat.eq_zero_or_pos L with rfl | h0
  · left; refine ⟨.inl ?_, rfl⟩; rfl
  · obtain ⟨ht, hlo, hhi, hlen⟩ := bitsOfNat_toNat h0 hL
    have hE : (bitsOfNat L).toNat / 2 ^ 52 % 2 ^ 11 = 1022 + (L.log2 + 1) := by rw [ht]; omega
    have hM : (bitsOfNat L).toNat % 2 ^ 52 = L * 2 ^ (53 - (L.log2 + 1)) - 2 ^ 52 := by rw [ht]; omega
    refine .inr ⟨by rw [ht]; omega, by omega, by omega, ?_⟩
    simp only [scaled, hE, hM]
    rw [Nat.sub_add_cancel hlo, Nat.mul_assoc, ← Nat.pow_add]
    congr 2; omega

theorem indexOfBits_bitsOfNat {i : Nat} (hi : i < 4294967295) : indexOfBits (bitsOfNat i) = some i :=
  denotes_indexOfBits (denotes_bitsOfNat (by omega)) hi

theorem magnitude_toNat (x : UInt64) : (x &&& 0x7fffffffffffffff).toNat = x.toNat % 2 ^ 63 := by
  rw [UInt64.toNat_and]
  have : (0x7fffffffffffffff : UInt64).toNat = 2 ^ 63 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem numberEqual_index {x y : UInt64} {i : Nat} (he : numberEqual x y = true) (hi : indexOfBits x = some i) :
    indexOfBits y = some i := by
  simp only [numberEqual, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at he
  rcases he.2 with rfl | ⟨hx, hy⟩
  · exact hi
  · have hx' := congrArg UInt64.toNat hx
    have hy' := congrArg UInt64.toNat hy
    rw [magnitude_toNat] at hx' hy'
    have hy0 := y.toNat_lt
    have hx0 := x.toNat_lt
    have dy : Denotes y 0 := .inl ⟨by simp at hy'; omega, rfl⟩
    have dx : Denotes x 0 := .inl ⟨by simp at hx'; omega, rfl⟩
    rw [denotes_indexOfBits dy (by decide)]
    rw [denotes_indexOfBits dx (by decide)] at hi
    exact hi

theorem strictEquals_index {x : UInt64} {v : Tm} {i : Nat} (he : strictEquals (.num x) v = some true)
    (hi : indexOfBits x = some i) : ∃ y, v = .num y ∧ indexOfBits y = some i := by
  simp only [strictEquals] at he
  split at he
  · cases he
  · rw [if_pos (by simp [isPrim])] at he
    cases v <;> simp [sameValue] at he
    exact ⟨_, rfl, numberEqual_index he hi⟩

theorem strictEquals_index_swap {x : UInt64} {v : Tm} {i : Nat} (he : strictEquals v (.num x) = some true)
    (hi : indexOfBits x = some i) : ∃ y, v = .num y ∧ indexOfBits y = some i := by
  simp only [strictEquals] at he
  split at he
  · cases he
  · rw [if_pos (by simp [isPrim])] at he
    cases v <;> simp [sameValue] at he
    refine ⟨_, rfl, ?_⟩
    simp only [numberEqual, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at he ⊢
    exact numberEqual_index (by
      simp only [numberEqual, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
      exact ⟨⟨he.1.2, he.1.1⟩, he.2.elim (fun h => .inl h.symm) (fun h => .inr ⟨h.2, h.1⟩)⟩) hi

/-! ## Conjunction with a non-negative mask -/

theorem intAnd_mask (t : Int) {M : Nat} (hM : M < 2 ^ 31) :
    ∃ r : Nat, intAnd t (M : Int) = (r : Int) ∧ r < 2 ^ 31 := by
  cases t with
  | ofNat a => exact ⟨a &&& M, rfl, Nat.lt_of_le_of_lt Nat.and_le_right hM⟩
  | negSucc a =>
    exact ⟨M ^^^ (a &&& M), rfl, Nat.xor_lt_two_pow hM (Nat.lt_of_le_of_lt Nat.and_le_right hM)⟩

theorem mask_intAnd (t : Int) {M : Nat} (hM : M < 2 ^ 31) :
    ∃ r : Nat, intAnd (M : Int) t = (r : Int) ∧ r < 2 ^ 31 := by
  cases t with
  | ofNat a => exact ⟨M &&& a, rfl, Nat.lt_of_le_of_lt Nat.and_le_left hM⟩
  | negSucc a =>
    exact ⟨M ^^^ (M &&& a), rfl, Nat.xor_lt_two_pow hM (Nat.lt_of_le_of_lt Nat.and_le_left hM)⟩

theorem int32Bits_nat (r : Nat) : int32Bits (r : Int) = bitsOfNat r := by
  simp only [int32Bits, if_neg (Int.not_lt.mpr (Int.natCast_nonneg r)), Int.toNat_natCast]

/-- `x & m`, `m` a mask whose `ToInt32` is a natural below `2^31`, is an index. -/
theorem bitAnd_index (x : UInt64) {m : UInt64} {M : Nat} (hm : toInt32 m = (M : Int)) (hM : M < 2 ^ 31) :
    ∃ r, indexOfBits (arithBits .bitAnd x m) = some r := by
  obtain ⟨r, hr, hlt⟩ := intAnd_mask (toInt32 x) hM
  refine ⟨r, ?_⟩
  simp only [arithBits, hm, hr, int32Bits_nat]
  exact indexOfBits_bitsOfNat (by omega)

/-- `m & x`, likewise. -/
theorem mask_bitAnd_index (x : UInt64) {m : UInt64} {M : Nat} (hm : toInt32 m = (M : Int)) (hM : M < 2 ^ 31) :
    ∃ r, indexOfBits (arithBits .bitAnd m x) = some r := by
  obtain ⟨r, hr, hlt⟩ := mask_intAnd (toInt32 x) hM
  refine ⟨r, ?_⟩
  simp only [arithBits, hm, hr, int32Bits_nat]
  exact indexOfBits_bitsOfNat (by omega)

/-! ## An index against a length -/

/-- The answers of the relational operator `op` that give an index at most a
length: with the index on the left (`left`), `>` and `>=` false, `<` and
`<=` true; with it on the right, `<` and `<=` false, `>` and `>=` true. -/
def boundAnswer : Arith → Bool → Bool → Bool
  | .gt, true, false | .ge, true, false | .lt, true, true | .le, true, true => true
  | .lt, false, false | .le, false, false | .gt, false, true | .ge, false, true => true
  | _, _, _ => false

theorem le_of_relation {x : UInt64} {L i : Nat} (hi : indexOfBits x = some i) {op : Arith} {q : Bool}
    (hb : boundAnswer op true q = true) (hr : relationHolds op (doubleOrder x (bitsOfNat L)) = q) : i ≤ L := by
  obtain ⟨hd, hlt⟩ := indexOfBits_denotes hi
  by_cases hL : L < 2 ^ 53
  · rw [doubleOrder_denotes hd (denotes_bitsOfNat hL)] at hr
    rcases Nat.lt_trichotomy i L with h | rfl | h
    · omega
    · omega
    · rw [Nat.compare_eq_gt.mpr h] at hr
      cases op <;> cases q <;> simp_all [boundAnswer, relationHolds]
  · omega

theorem le_of_relation_swap {x : UInt64} {L i : Nat} (hi : indexOfBits x = some i) {op : Arith} {q : Bool}
    (hb : boundAnswer op false q = true) (hr : relationHolds op (doubleOrder (bitsOfNat L) x) = q) : i ≤ L := by
  obtain ⟨hd, hlt⟩ := indexOfBits_denotes hi
  by_cases hL : L < 2 ^ 53
  · rw [doubleOrder_denotes (denotes_bitsOfNat hL) hd] at hr
    rcases Nat.lt_trichotomy i L with h | rfl | h
    · omega
    · omega
    · rw [Nat.compare_eq_lt.mpr h] at hr
      cases op <;> cases q <;> simp_all [boundAnswer, relationHolds]
  · omega

end Verification.IndexNumbers
