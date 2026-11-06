import Verification.Semantics.Safety

/-! # Signed 64-bit integers

The release profile uses wrapping addition, subtraction, multiplication and
negation. Division and remainder truncate toward zero and trap on zero or
MIN / -1 (including MIN % -1). Traps are represented as throws at the adapter.
-/
namespace Verification.I64

def half : Int := 9223372036854775808
def modulus : Int := 18446744073709551616

def InRange (z : Int) : Prop := -half ≤ z ∧ z < half
instance (z : Int) : Decidable (InRange z) := inferInstanceAs (Decidable (_ ∧ _))
abbrev Signed := {z : Int // InRange z}

def wrap (z : Int) : Int := (z + half) % modulus - half

theorem wrap_range (z : Int) : InRange (wrap z) := by
  have lo := Int.emod_nonneg (z + half) (by decide : modulus ≠ 0)
  have hi := Int.emod_lt_of_pos (z + half) (by decide : 0 < modulus)
  unfold InRange wrap half modulus at *
  omega

theorem wrap_identity {z : Int} (h : InRange z) : wrap z = z := by
  have hz : 0 ≤ z + half ∧ z + half < modulus := by
    unfold InRange half modulus at *
    omega
  simp only [wrap, Int.emod_eq_of_lt hz.1 hz.2]
  omega

def decode (z : Int) : Signed := ⟨wrap z, wrap_range z⟩
def encode (z : Signed) : Int := z.val

theorem decode_encode (z : Signed) : decode (encode z) = z := by
  apply Subtype.ext
  exact wrap_identity z.property

theorem encode_decode (z : Int) : encode (decode z) = wrap z := rfl

theorem wrap_idempotent (z : Int) : wrap (wrap z) = wrap z :=
  wrap_identity (wrap_range z)

theorem wrap_congr {a b : Int} (h : a % modulus = b % modulus) : wrap a = wrap b := by
  unfold wrap
  rw [Int.add_emod a, Int.add_emod b, h]

/-- Wrapping preserves the residue modulo 2^64. -/
theorem wrap_mod (z : Int) : wrap z % modulus = z % modulus := by
  unfold wrap
  rw [Int.emod_sub_emod]
  congr 1
  omega

/-- The expression emitted by the Rust lowering uses truncating remainder. -/
def jsWrap (z : Int) : Int :=
  (((z + half).tmod modulus + modulus).tmod modulus) - half

theorem jsWrap_eq_wrap (z : Int) : jsWrap z = wrap z := by
  have lo := Int.lt_tmod_of_pos (z + half) (by decide : 0 < modulus)
  have hn : 0 ≤ (z + half).tmod modulus + modulus := by omega
  unfold jsWrap wrap
  rw [Int.tmod_eq_emod_of_nonneg hn, Int.tmod_eq_emod]
  split
  · simp
  · have hm : (modulus.natAbs : Int) = modulus := by decide
    rw [hm]
    have : (z + half) % modulus - modulus + modulus = (z + half) % modulus := by omega
    rw [this, Int.emod_emod]

inductive Trap where
  | overflow | zero | divisionOverflow
  deriving DecidableEq, Repr

/-- Checked arithmetic returns the exact result or reports overflow. -/
def checked (z : Int) : Except Trap Signed :=
  if h : InRange z then .ok ⟨z, h⟩ else .error .overflow

def checkedAdd (a b : Signed) := checked (a.val + b.val)
def checkedSub (a b : Signed) := checked (a.val - b.val)
def checkedMul (a b : Signed) := checked (a.val * b.val)
def checkedNeg (a : Signed) := checked (-a.val)

def add (a b : Signed) : Signed := decode (a.val + b.val)
def sub (a b : Signed) : Signed := decode (a.val - b.val)
def mul (a b : Signed) : Signed := decode (a.val * b.val)
def neg (a : Signed) : Signed := decode (-a.val)
def lt (a b : Signed) : Bool := decide (a.val < b.val)
def le (a b : Signed) : Bool := decide (a.val ≤ b.val)

theorem tdiv_range (a b : Signed) (safe : ¬ (a.val = -half ∧ b.val = -1)) :
    InRange (a.val.tdiv b.val) := by
  have ha := a.property
  have upper := Int.le_natAbs (a := a.val.tdiv b.val)
  have lower := Int.le_natAbs (a := -(a.val.tdiv b.val))
  simp only [Int.natAbs_neg] at lower
  have habs := Int.natAbs_tdiv_le_natAbs a.val b.val
  by_cases hmin : a.val = -half
  · by_cases hone : b.val = 1
    · simp only [hone, Int.tdiv_one]; exact ha
    · by_cases hzero : b.val = 0
      · simp [hzero, InRange, half]
      · have absB := Int.natAbs_of_nonneg (a := b.val)
        have absNegB := Int.natAbs_of_nonneg (a := -b.val)
        have hlarge : 1 < b.val.natAbs := by
          unfold half at *
          by_cases h : 0 ≤ b.val <;> simp_all <;> omega
        have hdiv := Nat.div_lt_self (by decide : 0 < (9223372036854775808 : Nat)) hlarge
        have hqabs : (a.val.tdiv b.val).natAbs < 9223372036854775808 := by
          rw [Int.natAbs_tdiv, hmin]
          exact hdiv
        unfold InRange half
        omega
  · have absA := Int.natAbs_of_nonneg (a := a.val)
    have absNegA := Int.natAbs_of_nonneg (a := -a.val)
    unfold InRange half at *
    by_cases h : 0 ≤ a.val <;> simp_all <;> omega

theorem tmod_range (a b : Signed) : InRange (a.val.tmod b.val) := by
  by_cases hz : b.val = 0
  · simpa [hz] using a.property
  · have hb := b.property
    have absB := Int.natAbs_of_nonneg (a := b.val)
    have absNegB := Int.natAbs_of_nonneg (a := -b.val)
    have hn : b.val.natAbs ≠ 0 := by omega
    have hm := Nat.mod_lt a.val.natAbs (Nat.pos_of_ne_zero hn)
    rw [← Int.natAbs_tmod] at hm
    have upper := Int.le_natAbs (a := a.val.tmod b.val)
    have lower := Int.le_natAbs (a := -(a.val.tmod b.val))
    simp only [Int.natAbs_neg] at lower absNegB
    have hbabs : b.val.natAbs ≤ 9223372036854775808 := by
      unfold InRange half at hb
      by_cases h : 0 ≤ b.val
      · have := absB h; omega
      · have := absNegB (by omega); omega
    unfold InRange half
    omega

/-- Overflow is checked independently of the arithmetic profile. -/
def divRem (remainder : Bool) (a b : Signed) : Except Trap Signed :=
  if b.val = 0 then .error .zero
  else if a.val = -half ∧ b.val = -1 then .error .divisionOverflow
  else .ok (decode (if remainder then a.val.tmod b.val else a.val.tdiv b.val))

def div := divRem false
def rem := divRem true

/-- On a normal return, neither division nor remainder changes the exact
truncating integer result. -/
theorem divRem_exact (r : Bool) (a b : Signed) (hz : b.val ≠ 0)
    (hs : ¬ (a.val = -half ∧ b.val = -1)) :
    (divRem r a b).map encode =
      .ok (if r then a.val.tmod b.val else a.val.tdiv b.val) := by
  simp only [divRem, hz, hs, ↓reduceIte, Except.map, encode, decode]
  cases r
  · exact congrArg Except.ok (wrap_identity (tdiv_range a b hs))
  · exact congrArg Except.ok (wrap_identity (tmod_range a b))

theorem lt_correct (a b : Signed) : lt a b = true ↔ a.val < b.val := by simp [lt]
theorem le_correct (a b : Signed) : le a b = true ↔ a.val ≤ b.val := by simp [le]

theorem checked_exact {z : Int} {v : Signed} (h : checked z = .ok v) : v.val = z := by
  unfold checked at h
  split at h
  · cases h; rfl
  · cases h

theorem checked_overflow {z : Int} (h : ¬ InRange z) : checked z = .error .overflow := by
  simp [checked, h]

theorem divRem_zero (r : Bool) (a b : Signed) (h : b.val = 0) :
    divRem r a b = .error .zero := by simp [divRem, h]

theorem divRem_min (r : Bool) (a b : Signed) (ha : a.val = -half) (hb : b.val = -1) :
    divRem r a b = .error .divisionOverflow := by simp [divRem, ha, hb]

/-- The public bigint adapter wraps every input; a normal result is signed.
This pure adapter preserves any effect predicate already established for
its body: input conversion and result embedding make no heap change. -/
@[nospecialize] def adapter {H E : Type} (body : List Signed → H → Except E (Signed × H))
    (args : List Int) (heap : H) : Except E (Int × H) :=
  (body (args.map decode) heap).map fun (v, after) => (encode v, after)

theorem adapter_result {H E : Type} {body : List Signed → H → Except E (Signed × H)}
    {args heap result after} (h : adapter body args heap = .ok (result, after)) :
    InRange result := by
  unfold adapter at h
  cases hb : body (args.map decode) heap with
  | error e => simp [hb, Except.map] at h
  | ok v =>
    simp only [hb, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.1 ▸ v.1.property

theorem adapter_effect {H E : Type} {body : List Signed → H → Except E (Signed × H)}
    {effect : H → H → Prop}
    (bodyEffect : ∀ args h v h', body args h = .ok (v, h') → effect h h')
    {args heap result after} (h : adapter body args heap = .ok (result, after)) :
    effect heap after := by
  unfold adapter at h
  cases hb : body (args.map decode) heap with
  | error e => simp [hb, Except.map] at h
  | ok v =>
    simp only [hb, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ bodyEffect _ _ v.1 v.2 hb

/-- Exceptional results are preserved verbatim, including an exceptional
heap when the error type carries one. Thus an on-throw effect of the body
also holds for the adapter. -/
theorem adapter_error {H E : Type} {body : List Signed → H → Except E (Signed × H)}
    {args heap error} (h : adapter body args heap = .error error) :
    body (args.map decode) heap = .error error := by
  unfold adapter at h
  cases hb : body (args.map decode) heap with
  | error e => simpa [hb, Except.map] using h
  | ok v => simp [hb, Except.map] at h

end Verification.I64
