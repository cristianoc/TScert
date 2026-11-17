import Verification.Semantics.SafeIntegers
import Verification.Semantics.Linear

/-! # The arithmetic rules, as data

The arithmetic rules of the note "Tolerant frames" (§6, "Arithmetic
steps") that produce linear facts of a numeric operation's result, each
stated once as an `ArithRule`: the operator, each operand's domain, the
constant operand's side condition and normalisation, the premises and the
conclusion as linear facts over the operands and the result, with
coefficients computed from the bound constant, and the result's domain.
`rules` lists them in the paper's order.

`ArithRule.Sound` is the soundness of one rule against the calculus: for
operand values in their domains meeting the premises, the result
`arithBits` computes lies in the result's domain and meets the
conclusion. `rules_sound` proves it of every rule of `rules`.

The pass's producer (`IndexWrites.linearAtoms`) and the paper's derivation
(`Parity.Derivation.arith`) instantiate the rules through one substitution
(`RuleFact.instantiate`) and one interpretation lemma
(`RuleFact.instantiate_holds`). The verifier exports the rules with the
declarations that state and prove each (`RuleExport.ruleEntries`,
`verifier --export rules arithmetic`). -/
namespace Verification.ArithmeticRules
open Verification.SafeIntegers Verification.IndexNumbers Float.Model Float.Model.UnpackedFloat

/-! ## The datum -/

/-- A rule's variables: its left operand `x`, its right operand (`x'`, or
the constant), and its result `y`. -/
inductive RuleVar where
  | left | right | result
  deriving DecidableEq, Repr

/-- The values an operand or a result ranges over: a safe integer, its
integer value the variable's, or any number, which gives the variable no
value a fact may read. -/
inductive Domain where
  | safeInteger | number
  deriving DecidableEq, Repr

/-- A double in a domain, at an integer value. -/
def Domain.Admits : Domain → UInt64 → Int → Prop
  | .safeInteger, b, i => SafeInt b i
  | .number, _, _ => True

/-- How a rule reads its constant: as itself, or as a shift count, the
constant's `ToUint32` modulo 32 (`arithBits` on `<<`, `>>` and `>>>`). -/
inductive Normalisation where
  | identity | shiftCount
  deriving DecidableEq, Repr

/-- The constant as the rule reads it. For a safe integer `d`, the shift
count `d mod 32` is `ToUint32(d) mod 32` (`shiftCount_toUint32`). -/
def Normalisation.apply : Normalisation → Int → Int
  | .identity, d => d
  | .shiftCount, d => d % 32

/-- A constant operand: a safe integer, a literal or a value known to be
constant, within the bounds of its side condition, read by its
normalisation. -/
structure Constant where
  lower : Option Int
  upper : Option Int
  normalisation : Normalisation
  deriving DecidableEq, Repr

/-- The side condition of a constant: within its stated bounds. -/
def Constant.admits (c : Constant) (d : Int) : Bool :=
  (c.lower.all (· ≤ d)) && (c.upper.all (d ≤ ·))

/-- A right operand: an operand of a domain, or a constant. -/
inductive Right where
  | operand (d : Domain)
  | constant (c : Constant)
  deriving DecidableEq, Repr

/-- A right operand's double in its domain, at an integer value: a
constant is a safe integer meeting its side condition. -/
def Right.Admits : Right → UInt64 → Int → Prop
  | .operand d, b, i => d.Admits b i
  | .constant c, b, i => SafeInt b i ∧ c.admits i = true

/-- The value a rule's coefficients read: the normalised constant, `0` for
a rule without one. -/
def Right.bound : Right → Int → Int
  | .operand _, _ => 0
  | .constant c, d => c.normalisation.apply d

/-- A coefficient computed from the bound constant `k`:
`lit + byConstant·k + byPower·2^k`. -/
structure Coef where
  lit : Int := 0
  byConstant : Int := 0
  byPower : Int := 0
  deriving DecidableEq, Repr

def Coef.eval (c : Coef) (k : Int) : Int := c.lit + c.byConstant * k + c.byPower * 2 ^ k.toNat

/-- A linear fact over a rule's variables, `Σ aᵢ·vᵢ ≤ b`. -/
structure RuleFact where
  terms : List (RuleVar × Coef)
  bound : Coef
  deriving DecidableEq, Repr

/-- A fact's left side at a valuation. -/
def sumTerms (k : Int) (v : RuleVar → Int) : List (RuleVar × Coef) → Int
  | [] => 0
  | (x, a) :: t => a.eval k * v x + sumTerms k v t

def RuleFact.Holds (F : RuleFact) (k : Int) (v : RuleVar → Int) : Prop :=
  sumTerms k v F.terms ≤ F.bound.eval k

/-- **An arithmetic rule**: the paper's name (several triples of one rule
share it), the operator, the operands' domains, the premises, the result's
domain and the conclusion. -/
structure ArithRule where
  name : String
  op : Arith
  left : Domain
  right : Right
  premises : List RuleFact
  result : Domain
  conclusion : List RuleFact
  deriving DecidableEq, Repr

/-- The sort a rule's variable ranges over: any number, or a safe integer. -/
inductive VarSort where
  | num | safeInt
  deriving DecidableEq, Repr

/-- The values of a domain, as a sort. -/
def Domain.sort : Domain → VarSort
  | .safeInteger => .safeInt
  | .number => .num

/-- What a rule's variable is: an operand, a constant, or the result. -/
inductive Role where
  | operand | constant | result
  deriving DecidableEq, Repr

/-- **A rule's variables with their roles and sorts**: an operand of its
domain's sort, a constant a safe integer (`Right.Admits`), and the result
of its domain's sort. -/
def ArithRule.variables (r : ArithRule) : List (RuleVar × Role × VarSort) :=
  [(.left, .operand, r.left.sort),
    match r.right with
    | .operand d => (.right, .operand, d.sort)
    | .constant _ => (.right, .constant, .safeInt),
    (.result, .result, r.result.sort)]

/-- A valuation with the result set to `y`. -/
def resultAt (v : RuleVar → Int) (y : Int) : RuleVar → Int
  | .result => y
  | x => v x

/-- **A rule's soundness against the calculus**: for operand doubles `a`
and `b` in their domains at the values `v`, meeting the premises, the
result `arithBits` computes lies in the result's domain at a value `y`,
and the conclusion holds with the result at `y`. -/
def ArithRule.Sound (r : ArithRule) : Prop :=
  ∀ (a b : UInt64) (v : RuleVar → Int),
    r.left.Admits a (v .left) → r.right.Admits b (v .right) →
    (∀ F ∈ r.premises, F.Holds (r.right.bound (v .right)) v) →
    ∃ y, r.result.Admits (arithBits r.op a b) y ∧
      ∀ F ∈ r.conclusion, F.Holds (r.right.bound (v .right)) (resultAt v y)

/-! ## The rules -/

/-- `Σ aᵢ·vᵢ ≤ b` with integer coefficients. -/
def fact (terms : List (RuleVar × Int)) (b : Int) : RuleFact :=
  ⟨terms.map fun (x, a) => (x, { lit := a }), { lit := b }⟩

/-- The shift count `d`, read modulo 32. -/
def shiftCount : Constant := ⟨none, none, .shiftCount⟩

/-- A factor, any safe integer read as itself. -/
def factor : Constant := ⟨none, none, .identity⟩

/-- The largest safe integer, `M = 2^53 − 1`. -/
def maxSafeInt : Int := 2 ^ 53 - 1

/-- **Add**: `|x + x'| ≤ M` gives `y = x + x'`. -/
def add : ArithRule where
  name := "Add"
  op := .add
  left := .safeInteger
  right := .operand .safeInteger
  premises := [fact [(.left, -1), (.right, -1)] maxSafeInt, fact [(.left, 1), (.right, 1)] maxSafeInt]
  result := .safeInteger
  conclusion := [fact [(.result, 1), (.left, -1), (.right, -1)] 0, fact [(.result, -1), (.left, 1), (.right, 1)] 0]

/-- **Sub**: `|x − x'| ≤ M` gives `y = x − x'`. -/
def sub : ArithRule where
  name := "Sub"
  op := .sub
  left := .safeInteger
  right := .operand .safeInteger
  premises := [fact [(.left, -1), (.right, 1)] maxSafeInt, fact [(.left, 1), (.right, -1)] maxSafeInt]
  result := .safeInteger
  conclusion := [fact [(.result, 1), (.left, -1), (.right, 1)] 0, fact [(.result, -1), (.left, 1), (.right, -1)] 0]

/-- **Scale**: `|c·x| ≤ M` gives `y = c·x`. -/
def scale : ArithRule where
  name := "Scale"
  op := .mul
  left := .safeInteger
  right := .constant factor
  premises := [⟨[(.left, { byConstant := -1 })], { lit := maxSafeInt }⟩, ⟨[(.left, { byConstant := 1 })], { lit := maxSafeInt }⟩]
  result := .safeInteger
  conclusion := [⟨[(.result, { lit := 1 }), (.left, { byConstant := -1 })], {}⟩,
    ⟨[(.result, { lit := -1 }), (.left, { byConstant := 1 })], {}⟩]

/-- **Shr**: `-2^31 ≤ x < 2^31` gives `2^{d'}·y ≤ x ≤ 2^{d'}·y + 2^{d'} − 1`. -/
def shr : ArithRule where
  name := "Shr"
  op := .shr
  left := .safeInteger
  right := .constant shiftCount
  premises := [fact [(.left, -1)] (2 ^ 31), fact [(.left, 1)] (2 ^ 31 - 1)]
  result := .safeInteger
  conclusion := [⟨[(.result, { byPower := 1 }), (.left, { lit := -1 })], {}⟩,
    ⟨[(.left, { lit := 1 }), (.result, { byPower := -1 })], { lit := -1, byPower := 1 }⟩]

/-- **Mask**, its range: for any number `x` and `0 ≤ x' < 2^31`,
`0 ≤ y ≤ x'`. -/
def maskRange : ArithRule where
  name := "Mask"
  op := .bitAnd
  left := .number
  right := .operand .safeInteger
  premises := [fact [(.right, -1)] 0, fact [(.right, 1)] (2 ^ 31 - 1)]
  result := .safeInteger
  conclusion := [fact [(.result, -1)] 0, fact [(.result, 1), (.right, -1)] 0]

/-- **Mask**, its bound: for any number `x`, `0 ≤ x'` gives `y ≤ x'`. -/
def maskBound : ArithRule where
  name := "Mask"
  op := .bitAnd
  left := .number
  right := .operand .safeInteger
  premises := [fact [(.right, -1)] 0]
  result := .safeInteger
  conclusion := [fact [(.result, 1), (.right, -1)] 0]

/-- **Shl**: `-2^31 ≤ 2^{d'}·x < 2^31` gives `y = 2^{d'}·x`. -/
def shl : ArithRule where
  name := "Shl"
  op := .shl
  left := .safeInteger
  right := .constant shiftCount
  premises := [⟨[(.left, { byPower := -1 })], { lit := 2 ^ 31 }⟩, ⟨[(.left, { byPower := 1 })], { lit := 2 ^ 31 - 1 }⟩]
  result := .safeInteger
  conclusion := [⟨[(.result, { lit := 1 }), (.left, { byPower := -1 })], {}⟩,
    ⟨[(.result, { lit := -1 }), (.left, { byPower := 1 })], {}⟩]

/-- **Or**: `0 ≤ x < 2^31` and `0 ≤ x' < 2^31` give `x ≤ y`, `x' ≤ y` and
`y ≤ x + x'`. -/
def bitOr : ArithRule where
  name := "Or"
  op := .bitOr
  left := .safeInteger
  right := .operand .safeInteger
  premises := [fact [(.left, -1)] 0, fact [(.left, 1)] (2 ^ 31 - 1), fact [(.right, -1)] 0, fact [(.right, 1)] (2 ^ 31 - 1)]
  result := .safeInteger
  conclusion := [fact [(.left, 1), (.result, -1)] 0, fact [(.right, 1), (.result, -1)] 0,
    fact [(.result, 1), (.left, -1), (.right, -1)] 0]

/-- The rules, in the paper's order. -/
def rules : List ArithRule := [add, sub, scale, shr, maskRange, maskBound, shl, bitOr]

/-! ## Numbers through `ToInt32` -/

/-- **The shift count of a safe integer** `d` is `d mod 32`. -/
theorem shiftCount_toUint32 {y : UInt64} {d : Int} (hy : SafeInt y d) :
    ((toUint32 y % 32 : Nat) : Int) = d % 32 := by
  have h := toInt32_safe hy
  unfold toUint32
  simp only [h]
  unfold wrapInt32
  dsimp only
  split <;> split <;> omega

/-- The two's-complement conjunction with a natural is at most that natural. -/
theorem intAnd_le_right (j : Int) (m : Nat) : 0 ≤ intAnd j m ∧ intAnd j m ≤ m := by
  cases j with
  | ofNat a =>
    have := Nat.and_le_right (n := a) (m := m)
    simp only [intAnd, Int.ofNat_eq_natCast]; omega
  | negSucc a =>
    have : m ^^^ (a &&& m) ≤ m := Nat.le_of_testBit fun i h => by
      simp only [Nat.testBit_xor, Nat.testBit_and] at h
      cases hm : m.testBit i <;> simp_all
    simp only [intAnd, Int.ofNat_eq_natCast]; omega

/-- Clearing some of a natural's bits leaves at most it. -/
theorem xor_and_le (a b : Nat) : b ^^^ (a &&& b) ≤ b := Nat.le_of_testBit fun i h => by
  simp only [Nat.testBit_xor, Nat.testBit_and] at h
  cases hm : b.testBit i <;> simp_all

/-- The two's-complement conjunction of a natural with any integer is at
most that natural. -/
theorem intAnd_le_left (n : Nat) (j : Int) : intAnd n j ≤ n := by
  cases j with
  | ofNat b =>
    have := Nat.and_le_left (n := n) (m := b)
    simp only [intAnd, Int.ofNat_eq_natCast]; omega
  | negSucc b =>
    have := xor_and_le b n
    rw [Nat.and_comm] at this
    simp only [Int.ofNat_eq_natCast, intAnd]; omega

/-- The two's-complement conjunction of two signed 32-bit integers is one. -/
theorem intAnd_int32 {i j : Int} (hi : -2 ^ 31 ≤ i ∧ i < 2 ^ 31) (hj : -2 ^ 31 ≤ j ∧ j < 2 ^ 31) :
    -2 ^ 31 ≤ intAnd i j ∧ intAnd i j < 2 ^ 31 := by
  cases i with
  | ofNat a =>
    have := intAnd_le_left a j
    cases j with
    | ofNat b =>
      have := Nat.and_le_left (n := a) (m := b); simp only [intAnd, Int.ofNat_eq_natCast] at *; omega
    | negSucc b =>
      have := xor_and_le b a; rw [Nat.and_comm] at this
      simp only [intAnd, Int.ofNat_eq_natCast] at *; omega
  | negSucc a =>
    cases j with
    | ofNat b => have := xor_and_le a b; simp only [intAnd, Int.ofNat_eq_natCast] at *; omega
    | negSucc b =>
      have := Nat.or_lt_two_pow (n := 31) (x := a) (y := b) (by omega) (by omega)
      simp only [intAnd]; omega

theorem intAnd_comm (a b : Int) : intAnd a b = intAnd b a := by
  cases a <;> cases b <;> simp [intAnd, Nat.and_comm, Nat.or_comm]

/-- The disjunction of two naturals is at most their sum. -/
theorem or_le_add (a b : Nat) : a ||| b ≤ a + b := by
  induction a using Nat.div2Induction generalizing b with
  | _ a ih =>
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · have h1 := ih ha (b / 2)
      have hd : (a ||| b) / 2 = a / 2 ||| b / 2 := by
        have := Nat.shiftRight_or_distrib (a := a) (b := b) (i := 1)
        simpa only [Nat.shiftRight_eq_div_pow, Nat.pow_one] using this
      have hm : (a ||| b) % 2 ≤ a % 2 + b % 2 := by
        have := (Nat.or_mod_two_eq_one (a := a) (b := b))
        omega
      omega

/-! ## Each rule's soundness -/

/-- The integer result of a 32-bit result, a safe integer. -/
theorem safe_int32 {i : Int} (hlo : -2 ^ 31 ≤ i) (hhi : i < 2 ^ 31) : SafeInt (int32Bits i) i :=
  safeInt_int32Bits (by omega)

theorem shr_sound : shr.Sound := by
  intro a b v ha hb hp
  simp only [shr, shiftCount, Domain.Admits, Right.Admits, Right.bound, Normalisation.apply] at ha hb hp ⊢
  have h1 := hp _ (List.mem_cons_self ..)
  have h2 := hp _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  simp only [fact, RuleFact.Holds, sumTerms, Coef.eval, List.map_cons, List.map_nil] at h1 h2
  have hx := toInt32_small ha (by omega) (by omega)
  have hk := shiftCount_toUint32 hb.1
  generalize hK : (v .right % 32) = K at *
  have hK0 : 0 ≤ K := by omega
  have hn : toUint32 b % 32 = K.toNat := by omega
  have hP : (0 : Int) < 2 ^ K.toNat := Int.pow_pos (by decide)
  generalize hQ : (2 : Int) ^ K.toNat = Q at *
  have hlo := Int.emod_nonneg (v .left) (Int.ne_of_gt hP)
  have hhi := Int.emod_lt_of_pos (v .left) hP
  have he := Int.emod_add_mul_ediv (v .left) Q
  have hq0 : -2 ^ 31 ≤ v .left / Q := by
    rw [Int.le_ediv_iff_mul_le hP]
    have : (-2 ^ 31 : Int) * Q ≤ -2 ^ 31 * 1 := Int.mul_le_mul_of_nonpos_left (by decide) (show (1 : Int) ≤ Q from hP)
    omega
  have hq1 : v .left / Q < 2 ^ 31 := by
    rcases Int.lt_or_le (v .left) 0 with hn' | hn'
    · have : v .left / Q < 0 := Int.ediv_neg_of_neg_of_pos hn' hP
      omega
    · have := Int.ediv_le_self Q hn'; omega
  refine ⟨v .left / Q, ?_, ?_⟩
  · simp only [arithBits, hx, hn, hQ]
    exact safe_int32 hq0 hq1
  · intro F hF
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl <;>
      simp only [RuleFact.Holds, sumTerms, Coef.eval, resultAt, Int.zero_mul, Int.zero_add, Int.add_zero, Int.one_mul, Int.neg_mul, hQ] <;> omega

theorem maskRange_sound : maskRange.Sound := by
  intro a b v _ hb hp
  simp only [maskRange, Domain.Admits, Right.Admits, Right.bound] at hb hp ⊢
  have h := fun F hF => hp F hF
  simp only [fact, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, RuleFact.Holds, sumTerms, Coef.eval] at h
  obtain ⟨hm0, hm1⟩ := h
  have hm := toInt32_small hb (by omega) (by omega)
  obtain ⟨hr0, hr1⟩ := intAnd_le_right (toInt32 a) (v .right).toNat
  rw [Int.toNat_of_nonneg (by omega)] at hr0 hr1
  refine ⟨intAnd (toInt32 a) (v .right), ?_, ?_⟩
  · simp only [arithBits, hm]
    exact safe_int32 (by omega) (by omega)
  · intro F hF
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl <;>
      simp only [fact, RuleFact.Holds, sumTerms, Coef.eval, resultAt, List.map_cons, List.map_nil] <;> omega

theorem maskBound_sound : maskBound.Sound := by
  intro a b v _ hb hp
  simp only [maskBound, Domain.Admits, Right.Admits, Right.bound] at hb hp ⊢
  have h0 := hp _ (List.mem_cons_self ..)
  simp only [fact, RuleFact.Holds, sumTerms, Coef.eval, List.map_cons, List.map_nil] at h0
  have hr := intAnd_int32 (toInt32_range a) (toInt32_range b)
  have hle : intAnd (toInt32 a) (toInt32 b) ≤ v .right := by
    rw [intAnd_comm]
    rcases Int.lt_or_le (v .right) (2 ^ 31) with hs | hs
    · rw [toInt32_small hb (by omega) hs]
      obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ v .right by omega)
      rw [hn]
      exact intAnd_le_left n _
    · have := intAnd_int32 (toInt32_range b) (toInt32_range a); omega
  refine ⟨intAnd (toInt32 a) (toInt32 b), ?_, ?_⟩
  · simp only [arithBits]
    exact safe_int32 hr.1 hr.2
  · intro F hF
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
    subst hF
    simp only [fact, RuleFact.Holds, sumTerms, Coef.eval, resultAt, List.map_cons, List.map_nil]; omega

theorem shl_sound : shl.Sound := by
  intro a b v ha hb hp
  simp only [shl, shiftCount, Domain.Admits, Right.Admits, Right.bound, Normalisation.apply] at ha hb hp ⊢
  have h1 := hp _ (List.mem_cons_self ..)
  have h2 := hp _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  simp only [RuleFact.Holds, sumTerms, Coef.eval, Int.zero_mul, Int.zero_add, Int.add_zero, Int.one_mul, Int.neg_mul] at h1 h2
  have hk := shiftCount_toUint32 hb.1
  generalize hK : (v .right % 32) = K at *
  have hn : toUint32 b % 32 = K.toNat := by omega
  have hP : (1 : Int) ≤ 2 ^ K.toNat := Int.pow_pos (by decide)
  generalize hQ : (2 : Int) ^ K.toNat = Q at *
  have hx : -2 ^ 31 ≤ v .left ∧ v .left < 2 ^ 31 := by
    rcases Int.lt_or_le (v .left) 0 with hs | hs
    · have : Q * v .left ≤ 1 * v .left := Int.mul_le_mul_of_nonpos_right hP (by omega)
      constructor <;> omega
    · have : 1 * v .left ≤ Q * v .left := Int.mul_le_mul_of_nonneg_right hP hs
      constructor <;> omega
  have hx32 := toInt32_small ha hx.1 hx.2
  have hw : wrapInt32 (v .left * Q) = v .left * Q := by
    unfold wrapInt32; dsimp only; rw [Int.mul_comm]; split <;> omega
  refine ⟨Q * v .left, ?_, ?_⟩
  · simp only [arithBits, hx32, hn, hQ, hw]
    rw [Int.mul_comm]
    exact safe_int32 (by omega) (by omega)
  · intro F hF
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl <;>
      simp only [RuleFact.Holds, sumTerms, Coef.eval, resultAt, Int.zero_mul, Int.zero_add, Int.add_zero, Int.one_mul, Int.neg_mul, hQ] <;> omega

theorem bitOr_sound : bitOr.Sound := by
  intro a b v ha hb hp
  simp only [bitOr, Domain.Admits, Right.Admits, Right.bound] at ha hb hp ⊢
  have h := fun F hF => hp F hF
  simp only [fact, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, RuleFact.Holds, sumTerms, Coef.eval] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hx := toInt32_small ha (by omega) (by omega)
  have hy := toInt32_small hb (by omega) (by omega)
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ v .left by omega)
  obtain ⟨n', hn'⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ v .right by omega)
  have hl := Nat.left_le_or (n := n) (m := n')
  have hr := Nat.right_le_or (n := n) (m := n')
  have hs := or_le_add n n'
  have hlt : n ||| n' < 2 ^ 31 := Nat.or_lt_two_pow (by omega) (by omega)
  refine ⟨((n ||| n' : Nat) : Int), ?_, ?_⟩
  · simp only [arithBits, hx, hy, hn, hn', intOr, Int.ofNat_eq_natCast]
    exact safe_int32 (by omega) (by omega)
  · intro F hF
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl | rfl <;>
      simp only [fact, RuleFact.Holds, sumTerms, Coef.eval, resultAt, List.map_cons, List.map_nil] <;> omega

/-- **Every rule is sound.** -/
theorem add_sound : add.Sound := by
  intro a b v ha hb hp
  simp only [add, Domain.Admits, Right.Admits, Right.bound] at ha hb hp ⊢
  have h := fun F hF => hp F hF
  simp only [fact, maxSafeInt, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, RuleFact.Holds, sumTerms, Coef.eval] at h
  refine ⟨v .left + v .right, add_safe ha hb (by omega), fun F hF => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl <;>
    simp only [fact, RuleFact.Holds, sumTerms, Coef.eval, resultAt, List.map_cons, List.map_nil] <;> omega

theorem sub_sound : sub.Sound := by
  intro a b v ha hb hp
  simp only [sub, Domain.Admits, Right.Admits, Right.bound] at ha hb hp ⊢
  have h := fun F hF => hp F hF
  simp only [fact, maxSafeInt, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, RuleFact.Holds, sumTerms, Coef.eval] at h
  refine ⟨v .left - v .right, sub_safe ha hb (by omega), fun F hF => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl <;>
    simp only [fact, RuleFact.Holds, sumTerms, Coef.eval, resultAt, List.map_cons, List.map_nil] <;> omega

theorem scale_sound : scale.Sound := by
  intro a b v ha hb hp
  simp only [scale, factor, Domain.Admits, Right.Admits, Right.bound, Normalisation.apply] at ha hb hp ⊢
  have h := fun F hF => hp F hF
  simp only [maxSafeInt, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, RuleFact.Holds, sumTerms, Coef.eval, Int.zero_mul, Int.zero_add, Int.add_zero,
    Int.one_mul, Int.neg_mul] at h
  refine ⟨v .left * v .right, mul_safe ha hb.1 (by rw [Int.mul_comm]; omega), fun F hF => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl <;>
    simp only [RuleFact.Holds, sumTerms, Coef.eval, resultAt, Int.zero_mul, Int.zero_add, Int.add_zero,
      Int.one_mul, Int.neg_mul] <;> rw [Int.mul_comm] <;> omega

theorem rules_sound : ∀ r ∈ rules, r.Sound := by
  intro r hr
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact add_sound
  · exact sub_sound
  · exact scale_sound
  · exact shr_sound
  · exact maskRange_sound
  · exact maskBound_sound
  · exact shl_sound
  · exact bitOr_sound

/-! ## Instantiation

A rule is applied at a step by substituting a linear form plus a constant,
over the variables `V` of the side that applies it, for each of its
variables: the pass's producer substitutes slots, the derivation a
two-state's terms. -/

/-- A rule's variables substituted: each a linear form over `V` plus a
constant, or nothing. -/
abbrev Instance (V : Type) := RuleVar → Option (Linear.Form V × Int)

/-- An operand read by its domain: a safe integer by its form, which it
needs; any number by nothing. -/
def Domain.bind {V : Type} : Domain → Option (Linear.Form V × Int) → Option (Option (Linear.Form V × Int))
  | .safeInteger, f => f.map some
  | .number, _ => some none

/-- A right operand read by its kind: an operand by its domain, the bound
value `0`; a constant by its form, a constant `d` meeting the side
condition, bound at its normalisation. -/
def Right.bind {V : Type} : Right → Option (Linear.Form V × Int) → Option (Option (Linear.Form V × Int) × Int)
  | .operand d, f => (d.bind f).map (·, 0)
  | .constant c, some ([], d) => if c.admits d then some (some ([], d), c.normalisation.apply d) else none
  | .constant _, _ => none

/-- **A rule's operands bound**: the instance of its operands (the result
has none) and the bound constant, from the forms the operands have. -/
def ArithRule.bind {V : Type} (r : ArithRule) (lf rf : Option (Linear.Form V × Int)) :
    Option (Instance V × Int) :=
  match r.left.bind lf, r.right.bind rf with
  | some l, some (rt, K) => some (fun | .left => l | .right => rt | .result => none, K)
  | _, _ => none

/-- An instance with the result's form set. -/
def Instance.withResult {V : Type} (σ : Instance V) (y : Option (Linear.Form V × Int)) : Instance V
  | .result => y
  | x => σ x

/-- An instance over `W`, each variable of each form renamed by `g`. -/
def Instance.rename {V W : Type} (g : V → W) (σ : Instance V) : Instance W :=
  fun x => (σ x).map fun (F, c) => (F.map fun (y, a) => (g y, a), c)

/-- The terms of a fact substituted: their form and constant. -/
@[nospecialize] def instTerms {V : Type} (σ : Instance V) (k : Int) :
    List (RuleVar × Coef) → Option (Linear.Form V × Int)
  | [] => some ([], 0)
  | (x, a) :: t =>
    -- A term whose coefficient is `0` at `k` names no variable (`0·x` is
    -- the constant `0`), so a fact outlives the variable's slots.
    if a.eval k = 0 then instTerms σ k t
    else match σ x, instTerms σ k t with
      | some (F, c), some (G, d) => some (F.scale (a.eval k) ++ G, a.eval k * c + d)
      | _, _ => none

/-- **A fact substituted**: `Σ aᵢ·(Fᵢ + cᵢ) ≤ b` as `Σ aᵢ·Fᵢ ≤ b − Σ aᵢ·cᵢ`;
none where a variable it names has no form. -/
@[nospecialize] def RuleFact.instantiate {V : Type} (σ : Instance V) (k : Int) (F : RuleFact) :
    Option (Linear.Fact V) :=
  (instTerms σ k F.terms).map fun (G, d) => .le G (F.bound.eval k - d)

/-- Facts substituted, all or none. -/
@[nospecialize] def instantiateAll {V : Type} (σ : Instance V) (k : Int) :
    List RuleFact → Option (List (Linear.Fact V))
  | [] => some []
  | F :: Fs => match F.instantiate σ k, instantiateAll σ k Fs with
    | some G, some Gs => some (G :: Gs)
    | _, _ => none

/-- The values an instance denotes at a valuation of `V`: each variable with
a form is the form's value plus its constant. -/
def Instance.Denotes {V : Type} (σ : Instance V) (val : V → Int) (v : RuleVar → Int) : Prop :=
  ∀ x F c, σ x = some (F, c) → Linear.Form.eval val F + c = v x

theorem instTerms_eval {V : Type} {σ : Instance V} {val : V → Int} {v : RuleVar → Int} (hσ : σ.Denotes val v)
    (k : Int) : ∀ {ts : List (RuleVar × Coef)} {G : Linear.Form V} {d : Int}, instTerms σ k ts = some (G, d) →
      Linear.Form.eval val G + d = sumTerms k v ts
  | [], G, d, h => by simp only [instTerms, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | (x, a) :: t, G, d, h => by
    simp only [instTerms] at h
    split at h
    · rename_i h0
      have := instTerms_eval hσ k h
      simp only [sumTerms, h0, Int.zero_mul, Int.zero_add]; exact this
    split at h
    · rename_i F c G' d' hx ht
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have e1 := hσ x F c hx
      have e2 := instTerms_eval hσ k ht
      simp only [sumTerms, Linear.Form.eval_append, Linear.Form.eval_scale]
      rw [← e1, ← e2, Int.mul_add]; omega
    · cases h

theorem instTerms_vars {V : Type} {σ : Instance V} {k : Int} :
    ∀ {ts : List (RuleVar × Coef)} {G : Linear.Form V} {d : Int}, instTerms σ k ts = some (G, d) →
      ∀ t ∈ G.map (·.1), ∃ x F c, σ x = some (F, c) ∧ t ∈ F.map (·.1)
  | [], G, d, h => by simp only [instTerms, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | (x, a) :: t, G, d, h => by
    simp only [instTerms] at h
    split at h
    · exact instTerms_vars h
    split at h
    · rename_i F c G' d' hx ht
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      intro u hu
      simp only [List.map_append, List.mem_append, Linear.Form.scale, List.map_map, Function.comp_def] at hu
      rcases hu with hu | hu
      · exact ⟨x, F, c, hx, by simpa using hu⟩
      · exact instTerms_vars ht u hu
    · cases h

/-- **The interpretation lemma**: a substituted fact holds at a valuation of
`V` exactly where the rule's fact holds at the values the instance denotes. -/
theorem RuleFact.instantiate_holds {V : Type} {σ : Instance V} {val : V → Int} {v : RuleVar → Int}
    (hσ : σ.Denotes val v) {k : Int} {F : RuleFact} {G : Linear.Fact V} (h : F.instantiate σ k = some G) :
    G.Holds val ↔ F.Holds k v := by
  simp only [RuleFact.instantiate, Option.map_eq_some_iff] at h
  obtain ⟨⟨G', d⟩, hG, rfl⟩ := h
  have := instTerms_eval hσ k hG
  simp only [Linear.Fact.Holds, RuleFact.Holds]
  omega

/-- A substituted fact names only variables of the instance's forms. -/
theorem RuleFact.instantiate_vars {V : Type} {σ : Instance V} {k : Int} {F : RuleFact} {G : Linear.Fact V}
    (h : F.instantiate σ k = some G) : ∀ t ∈ G.vars, ∃ x F c, σ x = some (F, c) ∧ t ∈ F.map (·.1) := by
  simp only [RuleFact.instantiate, Option.map_eq_some_iff] at h
  obtain ⟨⟨G', d⟩, hG, rfl⟩ := h
  exact instTerms_vars hG

theorem instTerms_rename {V W : Type} (g : V → W) (σ : Instance V) (k : Int) :
    ∀ ts : List (RuleVar × Coef), instTerms (σ.rename g) k ts =
      (instTerms σ k ts).map fun (G, d) => (G.map fun (y, a) => (g y, a), d)
  | [] => rfl
  | (x, a) :: t => by
    simp only [instTerms, Instance.rename, instTerms_rename g σ k t]
    split
    · rfl
    · cases σ x <;> cases instTerms σ k t <;>
        simp [Linear.Form.scale, Function.comp_def]

/-- A linear fact with each variable renamed by `g`. -/
def renameFact {V W : Type} (g : V → W) : Linear.Fact V → Linear.Fact W
  | .le G d => .le (G.map fun (y, a) => (g y, a)) d
  | .ne G d => .ne (G.map fun (y, a) => (g y, a)) d

/-- **Renaming commutes with substitution.** -/
theorem RuleFact.instantiate_rename {V W : Type} (g : V → W) (σ : Instance V) (k : Int) (F : RuleFact) :
    F.instantiate (σ.rename g) k = (F.instantiate σ k).map (renameFact g) := by
  simp only [RuleFact.instantiate, instTerms_rename, Option.map_map]
  cases instTerms σ k F.terms <;> rfl

theorem instantiateAll_rename {V W : Type} (g : V → W) (σ : Instance V) (k : Int) :
    ∀ Fs : List RuleFact, instantiateAll (σ.rename g) k Fs = (instantiateAll σ k Fs).map (·.map (renameFact g))
  | [] => rfl
  | F :: Fs => by
    simp only [instantiateAll, RuleFact.instantiate_rename, instantiateAll_rename g σ k Fs]
    cases F.instantiate σ k <;> cases instantiateAll σ k Fs <;> rfl

/-- A form plus a constant with each variable renamed by `g`. -/
def renamePair {V W : Type} (g : V → W) (f : Linear.Form V × Int) : Linear.Form W × Int :=
  (f.1.map fun (y, a) => (g y, a), f.2)

theorem Instance.rename_withResult {V W : Type} (g : V → W) (σ : Instance V) (y : Option (Linear.Form V × Int)) :
    (σ.withResult y).rename g = (σ.rename g).withResult (y.map (renamePair g)) := by
  funext x; cases x <;> rfl

theorem Instance.rename_rename {U V W : Type} (f : U → V) (g : V → W) (σ : Instance U) :
    (σ.rename f).rename g = σ.rename (g ∘ f) := by
  funext x
  simp only [Instance.rename, Option.map_map]
  cases σ x <;> simp [Function.comp_def]

/-- **Binding commutes with renaming**: the operands' forms renamed bind the
renamed instance, at the same constant. -/
theorem ArithRule.bind_rename {V W : Type} (g : V → W) (r : ArithRule) (lf rf : Option (Linear.Form V × Int)) :
    r.bind (lf.map (renamePair g)) (rf.map (renamePair g)) = (r.bind lf rf).map fun (σ, K) => (σ.rename g, K) := by
  have hl : r.left.bind (lf.map (renamePair g)) = (r.left.bind lf).map (·.map (renamePair g)) := by
    cases r.left <;> cases lf <;> rfl
  have hr : r.right.bind (rf.map (renamePair g)) = (r.right.bind rf).map fun (rt, K) => (rt.map (renamePair g), K) := by
    cases r.right with
    | operand d => cases d <;> cases rf <;> rfl
    | constant c =>
      match rf with
      | none => rfl
      | some ([], d) => simp only [Right.bind, Option.map_some, renamePair, List.map_nil]; split <;> rfl
      | some ((_ :: _), _) => rfl
  simp only [ArithRule.bind, hl, hr]
  cases r.left.bind lf <;> cases r.right.bind rf <;> try rfl
  rename_i rtK
  obtain ⟨rt, K⟩ := rtK
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
  funext x; cases x <;> rfl

/-- Each fact of a list substituted all at once has its substitution. -/
theorem instantiateAll_mem {V : Type} {σ : Instance V} {k : Int} :
    ∀ {Fs : List RuleFact} {Gs : List (Linear.Fact V)}, instantiateAll σ k Fs = some Gs →
      ∀ F ∈ Fs, ∃ G ∈ Gs, F.instantiate σ k = some G
  | [], _, _, F, hF => by cases hF
  | F₀ :: Fs, Gs, h, F, hF => by
    simp only [instantiateAll] at h
    split at h
    · rename_i G Gs' hG hGs
      cases h
      rcases List.mem_cons.mp hF with rfl | hF
      · exact ⟨G, List.mem_cons_self .., hG⟩
      · obtain ⟨G', hG', he⟩ := instantiateAll_mem hGs F hF
        exact ⟨G', List.mem_cons_of_mem _ hG', he⟩
    · cases h

/-- Each fact of a substituted list is a fact's substitution. -/
theorem instantiateAll_mem' {V : Type} {σ : Instance V} {k : Int} :
    ∀ {Fs : List RuleFact} {Gs : List (Linear.Fact V)}, instantiateAll σ k Fs = some Gs →
      ∀ G ∈ Gs, ∃ F ∈ Fs, F.instantiate σ k = some G
  | [], Gs, h, G, hG => by simp only [instantiateAll, Option.some.injEq] at h; subst h; cases hG
  | F₀ :: Fs, Gs, h, G, hG => by
    simp only [instantiateAll] at h
    split at h
    · rename_i G₀ Gs' hG₀ hGs
      cases h
      rcases List.mem_cons.mp hG with rfl | hG
      · exact ⟨F₀, List.mem_cons_self .., hG₀⟩
      · obtain ⟨F', hF', he⟩ := instantiateAll_mem' hGs G hG
        exact ⟨F', List.mem_cons_of_mem _ hF', he⟩
    · cases h

/-- **A rule's operation computes its result on numbers**: the operator is
no comparison, and either it takes numbers alone, so that a step on it has
number operands, or each operand is a safe integer. -/
def ArithRule.numeric (r : ArithRule) : Bool :=
  !r.op.relational && decide (r.op ≠ .eq) && decide (r.op ≠ .looseEq) &&
    (r.op.numberOnly || (decide (r.left = .safeInteger) && decide (r.right ≠ .operand .number)))

theorem rules_numeric : ∀ r ∈ rules, r.numeric = true := by decide

/-- A computing operator on two numbers gives `arithBits`. -/
theorem binop_num {op : Arith} (hrel : op.relational = false) (heq : op ≠ .eq) (hloose : op ≠ .looseEq)
    {x y : UInt64} {u : Tm} (hu : binop op (.num x) (.num y) = some u) : u = .num (arithBits op x y) := by
  unfold binop at hu
  rw [if_neg heq, if_neg hloose, hrel] at hu
  simp only [Bool.false_eq_true, if_false, Option.some.injEq] at hu
  exact hu.symm

/-- A step of an operator on numbers alone has number operands. -/
theorem binop_numberOnly {op : Arith} (h : op.numberOnly = true) {a b u : Tm} (hu : binop op a b = some u) :
    ∃ x y, a = .num x ∧ b = .num y := by
  have hrel : op.relational = false := by cases op <;> simp_all [Arith.numberOnly, Arith.relational]
  have heq : op ≠ .eq := by rintro rfl; simp [Arith.numberOnly] at h
  have hloose : op ≠ .looseEq := by rintro rfl; simp [Arith.numberOnly] at h
  have hadd : (op == .add) = false := by cases op <;> first | rfl | simp [Arith.numberOnly] at h
  have hbig : ∀ i j, bigintArith op i j = none := by intro i j; cases op <;> simp_all [Arith.numberOnly, bigintArith]
  unfold binop at hu
  rw [if_neg heq, if_neg hloose, hrel] at hu
  simp only [Bool.false_eq_true, if_false] at hu
  split at hu
  · exact ⟨_, _, rfl, rfl⟩
  · simp [hbig] at hu
  all_goals simp [hadd] at hu

/-! ## Operands exchanged -/

theorem sign_mul_comm (a b : Sign) : a * b = b * a := by cases a <;> cases b <;> rfl

/-- The model's sum of two doubles is symmetric: its NaN is one value. -/
theorem unpacked_add_comm (spec : Format) (x y : UnpackedFloat) :
    UnpackedFloat.add spec x y = UnpackedFloat.add spec y x := by
  cases x <;> cases y <;> simp only [UnpackedFloat.add]
  all_goals first
    | rfl
    | (rename_i a b; cases a <;> cases b <;> rfl)
    | (rw [Int.min_comm]; congr 1; omega)

theorem unpacked_mul_comm (spec : Format) (x y : UnpackedFloat) :
    UnpackedFloat.mul spec x y = UnpackedFloat.mul spec y x := by
  cases x <;> cases y <;> simp only [UnpackedFloat.mul, sign_mul_comm, Nat.mul_comm, Int.add_comm]

theorem intOr_comm (a b : Int) : intOr a b = intOr b a := by
  cases a <;> cases b <;> simp [intOr, Nat.and_comm, Nat.or_comm]

theorem intXor_comm (a b : Int) : intXor a b = intXor b a := by
  cases a <;> cases b <;> simp [intXor, Nat.xor_comm]

/-- **`arithBits` is symmetric** for `+`, `*`, `&`, `|` and `^`: the model's
sum and product, and the two's-complement operations. -/
theorem arithBits_comm {op : Arith} (h : op = .add ∨ op = .mul ∨ op = .bitAnd ∨ op = .bitOr ∨ op = .xor)
    (x y : UInt64) : arithBits op x y = arithBits op y x := by
  rcases h with rfl | rfl | rfl | rfl | rfl
  · rw [arithBits_add, arithBits_add, unpacked_add_comm]
  · rw [arithBits_mul, arithBits_mul, unpacked_mul_comm]
  · simp only [arithBits, intAnd_comm]
  · simp only [arithBits, intOr_comm]
  · simp only [arithBits, intXor_comm]

/-- **The operators whose step is the same with its operands exchanged**,
on every pair of values (`binop_comm`): `&`, `|`, `^` and `*`. `+` is
not one: on two strings it concatenates, and on numbers alone it is
(`arithBits_comm`). -/
def _root_.Verification.Arith.commutes : Arith → Bool
  | .bitAnd | .bitOr | .xor | .mul => true
  | _ => false

theorem binop_comm_some {op : Arith} (h : op.commutes = true) {a b u : Tm} (hu : binop op a b = some u) :
    binop op b a = some u := by
  have hrel : op.relational = false := by cases op <;> simp_all [Arith.commutes, Arith.relational]
  have heq : op ≠ .eq := by rintro rfl; simp [Arith.commutes] at h
  have hloose : op ≠ .looseEq := by rintro rfl; simp [Arith.commutes] at h
  have hadd : (op == .add) = false := by cases op <;> first | rfl | simp [Arith.commutes] at h
  have hops : op = .add ∨ op = .mul ∨ op = .bitAnd ∨ op = .bitOr ∨ op = .xor := by
    cases op <;> simp_all [Arith.commutes]
  have hbig : ∀ i j, bigintArith op i j = bigintArith op j i := by
    intro i j; cases op <;> simp_all [Arith.commutes, bigintArith, Int.mul_comm, intXor_comm]
  unfold binop at hu ⊢
  rw [if_neg heq, if_neg hloose, hrel] at hu ⊢
  simp only [Bool.false_eq_true, if_false] at hu ⊢
  split at hu
  · rw [← hu, arithBits_comm hops]
  · rw [hbig]; exact hu
  all_goals simp [hadd] at hu

/-- **A commuting operator's step is the same with its operands exchanged.** -/
theorem binop_comm {op : Arith} (h : op.commutes = true) (a b : Tm) : binop op a b = binop op b a := by
  cases hab : binop op a b with
  | some u => exact (binop_comm_some h hab).symm
  | none =>
    cases hba : binop op b a with
    | none => rfl
    | some u => rw [binop_comm_some h hba] at hab; cases hab

/-- **A step of a rule's operation**: its result is `arithBits` of its
number operands, which an operand of a safe integer is. -/
theorem ArithRule.operation {r : ArithRule} (hn : r.numeric = true) {a b u : Tm}
    (hu : binop r.op a b = some u) (ha : r.left = .safeInteger → ∃ x, a = .num x)
    (hb : r.right ≠ .operand .number → ∃ y, b = .num y) :
    ∃ x y, a = .num x ∧ b = .num y ∧ u = .num (arithBits r.op x y) := by
  simp only [ArithRule.numeric, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, Bool.or_eq_true] at hn
  obtain ⟨⟨⟨hrel, heq⟩, hloose⟩, hnum⟩ := hn
  have hnum' : (∃ x, a = .num x) ∧ (∃ y, b = .num y) := by
    rcases hnum with hnum | ⟨hl, hr⟩
    · obtain ⟨x, y, rfl, rfl⟩ := binop_numberOnly hnum hu
      exact ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
    · exact ⟨ha hl, hb hr⟩
  obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := hnum'
  exact ⟨x, y, rfl, rfl, binop_num hrel heq hloose hu⟩

/-- **A rule applied**: where a rule's operands are bound from forms
(`ArithRule.bind`) that denote, at a valuation of `V`, the safe integers of
the step's operands, and its substituted premises hold, a step of its
operation gives a number in the result's domain at a value `y`, and the
conclusion holds at the values the instance denotes, with the result at
`y`. -/
theorem ArithRule.apply {V : Type} {r : ArithRule} (hr : r ∈ rules) {lf rf : Option (Linear.Form V × Int)}
    {σ : Instance V} {K : Int} (h : r.bind lf rf = some (σ, K)) {val : V → Int} {a b u : Tm}
    (hl : r.left = .safeInteger → ∀ F c, lf = some (F, c) → ∃ x, a = .num x ∧ SafeInt x (Linear.Form.eval val F + c))
    (hrt : r.right ≠ .operand .number → ∀ F c, rf = some (F, c) → ∃ y, b = .num y ∧ SafeInt y (Linear.Form.eval val F + c))
    (hu : binop r.op a b = some u)
    (hp : ∀ F ∈ r.premises, ∃ G, F.instantiate σ K = some G ∧ G.Holds val) :
    ∃ v y bits, σ.Denotes val v ∧ u = .num bits ∧ r.result.Admits bits y ∧
      ∀ F ∈ r.conclusion, F.Holds K (resultAt v y) := by
  simp only [ArithRule.bind] at h
  split at h
  · rename_i l rt K' hlb hrb
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    -- The left operand's value and evidence.
    obtain ⟨vl, hdl, hal⟩ : ∃ vl : Int, (∀ F c, l = some (F, c) → Linear.Form.eval val F + c = vl) ∧
        (r.left = .safeInteger → ∃ x, a = .num x ∧ SafeInt x vl) := by
      cases hd : r.left <;> rw [hd] at hlb <;> simp only [Domain.bind, Option.map_eq_some_iff, Option.some.injEq] at hlb
      · obtain ⟨⟨F, c⟩, hf, rfl⟩ := hlb
        obtain ⟨x, hx, hs⟩ := hl hd F c hf
        exact ⟨_, (fun F' c' he => by cases he; rfl), fun _ => ⟨x, hx, hs⟩⟩
      · subst hlb
        exact ⟨0, (fun _ _ he => by cases he), fun he => by cases he⟩
    obtain ⟨vr, hdr, hK, har⟩ : ∃ vr : Int, (∀ F c, rt = some (F, c) → Linear.Form.eval val F + c = vr) ∧
        K' = r.right.bound vr ∧ (r.right ≠ .operand .number → ∃ y, b = .num y ∧ r.right.Admits y vr) := by
      cases hd : r.right with
      | operand d =>
        rw [hd] at hrb
        cases d <;> simp only [Right.bind, Domain.bind, Option.map_eq_some_iff, Option.map_map,
          Function.comp_def, Prod.mk.injEq] at hrb
        · obtain ⟨⟨F, c⟩, hf, rfl, rfl⟩ := hrb
          obtain ⟨y, hy, hs⟩ := hrt (by rw [hd]; simp) F c hf
          exact ⟨_, (fun F' c' he => by cases he; rfl), rfl, fun _ => ⟨y, hy, hs⟩⟩
        · simp at hrb
          obtain ⟨rfl, rfl⟩ := hrb
          exact ⟨0, (fun _ _ he => by cases he), rfl, fun hne => absurd rfl hne⟩
      | constant c =>
        rw [hd] at hrb
        match hrf : rf, hrb with
        | some ([], dv), hrb =>
          simp only [Right.bind] at hrb
          split at hrb
          · rename_i hadm
            simp only [Option.some.injEq, Prod.mk.injEq] at hrb
            obtain ⟨rfl, rfl⟩ := hrb
            obtain ⟨y, hy, hs⟩ := hrt (by rw [hd]; simp) [] dv rfl
            simp only [Linear.Form.eval, Int.zero_add] at hs
            exact ⟨dv, (fun F' c' he => by cases he; simp [Linear.Form.eval]), rfl,
              fun _ => ⟨y, hy, hs, hadm⟩⟩
          · cases hrb
        | some ((_ :: _), _), hrb => simp [Right.bind] at hrb
        | none, hrb => simp [Right.bind] at hrb
    subst hK
    let v : RuleVar → Int := fun | .left => vl | .right => vr | .result => 0
    have hσ : Instance.Denotes (fun | .left => l | .right => rt | .result => none) val v := by
      intro x F c hx
      cases x
      · exact hdl F c hx
      · exact hdr F c hx
      · cases hx
    obtain ⟨x, y, rfl, rfl, rfl⟩ := ArithRule.operation (rules_numeric r hr) hu
      (fun hd => (hal hd).imp fun _ h => h.1) (fun hd => (har hd).imp fun _ h => h.1)
    have hadl : r.left.Admits x (v .left) := by
      cases hd : r.left
      · obtain ⟨x', hx', hs⟩ := hal hd; cases hx'; exact hs
      · trivial
    have hadr : r.right.Admits y (v .right) := by
      by_cases hd : r.right = .operand .number
      · rw [hd]; trivial
      · obtain ⟨y', hy', hs⟩ := har hd; cases hy'; exact hs
    have hprem : ∀ F ∈ r.premises, F.Holds (r.right.bound (v .right)) v := by
      intro F hF
      obtain ⟨G, hG, hh⟩ := hp F hF
      exact (RuleFact.instantiate_holds hσ hG).mp hh
    obtain ⟨res, hres, hconc⟩ := rules_sound r hr x y v hadl hadr hprem
    exact ⟨v, res, _, hσ, rfl, hres, hconc⟩
  · cases h

/-- **The forms of a bound instance**: the left operand's where its domain
is the safe integers, the right one's where it is not any number, and no
form for the result. -/
theorem ArithRule.bind_forms {V : Type} {r : ArithRule} {lf rf : Option (Linear.Form V × Int)} {σ : Instance V}
    {K : Int} (h : r.bind lf rf = some (σ, K)) :
    (∀ f, σ .left = some f → r.left = .safeInteger ∧ lf = some f) ∧
      (∀ f, σ .right = some f → r.right ≠ .operand .number ∧ rf = some f) ∧ σ .result = none := by
  simp only [ArithRule.bind] at h
  split at h
  · rename_i l rt K' hlb hrb
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨fun f hx => ?_, fun f hx => ?_, rfl⟩
    · cases hd : r.left <;> rw [hd] at hlb <;> simp only [Domain.bind, Option.map_eq_some_iff, Option.some.injEq] at hlb
      · obtain ⟨f', hf, rfl⟩ := hlb; cases hx; exact ⟨rfl, hf⟩
      · subst hlb; cases hx
    · cases hd : r.right with
      | operand d =>
        rw [hd] at hrb
        cases d <;> simp [Right.bind, Domain.bind] at hrb
        · obtain ⟨a, b, hf, rfl, rfl⟩ := hrb; cases hx; exact ⟨by simp, hf⟩
        · obtain ⟨rfl, rfl⟩ := hrb; cases hx
      | constant c =>
        rw [hd] at hrb
        match hrf : rf, hrb with
        | some ([], dv), hrb =>
          simp only [Right.bind] at hrb
          split at hrb
          · simp only [Option.some.injEq, Prod.mk.injEq] at hrb
            obtain ⟨rfl, rfl⟩ := hrb; cases hx; exact ⟨by simp, rfl⟩
          · cases hrb
        | some ((_ :: _), _), hrb => simp [Right.bind] at hrb
        | none, hrb => simp [Right.bind] at hrb
  · cases h

/-- An instance denoting `v` with the result's form denoting `y` denotes
`v` with the result at `y`. -/
theorem Instance.denotes_withResult {V : Type} {σ : Instance V} {val : V → Int} {v : RuleVar → Int}
    (hσ : ∀ x, x ≠ .result → ∀ F c, σ x = some (F, c) → Linear.Form.eval val F + c = v x)
    {yf : Option (Linear.Form V × Int)} {y : Int} (hy : ∀ F c, yf = some (F, c) → Linear.Form.eval val F + c = y) :
    (σ.withResult yf).Denotes val (resultAt v y) := by
  intro x F c hx
  cases x
  · exact hσ .left (by decide) F c hx
  · exact hσ .right (by decide) F c hx
  · exact hy F c hx

/-- The variables a rule's facts may name: those whose values are safe
integers (a constant is one). A fact naming any other has no form to
substitute, and the rule would apply nowhere. -/
def ArithRule.integerVar (r : ArithRule) : RuleVar → Bool
  | .left => r.left == .safeInteger
  | .right => match r.right with
    | .operand d => d == .safeInteger
    | .constant _ => true
  | .result => r.result == .safeInteger

/-- Every fact of a rule names only variables of safe integers. -/
def ArithRule.factsInteger (r : ArithRule) : Bool :=
  (r.premises ++ r.conclusion).all fun F => F.terms.all fun (x, _) => r.integerVar x

#guard rules.all (·.factsInteger)

end Verification.ArithmeticRules
