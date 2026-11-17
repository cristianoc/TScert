import Verification.Paper.TolerantFrames.BitwiseArithmetic
import Verification.Paper.TolerantFrames.PureOperations
import Verification.Paper.TolerantFrames.Admission

/-! # Arithmetic command rules

These are actual command triples and effects. Integer operands/results are
interpreted using SafeInt, which admits both encodings of zero. The generic
pure rule supplies the exit world; no command or host summary is assumed.
-/
namespace Verification.Paper.TolerantFrames
open Verification SafeIntegers HeapObservations Footprints TolerantFrames

/-- A source result denotes a mathematical integer satisfying the predicate. -/
def IntegerResult (P : Int → Prop) (v : Val) : Prop :=
  ∃ bits r, v = .num bits ∧ SafeInt bits r ∧ P r

/-- Both operands denote safe integers. This is the paper's ambient numeric
operand assumption, separate from each displayed arithmetic precondition. -/
def IntegerOperands (a b : Argument) (i j : Int) : Assertion := fun ρ _ _ =>
  ∃ x z, a.eval ρ = .num x ∧ b.eval ρ = .num z ∧ SafeInt x i ∧ SafeInt z j

/-- Exact result binding, before expressing any current-state operand fact. -/
def BoundIntegerResult (y : Nat) (P : Int → Prop) : Postcondition :=
  fun ρ ρ' _ _ _ => ∃ v, ρ' = bindName ρ y v ∧ IntegerResult P v

private theorem numeric_binary_compute {host op a b ρ h x z}
    (hop : op ≠ .eq ∧ op ≠ .looseEq ∧ op.relational = false)
    (ha : a.eval ρ = .num x) (hb : b.eval ρ = .num z) :
    Steps 1 h ((Operation.binary op a b).code host ρ) h (.num (arithBits op x z)) := by
  apply Steps.next (k := 0) _ .refl
  simp only [Operation.code, ha, hb]
  exact .arithV (by simp [binop, hop.1, hop.2.1, hop.2.2])

/-- Every noncomparison numeric operator uses the existing one-step model.
The only result premise here is a mathematical fact about its computed bits. -/
theorem triple_numeric_binary {host P y op a b} {R : Int → Prop}
    (hop : op ≠ .eq ∧ op ≠ .looseEq ∧ op.relational = false)
    (facts : ∀ ρ m s, ValidContext ρ m s → P ρ m s →
      ∃ x z, a.eval ρ = .num x ∧ b.eval ρ = .num z ∧
        IntegerResult R (.num (arithBits op x z))) :
    Triple host P (.step (.bind y (.binary op a b))) (BoundIntegerResult y R)
      (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False) (fun _ _ _ _ _ _ => False) := by
  apply triple_pure_bind (R := fun _ _ => IntegerResult R)
  intro ρ m s context pre
  obtain ⟨x, z, ha, hb, hr⟩ := facts ρ m s context pre
  exact ⟨1, .num (arithBits op x z), numeric_binary_compute hop ha hb,
    rfl, RefsOk_of_nil rfl, hr⟩

theorem effects_numeric_binary {host P y op a b}
    (hop : op ≠ .eq ∧ op ≠ .looseEq ∧ op.relational = false)
    (numbers : ∀ ρ m s, ValidContext ρ m s → P ρ m s →
      ∃ x z, a.eval ρ = .num x ∧ b.eval ρ = .num z) :
    Effects host P (.step (.bind y (.binary op a b))) [] [] := by
  apply effects_pure
  intro ρ m s context pre
  obtain ⟨x, z, ha, hb⟩ := numbers ρ m s context pre
  exact ⟨1, .num (arithBits op x z), numeric_binary_compute hop ha hb, rfl⟩

/-- Mask at every safe first operand, including negative and large operands. -/
theorem mask_rule {host a b y i m} (hm : 0 ≤ m) (hmlt : m < 2 ^ 31) :
    Triple host (IntegerOperands a b i m) (.step (.bind y (.binary .bitAnd a b)))
      (BoundIntegerResult y (fun r => 0 ≤ r ∧ r ≤ m))
      (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False) (fun _ _ _ _ _ _ => False) := by
  apply triple_numeric_binary (by decide)
  intro ρ mark s _ pre
  obtain ⟨x, z, ha, hb, _, hz⟩ := pre
  obtain ⟨r, hr, h0, hm⟩ := mask_general (x := x) hz hm hmlt
  exact ⟨x, z, ha, hb, _, r, rfl, hr, h0, hm⟩

/-- The separate Mask consequence y≤x needs x≥0, without x<2^31. -/
theorem mask_nonneg_rule {host a b y i m} (hi : 0 ≤ i) (hm : 0 ≤ m) (hmlt : m < 2 ^ 31) :
    Triple host (IntegerOperands a b i m) (.step (.bind y (.binary .bitAnd a b)))
      (BoundIntegerResult y (fun r => 0 ≤ r ∧ r ≤ m ∧ r ≤ i))
      (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False) (fun _ _ _ _ _ _ => False) := by
  apply triple_numeric_binary (by decide)
  intro ρ mark s _ pre
  obtain ⟨x, z, ha, hb, hx, hz⟩ := pre
  obtain ⟨r, hr, h0, hm, hi⟩ := mask_nonneg hx hz hi hm hmlt
  exact ⟨x, z, ha, hb, _, r, rfl, hr, h0, hm, hi⟩

/-- The current paper's Or lower bounds and sum upper bound. -/
theorem or_rule {host a b y i j} (hi : 0 ≤ i) (hlt : i < 2 ^ 31)
    (hj : 0 ≤ j) (hjlt : j < 2 ^ 31) :
    Triple host (IntegerOperands a b i j) (.step (.bind y (.binary .bitOr a b)))
      (BoundIntegerResult y (fun r => i ≤ r ∧ j ≤ r ∧ r ≤ i + j))
      (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False) (fun _ _ _ _ _ _ => False) := by
  apply triple_numeric_binary (by decide)
  intro ρ mark s _ pre
  obtain ⟨x, z, ha, hb, hx, hz⟩ := pre
  obtain ⟨r, hr, hl, hr', hu⟩ := or_general hx hz hi hlt hj hjlt
  exact ⟨x, z, ha, hb, _, r, rfl, hr, hl, hr', hu⟩

/-- Every integer-operand bitwise instance above has the empty normal and
exceptional effects; the triples also prove absence of exceptional exits. -/
theorem bitwise_effects {host a b y i j op}
    (hop : op ≠ .eq ∧ op ≠ .looseEq ∧ op.relational = false) :
    Effects host (IntegerOperands a b i j) (.step (.bind y (.binary op a b))) [] [] := by
  apply effects_numeric_binary hop
  intro ρ m s _ pre
  obtain ⟨x, z, ha, hb, _, _⟩ := pre
  exact ⟨x, z, ha, hb⟩

/-- Actual current-state syntax for a named integer operand. -/
def integerVariable (x : Nat) : Expression := .scale 1 (.path .value ⟨x, []⟩)

theorem integerVariable_eval {ρ h x bits i} (he : ρ x = .num bits) (hi : SafeInt bits i) :
    (integerVariable x).eval ρ h = some i := by
  simp [integerVariable, Expression.eval, Term.eval, Verification.Parity.Path.read, HeapKnowledge.readPath,
    HeapKnowledge.kindValue, HeapKnowledge.intValue, he, safeIntOfBits_complete hi]

def maskConclusion (y : Nat) (m : Int) : Formula := .and
  (.atom (.le (.constant 0) (integerVariable y)))
  (.atom (.le (integerVariable y) (.constant m)))

def maskNonnegConclusion (x y : Nat) (m : Int) : Formula :=
  .and (maskConclusion y m) (.atom (.le (integerVariable y) (integerVariable x)))

def orConclusion (x z y : Nat) : Formula := .and
  (.atom (.le (integerVariable x) (integerVariable y))) (.and
    (.atom (.le (integerVariable z) (integerVariable y)))
    (.atom (.le (integerVariable y) (.add (integerVariable x) (integerVariable z)))))

/-- The stored result gives the integer reading; no reverse inference
identifies the two stored encodings of zero. -/
theorem BoundIntegerResult.reading {P y ρ ρ' mark s t}
    (post : BoundIntegerResult y P ρ ρ' mark s t) :
    ∃ r, (integerVariable y).eval ρ' t.h = some r ∧ P r := by
  obtain ⟨v, rfl, bits, r, rfl, hr, hp⟩ := post
  exact ⟨r, integerVariable_eval (by simp [bindName]) hr, hp⟩

theorem mask_rule_syntax {host a b y i m} (hm : 0 ≤ m) (hmlt : m < 2 ^ 31) :
    Triple host (IntegerOperands a b i m) (.step (.bind y (.binary .bitAnd a b)))
      (Now (maskConclusion y m).meaning)
      (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False) (fun _ _ _ _ _ _ => False) := by
  apply triple_consequence (mask_rule hm hmlt) (fun _ _ _ hp => hp)
  intro e ρ ρ' mark s t post
  cases e <;> try exact post
  obtain ⟨r, hr, h0, hm⟩ := BoundIntegerResult.reading (mark := mark) (s := s) post
  exact ⟨⟨0, r, rfl, hr, h0⟩, r, m, hr, rfl, hm⟩

/-- General postcondition consequence may use the entry precondition too.
It is retained explicitly rather than silently reinterpreting entry facts. -/
theorem triple_consequence_entry {host P c Q Qe J Ret Q' Qe' J' Ret'}
    (ht : Triple host P c Q Qe J Ret)
    (consequence : ∀ e ρ ρ' mark s t, P ρ mark s →
      ExitPost Q Qe J Ret e ρ ρ' mark s t → ExitPost Q' Qe' J' Ret' e ρ ρ' mark s t) :
    Triple host P c Q' Qe' J' Ret' := by
  intro ρ mark s n ρ' h' e context pre run budget
  obtain ⟨t, ha, hh, hn, ht, he, post⟩ := ht ρ mark s n ρ' h' e context pre run budget
  exact ⟨t, ha, hh, hn, ht, he, consequence e ρ ρ' mark s t pre post⟩

theorem mask_nonneg_rule_syntax {host x b y i m}
    (fresh : y ≠ x) (hi : 0 ≤ i) (hm : 0 ≤ m) (hmlt : m < 2 ^ 31) :
    Triple host (IntegerOperands (.variable x) b i m)
      (.step (.bind y (.binary .bitAnd (.variable x) b)))
      (Now (maskNonnegConclusion x y m).meaning)
      (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False) (fun _ _ _ _ _ _ => False) := by
  apply triple_consequence_entry (mask_nonneg_rule hi hm hmlt)
  intro e ρ ρ' mark s t pre post
  cases e <;> try exact post
  obtain ⟨bx, bz, hx, _, hxi, _⟩ := pre
  obtain ⟨v, rfl, bits, r, rfl, hr, h0, hmask, hbound⟩ := post
  have hyread := integerVariable_eval (ρ := bindName ρ y (.num bits)) (h := t.h) (x := y) (by simp [bindName]) hr
  have hxread : (integerVariable x).eval (bindName ρ y (.num bits)) t.h = some i :=
    integerVariable_eval (by simpa [bindName, Argument.eval, Ne.symm fresh] using hx) hxi
  exact ⟨⟨⟨0, r, rfl, hyread, h0⟩, r, m, hyread, rfl, hmask⟩,
    r, i, hyread, hxread, hbound⟩

theorem or_rule_syntax {host x z y i j} (freshx : y ≠ x) (freshz : y ≠ z)
    (hi : 0 ≤ i) (hlt : i < 2 ^ 31) (hj : 0 ≤ j) (hjlt : j < 2 ^ 31) :
    Triple host (IntegerOperands (.variable x) (.variable z) i j)
      (.step (.bind y (.binary .bitOr (.variable x) (.variable z))))
      (Now (orConclusion x z y).meaning)
      (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False) (fun _ _ _ _ _ _ => False) := by
  apply triple_consequence_entry (or_rule hi hlt hj hjlt)
  intro e ρ ρ' mark s t pre post
  cases e <;> try exact post
  obtain ⟨bx, bz, hx, hz, hxi, hzj⟩ := pre
  obtain ⟨v, rfl, bits, r, rfl, hr, hl, hr', hu⟩ := post
  have hyread := integerVariable_eval (ρ := bindName ρ y (.num bits)) (h := t.h) (x := y) (by simp [bindName]) hr
  have hxread : (integerVariable x).eval (bindName ρ y (.num bits)) t.h = some i :=
    integerVariable_eval (by simpa [bindName, Argument.eval, Ne.symm freshx] using hx) hxi
  have hzread : (integerVariable z).eval (bindName ρ y (.num bits)) t.h = some j :=
    integerVariable_eval (by simpa [bindName, Argument.eval, Ne.symm freshz] using hz) hzj
  exact ⟨⟨i, r, hxread, hyread, hl⟩, ⟨j, r, hzread, hyread, hr'⟩,
    r, i + j, hyread, by simp [Expression.eval, hxread, hzread], hu⟩

/-- The name inequality in current-state syntax follows from the paper's
existing fresh-binding judgment; it is not a new arithmetic premise. -/
theorem Command.WellScoped.bind_fresh {Γ Δ y op x}
    (scope : Command.WellScoped Γ (.step (.bind y op)) Δ) (hx : Γ x) : y ≠ x := by
  cases scope with
  | bind fresh _ _ => intro eq; subst y; exact fresh hx

theorem admitted_mask_rule {host Γ Δ a b y i m}
    (_scope : Command.WellScoped Γ (.step (.bind y (.binary .bitAnd a b))) Δ)
    (hm : 0 ≤ m) (hmlt : m < 2 ^ 31) :
    Triple host (IntegerOperands a b i m) (.step (.bind y (.binary .bitAnd a b)))
      (Now (maskConclusion y m).meaning)
      (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False) (fun _ _ _ _ _ _ => False) ∧
    Effects host (IntegerOperands a b i m) (.step (.bind y (.binary .bitAnd a b))) [] [] :=
  ⟨mask_rule_syntax hm hmlt, bitwise_effects (by decide)⟩

theorem admitted_mask_nonneg_rule {host Γ Δ x b y i m}
    (scope : Command.WellScoped Γ (.step (.bind y (.binary .bitAnd (.variable x) b))) Δ)
    (hx : Γ x) (hi : 0 ≤ i) (hm : 0 ≤ m) (hmlt : m < 2 ^ 31) :
    Triple host (IntegerOperands (.variable x) b i m)
      (.step (.bind y (.binary .bitAnd (.variable x) b)))
      (Now (maskNonnegConclusion x y m).meaning)
      (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False) (fun _ _ _ _ _ _ => False) ∧
    Effects host (IntegerOperands (.variable x) b i m)
      (.step (.bind y (.binary .bitAnd (.variable x) b))) [] [] :=
  ⟨mask_nonneg_rule_syntax (scope.bind_fresh hx) hi hm hmlt, bitwise_effects (by decide)⟩

theorem admitted_or_rule {host Γ Δ x z y i j}
    (scope : Command.WellScoped Γ (.step (.bind y (.binary .bitOr (.variable x) (.variable z)))) Δ)
    (hx : Γ x) (hz : Γ z) (hi : 0 ≤ i) (hlt : i < 2 ^ 31) (hj : 0 ≤ j) (hjlt : j < 2 ^ 31) :
    Triple host (IntegerOperands (.variable x) (.variable z) i j)
      (.step (.bind y (.binary .bitOr (.variable x) (.variable z))))
      (Now (orConclusion x z y).meaning)
      (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False) (fun _ _ _ _ _ _ => False) ∧
    Effects host (IntegerOperands (.variable x) (.variable z) i j)
      (.step (.bind y (.binary .bitOr (.variable x) (.variable z)))) [] [] :=
  ⟨or_rule_syntax (scope.bind_fresh hx) (scope.bind_fresh hz) hi hlt hj hjlt,
    bitwise_effects (by decide)⟩

end Verification.Paper.TolerantFrames
