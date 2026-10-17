import Verification.Programs.TypingBasics

/-! ## Binary operators

One rule types every binary operator (`arith`): each pair of operand clauses
must make the operator answer (`binop`) for every pair of their members, all
with one kind of result. Arithmetic takes two numbers or two bigints, never one
of each, the operators `numberOnly` states on numbers alone (`&`, `|`, `<<`,
`>>`, `>>>`) two numbers; a bigint divisor (of `/` or `%`) must exclude zero, and a bigint exponent be
non-negative, since those throw. `+` also takes a string and a primitive other
than a symbol, in either order, and concatenates. A relational operator takes
two numeric operands, of either kind, or two strings. -/
namespace Verification.ProgramTyping
open PositiveNormalization PositiveGraphs PositiveRules Tower
open CallEffects (Arrow RestArrow MethodArrow MethodRestArrow Contract Effect PromiseWith)
open HeapObservations (SafePost)

variable {ι : Type}

/-- The kind of value an operator yields. -/
inductive OpResult where
  | num | bigint | bool | str
  deriving DecidableEq, Repr

def numberClause : Clause α → Bool
  | .num | .numLit _ => true
  | _ => false

def bigintClause : Clause α → Bool
  | .bigint | .bigintLit _ => true
  | _ => false

def stringClause : Clause α → Bool
  | .str | .strLit _ => true
  | _ => false

/-- Primitives `ToNumeric` converts to a number or a bigint without running
code (`relNumeric`): numbers, bigints, Booleans, `null` and `undefined`. -/
def numericClause : Clause α → Bool
  | .num | .numLit _ | .bigint | .bigintLit _ | .bool | .boolLit _ | .nul | .undef => true
  | _ => false

/-- Primitives `ToString` converts without running code (`primString`):
every primitive but a symbol. -/
def printableClause : Clause α → Bool
  | .str | .strLit _ | .num | .numLit _ | .bigint | .bigintLit _
  | .bool | .boolLit _ | .nul | .undef => true
  | _ => false

/-- A clause of primitives only, which strict equality compares by content. -/
def primitiveClause : Clause α → Bool
  | .nul | .undef | .bool | .boolLit _ | .num | .numLit _ | .str | .strLit _
  | .bigint | .bigintLit _ | .symbol => true
  | _ => false

@[nospecialize] def nullishClause : Clause α → Bool
  | .nul | .undef => true
  | _ => false

/-- Clauses whose members are JavaScript objects, including callable objects. -/
@[nospecialize] def objectClause : Clause α → Bool
  | .refs .. | .dict .. | .arrs .. | .callable .. | .ctors .. => true
  | _ => false

/-- What an operator yields on members of two clauses, when it answers or
throws for every pair of them. Strict equality answers where either clause
is of primitives or of objects, which carry their identity. Two bigints give a bigint for every arithmetic
operator: a division or remainder by zero or a negative exponent throws a `RangeError`
(`binopThrows`), which is an outcome, not a wrong value, so no divisor or
exponent condition is needed. -/
def opResult (op : Arith) (c d : Clause α) : Option OpResult :=
  if op = .looseEq then
    (if primitiveClause c && primitiveClause d || nullishClause c || nullishClause d ||
       objectClause c && objectClause d
     then some .bool else none)
  else if op = .eq then
    (if primitiveClause c || primitiveClause d || objectClause c || objectClause d
     then some .bool else none)
  else if op.relational then
    if numericClause c && numericClause d || stringClause c && stringClause d
    then some .bool else none
  else if op == .add && (stringClause c && printableClause d || printableClause c && stringClause d)
  then some .str
  else if numberClause c && numberClause d then some .num
  else if bigintClause c && bigintClause d && !op.numberOnly then some .bigint
  else none

/-- The values of a result kind. -/
def OpResult.holds : OpResult → Val → Prop
  | .num, v => ∃ x, v = .num x
  | .bigint, v => ∃ i, v = .bigint i
  | .bool, v => v = .tru ∨ v = .fls
  | .str, v => ∃ s, v = .str s

theorem numberClause_member {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (hc : numberClause c = true) (hv : semWithArgs Ξ X P c n W v) : ∃ x, v = .num x := by
  cases c <;> simp [numberClause] at hc
  · exact hv
  · exact ⟨_, hv⟩

theorem bigintClause_member {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (hc : bigintClause c = true) (hv : semWithArgs Ξ X P c n W v) : ∃ i, v = .bigint i := by
  cases c <;> simp [bigintClause] at hc
  · exact hv
  · exact ⟨_, hv⟩

theorem stringClause_member {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (hc : stringClause c = true) (hv : semWithArgs Ξ X P c n W v) : ∃ s, v = .str s := by
  cases c <;> simp [stringClause] at hc
  · exact hv
  · exact ⟨_, hv⟩

/-- A member of a printable clause converts by `ToString`. -/
theorem printableClause_member {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (hc : printableClause c = true) (hv : semWithArgs Ξ X P c n W v) : ∃ t, primString v = some t := by
  cases c <;> simp [printableClause] at hc <;> simp only [semWithArgs] at hv
  all_goals first
    | (rcases hv with rfl | rfl <;> exact ⟨_, rfl⟩)
    | (obtain ⟨_, rfl⟩ := hv; exact ⟨_, rfl⟩)
    | (subst hv; exact ⟨_, rfl⟩)
    | (split at hv <;> subst hv <;> exact ⟨_, rfl⟩)

theorem primitiveClause_member {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (hc : primitiveClause c = true) (hv : semWithArgs Ξ X P c n W v) : isPrim v = true := by
  cases c <;> simp [primitiveClause] at hc <;> simp only [semWithArgs] at hv
  all_goals first
    | (rcases hv with rfl | rfl <;> rfl)
    | (obtain ⟨_, rfl⟩ := hv; rfl)
    | (subst hv; rfl)
    | (split at hv <;> subst hv <;> rfl)
    | (simp only [nulT, undefT, boolT, numT, strT, bigintT, symbolT] at hv;
       first | (subst hv; rfl) | (rcases hv with rfl | rfl <;> rfl) | (obtain ⟨_, rfl⟩ := hv; rfl))

/-- A member of a numeric clause converts by `ToNumeric` to a number or a bigint. -/
theorem numericClause_member {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (hc : numericClause c = true) (hv : semWithArgs Ξ X P c n W v) :
    ∃ x, relNumeric v = some x ∧ ((∃ y, x = .num y) ∨ ∃ i, x = .bigint i) := by
  cases c <;> simp [numericClause] at hc <;> simp only [semWithArgs] at hv
  all_goals first
    | (rcases hv with rfl | rfl <;> exact ⟨_, rfl, by simp⟩)
    | (obtain ⟨_, rfl⟩ := hv; exact ⟨_, rfl, by simp⟩)
    | (subst hv; exact ⟨_, rfl, by simp⟩)
    | (split at hv <;> subst hv <;> exact ⟨_, rfl, by simp⟩)

/-- Two operands `ToNumeric` converts compare to a Boolean. -/
theorem relationalValue_numeric {op : Arith} {v w x y : Tm}
    (hx : relNumeric v = some x) (hy : relNumeric w = some y)
    (hxk : (∃ u, x = .num u) ∨ ∃ i, x = .bigint i) (hyk : (∃ u, y = .num u) ∨ ∃ i, y = .bigint i) :
    ∃ q, relationalValue op v w = some (boolVal q) := by
  have hnum : relationalValue op v w = numericRelation op x y := by
    unfold relationalValue
    split
    · simp [relNumeric] at hx
    · simp [hx, hy]
  rw [hnum]
  rcases hxk with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;> rcases hyk with ⟨b, rfl⟩ | ⟨b, rfl⟩ <;>
    exact ⟨_, rfl⟩

theorem nullishClause_member {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (hc : nullishClause c = true) (hv : semWithArgs Ξ X P c n W v) : isNullish v = true := by
  cases c <;> simp [nullishClause] at hc <;> simp only [semWithArgs] at hv
  all_goals subst hv; rfl

theorem looseEquals_some {v w : Tm} (hv : isVal v = true) (hw : isVal w = true)
    (h : (isPrim v && isPrim w || isNullish v || isNullish w) = true) :
    ∃ q, looseEquals v w = some q := by
  unfold looseEquals
  simp only [hv, hw, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  by_cases hp : (isPrim v && isPrim w) = true
  · exact ⟨primitiveEquals v w, by simp [hp]⟩
  · have hn : (isNullish v || isNullish w) = true := by simpa [hp] using h
    exact ⟨false, by simp [hp, hn]⟩

theorem objectClause_member {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (hc : objectClause c = true) (hv : semWithArgs Ξ X P c n W v) :
    ∃ fs code oid, v = .objAt fs code oid := by
  cases c with
  | refs | dict => obtain ⟨fs, oid, h, _⟩ := hv.1.1; exact ⟨fs, .absent, oid, h⟩
  | callable => obtain ⟨fs, code, oid, h, _⟩ := hv.1.1.1; exact ⟨fs, code, oid, h⟩
  | arrs => obtain ⟨fs, code, oid, h, _⟩ := hv.1.1; exact ⟨fs, code, oid, h⟩
  | ctors => obtain ⟨fs, _, _, _, _, _, _, oid, h, _⟩ := hv.1.1.1; exact ⟨fs, _, oid, h⟩
  | _ => simp [objectClause] at hc

/-- Strict equality answers when one operand is a primitive or an object. -/
theorem strictEquals_some {v w : Tm} (hv : isVal v = true) (hw : isVal w = true)
    (h : (isPrim v || isPrim w) = true ∨ (∃ fs code oid, v = .objAt fs code oid) ∨
      (∃ fs code oid, w = .objAt fs code oid)) :
    ∃ q, strictEquals v w = some q := by
  unfold strictEquals
  simp only [hv, hw, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  by_cases hp : (isPrim v || isPrim w) = true
  · exact ⟨sameValue v w, by simp [hp]⟩
  simp only [hp, Bool.false_eq_true, ↓reduceIte]
  have hp' : isPrim v = false ∧ isPrim w = false := by simpa using hp
  rcases h with h | ⟨fs, code, oid, rfl⟩ | ⟨fs, code, oid, rfl⟩
  · exact absurd h hp
  · cases w <;> simp_all [isPrim, isVal]
  · cases v <;> simp_all [isPrim, isVal]

/-- `+` of a string and a printable value, in either order, is a string. -/
theorem add_string {s : String} {w : Tm} {t : String} (ht : primString w = some t) :
    binop .add (.str s) w = some (.str (s ++ t)) ∧ binop .add w (.str s) = some (.str (t ++ s)) := by
  cases w <;> simp [primString] at ht <;> subst ht <;> simp [binop, primString, Arith.relational]
  all_goals rfl

theorem boolVal_holds (q : Bool) : OpResult.holds .bool (boolVal q) := by
  cases q <;> simp [OpResult.holds, boolVal]

/-- **The classification is sound**: on members of the two clauses the
operator answers, with a value of the kind it names, or throws. -/
theorem opResult_sound {X : α → Fam} {P : α → ArgFam} {op : Arith} {c d : Clause α} {r n W v w}
    (h : opResult op c d = some r) (hv : semWithArgs Ξ X P c n W v) (hw : semWithArgs Ξ X P d n W w) :
    (∃ z, binop op v w = some z ∧ r.holds z) ∨ binopThrows op v w = true := by
  unfold opResult at h
  by_cases hloose : op = .looseEq
  · subst hloose
    simp only [↓reduceIte] at h
    split at h
    · rename_i hp
      cases h
      have answer : ∃ q, looseEquals v w = some q := by
        rcases Bool.or_eq_true_iff.mp hp with hp | ho
        · apply looseEquals_some (semWithArgs_value hv).1 (semWithArgs_value hw).1
          simp only [Bool.or_eq_true, Bool.and_eq_true] at hp ⊢
          rcases hp with (⟨hc, hd⟩ | hc) | hd
          · exact .inl (.inl ⟨primitiveClause_member hc hv, primitiveClause_member hd hw⟩)
          · exact .inl (.inr (nullishClause_member hc hv))
          · exact .inr (nullishClause_member hd hw)
        · simp only [Bool.and_eq_true] at ho
          obtain ⟨hc, hd⟩ := ho
          obtain ⟨fs, code, oid, rfl⟩ := objectClause_member hc hv
          obtain ⟨gs, other, oid', rfl⟩ := objectClause_member hd hw
          exact ⟨oid == oid', by simp [looseEquals, strictEquals, isVal, isPrim, isNullish]⟩
      obtain ⟨q, hq⟩ := answer
      exact .inl ⟨boolVal q, by simp [binop, hq], boolVal_holds _⟩
    · cases h
  simp only [hloose, ↓reduceIte] at h
  by_cases heq : op = .eq
  · subst heq
    simp only [↓reduceIte] at h
    split at h
    · rename_i hp
      cases h
      have hval := (semWithArgs_value hv).1
      have wval := (semWithArgs_value hw).1
      simp only [Bool.or_eq_true] at hp
      obtain ⟨q, hq⟩ := strictEquals_some hval wval (by
        rcases hp with ((hp | hp) | hp) | hp
        · exact .inl (by simp [primitiveClause_member hp hv])
        · exact .inl (by simp [primitiveClause_member hp hw])
        · exact .inr (.inl (objectClause_member hp hv))
        · exact .inr (.inr (objectClause_member hp hw)))
      exact .inl ⟨boolVal q, by simp [binop, hq], boolVal_holds _⟩
    · cases h
  simp only [heq, ↓reduceIte] at h
  by_cases hrel : op.relational = true
  · simp only [hrel, ↓reduceIte] at h
    split at h
    · rename_i hops
      cases h
      rcases Bool.or_eq_true_iff.mp hops with hops | hops
      · rcases Bool.and_eq_true_iff.mp hops with ⟨hc, hd⟩
        obtain ⟨x, hx, hxk⟩ := numericClause_member hc hv
        obtain ⟨y, hy, hyk⟩ := numericClause_member hd hw
        obtain ⟨q, hq⟩ := relationalValue_numeric (op := op) hx hy hxk hyk
        exact .inl ⟨boolVal q, by simp [binop, hloose, hrel, heq, hq], boolVal_holds _⟩
      · rcases Bool.and_eq_true_iff.mp hops with ⟨hc, hd⟩
        obtain ⟨x, rfl⟩ := stringClause_member hc hv
        obtain ⟨y, rfl⟩ := stringClause_member hd hw
        exact .inl ⟨boolVal (relationHolds op (some (unitsOrder (utf16Units x) (utf16Units y)))),
          by simp [binop, hloose, hrel, heq, relationalValue], boolVal_holds _⟩
    · cases h
  · simp only [hrel, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · rename_i hops
      cases h
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hops
      obtain ⟨hadd, (⟨hc, hd⟩ | ⟨hc, hd⟩)⟩ := hops <;>
        obtain rfl : op = .add := by cases op <;> first | rfl | exact absurd hadd (by decide)
      · obtain ⟨x, rfl⟩ := stringClause_member hc hv
        obtain ⟨t, ht⟩ := printableClause_member hd hw
        exact .inl ⟨_, (add_string ht).1, _, rfl⟩
      · obtain ⟨t, ht⟩ := printableClause_member hc hv
        obtain ⟨y, rfl⟩ := stringClause_member hd hw
        exact .inl ⟨_, (add_string ht).2, _, rfl⟩
    split at h
    · rename_i hops
      cases h
      rcases Bool.and_eq_true_iff.mp hops with ⟨hc, hd⟩
      obtain ⟨x, rfl⟩ := numberClause_member hc hv
      obtain ⟨y, rfl⟩ := numberClause_member hd hw
      exact .inl ⟨.num (arithBits op x y), by simp [binop, hloose, hrel, heq], _, rfl⟩
    · split at h
      · rename_i _ hops
        cases h
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hops
        obtain ⟨⟨hc, hd⟩, hnum⟩ := hops
        obtain ⟨x, rfl⟩ := bigintClause_member hc hv
        obtain ⟨y, rfl⟩ := bigintClause_member hd hw
        cases hz : bigintArith op x y with
        | some z => exact .inl ⟨.bigint z, by simp [binop, hloose, hrel, heq, hz], z, rfl⟩
        | none =>
          refine .inr ?_
          cases op <;> simp [Arith.relational, Arith.numberOnly] at hrel heq hloose hnum <;>
            simp [bigintArith] at hz <;> simp [binopThrows, hz]
      · cases h

/-- Two operand types an operator answers for, pair by pair, with one kind
of result. -/
def Operands (G : NormalGraph ι) (op : Arith) (A B : Ty ι) (r : OpResult) : Prop :=
  G.plainTy A = true ∧ G.plainTy B = true ∧
    ∀ c ∈ expand G A, ∀ d ∈ expand G B, opResult op c d = some r

/-- A result type holding every value of the kind: the number, bigint or
string family, or both Booleans. -/
def OpResult.covers (G : NormalGraph ι) (N : Ty ι) : OpResult → Prop
  | .num => Represents G N .num
  | .bigint => Represents G N .bigint
  | .bool => (.boolLit true) ∈ expand G N ∧ (.boolLit false) ∈ expand G N
  | .str => Represents G N .str

instance [DecidableEq ι] (G : NormalGraph ι) (op : Arith) (A B : Ty ι) (r : OpResult) :
    Decidable (Operands G op A B r) := by unfold Operands; infer_instance

instance [DecidableEq ι] (G : NormalGraph ι) (N : Ty ι) (r : OpResult) :
    Decidable (r.covers G N) := by
  cases r <;> unfold OpResult.covers <;> unfold Represents <;> infer_instance

/-- The kind a pair of operand types gives, read from their first clauses;
`Operands` then checks every pair. -/
def operandsResult (G : NormalGraph ι) (op : Arith) (A B : Ty ι) : Option OpResult :=
  match expand G A, expand G B with
  | c :: _, d :: _ => opResult op c d
  | _, _ => none

/-- The operand types give one kind of result, pair by pair, and the result
type holds every value of it. -/
def ClauseOperatorTypes (G : NormalGraph ι) (op : Arith) (A B N : Ty ι) : Prop :=
  match operandsResult G op A B with
  | some r => Operands G op A B r ∧ r.covers G N
  | none => False

instance [DecidableEq ι] (G : NormalGraph ι) (op : Arith) (A B N : Ty ι) :
    Decidable (ClauseOperatorTypes G op A B N) := by
  unfold ClauseOperatorTypes; split <;> infer_instance

/-- A clause whose members decide an equality operator against any value:
primitives or objects for strict equality, nullish values for loose. -/
def decidingClause (op : Arith) (c : Clause α) : Bool :=
  (decide (op = .eq) && sourceClause c) ||
    (decide (op = .looseEq) && nullishClause c)

/-- An operand type every clause of which decides the equality operator. -/
def EqualityDecided (G : NormalGraph ι) (op : Arith) (X : Ty ι) : Prop :=
  G.plainTy X = true ∧ ∀ c ∈ expand G X, decidingClause op c = true

instance [DecidableEq ι] (G : NormalGraph ι) (op : Arith) (X : Ty ι) :
    Decidable (EqualityDecided G op X) := by unfold EqualityDecided; infer_instance

/-- A member of a deciding clause compared with any value, in either order,
gives a Boolean. -/
theorem decidingClause_sound {X : α → Fam} {P : α → ArgFam} {op : Arith} {c : Clause α} {n W v w}
    (hc : decidingClause op c = true) (hv : semWithArgs Ξ X P c n W v) (hw : isVal w = true) :
    (∃ z, binop op v w = some z ∧ OpResult.bool.holds z) ∧
      (∃ z, binop op w v = some z ∧ OpResult.bool.holds z) := by
  have hval := (semWithArgs_value hv).1
  simp only [decidingClause, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc
  rcases hc with ⟨rfl, hc⟩ | ⟨rfl, hc⟩
  · have hk : (isPrim v = true) ∨ ∃ fs code oid, v = .objAt fs code oid := by
      have hj := (sourceClause_sound hc hv).1
      cases v <;> simp_all [isSourceVal, isPrim]
    obtain ⟨q, hq⟩ := strictEquals_some hval hw (by
      rcases hk with hk | hk
      · exact .inl (by simp [hk])
      · exact .inr (.inl hk))
    obtain ⟨q', hq'⟩ := strictEquals_some hw hval (by
      rcases hk with hk | hk
      · exact .inl (by simp [hk])
      · exact .inr (.inr hk))
    exact ⟨⟨boolVal q, by simp [binop, hq], boolVal_holds _⟩,
      ⟨boolVal q', by simp [binop, hq'], boolVal_holds _⟩⟩
  · have hn := nullishClause_member hc hv
    obtain ⟨q, hq⟩ := looseEquals_some hval hw (by simp [hn])
    obtain ⟨q', hq'⟩ := looseEquals_some hw hval (by simp [hn])
    exact ⟨⟨boolVal q, by simp [binop, hq], boolVal_holds _⟩,
      ⟨boolVal q', by simp [binop, hq'], boolVal_holds _⟩⟩

/-- The operator rule's premise on the types: the operand types give one kind
of result, pair by pair; or one operand's type decides the equality operator
whatever the other's value, a type parameter's included. The result type
holds every value of the kind. -/
def OperatorTypes (G : NormalGraph ι) (op : Arith) (A B N : Ty ι) : Prop :=
  ClauseOperatorTypes G op A B N ∨
    ((EqualityDecided G op A ∨ EqualityDecided G op B) ∧ OpResult.bool.covers G N)

instance [DecidableEq ι] (G : NormalGraph ι) (op : Arith) (A B N : Ty ι) :
    Decidable (OperatorTypes G op A B N) := by unfold OperatorTypes; infer_instance

end Verification.ProgramTyping
