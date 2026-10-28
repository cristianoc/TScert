import Verification.Programs.PointClaims
import Verification.Semantics.HeapObservations

/-! The atoms of today's heap facts: finite predicates on current values,
which value sets translate (`ValueSets.ofAtoms`). -/
namespace Verification.HeapFacts
open ProgramTyping PositiveRules PositiveGraphs HeapObservations

/-- Finite predicates on current values. Primitive predicates describe a
value family. Nullish exclusions apply to values of any shape and support a
read at the storage contract's corresponding negative slice. A tag atom is
a test's observed answer, `tagHolds` as `BranchRefinement.Observation`
states it, and supports a read at the contract's slice by that answer. -/
inductive Atom where
  | nul | undef | tru | fls | num | numLit (bits : UInt64) | str | strLit (value : String)
  | defined | nonNull | nonNullish
  | tag (test : Tag) (answer : Bool)
  deriving DecidableEq, Repr

def Atom.holds : Atom → Tm → Prop
  | .nul, v => v = .nul
  | .undef, v => v = .undef
  | .tru, v => v = .tru
  | .fls, v => v = .fls
  | .num, v => ∃ bits, v = .num bits
  | .numLit bits, v => v = .num bits
  | .str, v => ∃ s, v = .str s
  | .strLit s, v => v = .str s
  | .defined, v => isVal v = true ∧ v ≠ .undef
  | .nonNull, v => isVal v = true ∧ v ≠ .nul
  | .nonNullish, v => isVal v = true ∧ v ≠ .nul ∧ v ≠ .undef
  | .tag t q, v => isVal v = true ∧ (tagHolds t v = q ∨ protoFree t v = false)

theorem Atom.isValue {a : Atom} {v} (h : a.holds v) : isVal v = true := by
  cases a <;> simp only [Atom.holds] at h
  all_goals first | exact h.1 | (rcases h with ⟨bits,rfl⟩; rfl) | (subst v; rfl)

def Atom.clause (a : Atom) : PositiveNormalization.Clause α :=
  match a with
  | .nul => .nul | .undef => .undef | .tru => .boolLit true
  | .fls => .boolLit false | .num => .num | .numLit b => .numLit b
  | .str => .str | .strLit s => .strLit s
  | .defined | .nonNull | .nonNullish | .tag _ _ => .top

/-- Whether an atom is a tag's observed answer. -/
def Atom.isTag : Atom → Bool
  | .tag _ _ => true
  | _ => false

/-- A primitive atom is exactly its clause. -/
theorem Atom.sem {a : Atom} {S : α → Fam} {P : α → ArgFam} {n W v} (hd : a ≠ .defined) (hn : a ≠ .nonNull) (hb : a ≠ .nonNullish)
    (ht : a.isTag = false) :
    PositiveNormalization.semWithArgs Ξ S P a.clause n W v ↔ a.holds v := by
  cases a <;> first | rfl | exact absurd rfl hd | exact absurd rfl hn | exact absurd rfl hb | simp [Atom.isTag] at ht

/-- The nullish tests a predicate guarantees false. -/
def Atom.excludes (a : Atom) (tag : Tag) : Bool :=
  match tag, a with
  | _, .tag _ _ => false
  | .isUndef, .undef | .isUndef, .nonNull => false
  | .isNul, .nul | .isNul, .defined => false
  | .isNullish, .nul | .isNullish, .undef | .isNullish, .defined | .isNullish, .nonNull => false
  | .isUndef, _ | .isNul, _ | .isNullish, _ => true
  | _, _ => false

theorem Atom.excludes_sound {a : Atom} {tag : Tag} {v : Tm}
    (he : a.excludes tag = true) (hv : a.holds v) : tagHolds tag v = false := by
  cases tag <;> cases a <;> simp_all [Atom.excludes, Atom.holds]
  all_goals first
    | (subst v; rfl)
    | (obtain ⟨_, rfl⟩ := hv; rfl)
    | (cases v <;> simp_all [tagHolds])

/-- Whether a value meeting the atom answers `t` with `q`, or reads a
prototype for it: a nullish exclusion answers its test `false`, and a tag
atom is the answer. -/
def Atom.answers (a : Atom) (t : Tag) (q : Bool) : Bool :=
  (!q && a.excludes t) || a == .tag t q

theorem Atom.answers_sound {a : Atom} {t : Tag} {q : Bool} {v : Tm}
    (h : a.answers t q = true) (hv : a.holds v) : tagHolds t v = q ∨ protoFree t v = false := by
  simp only [Atom.answers, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  rcases h with ⟨rfl, he⟩ | rfl
  · exact Or.inl (Atom.excludes_sound he hv)
  · exact hv.2

def Atom.le (a b : Atom) : Bool :=
  a == b || match b with
    | .defined => a.excludes .isUndef
    | .nonNull => a.excludes .isNul
    | .nonNullish => a.excludes .isNullish
    | _ => match a, b with
      | .numLit _, .num | .strLit _, .str => true
      | _, _ => false

theorem Atom.le_sound {a b : Atom} {v} (h : a.le b = true) (hv : a.holds v) : b.holds v := by
  simp only [Atom.le, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h
  · exact hv
  · cases b with
    | defined =>
      have ht := Atom.excludes_sound h hv
      exact ⟨Atom.isValue hv, by intro he; subst v; simp [tagHolds] at ht⟩
    | nonNull =>
      have ht := Atom.excludes_sound h hv
      exact ⟨Atom.isValue hv, by intro he; subst v; simp [tagHolds] at ht⟩
    | nonNullish =>
      have ht := Atom.excludes_sound h hv
      exact ⟨Atom.isValue hv, by intro he; subst v; simp [tagHolds] at ht,
        by intro he; subst v; simp [tagHolds] at ht⟩
    | _ => cases a <;> simp_all [Atom.holds]


def covers (source target : List Atom) : Bool :=
  source.all fun a => target.any a.le

theorem covers_sound {source target v} (h : covers source target = true)
    (hv : ∃ a ∈ source, a.holds v) : ∃ b ∈ target, b.holds v := by
  obtain ⟨a,ha,hv⟩ := hv
  obtain ⟨b,hb,hab⟩ := List.any_eq_true.mp (List.all_eq_true.mp h a ha)
  exact ⟨b,hb,Atom.le_sound hab hv⟩

end Verification.HeapFacts
