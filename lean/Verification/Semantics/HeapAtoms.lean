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

/-- Whether an atom is a tag's observed answer. -/
def Atom.isTag : Atom → Bool
  | .tag _ _ => true
  | _ => false


end Verification.HeapFacts
