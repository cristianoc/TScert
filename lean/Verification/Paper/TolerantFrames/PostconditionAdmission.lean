import Verification.Paper.TolerantFrames.PostconditionScope

/-! # Admission of two-state syntax

Scope and declared-region admission are distinct. Raw shared regions include
helpers that the paper's seven-form judgment excludes. Entry and current
program declarations are separate, and value binders shift only odd roots.
Nested old terms and old assertions containing old terms are raw syntax only.
-/
namespace Verification.Paper.TolerantFrames.TwoState
open Verification Footprints HeapKnowledge TolerantFrames

/-- Insert a logical value slot, leaving all program roots untouched. -/
def liftValueRoot (x : Nat) : Nat := if x % 2 = 0 then x else x + 2

/-- The fresh logical value has no declared object or collection type. -/
def parentValueRoot (x : Nat) : Option Nat :=
  if x % 2 = 0 then some x else if x = 1 then none else some (x - 2)

def underLogicalValue (types : DeclaredPaths) : DeclaredPaths where
  collection p := ∃ x, parentValueRoot p.root = some x ∧ types.collection ⟨x, p.fields⟩
  object p := ∃ x, parentValueRoot p.root = some x ∧ types.object ⟨x, p.fields⟩
  field p f := ∃ x, parentValueRoot p.root = some x ∧ types.field ⟨x, p.fields⟩ f

mutual
def Term.NoOld : Term → Prop
  | .literal _ | .index _ | .path _ _ => True
  | .element _ _ e _ _ => e.NoOld
  | .old _ => False

def Expression.NoOld : Expression → Prop
  | .constant _ => True
  | .scale _ t => t.NoOld
  | .add e f => e.NoOld ∧ f.NoOld
end

mutual
def Term.WellFormed : Term → Prop
  | .literal _ | .index _ | .path _ _ => True
  | .element _ _ e _ _ => e.WellFormed
  | .old t => t.NoOld

def Expression.WellFormed : Expression → Prop
  | .constant _ => True
  | .scale _ t => t.WellFormed
  | .add e f => e.WellFormed ∧ f.WellFormed
end

def BodyTerm.NoOld : BodyTerm → Prop
  | .free t => t.NoOld
  | _ => True

def BodyTerm.WellFormed : BodyTerm → Prop
  | .free t => t.WellFormed
  | _ => True

def BodyExpression.NoOld : BodyExpression → Prop
  | .constant _ => True
  | .scale _ t => t.NoOld
  | .add e f => e.NoOld ∧ f.NoOld

def BodyExpression.WellFormed : BodyExpression → Prop
  | .constant _ => True
  | .scale _ t => t.WellFormed
  | .add e f => e.WellFormed ∧ f.WellFormed

def Clause.NoOld : Clause → Prop
  | .le e f => e.NoOld ∧ f.NoOld
  | .or c d => c.NoOld ∧ d.NoOld

def Clause.WellFormed : Clause → Prop
  | .le e f => e.WellFormed ∧ f.WellFormed
  | .or c d => c.WellFormed ∧ d.WellFormed

def Body.NoOld : Body → Prop
  | .clause c => c.NoOld
  | .and c d => c.NoOld ∧ d.NoOld

def Body.WellFormed : Body → Prop
  | .clause c => c.WellFormed
  | .and c d => c.WellFormed ∧ d.WellFormed

def Atom.NoOld : Atom → Prop
  | .le e f => e.NoOld ∧ f.NoOld
  | .dense _ e | .element _ e _ => e.NoOld
  | .every _ e b => e.NoOld ∧ b.NoOld
  | _ => True

def Atom.WellFormed : Atom → Prop
  | .le e f => e.WellFormed ∧ f.WellFormed
  | .dense _ e | .element _ e _ => e.WellFormed
  | .every _ e b => e.WellFormed ∧ b.WellFormed
  | _ => True

def Assertion.NoOld : Assertion → Prop
  | .atom a => a.NoOld
  | .and F G | .or F G => F.NoOld ∧ G.NoOld
  | .existsValue F | .box _ F => F.NoOld
  | _ => True

/-- Only the seven shared paper-region constructors pass this judgment. -/
def Assertion.WellFormed (types : DeclaredPaths) : Assertion → Prop
  | .truth | .falsity | .separated _ _ | .apart _ _ => True
  | .atom a => a.WellFormed
  | .and F G | .or F G => F.WellFormed types ∧ G.WellFormed types
  | .existsValue F => F.WellFormed (underLogicalValue types)
  | .fresh r => RegionWellFormed types r
  | .box Φ F => EffectWellFormed types Φ ∧ F.WellFormed types

/-- Declared roots are interpreted in the namespace of the selected phase.
Logical value binders update both declaration contexts without asserting that
the witness is reference-valid at both states. -/
def Post.WellFormed (entryTypes currentTypes : DeclaredPaths) : Post → Prop
  | .assertion F => F.WellFormed currentTypes
  | .old F => F.NoOld ∧ F.WellFormed entryTypes
  | .transition Φ => EffectWellFormed entryTypes Φ
  | .and Q R | .or Q R | .implication Q R => Q.WellFormed entryTypes currentTypes ∧ R.WellFormed entryTypes currentTypes
  | .forallIndex Q => Q.WellFormed entryTypes currentTypes
  | .forallValue Q => Q.WellFormed (underLogicalValue entryTypes) (underLogicalValue currentTypes)

/-- Closed and admitted two-state postconditions of the paper. -/
def Post.Admitted (entryPrograms currentPrograms : Nat → Prop) (entryTypes currentTypes : DeclaredPaths)
    (Q : Post) : Prop :=
  Q.Scoped entryPrograms currentPrograms 0 0 ∧ Q.WellFormed entryTypes currentTypes

theorem parent_liftValueRoot (x : Nat) : parentValueRoot (liftValueRoot x) = some x := by
  by_cases he : x % 2 = 0
  · simp [parentValueRoot, liftValueRoot, he]
  · have hm : x % 2 = 1 := by omega
    have hn : x + 2 ≠ 1 := by omega
    simp [parentValueRoot, liftValueRoot, hm, hn]

theorem liftValueRoot_program (x : Nat) : liftValueRoot (Root.program x).encode = (Root.program x).encode := by
  simp [liftValueRoot, Root.encode]

theorem liftValueRoot_value (x : Nat) : liftValueRoot (Root.value x).encode = (Root.value (x + 1)).encode := by
  simp [liftValueRoot, Root.encode, Nat.add_mod]
  omega

/-- Opening a value binder does not shift program names or index variables. -/
theorem mixedEnv_push_lift (ρ : Env) (ν : Nat → Val) (v : Val) (x : Nat) :
    mixedEnv ρ (push v ν) (liftValueRoot x) = mixedEnv ρ ν x := by
  unfold mixedEnv liftValueRoot
  split
  · simp
  · rename_i ho
    have hdiv : (x + 2) / 2 = x / 2 + 1 := by omega
    simp [ho, hdiv, push]

end Verification.Paper.TolerantFrames.TwoState
