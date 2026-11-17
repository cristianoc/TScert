import Verification.Paper.TolerantFrames.PostconditionRenaming

/-! # Frozen integer-value instantiation

A logical index denotes one integer across entry/current states and modalities.
Substitution by a changing heap-reading expression is a different operation.
This construction is expressible in the paper's first-order grammar: require
the expression defined, then quantify a fresh index equated to it outside the
body. Its interpretation evaluates the expression once and freezes that value.
It is not claimed to resolve the paper's underspecified instantiation sentence.
-/
namespace Verification.Paper.TolerantFrames.TwoState
open Verification Footprints HeapKnowledge TolerantFrames

def shiftIndex : Renaming := ⟨id, Nat.succ, id⟩

def expressionDefined (e : Expression) : Post := .assertion (.atom (.le e e))

def indexGuard (e : Expression) : Post :=
  .assertion (.and (.atom (.le (.scale 1 (.index 0)) (e.rename shiftIndex)))
    (.atom (.le (e.rename shiftIndex) (.scale 1 (.index 0)))))

/-- Defined(e) ∧ ∀j. (j=e ⇒ Q(j)), with e shifted below the new index binder. -/
def frozenInstance (e : Expression) (Q : Post) : Post :=
  .and (expressionDefined e) (.forallIndex (.implication (indexGuard e) Q))

theorem Expression.eval_shiftIndex (e : Expression) (entry focus : State) (η : LogicalEnv) (i : Int) :
    (e.rename shiftIndex).eval entry focus {η with indices := pushIndex i η.indices} = e.eval entry focus η := by
  have hr := Expression.eval_rename shiftIndex entry focus {η with indices := pushIndex i η.indices} e
  exact hr

theorem expressionDefined_holds (e : Expression) (c : Context) (η : LogicalEnv) :
    (expressionDefined e).Holds c η ↔ ∃ n, e.eval c.entry c.current η = some n := by
  cases he : e.eval c.entry c.current η <;>
    simp [expressionDefined, Post.Holds, Assertion.Holds, Atom.Holds, he]

theorem indexGuard_holds {e : Expression} {c : Context} {η : LogicalEnv} {n : Int}
    (he : e.eval c.entry c.current η = some n) (i : Int) :
    (indexGuard e).Holds c {η with indices := pushIndex i η.indices} ↔ i = n := by
  simp [indexGuard, Post.Holds, Assertion.Holds, Atom.Holds, Expression.eval, Term.eval,
    Expression.eval_shiftIndex, he, pushIndex]
  omega

/-- Exact interpretation of the defined frozen-value instance. -/
theorem frozenInstance_holds (e : Expression) (Q : Post) (c : Context) (η : LogicalEnv) :
    (frozenInstance e Q).Holds c η ↔
      ∃ n, e.eval c.entry c.current η = some n ∧ Q.Holds c {η with indices := pushIndex n η.indices} := by
  change (_ ∧ _) ↔ _
  rw [expressionDefined_holds]
  constructor
  · rintro ⟨⟨n, he⟩, hQ⟩
    exact ⟨n, he, hQ n ((indexGuard_holds he n).mpr rfl)⟩
  · rintro ⟨n, he, hQ⟩
    refine ⟨⟨n, he⟩, fun i hi => ?_⟩
    have hin := (indexGuard_holds he i).mp hi
    subst i
    exact hQ

/-- General defined value instantiation, including old/modal bodies. The
selected integer is fixed through every phase of Q. -/
theorem frozen_index_instance {e : Expression} {Q : Post} {c : Context} {η : LogicalEnv}
    (hQ : (Post.forallIndex Q).Holds c η) (hd : (expressionDefined e).Holds c η) :
    (frozenInstance e Q).Holds c η := by
  obtain ⟨n, hn⟩ := (expressionDefined_holds e c η).mp hd
  exact (frozenInstance_holds e Q c η).mpr ⟨n, hn, hQ n⟩

/-- Logical j is the same value at entry and current, so this universally
quantified implication is always true. It does not justify textual replacement
by an expression whose entry and current values differ. -/
def indexZero : Assertion := .and (.atom (.le (.scale 1 (.index 0)) (.constant 0)))
  (.atom (.le (.constant 0) (.scale 1 (.index 0))))

def frozenIndexIdentity : Post := .forallIndex (.implication (.old indexZero) (.assertion indexZero))

def expressionZero (e : Expression) : Assertion := .and (.atom (.le e (.constant 0)))
  (.atom (.le (.constant 0) e))

def textualIndexIdentity (e : Expression) : Post :=
  .implication (.old (expressionZero e)) (.assertion (expressionZero e))

theorem frozenIndexIdentity_holds (c : Context) (η : LogicalEnv) : frozenIndexIdentity.Holds c η := by
  simp [frozenIndexIdentity, Post.Holds, indexZero, Assertion.Holds, Atom.Holds,
    Expression.eval, Term.eval, pushIndex]

/-- A precise obstruction to unrestricted textual instantiation, even where
both readings are defined and the body contains no modality. -/
theorem textual_index_obstruction {e : Expression} {c : Context} {η : LogicalEnv}
    (hentry : e.eval c.entry c.entry η = some 0)
    (hcurrent : e.eval c.entry c.current η = some 1) :
    frozenIndexIdentity.Holds c η ∧ ¬ (textualIndexIdentity e).Holds c η := by
  refine ⟨frozenIndexIdentity_holds c η, ?_⟩
  simp [textualIndexIdentity, Post.Holds, expressionZero, Assertion.Holds, Atom.Holds,
    hentry, hcurrent, Expression.eval]

end Verification.Paper.TolerantFrames.TwoState
