import Verification.Paper.TolerantFrames.PostconditionSyntax

/-! # Semantic mark independence and its sufficient syntax check

Displayed Call uses assertions independent of the invocation mark. MarkFree is
only a structural sufficient check; a formula mentioning freshness can also be
semantically independent, for example fresh(r) or true. No arbitrary freshness
postcondition is silently transported to a caller's earlier mark.
-/
namespace Verification.Paper.TolerantFrames
open Verification TolerantFrames

def MarkIndependent (P : Assertion) : Prop := ∀ ρ s m k, P ρ m s ↔ P ρ k s

def PostMarkIndependent (Q : Postcondition) : Prop := ∀ ρ ρ' s t m k, Q ρ ρ' m s t ↔ Q ρ ρ' k s t

def Formula.MarkFree : Formula → Prop
  | .fresh _ => False
  | .and P Q | .or P Q => P.MarkFree ∧ Q.MarkFree
  | .existsValue P | .box _ P => P.MarkFree
  | _ => True

theorem Formula.markFree_independent {P : Formula} (free : P.MarkFree) : MarkIndependent P.meaning := by
  intro ρ s m k
  induction P generalizing ρ s with
  | truth | falsity | atom _ | separated _ _ | apart _ _ => rfl
  | fresh _ => exact free.elim
  | and P Q ihP ihQ => exact and_congr (ihP free.1 ρ s) (ihQ free.2 ρ s)
  | or P Q ihP ihQ => exact or_congr (ihP free.1 ρ s) (ihQ free.2 ρ s)
  | existsValue P ih =>
    exact exists_congr fun v => and_congr_right fun _ => and_congr_right fun _ => ih free (push v ρ) s
  | box Φ P ih => exact forall_congr' fun t => imp_congr Iff.rfl (ih free ρ t)

namespace TwoState

def Assertion.MarkFree : Assertion → Prop
  | .fresh _ => False
  | .and P Q | .or P Q => P.MarkFree ∧ Q.MarkFree
  | .existsValue P | .box _ P => P.MarkFree
  | _ => True

def Post.MarkFree : Post → Prop
  | .assertion P | .old P => P.MarkFree
  | .and P Q | .or P Q | .implication P Q => P.MarkFree ∧ Q.MarkFree
  | .forallIndex P | .forallValue P => P.MarkFree
  | .transition _ => True

theorem Assertion.markFree_holds {P : Assertion} (free : P.MarkFree)
    (entry focus : State) (η : LogicalEnv) (m k : Nat) :
    P.Holds entry focus m η ↔ P.Holds entry focus k η := by
  induction P generalizing focus η with
  | truth | falsity | atom _ | separated _ _ | apart _ _ => rfl
  | fresh _ => exact free.elim
  | and P Q ihP ihQ => exact and_congr (ihP free.1 focus η) (ihQ free.2 focus η)
  | or P Q ihP ihQ => exact or_congr (ihP free.1 focus η) (ihQ free.2 focus η)
  | existsValue P ih =>
    exact exists_congr fun v => and_congr_right fun _ => and_congr_right fun _ =>
      ih free focus {η with values := push v η.values}
  | box Φ P ih => exact forall_congr' fun t => imp_congr Iff.rfl (ih free {focus with heap := t} η)

theorem Post.markFree_holds {Q : Post} (free : Q.MarkFree) (c : Context) (η : LogicalEnv) (k : Nat) :
    Q.Holds c η ↔ Q.Holds {c with mark := k} η := by
  induction Q generalizing η with
  | assertion P => exact P.markFree_holds free c.entry c.current η c.mark k
  | old P => exact P.markFree_holds free c.entry c.entry η c.mark k
  | transition _ => rfl
  | and P Q ihP ihQ => exact and_congr (ihP free.1 η) (ihQ free.2 η)
  | or P Q ihP ihQ => exact or_congr (ihP free.1 η) (ihQ free.2 η)
  | implication P Q ihP ihQ => exact imp_congr (ihP free.1 η) (ihQ free.2 η)
  | forallIndex Q ih => exact forall_congr' fun i => ih free {η with indices := pushIndex i η.indices}
  | forallValue Q ih =>
    exact forall_congr' fun v => imp_congr_right fun _ => imp_congr_right fun _ =>
      ih free {η with values := push v η.values}

theorem Post.markFree_independent {Q : Post} (free : Q.MarkFree) (η : LogicalEnv) :
    PostMarkIndependent (Q.meaning η) := by
  intro ρ ρ' s t m k
  exact Q.markFree_holds free ⟨⟨ρ, s⟩, ⟨ρ', t⟩, m⟩ η k

end TwoState
end Verification.Paper.TolerantFrames
