import Verification.Paper.TolerantFrames.PostconditionSyntax

/-! # Paper term forms inside the auxiliary syntax

Canonical lengths use one runtime-dispatched operator. The old sorted length
readers remain auxiliary forms for existing semantic bridges. This predicate
checks term forms recursively, including free body terms, binders and old.
Scope, declared-region admission and receiver typing are separate judgments.
-/
namespace Verification.Paper.TolerantFrames

mutual
def Term.PaperTerms : Term → Prop
  | .literal _ | .lengthPath _ => True
  | .path k _ => k = .value
  | .element k _ e _ _ => k = .value ∧ e.PaperTerms
  | .lengthElement _ e _ => e.PaperTerms

def Expression.PaperTerms : Expression → Prop
  | .constant _ => True
  | .scale _ t => t.PaperTerms
  | .add e f => e.PaperTerms ∧ f.PaperTerms
end

def BodyTerm.PaperTerms : BodyTerm → Prop
  | .index | .element _ | .lengthProject _ => True
  | .project k _ _ => k = .value
  | .free t => t.PaperTerms

def BodyExpression.PaperTerms : BodyExpression → Prop
  | .constant _ => True
  | .scale _ t => t.PaperTerms
  | .add e f => e.PaperTerms ∧ f.PaperTerms

def Clause.PaperTerms : Clause → Prop
  | .le e f => e.PaperTerms ∧ f.PaperTerms
  | .or c d => c.PaperTerms ∧ d.PaperTerms

def Body.PaperTerms : Body → Prop
  | .clause c => c.PaperTerms
  | .and b c => b.PaperTerms ∧ c.PaperTerms

def Atom.PaperTerms : Atom → Prop
  | .le e f => e.PaperTerms ∧ f.PaperTerms
  | .dense _ e | .element _ e _ => e.PaperTerms
  | .every _ e b => e.PaperTerms ∧ b.PaperTerms
  | _ => True

def Formula.PaperTerms : Formula → Prop
  | .atom a => a.PaperTerms
  | .and F G | .or F G => F.PaperTerms ∧ G.PaperTerms
  | .existsValue F | .box _ F => F.PaperTerms
  | _ => True

namespace TwoState

mutual
def Term.PaperTerms : Term → Prop
  | .literal _ | .index _ | .lengthPath _ => True
  | .path k _ => k = .value
  | .element k _ e _ _ => k = .value ∧ e.PaperTerms
  | .lengthElement _ e _ => e.PaperTerms
  | .old t => t.PaperTerms

def Expression.PaperTerms : Expression → Prop
  | .constant _ => True
  | .scale _ t => t.PaperTerms
  | .add e f => e.PaperTerms ∧ f.PaperTerms
end

def BodyTerm.PaperTerms : BodyTerm → Prop
  | .index | .element _ | .lengthProject _ => True
  | .project k _ _ => k = .value
  | .free t => t.PaperTerms

def BodyExpression.PaperTerms : BodyExpression → Prop
  | .constant _ => True
  | .scale _ t => t.PaperTerms
  | .add e f => e.PaperTerms ∧ f.PaperTerms

def Clause.PaperTerms : Clause → Prop
  | .le e f => e.PaperTerms ∧ f.PaperTerms
  | .or c d => c.PaperTerms ∧ d.PaperTerms

def Body.PaperTerms : Body → Prop
  | .clause c => c.PaperTerms
  | .and b c => b.PaperTerms ∧ c.PaperTerms

def Atom.PaperTerms : Atom → Prop
  | .le e f => e.PaperTerms ∧ f.PaperTerms
  | .dense _ e | .element _ e _ => e.PaperTerms
  | .every _ e b => e.PaperTerms ∧ b.PaperTerms
  | _ => True

def Assertion.PaperTerms : Assertion → Prop
  | .atom a => a.PaperTerms
  | .and F G | .or F G => F.PaperTerms ∧ G.PaperTerms
  | .existsValue F | .box _ F => F.PaperTerms
  | _ => True

def Post.PaperTerms : Post → Prop
  | .assertion F | .old F => F.PaperTerms
  | .and Q R | .or Q R | .implication Q R => Q.PaperTerms ∧ R.PaperTerms
  | .forallIndex Q | .forallValue Q => Q.PaperTerms
  | .transition _ => True

end TwoState
end Verification.Paper.TolerantFrames
