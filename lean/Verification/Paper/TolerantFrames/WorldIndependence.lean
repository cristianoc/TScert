import Verification.Paper.TolerantFrames.AllSupport
import Verification.Paper.TolerantFrames.PostconditionSyntax

/-! # Only the modality reads the world

These equal-heap equivalences include existential binders. No common world
extension, root-role comparison or quantifier-freeness premise is required.
Two-state logical valuations stay fixed: a current witness is never required
to have existed at frozen entry.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge TolerantFrames

/-- Every assertion without a box reads only its environment, mark and heap. -/
theorem Formula.holds_heap {F : Formula} (hf : F.ModalityFree) {ρ m s t}
    (hh : s.h = t.h) : F.Holds ρ m s ↔ F.Holds ρ m t := by
  induction F generalizing ρ with
  | truth | falsity | atom _ | separated _ _ | apart _ _ | fresh _ =>
    simp only [Formula.Holds, Fresh, hh]
  | and F G ihF ihG => exact and_congr (ihF hf.1) (ihG hf.2)
  | or F G ihF ihG => exact or_congr (ihF hf.1) (ihG hf.2)
  | existsValue F ih => simp only [Formula.Holds, hh, ih hf]
  | box _ _ _ => exact hf.elim

/-- Definition 16, including every modality-free existential assertion. -/
theorem Formula.independent {F : Formula} (hf : F.ModalityFree) : Independent (Now F.meaning) :=
  fun _ _ _ _ _ _ _ _ _ _ _ hh _ => F.holds_heap hf hh

namespace TwoState

/-- Same ordinary reads; worlds and budgets may differ independently. -/
def SameHeapReads (s t : State) : Prop := s.env = t.env ∧ s.heap.h = t.heap.h

theorem Path.read_heap {s t : State} (he : SameHeapReads s t) (ν : Nat → Val) (p : Path) :
    p.read s ν = p.read t ν := by simp only [Path.read, he.1, he.2]

theorem BaseValue.eval_heap {s t : State} (he : SameHeapReads s t) (ν : Nat → Val) (v : BaseValue) :
    v.eval s ν = v.eval t ν := by cases v <;> simp only [BaseValue.eval, he.1]

theorem Value.eval_heap {s t : State} (he : SameHeapReads s t) (ν : Nat → Val) (v : Value) :
    v.eval s ν = v.eval t ν := by cases v <;> simp only [Value.eval, BaseValue.eval_heap he]

mutual
theorem Term.eval_heap {entry entry' focus focus' : State}
    (he : SameHeapReads entry entry') (hf : SameHeapReads focus focus') (η : LogicalEnv) (t : Term) :
    t.eval entry focus η = t.eval entry' focus' η := by
  cases t with
  | literal _ | index _ => rfl
  | path k p => simp only [Term.eval, Path.read_heap hf, hf.2]
  | element k p i fs valid => simp only [Term.eval, Path.read_heap hf, Expression.eval_heap he hf, hf.2]
  | old t => exact Term.eval_heap he he η t

theorem Expression.eval_heap {entry entry' focus focus' : State}
    (he : SameHeapReads entry entry') (hf : SameHeapReads focus focus') (η : LogicalEnv) (e : Expression) :
    e.eval entry focus η = e.eval entry' focus' η := by
  cases e with
  | constant _ => rfl
  | scale _ _ => simp only [Expression.eval, Term.eval_heap he hf]
  | add _ _ => simp only [Expression.eval, Expression.eval_heap he hf]
end

theorem BodyTerm.eval_heap {entry entry' focus focus' : State}
    (he : SameHeapReads entry entry') (hf : SameHeapReads focus focus') (η : LogicalEnv) (z : Val) (i : Int) (t : BodyTerm) :
    t.eval entry focus η z i = t.eval entry' focus' η z i := by
  cases t <;> simp only [BodyTerm.eval, hf.2, Term.eval_heap he hf]

theorem BodyExpression.eval_heap {entry entry' focus focus' : State}
    (he : SameHeapReads entry entry') (hf : SameHeapReads focus focus') (η : LogicalEnv) (z : Val) (i : Int) (e : BodyExpression) :
    e.eval entry focus η z i = e.eval entry' focus' η z i := by
  induction e with
  | constant _ => rfl
  | scale _ _ => simp only [BodyExpression.eval, BodyTerm.eval_heap he hf]
  | add _ _ ih₁ ih₂ => simp only [BodyExpression.eval, ih₁, ih₂]

theorem Clause.holds_heap {entry entry' focus focus' : State}
    (he : SameHeapReads entry entry') (hf : SameHeapReads focus focus') (η : LogicalEnv) (z : Val) (i : Int) (c : Clause) :
    c.Holds entry focus η z i ↔ c.Holds entry' focus' η z i := by
  induction c with
  | le _ _ => simp only [Clause.Holds, BodyExpression.eval_heap he hf]
  | or _ _ ih₁ ih₂ => exact or_congr ih₁ ih₂

theorem Body.holds_heap {entry entry' focus focus' : State}
    (he : SameHeapReads entry entry') (hf : SameHeapReads focus focus') (η : LogicalEnv) (z : Val) (i : Int) (b : Body) :
    b.Holds entry focus η z i ↔ b.Holds entry' focus' η z i := by
  induction b with
  | clause c => exact c.holds_heap he hf η z i
  | and _ _ ih₁ ih₂ => exact and_congr ih₁ ih₂

theorem Atom.holds_heap {entry entry' focus focus' : State}
    (he : SameHeapReads entry entry') (hf : SameHeapReads focus focus') (η : LogicalEnv) (a : Atom) :
    a.Holds entry focus η ↔ a.Holds entry' focus' η := by
  cases a <;> simp only [Atom.Holds, Path.read_heap hf, Expression.eval_heap he hf,
    Value.eval_heap hf, Body.holds_heap he hf, hf.1, hf.2]

def Assertion.ModalityFree : Assertion → Prop
  | .and F G | .or F G => F.ModalityFree ∧ G.ModalityFree
  | .existsValue F => F.ModalityFree
  | .box _ _ => False
  | _ => True

theorem Assertion.holds_heap {F : Assertion} (hn : F.ModalityFree) {entry entry' focus focus' : State}
    (he : SameHeapReads entry entry') (hf : SameHeapReads focus focus') (m : Nat) (η : LogicalEnv) :
    F.Holds entry focus m η ↔ F.Holds entry' focus' m η := by
  induction F generalizing η with
  | truth | falsity => rfl
  | atom a => exact a.holds_heap he hf η
  | and _ _ ih₁ ih₂ => exact and_congr (ih₁ hn.1 η) (ih₂ hn.2 η)
  | or _ _ ih₁ ih₂ => exact or_congr (ih₁ hn.1 η) (ih₂ hn.2 η)
  | existsValue F ih => simp only [Assertion.Holds, hf.2, ih hn]
  | separated _ _ | apart _ _ | fresh _ => simp only [Assertion.Holds, Fresh, hf.1, hf.2]
  | box _ _ _ => exact hn.elim

/-- The modality-free fragment of postconditions excludes transition atoms,
which themselves read admissibility/worlds, and boxes in assertions. -/
def Post.HeapOnly : Post → Prop
  | .assertion F | .old F => F.ModalityFree
  | .transition _ => False
  | .and Q R | .or Q R | .implication Q R => Q.HeapOnly ∧ R.HeapOnly
  | .forallIndex Q | .forallValue Q => Q.HeapOnly

theorem Post.holds_heap {Q : Post} (hq : Q.HeapOnly) {c d : Context}
    (he : SameHeapReads c.entry d.entry) (hf : SameHeapReads c.current d.current) (hm : c.mark = d.mark)
    (η : LogicalEnv) : Q.Holds c η ↔ Q.Holds d η := by
  induction Q generalizing η with
  | assertion F => simpa only [Post.Holds, hm] using F.holds_heap hq he hf c.mark η
  | old F => simpa only [Post.Holds, hm] using F.holds_heap hq he he c.mark η
  | transition _ => exact hq.elim
  | and _ _ ih₁ ih₂ => exact and_congr (ih₁ hq.1 η) (ih₂ hq.2 η)
  | or _ _ ih₁ ih₂ => exact or_congr (ih₁ hq.1 η) (ih₂ hq.2 η)
  | implication _ _ ih₁ ih₂ => exact imp_congr (ih₁ hq.1 η) (ih₂ hq.2 η)
  | forallIndex Q ih => exact forall_congr' fun i => ih hq {η with indices := pushIndex i η.indices}
  | forallValue Q ih =>
    simp only [Post.Holds, hf.2]
    exact forall_congr' fun v => imp_congr Iff.rfl (imp_congr Iff.rfl (ih hq {η with values := push v η.values}))

/-- Ordinary value-quantifier reflexivity uses one heap domain at the
current focus, independently of any initial logical valuation or world. -/
theorem forall_exists_value (c : Context) (η : LogicalEnv) :
    (Post.forallValue (.assertion (.existsValue (.atom (.equal
      ⟨.value 0, []⟩ (.base (.root (.value 1)))))))).Holds c η := by
  intro v hs hr
  exact ⟨v, hs, hr, v, rfl, rfl⟩

/-- The exact Definition 16 independence premise of command Conj. -/
theorem Post.independent {Q : Post} (hq : Q.HeapOnly) (η : LogicalEnv) : Independent (Q.meaning η) := by
  intro ρ ρ' m s u v _ _ _ _ _ hh _
  exact Q.holds_heap (c := ⟨⟨ρ, s⟩, ⟨ρ', u⟩, m⟩) (d := ⟨⟨ρ, s⟩, ⟨ρ', v⟩, m⟩) hq ⟨rfl, rfl⟩ ⟨rfl, hh⟩ rfl η

end TwoState
end Verification.Paper.TolerantFrames
