import Verification.Paper.TolerantFrames.PaperTermForms
import Verification.Paper.TolerantFrames.QuantifiedRules

/-! # Qualified bridges from the auxiliary length readers

The reader is selected by the runtime category, not an arbitrary legacy
reading annotation. These equalities preserve partial definedness; they assume
no successful final length reading. The empty array/view suffix forms have no
legacy constructor, and use the canonical syntax directly.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge

/-- Array lengths retain the stronger array bound within the unified reader. -/
theorem lengthReading_array_range {h : Heap} {v : Val} {n : Int}
    (hk : lengthKind v = some .length) (he : lengthReading h v = some n) :
    0 ≤ n ∧ n ≤ maxArrayLength := by
  simp only [lengthReading, hk, Option.bind_some, kindValue] at he
  obtain ⟨_, es, _, _, rfl, hm⟩ := lengthOf_spine he
  exact ⟨by omega, by exact_mod_cast hm⟩

theorem Term.lengthPath_eval_of_kind {ρ : Env} {h : Heap} {p : Parity.Path} {v : Val} {k : Reading}
    (hp : p.read ρ h = some v) (hk : lengthKind v = some k) :
    (Term.lengthPath p).eval ρ h = (Term.path k p).eval ρ h := by
  simp only [Term.eval, hp, Option.bind_some, lengthReading, hk]

theorem Term.lengthElement_eval_of_kind {ρ : Env} {h : Heap} {p : Parity.Path} {e : Expression}
    {fs : List String} {k : Reading} (valid : k = .value ∨ k = .strLength ∨ fs ≠ [])
    {coll element value : Val} {i : Int}
    (hp : p.read ρ h = some coll) (hi : e.eval ρ h = some i)
    (he : elementValue h coll i = some element) (hf : readPath h element fs = some value)
    (hk : lengthKind value = some k) :
    (Term.lengthElement p e fs).eval ρ h = (Term.element k p e fs valid).eval ρ h := by
  simp only [Term.eval, hp, hi, he, hf, bind, Option.bind_some, lengthReading, hk]

theorem BodyTerm.lengthProject_eval_of_kind {ρ : Env} {h : Heap} {z : Val} {i : Int}
    {fs : List String} {k : Reading} (valid : k = .value ∨ k = .strLength ∨ fs ≠ [])
    {element value : Val} (he : elementValue h z i = some element)
    (hf : readPath h element fs = some value) (hk : lengthKind value = some k) :
    (BodyTerm.lengthProject fs).eval ρ h z i = (BodyTerm.project k fs valid).eval ρ h z i := by
  simp only [BodyTerm.eval, he, hf, Option.bind_some, lengthReading, hk]

/-- Instantiation preserves the canonical term forms at every body position. -/
theorem BodyTerm.instantiate_paperTerms {z : Parity.Path} {k : Expression} {t : BodyTerm}
    (hk : k.PaperTerms) (ht : t.PaperTerms) : (t.instantiate z k).PaperTerms := by
  cases t <;> simp_all [BodyTerm.instantiate, Expression.PaperTerms, Term.PaperTerms, BodyTerm.PaperTerms]

theorem Expression.scaleBy_paperTerms {e : Expression} (he : e.PaperTerms) (c : Int) :
    (e.scaleBy c).PaperTerms := by
  cases e with
  | constant _ => trivial
  | scale _ _ => exact he
  | add e f => exact ⟨Expression.scaleBy_paperTerms (e := e) he.1 c,
      Expression.scaleBy_paperTerms (e := f) he.2 c⟩

theorem BodyExpression.instantiate_paperTerms {z : Parity.Path} {k : Expression} {e : BodyExpression}
    (hk : k.PaperTerms) (he : e.PaperTerms) : (e.instantiate z k).PaperTerms := by
  induction e with
  | constant _ => trivial
  | scale c t => exact Expression.scaleBy_paperTerms (BodyTerm.instantiate_paperTerms hk he) c
  | add _ _ ih₁ ih₂ => exact ⟨ih₁ he.1, ih₂ he.2⟩

theorem Clause.instantiate_paperTerms {z : Parity.Path} {k : Expression} {c : Clause}
    (hk : k.PaperTerms) (hc : c.PaperTerms) : (c.instantiate z k).PaperTerms := by
  induction c with
  | le _ _ => exact ⟨BodyExpression.instantiate_paperTerms hk hc.1, BodyExpression.instantiate_paperTerms hk hc.2⟩
  | or _ _ ih₁ ih₂ => exact ⟨ih₁ hc.1, ih₂ hc.2⟩

theorem Body.instantiate_paperTerms {z : Parity.Path} {k : Expression} {b : Body}
    (hk : k.PaperTerms) (hb : b.PaperTerms) : (b.instantiate z k).PaperTerms := by
  induction b with
  | clause _ => exact Clause.instantiate_paperTerms hk hb
  | and _ _ ih₁ ih₂ => exact ⟨ih₁ hb.1, ih₂ hb.2⟩

namespace TwoState

theorem Term.lengthPath_eval_of_kind {entry focus : State} {η : LogicalEnv} {p : Path} {v : Val} {k : Reading}
    (hp : p.read focus η.values = some v) (hk : lengthKind v = some k) :
    (Term.lengthPath p).eval entry focus η = (Term.path k p).eval entry focus η := by
  simp only [Term.eval, hp, Option.bind_some, lengthReading, hk]

theorem Term.lengthElement_eval_of_kind {entry focus : State} {η : LogicalEnv} {p : Path} {e : Expression}
    {fs : List String} {k : Reading} (valid : k = .value ∨ k = .strLength ∨ fs ≠ [])
    {coll element value : Val} {i : Int}
    (hp : p.read focus η.values = some coll) (hi : e.eval entry focus η = some i)
    (he : elementValue focus.heap.h coll i = some element)
    (hf : readPath focus.heap.h element fs = some value) (hk : lengthKind value = some k) :
    (Term.lengthElement p e fs).eval entry focus η = (Term.element k p e fs valid).eval entry focus η := by
  simp only [Term.eval, hp, hi, he, hf, bind, Option.bind_some, lengthReading, hk]

theorem BodyTerm.lengthProject_eval_of_kind {entry focus : State} {η : LogicalEnv} {z : Val} {i : Int}
    {fs : List String} {k : Reading} (valid : k = .value ∨ k = .strLength ∨ fs ≠ [])
    {element value : Val} (he : elementValue focus.heap.h z i = some element)
    (hf : readPath focus.heap.h element fs = some value) (hk : lengthKind value = some k) :
    (BodyTerm.lengthProject fs).eval entry focus η z i = (BodyTerm.project k fs valid).eval entry focus η z i := by
  simp only [BodyTerm.eval, he, hf, Option.bind_some, lengthReading, hk]

end TwoState
end Verification.Paper.TolerantFrames
