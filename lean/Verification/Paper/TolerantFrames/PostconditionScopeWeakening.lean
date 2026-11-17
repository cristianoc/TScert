import Verification.Paper.TolerantFrames.PostconditionSyntax

/-! # Weakening program scopes

Scope tracks names actually mentioned, so extending either program scope never
invalidates syntax. Logical binder depths remain explicit and unchanged.
-/
namespace Verification.Paper.TolerantFrames.TwoState
open Verification Footprints HeapKnowledge TolerantFrames

theorem Root.Scoped.weaken {Γ Δ : Nat → Prop} {v r} (hm : ∀ x, Γ x → Δ x) (h : Root.Scoped Γ v r) : r.Scoped Δ v := by
  cases r with | program x => exact hm x h | value _ => exact h

theorem Path.Scoped.weaken {Γ Δ : Nat → Prop} {v p} (hm : ∀ x, Γ x → Δ x) (h : Path.Scoped Γ v p) : p.Scoped Δ v := Root.Scoped.weaken hm h

theorem BaseValue.Scoped.weaken {Γ Δ : Nat → Prop} {v a} (hm : ∀ x, Γ x → Δ x) (h : BaseValue.Scoped Γ v a) : a.Scoped Δ v := by
  cases a with | root _ => exact Root.Scoped.weaken hm h | literal _ => trivial

theorem Value.Scoped.weaken {Γ Δ : Nat → Prop} {v a} (hm : ∀ x, Γ x → Δ x) (h : Value.Scoped Γ v a) : a.Scoped Δ v := by
  cases a <;> exact BaseValue.Scoped.weaken hm h

mutual
theorem Term.Scoped.weaken {Γ Δ Γ' Δ' : Nat → Prop} {i v t}
    (he : ∀ x, Γ x → Γ' x) (hc : ∀ x, Δ x → Δ' x) (h : Term.Scoped Γ Δ i v t) : t.Scoped Γ' Δ' i v := by
  cases t with
  | literal _ => trivial
  | index _ => exact h
  | path _ _ | lengthPath _ => exact Path.Scoped.weaken hc h
  | element _ _ _ _ _ | lengthElement _ _ _ => exact ⟨Path.Scoped.weaken hc h.1, Expression.Scoped.weaken he hc h.2⟩
  | old t => exact Term.Scoped.weaken (t := t) he he h

theorem Expression.Scoped.weaken {Γ Δ Γ' Δ' : Nat → Prop} {i v e}
    (he : ∀ x, Γ x → Γ' x) (hc : ∀ x, Δ x → Δ' x) (h : Expression.Scoped Γ Δ i v e) : e.Scoped Γ' Δ' i v := by
  cases e with
  | constant _ => trivial
  | scale _ _ => exact Term.Scoped.weaken he hc h
  | add _ _ => exact ⟨Expression.Scoped.weaken he hc h.1, Expression.Scoped.weaken he hc h.2⟩
end

theorem BodyTerm.Scoped.weaken {Γ Δ Γ' Δ' : Nat → Prop} {i v t}
    (he : ∀ x, Γ x → Γ' x) (hc : ∀ x, Δ x → Δ' x) (h : BodyTerm.Scoped Γ Δ i v t) : t.Scoped Γ' Δ' i v := by
  cases t with | free _ => exact Term.Scoped.weaken he hc h | _ => trivial

theorem BodyExpression.Scoped.weaken {Γ Δ Γ' Δ' : Nat → Prop} {i v e}
    (he : ∀ x, Γ x → Γ' x) (hc : ∀ x, Δ x → Δ' x) (h : BodyExpression.Scoped Γ Δ i v e) : e.Scoped Γ' Δ' i v := by
  induction e with
  | constant _ => trivial
  | scale _ _ => exact BodyTerm.Scoped.weaken he hc h
  | add _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem Clause.Scoped.weaken {Γ Δ Γ' Δ' : Nat → Prop} {i v c}
    (he : ∀ x, Γ x → Γ' x) (hc : ∀ x, Δ x → Δ' x) (h : Clause.Scoped Γ Δ i v c) : c.Scoped Γ' Δ' i v := by
  induction c with
  | le _ _ => exact ⟨BodyExpression.Scoped.weaken he hc h.1, BodyExpression.Scoped.weaken he hc h.2⟩
  | or _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem Body.Scoped.weaken {Γ Δ Γ' Δ' : Nat → Prop} {i v b}
    (he : ∀ x, Γ x → Γ' x) (hc : ∀ x, Δ x → Δ' x) (h : Body.Scoped Γ Δ i v b) : b.Scoped Γ' Δ' i v := by
  induction b with
  | clause _ => exact Clause.Scoped.weaken he hc h
  | and _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem Atom.Scoped.weaken {Γ Δ Γ' Δ' : Nat → Prop} {i v a}
    (he : ∀ x, Γ x → Γ' x) (hc : ∀ x, Δ x → Δ' x) (h : Atom.Scoped Γ Δ i v a) : a.Scoped Γ' Δ' i v := by
  cases a with
  | le _ _ => exact ⟨Expression.Scoped.weaken he hc h.1, Expression.Scoped.weaken he hc h.2⟩
  | equal _ _ | optionalEqual _ _ _ => exact ⟨Path.Scoped.weaken hc h.1, Value.Scoped.weaken hc h.2⟩
  | dense _ _ => exact ⟨Root.Scoped.weaken hc h.1, Expression.Scoped.weaken he hc h.2⟩
  | contents _ _ => exact Path.Scoped.weaken hc h
  | element _ _ _ => exact ⟨Path.Scoped.weaken hc h.1, Expression.Scoped.weaken he hc h.2.1, Value.Scoped.weaken hc h.2.2⟩
  | every _ _ _ => exact ⟨Path.Scoped.weaken hc h.1, Expression.Scoped.weaken he hc h.2.1, Body.Scoped.weaken he hc h.2.2⟩

theorem regionScoped_weaken {Γ Δ : Nat → Prop} {v r} (hm : ∀ x, Γ x → Δ x) (h : RegionScoped Γ v r) : RegionScoped Δ v r := by
  induction r with
  | field x _ | fields x | cells x | path x _ _ | pathFields x _ | pathCells x _ | spine x _ =>
    by_cases hx : x % 2 = 0
    · simp only [RegionScoped, if_pos hx] at h ⊢
      exact hm _ h
    · simpa only [RegionScoped, if_neg hx] using h
  | cls _ | all => trivial
  | inCls _ _ ih => exact ih h

theorem effectScoped_weaken {Γ Δ : Nat → Prop} {v Φ} (hm : ∀ x, Γ x → Δ x) (h : EffectScoped Γ v Φ) : EffectScoped Δ v Φ :=
  fun e he => regionScoped_weaken hm (h e he)

theorem Assertion.Scoped.weaken {Γ Δ Γ' Δ' : Nat → Prop} {i v F}
    (he : ∀ x, Γ x → Γ' x) (hc : ∀ x, Δ x → Δ' x) (h : Assertion.Scoped Γ Δ i v F) : F.Scoped Γ' Δ' i v := by
  induction F generalizing v with
  | truth | falsity => trivial
  | atom _ => exact Atom.Scoped.weaken he hc h
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | existsValue _ ih => exact ih h
  | separated _ _ => exact ⟨Path.Scoped.weaken hc h.1, Path.Scoped.weaken hc h.2⟩
  | apart _ _ => exact ⟨Root.Scoped.weaken hc h.1, Root.Scoped.weaken hc h.2⟩
  | fresh _ => exact regionScoped_weaken hc h
  | box _ _ ih => exact ⟨effectScoped_weaken hc h.1, ih h.2⟩

theorem Post.Scoped.weaken {Γ Δ Γ' Δ' : Nat → Prop} {i v Q}
    (he : ∀ x, Γ x → Γ' x) (hc : ∀ x, Δ x → Δ' x) (h : Post.Scoped Γ Δ i v Q) : Q.Scoped Γ' Δ' i v := by
  induction Q generalizing i v with
  | assertion _ => exact Assertion.Scoped.weaken he hc h
  | old _ => exact Assertion.Scoped.weaken he he h
  | transition _ => exact effectScoped_weaken he h
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | implication _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | forallIndex _ ih | forallValue _ ih => exact ih h

end Verification.Paper.TolerantFrames.TwoState
