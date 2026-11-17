import Verification.Paper.TolerantFrames.PostconditionProgramRenaming

/-! # Scope preservation by program renaming

Only free program names change. Logical values and mathematical indices retain
their binders; entry and current program scopes are pulled back separately.
-/
namespace Verification.Paper.TolerantFrames.TwoState
open Verification Footprints HeapKnowledge TolerantFrames

theorem liftRenaming_id : liftRenaming id = id := by funext x; cases x <;> rfl

theorem programMap_liftValue (σ : Nat → Nat) : (programMap σ id id).liftValue = programMap σ id id := by
  simp only [Renaming.liftValue, liftRenaming_id]

theorem programMap_liftIndex (σ : Nat → Nat) : (programMap σ id id).liftIndex = programMap σ id id := by
  simp only [Renaming.liftIndex, liftRenaming_id]

theorem Root.Scoped.rename_program {Γ : Nat → Prop} {values : Nat} {σ : Nat → Nat} {r : Root}
    (h : r.Scoped (fun x => Γ (σ x)) values) : (r.rename (programMap σ id id)).Scoped Γ values := by
  cases r <;> exact h

theorem Path.Scoped.rename_program {Γ : Nat → Prop} {values : Nat} {σ : Nat → Nat} {p : Path}
    (h : p.Scoped (fun x => Γ (σ x)) values) : (p.rename (programMap σ id id)).Scoped Γ values :=
  Root.Scoped.rename_program h

theorem BaseValue.Scoped.rename_program {Γ : Nat → Prop} {values : Nat} {σ : Nat → Nat} {v : BaseValue}
    (h : v.Scoped (fun x => Γ (σ x)) values) : (v.rename (programMap σ id id)).Scoped Γ values := by
  cases v with | root _ => exact Root.Scoped.rename_program h | literal _ => trivial

theorem Value.Scoped.rename_program {Γ : Nat → Prop} {values : Nat} {σ : Nat → Nat} {v : Value}
    (h : v.Scoped (fun x => Γ (σ x)) values) : (v.rename (programMap σ id id)).Scoped Γ values := by
  cases v <;> exact BaseValue.Scoped.rename_program h

mutual
theorem Term.Scoped.rename_program {Γ Δ : Nat → Prop} {indices values : Nat} {σ : Nat → Nat} {t : Term}
    (h : t.Scoped (fun x => Γ (σ x)) (fun x => Δ (σ x)) indices values) :
    (t.rename (programMap σ id id)).Scoped Γ Δ indices values := by
  cases t with
  | literal _ => trivial
  | index _ => exact h
  | path _ _ => exact Path.Scoped.rename_program h
  | element _ _ _ _ _ => exact ⟨Path.Scoped.rename_program h.1, Expression.Scoped.rename_program h.2⟩
  | old t => exact Term.Scoped.rename_program (t := t) (Δ := Γ) h

theorem Expression.Scoped.rename_program {Γ Δ : Nat → Prop} {indices values : Nat} {σ : Nat → Nat} {e : Expression}
    (h : e.Scoped (fun x => Γ (σ x)) (fun x => Δ (σ x)) indices values) :
    (e.rename (programMap σ id id)).Scoped Γ Δ indices values := by
  cases e with
  | constant _ => trivial
  | scale _ _ => exact Term.Scoped.rename_program h
  | add _ _ => exact ⟨Expression.Scoped.rename_program h.1, Expression.Scoped.rename_program h.2⟩
end

theorem BodyTerm.Scoped.rename_program {Γ Δ : Nat → Prop} {indices values : Nat} {σ : Nat → Nat} {t : BodyTerm}
    (h : t.Scoped (fun x => Γ (σ x)) (fun x => Δ (σ x)) indices values) :
    (t.rename (programMap σ id id)).Scoped Γ Δ indices values := by
  cases t with | free _ => exact Term.Scoped.rename_program h | _ => trivial

theorem BodyExpression.Scoped.rename_program {Γ Δ : Nat → Prop} {indices values : Nat} {σ : Nat → Nat} {e : BodyExpression}
    (h : e.Scoped (fun x => Γ (σ x)) (fun x => Δ (σ x)) indices values) :
    (e.rename (programMap σ id id)).Scoped Γ Δ indices values := by
  induction e with
  | constant _ => trivial
  | scale _ _ => exact BodyTerm.Scoped.rename_program h
  | add _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem Clause.Scoped.rename_program {Γ Δ : Nat → Prop} {indices values : Nat} {σ : Nat → Nat} {c : Clause}
    (h : c.Scoped (fun x => Γ (σ x)) (fun x => Δ (σ x)) indices values) :
    (c.rename (programMap σ id id)).Scoped Γ Δ indices values := by
  induction c with
  | le _ _ => exact ⟨BodyExpression.Scoped.rename_program h.1, BodyExpression.Scoped.rename_program h.2⟩
  | or _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem Body.Scoped.rename_program {Γ Δ : Nat → Prop} {indices values : Nat} {σ : Nat → Nat} {b : Body}
    (h : b.Scoped (fun x => Γ (σ x)) (fun x => Δ (σ x)) indices values) :
    (b.rename (programMap σ id id)).Scoped Γ Δ indices values := by
  induction b with
  | clause _ => exact Clause.Scoped.rename_program h
  | and _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem Atom.Scoped.rename_program {Γ Δ : Nat → Prop} {indices values : Nat} {σ : Nat → Nat} {a : Atom}
    (h : a.Scoped (fun x => Γ (σ x)) (fun x => Δ (σ x)) indices values) :
    (a.rename (programMap σ id id)).Scoped Γ Δ indices values := by
  cases a with
  | le _ _ => exact ⟨Expression.Scoped.rename_program h.1, Expression.Scoped.rename_program h.2⟩
  | equal _ _ | optionalEqual _ _ _ => exact ⟨Path.Scoped.rename_program h.1, Value.Scoped.rename_program h.2⟩
  | dense _ _ => exact ⟨Root.Scoped.rename_program h.1, Expression.Scoped.rename_program h.2⟩
  | contents _ _ => exact Path.Scoped.rename_program h
  | element _ _ _ => exact ⟨Path.Scoped.rename_program h.1, Expression.Scoped.rename_program h.2.1, Value.Scoped.rename_program h.2.2⟩
  | every _ _ _ => exact ⟨Path.Scoped.rename_program h.1, Expression.Scoped.rename_program h.2.1, Body.Scoped.rename_program h.2.2⟩

theorem regionScoped_program {Γ : Nat → Prop} {values : Nat} {σ : Nat → Nat} {r : Region}
    (h : RegionScoped (fun x => Γ (σ x)) values r) : RegionScoped Γ values (r.rename (programMap σ id id).encoded) := by
  induction r with
  | field x _ | fields x | cells x | path x _ _ | pathFields x _ | pathCells x _ | spine x _ =>
    by_cases hx : x % 2 = 0
    · simpa [Region.rename, RegionScoped, Renaming.encoded, hx] using h
    · have hd : (2 * (x / 2) + 1) / 2 = x / 2 := by omega
      simpa [Region.rename, RegionScoped, Renaming.encoded, hx, Nat.add_mod, hd] using h
  | cls _ | all => trivial
  | inCls _ _ ih => exact ih h

theorem effectScoped_program {Γ : Nat → Prop} {values : Nat} {σ : Nat → Nat} {Φ : Footprint}
    (h : EffectScoped (fun x => Γ (σ x)) values Φ) :
    EffectScoped Γ values (Footprint.rename (programMap σ id id).encoded Φ) := by
  intro e he
  obtain ⟨original, hm, heq⟩ := List.mem_map.mp he
  subst e
  exact regionScoped_program (h original hm)

theorem Assertion.Scoped.rename_program {Γ Δ : Nat → Prop} {indices values : Nat} {σ : Nat → Nat} {F : Assertion}
    (h : F.Scoped (fun x => Γ (σ x)) (fun x => Δ (σ x)) indices values) :
    (F.rename (programMap σ id id)).Scoped Γ Δ indices values := by
  induction F generalizing values with
  | truth | falsity => trivial
  | atom _ => exact Atom.Scoped.rename_program h
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | existsValue _ ih => simpa only [Assertion.rename, programMap_liftValue, Assertion.Scoped] using ih h
  | separated _ _ => exact ⟨Path.Scoped.rename_program h.1, Path.Scoped.rename_program h.2⟩
  | apart _ _ => exact ⟨Root.Scoped.rename_program h.1, Root.Scoped.rename_program h.2⟩
  | fresh _ => exact regionScoped_program h
  | box _ _ ih => exact ⟨effectScoped_program h.1, ih h.2⟩

theorem Post.Scoped.rename_program {Γ Δ : Nat → Prop} {indices values : Nat} {σ : Nat → Nat} {Q : Post}
    (h : Q.Scoped (fun x => Γ (σ x)) (fun x => Δ (σ x)) indices values) :
    (Q.rename (programMap σ id id)).Scoped Γ Δ indices values := by
  induction Q generalizing indices values with
  | assertion _ | old _ => exact Assertion.Scoped.rename_program h
  | transition _ => exact effectScoped_program h
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | implication _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | forallIndex _ ih => simpa only [Post.rename, programMap_liftIndex, Post.Scoped] using ih h
  | forallValue _ ih => simpa only [Post.rename, programMap_liftValue, Post.Scoped] using ih h

end Verification.Paper.TolerantFrames.TwoState
