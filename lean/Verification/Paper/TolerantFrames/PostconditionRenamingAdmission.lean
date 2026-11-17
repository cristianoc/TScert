import Verification.Paper.TolerantFrames.PostconditionRenamingScopes
import Verification.Paper.TolerantFrames.RenamingAdmission

/-! # Declared admission of program-renamed postconditions

The existing declaration pullback is reused. The logical-value declaration
shift commutes with program-only renaming of even/odd roots, so no fresh
logical witness acquires a program declaration. Nested-old restrictions and
both phase-specific declaration contexts are preserved.
-/
namespace Verification.Paper.TolerantFrames.TwoState
open Verification Footprints HeapKnowledge TolerantFrames

theorem program_encoded_odd (σ : Nat → Nat) {x : Nat} (hx : x % 2 ≠ 0) :
    (programMap σ id id).encoded x = x := by
  simp only [Renaming.encoded, if_neg hx]
  change 2 * (x / 2) + 1 = x
  omega

theorem parent_program_encoded (σ : Nat → Nat) (x : Nat) :
    parentValueRoot ((programMap σ id id).encoded x) =
      (parentValueRoot x).map (programMap σ id id).encoded := by
  by_cases he : x % 2 = 0
  · simp [parentValueRoot, Renaming.encoded, he]
  · rw [program_encoded_odd σ he]
    simp only [parentValueRoot, if_neg he]
    by_cases hx : x = 1
    · simp [hx]
    · simp only [if_neg hx, Option.map_some]
      congr 1
      exact (program_encoded_odd σ (by omega)).symm

private theorem parent_predicate_program (σ : Nat → Nat) (x : Nat) (P : Nat → Prop) :
    (∃ y, parentValueRoot x = some y ∧ P ((programMap σ id id).encoded y)) ↔
      ∃ y, parentValueRoot ((programMap σ id id).encoded x) = some y ∧ P y := by
  rw [parent_program_encoded]
  simp only [Option.map_eq_some_iff]
  constructor
  · rintro ⟨y, hy, hp⟩
    exact ⟨_, ⟨y, hy, rfl⟩, hp⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, hp⟩
    exact ⟨y, hy, hp⟩

theorem underLogicalValue_program_pullback (σ : Nat → Nat) (types : DeclaredPaths) :
    underLogicalValue (types.pullback (programMap σ id id).encoded) =
      (underLogicalValue types).pullback (programMap σ id id).encoded := by
  unfold underLogicalValue DeclaredPaths.pullback
  congr 1
  · funext p
    exact propext (parent_predicate_program σ p.root (fun x => types.collection ⟨x, p.fields⟩))
  · funext p
    exact propext (parent_predicate_program σ p.root (fun x => types.object ⟨x, p.fields⟩))
  · funext p f
    exact propext (parent_predicate_program σ p.root (fun x => types.field ⟨x, p.fields⟩ f))

mutual
theorem Term.noOld_rename (σ : Renaming) (t : Term) : (t.rename σ).NoOld ↔ t.NoOld := by
  cases t with
  | element _ _ e _ _ => exact Expression.noOld_rename σ e
  | _ => rfl

theorem Expression.noOld_rename (σ : Renaming) (e : Expression) : (e.rename σ).NoOld ↔ e.NoOld := by
  cases e with
  | constant _ => rfl
  | scale _ t => exact t.noOld_rename σ
  | add e f => exact and_congr (e.noOld_rename σ) (f.noOld_rename σ)
end

mutual
theorem Term.wellFormed_rename (σ : Renaming) (t : Term) : (t.rename σ).WellFormed ↔ t.WellFormed := by
  cases t with
  | element _ _ e _ _ => exact Expression.wellFormed_rename σ e
  | old t => exact t.noOld_rename σ
  | _ => rfl

theorem Expression.wellFormed_rename (σ : Renaming) (e : Expression) : (e.rename σ).WellFormed ↔ e.WellFormed := by
  cases e with
  | constant _ => rfl
  | scale _ t => exact t.wellFormed_rename σ
  | add e f => exact and_congr (e.wellFormed_rename σ) (f.wellFormed_rename σ)
end

theorem BodyTerm.noOld_rename (σ : Renaming) (t : BodyTerm) : (t.rename σ).NoOld ↔ t.NoOld := by
  cases t with | free t => exact t.noOld_rename σ | _ => rfl

theorem BodyTerm.wellFormed_rename (σ : Renaming) (t : BodyTerm) : (t.rename σ).WellFormed ↔ t.WellFormed := by
  cases t with | free t => exact t.wellFormed_rename σ | _ => rfl

theorem BodyExpression.noOld_rename (σ : Renaming) (e : BodyExpression) : (e.rename σ).NoOld ↔ e.NoOld := by
  induction e with
  | constant _ => rfl
  | scale _ t => exact t.noOld_rename σ
  | add _ _ ih₁ ih₂ => exact and_congr ih₁ ih₂

theorem BodyExpression.wellFormed_rename (σ : Renaming) (e : BodyExpression) : (e.rename σ).WellFormed ↔ e.WellFormed := by
  induction e with
  | constant _ => rfl
  | scale _ t => exact t.wellFormed_rename σ
  | add _ _ ih₁ ih₂ => exact and_congr ih₁ ih₂

theorem Clause.noOld_rename (σ : Renaming) (c : Clause) : (c.rename σ).NoOld ↔ c.NoOld := by
  induction c with
  | le e f => exact and_congr (e.noOld_rename σ) (f.noOld_rename σ)
  | or _ _ ih₁ ih₂ => exact and_congr ih₁ ih₂

theorem Clause.wellFormed_rename (σ : Renaming) (c : Clause) : (c.rename σ).WellFormed ↔ c.WellFormed := by
  induction c with
  | le e f => exact and_congr (e.wellFormed_rename σ) (f.wellFormed_rename σ)
  | or _ _ ih₁ ih₂ => exact and_congr ih₁ ih₂

theorem Body.noOld_rename (σ : Renaming) (b : Body) : (b.rename σ).NoOld ↔ b.NoOld := by
  induction b with
  | clause c => exact c.noOld_rename σ
  | and _ _ ih₁ ih₂ => exact and_congr ih₁ ih₂

theorem Body.wellFormed_rename (σ : Renaming) (b : Body) : (b.rename σ).WellFormed ↔ b.WellFormed := by
  induction b with
  | clause c => exact c.wellFormed_rename σ
  | and _ _ ih₁ ih₂ => exact and_congr ih₁ ih₂

theorem Atom.noOld_rename (σ : Renaming) (a : Atom) : (a.rename σ).NoOld ↔ a.NoOld := by
  cases a with
  | le e f => exact and_congr (e.noOld_rename σ) (f.noOld_rename σ)
  | dense _ e | element _ e _ => exact e.noOld_rename σ
  | every _ e b => exact and_congr (e.noOld_rename σ) (b.noOld_rename σ)
  | _ => rfl

theorem Atom.wellFormed_rename (σ : Renaming) (a : Atom) : (a.rename σ).WellFormed ↔ a.WellFormed := by
  cases a with
  | le e f => exact and_congr (e.wellFormed_rename σ) (f.wellFormed_rename σ)
  | dense _ e | element _ e _ => exact e.wellFormed_rename σ
  | every _ e b => exact and_congr (e.wellFormed_rename σ) (b.wellFormed_rename σ)
  | _ => rfl

theorem Assertion.noOld_rename (σ : Renaming) (F : Assertion) : (F.rename σ).NoOld ↔ F.NoOld := by
  induction F generalizing σ with
  | atom a => exact a.noOld_rename σ
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ => exact and_congr (ih₁ σ) (ih₂ σ)
  | existsValue _ ih => exact ih σ.liftValue
  | box _ _ ih => exact ih σ
  | _ => rfl

theorem Assertion.WellFormed.rename_program {σ : Nat → Nat} {types : DeclaredPaths} {F : Assertion}
    (hF : F.WellFormed (types.pullback (programMap σ id id).encoded)) :
    (F.rename (programMap σ id id)).WellFormed types := by
  induction F generalizing types with
  | truth | falsity | separated _ _ | apart _ _ => trivial
  | atom a => exact (a.wellFormed_rename _).mpr hF
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ => exact ⟨ih₁ hF.1, ih₂ hF.2⟩
  | existsValue _ ih =>
    simp only [Assertion.rename, programMap_liftValue, Assertion.WellFormed]
    apply ih
    rw [← underLogicalValue_program_pullback]
    exact hF
  | fresh _ => exact RegionWellFormed.rename hF
  | box _ _ ih => exact ⟨EffectWellFormed.rename hF.1, ih hF.2⟩

theorem Post.WellFormed.rename_program {σ : Nat → Nat} {entryTypes currentTypes : DeclaredPaths} {Q : Post}
    (hQ : Q.WellFormed (entryTypes.pullback (programMap σ id id).encoded) (currentTypes.pullback (programMap σ id id).encoded)) :
    (Q.rename (programMap σ id id)).WellFormed entryTypes currentTypes := by
  induction Q generalizing entryTypes currentTypes with
  | assertion _ => exact Assertion.WellFormed.rename_program hQ
  | old F => exact ⟨(F.noOld_rename _).mpr hQ.1, Assertion.WellFormed.rename_program hQ.2⟩
  | transition _ => exact EffectWellFormed.rename hQ
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | implication _ _ ih₁ ih₂ => exact ⟨ih₁ hQ.1, ih₂ hQ.2⟩
  | forallIndex _ ih => simpa only [Post.rename, programMap_liftIndex, Post.WellFormed] using ih hQ
  | forallValue _ ih =>
    simp only [Post.rename, programMap_liftValue, Post.WellFormed]
    apply ih
    rw [← underLogicalValue_program_pullback, ← underLogicalValue_program_pullback]
    exact hQ

/-- Scope, phase and declared-region admission all transport together. -/
theorem Post.Admitted.rename_program {σ : Nat → Nat} {Γ Δ : Nat → Prop} {entryTypes currentTypes : DeclaredPaths} {Q : Post}
    (hQ : Q.Admitted (fun x => Γ (σ x)) (fun x => Δ (σ x))
      (entryTypes.pullback (programMap σ id id).encoded) (currentTypes.pullback (programMap σ id id).encoded)) :
    (Q.rename (programMap σ id id)).Admitted Γ Δ entryTypes currentTypes :=
  ⟨Post.Scoped.rename_program hQ.1, Post.WellFormed.rename_program hQ.2⟩

end Verification.Paper.TolerantFrames.TwoState
