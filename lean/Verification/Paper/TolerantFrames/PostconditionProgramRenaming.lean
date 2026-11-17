import Verification.Paper.TolerantFrames.PostconditionRenaming

/-! # Program renamings depend only on names in scope

This extends the existing first-order scope judgment and capture-avoiding
renaming. The logical maps are common to both renamings and lift together at
binders. Unused program names may have arbitrary images, even when actual
arguments alias. Equality is of the complete syntax, including old and effects,
so semantic interpretation cannot depend on a chosen total-map extension.
-/
namespace Verification.Paper.TolerantFrames.TwoState
open Verification Footprints HeapKnowledge TolerantFrames

abbrev programMap (σ ι ν : Nat → Nat) : Renaming := ⟨σ, ι, ν⟩

theorem Root.rename_program_agree {programs : Nat → Prop} {values : Nat} {σ τ : Nat → Nat}
    (h : ∀ x, programs x → σ x = τ x) (ι ν : Nat → Nat) {r : Root} (hr : r.Scoped programs values) :
    r.rename (programMap σ ι ν) = r.rename (programMap τ ι ν) := by
  cases r with
  | program x => exact congrArg Root.program (h x hr)
  | value _ => rfl

theorem Path.rename_program_agree {programs : Nat → Prop} {values : Nat} {σ τ : Nat → Nat}
    (h : ∀ x, programs x → σ x = τ x) (ι ν : Nat → Nat) {p : Path} (hp : p.Scoped programs values) :
    p.rename (programMap σ ι ν) = p.rename (programMap τ ι ν) := by
  simp only [Path.rename, Root.rename_program_agree h ι ν hp]

theorem BaseValue.rename_program_agree {programs : Nat → Prop} {values : Nat} {σ τ : Nat → Nat}
    (h : ∀ x, programs x → σ x = τ x) (ι ν : Nat → Nat) {v : BaseValue} (hv : v.Scoped programs values) :
    v.rename (programMap σ ι ν) = v.rename (programMap τ ι ν) := by
  cases v with
  | root _ => simp only [BaseValue.rename, Root.rename_program_agree h ι ν hv]
  | literal _ => rfl

theorem Value.rename_program_agree {programs : Nat → Prop} {values : Nat} {σ τ : Nat → Nat}
    (h : ∀ x, programs x → σ x = τ x) (ι ν : Nat → Nat) {v : Value} (hv : v.Scoped programs values) :
    v.rename (programMap σ ι ν) = v.rename (programMap τ ι ν) := by
  cases v <;> simp only [Value.rename, BaseValue.rename_program_agree h ι ν hv]

mutual
theorem Term.rename_program_agree {entryPrograms programs : Nat → Prop} {indices values : Nat} {σ τ : Nat → Nat}
    (he : ∀ x, entryPrograms x → σ x = τ x) (hc : ∀ x, programs x → σ x = τ x)
    (ι ν : Nat → Nat) {t : Term} (ht : t.Scoped entryPrograms programs indices values) :
    t.rename (programMap σ ι ν) = t.rename (programMap τ ι ν) := by
  cases t with
  | literal _ | index _ => rfl
  | path _ _ => simp only [Term.rename, Path.rename_program_agree hc ι ν ht]
  | element _ _ _ _ _ =>
    simp only [Term.rename, Path.rename_program_agree hc ι ν ht.1, Expression.rename_program_agree he hc ι ν ht.2]
  | old t => exact congrArg Term.old (Term.rename_program_agree he he ι ν ht)

theorem Expression.rename_program_agree {entryPrograms programs : Nat → Prop} {indices values : Nat} {σ τ : Nat → Nat}
    (he : ∀ x, entryPrograms x → σ x = τ x) (hc : ∀ x, programs x → σ x = τ x)
    (ι ν : Nat → Nat) {e : Expression} (h : e.Scoped entryPrograms programs indices values) :
    e.rename (programMap σ ι ν) = e.rename (programMap τ ι ν) := by
  cases e with
  | constant _ => rfl
  | scale _ _ => simp only [Expression.rename, Term.rename_program_agree he hc ι ν h]
  | add _ _ => simp only [Expression.rename, Expression.rename_program_agree he hc ι ν h.1,
      Expression.rename_program_agree he hc ι ν h.2]
end

theorem BodyTerm.rename_program_agree {entryPrograms programs : Nat → Prop} {indices values : Nat} {σ τ : Nat → Nat}
    (he : ∀ x, entryPrograms x → σ x = τ x) (hc : ∀ x, programs x → σ x = τ x)
    (ι ν : Nat → Nat) {t : BodyTerm} (ht : t.Scoped entryPrograms programs indices values) :
    t.rename (programMap σ ι ν) = t.rename (programMap τ ι ν) := by
  cases t with
  | free _ => simp only [BodyTerm.rename, Term.rename_program_agree he hc ι ν ht]
  | _ => rfl

theorem BodyExpression.rename_program_agree {entryPrograms programs : Nat → Prop} {indices values : Nat} {σ τ : Nat → Nat}
    (he : ∀ x, entryPrograms x → σ x = τ x) (hc : ∀ x, programs x → σ x = τ x)
    (ι ν : Nat → Nat) {e : BodyExpression} (h : e.Scoped entryPrograms programs indices values) :
    e.rename (programMap σ ι ν) = e.rename (programMap τ ι ν) := by
  induction e with
  | constant _ => rfl
  | scale _ _ => simp only [BodyExpression.rename, BodyTerm.rename_program_agree he hc ι ν h]
  | add _ _ ih₁ ih₂ => simp only [BodyExpression.rename, ih₁ h.1, ih₂ h.2]

theorem Clause.rename_program_agree {entryPrograms programs : Nat → Prop} {indices values : Nat} {σ τ : Nat → Nat}
    (he : ∀ x, entryPrograms x → σ x = τ x) (hc : ∀ x, programs x → σ x = τ x)
    (ι ν : Nat → Nat) {c : Clause} (h : c.Scoped entryPrograms programs indices values) :
    c.rename (programMap σ ι ν) = c.rename (programMap τ ι ν) := by
  induction c with
  | le _ _ => simp only [Clause.rename, BodyExpression.rename_program_agree he hc ι ν h.1,
      BodyExpression.rename_program_agree he hc ι ν h.2]
  | or _ _ ih₁ ih₂ => simp only [Clause.rename, ih₁ h.1, ih₂ h.2]

theorem Body.rename_program_agree {entryPrograms programs : Nat → Prop} {indices values : Nat} {σ τ : Nat → Nat}
    (he : ∀ x, entryPrograms x → σ x = τ x) (hc : ∀ x, programs x → σ x = τ x)
    (ι ν : Nat → Nat) {b : Body} (h : b.Scoped entryPrograms programs indices values) :
    b.rename (programMap σ ι ν) = b.rename (programMap τ ι ν) := by
  induction b with
  | clause _ => simp only [Body.rename, Clause.rename_program_agree he hc ι ν h]
  | and _ _ ih₁ ih₂ => simp only [Body.rename, ih₁ h.1, ih₂ h.2]

theorem Atom.rename_program_agree {entryPrograms programs : Nat → Prop} {indices values : Nat} {σ τ : Nat → Nat}
    (he : ∀ x, entryPrograms x → σ x = τ x) (hc : ∀ x, programs x → σ x = τ x)
    (ι ν : Nat → Nat) {a : Atom} (h : a.Scoped entryPrograms programs indices values) :
    a.rename (programMap σ ι ν) = a.rename (programMap τ ι ν) := by
  cases a with
  | le _ _ => simp only [Atom.rename, Expression.rename_program_agree he hc ι ν h.1, Expression.rename_program_agree he hc ι ν h.2]
  | equal _ _ | optionalEqual _ _ _ =>
    simp only [Atom.rename, Path.rename_program_agree hc ι ν h.1, Value.rename_program_agree hc ι ν h.2]
  | dense _ _ => simp only [Atom.rename, Root.rename_program_agree hc ι ν h.1, Expression.rename_program_agree he hc ι ν h.2]
  | contents _ _ => simp only [Atom.rename, Path.rename_program_agree hc ι ν h]
  | element _ _ _ => simp only [Atom.rename, Path.rename_program_agree hc ι ν h.1,
      Expression.rename_program_agree he hc ι ν h.2.1, Value.rename_program_agree hc ι ν h.2.2]
  | every _ _ _ => simp only [Atom.rename, Path.rename_program_agree hc ι ν h.1,
      Expression.rename_program_agree he hc ι ν h.2.1, Body.rename_program_agree he hc ι ν h.2.2]

theorem encoded_program_agree {programs : Nat → Prop} {values : Nat} {σ τ : Nat → Nat}
    (h : ∀ x, programs x → σ x = τ x) (ι ν : Nat → Nat) {x : Nat}
    (hx : if x % 2 = 0 then programs (x / 2) else x / 2 < values) :
    (programMap σ ι ν).encoded x = (programMap τ ι ν).encoded x := by
  by_cases he : x % 2 = 0
  · simp only [if_pos he] at hx
    simp only [Renaming.encoded, he, ↓reduceIte, h _ hx]
  · simp only [Renaming.encoded, he, ↓reduceIte]

theorem region_rename_program_agree {programs : Nat → Prop} {values : Nat} {σ τ : Nat → Nat}
    (h : ∀ x, programs x → σ x = τ x) (ι ν : Nat → Nat) {r : Region} (hr : RegionScoped programs values r) :
    r.rename (programMap σ ι ν).encoded = r.rename (programMap τ ι ν).encoded := by
  induction r with
  | field _ _ | fields _ | cells _ | path _ _ _ | pathFields _ _ | pathCells _ _ | spine _ _ =>
    simp only [Region.rename, encoded_program_agree h ι ν hr]
  | cls _ | all => rfl
  | inCls _ _ ih => simp only [Region.rename, ih hr]

theorem effect_rename_program_agree {programs : Nat → Prop} {values : Nat} {σ τ : Nat → Nat}
    (h : ∀ x, programs x → σ x = τ x) (ι ν : Nat → Nat) {Φ : Footprint} (hΦ : EffectScoped programs values Φ) :
    Footprint.rename (programMap σ ι ν).encoded Φ = Footprint.rename (programMap τ ι ν).encoded Φ := by
  apply List.map_congr_left
  intro e he
  simp only [region_rename_program_agree h ι ν (hΦ e he)]

theorem Assertion.rename_program_agree {entryPrograms programs : Nat → Prop} {indices values : Nat} {σ τ : Nat → Nat}
    (he : ∀ x, entryPrograms x → σ x = τ x) (hc : ∀ x, programs x → σ x = τ x)
    (ι ν : Nat → Nat) {F : Assertion} (hF : F.Scoped entryPrograms programs indices values) :
    F.rename (programMap σ ι ν) = F.rename (programMap τ ι ν) := by
  induction F generalizing values ν with
  | truth | falsity => rfl
  | atom _ => simp only [Assertion.rename, Atom.rename_program_agree he hc ι ν hF]
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ => simp only [Assertion.rename, ih₁ ν hF.1, ih₂ ν hF.2]
  | existsValue _ ih => exact congrArg Assertion.existsValue (ih (liftRenaming ν) hF)
  | separated _ _ => simp only [Assertion.rename, Path.rename_program_agree hc ι ν hF.1, Path.rename_program_agree hc ι ν hF.2]
  | apart _ _ => simp only [Assertion.rename, Root.rename_program_agree hc ι ν hF.1, Root.rename_program_agree hc ι ν hF.2]
  | fresh _ => simp only [Assertion.rename, region_rename_program_agree hc ι ν hF]
  | box _ _ ih => simp only [Assertion.rename, effect_rename_program_agree hc ι ν hF.1, ih ν hF.2]

theorem Post.rename_program_agree {entryPrograms programs : Nat → Prop} {indices values : Nat} {σ τ : Nat → Nat}
    (he : ∀ x, entryPrograms x → σ x = τ x) (hc : ∀ x, programs x → σ x = τ x)
    (ι ν : Nat → Nat) {Q : Post} (hQ : Q.Scoped entryPrograms programs indices values) :
    Q.rename (programMap σ ι ν) = Q.rename (programMap τ ι ν) := by
  induction Q generalizing indices values ι ν with
  | assertion _ => simp only [Post.rename, Assertion.rename_program_agree he hc ι ν hQ]
  | old _ => simp only [Post.rename, Assertion.rename_program_agree he he ι ν hQ]
  | transition _ => simp only [Post.rename, effect_rename_program_agree he ι ν hQ]
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | implication _ _ ih₁ ih₂ =>
    simp only [Post.rename, ih₁ ι ν hQ.1, ih₂ ι ν hQ.2]
  | forallIndex _ ih => exact congrArg Post.forallIndex (ih (liftRenaming ι) ν hQ)
  | forallValue _ ih => exact congrArg Post.forallValue (ih ι (liftRenaming ν) hQ)

/-- The interpretation is independent of arbitrary images of unused names. -/
theorem Post.program_extension_independent {entryPrograms programs : Nat → Prop} {indices values : Nat} {σ τ : Nat → Nat}
    (he : ∀ x, entryPrograms x → σ x = τ x) (hc : ∀ x, programs x → σ x = τ x)
    (ι ν : Nat → Nat) {Q : Post} (hQ : Q.Scoped entryPrograms programs indices values) (c : Context) (η : LogicalEnv) :
    (Q.rename (programMap σ ι ν)).Holds c η ↔ (Q.rename (programMap τ ι ν)).Holds c η := by
  rw [Q.rename_program_agree he hc ι ν hQ]

end Verification.Paper.TolerantFrames.TwoState
