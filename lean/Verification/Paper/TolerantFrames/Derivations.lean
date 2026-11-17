import Verification.Paper.TolerantFrames.Loops
import Verification.Paper.TolerantFrames.ModalReplacement
import Verification.Paper.TolerantFrames.Admission
import Verification.Paper.TolerantFrames.QuantifiedRules

/-! # General logical derivations

The existing mechanism extended here is the sound finite `Parity.Derivation`.
This proof layer separates semantic rule premises from its serialized checker:
a derivation is a finite proof, and no constructor asserts an arbitrary semantic
entailment. The logic and modal laws below apply to arbitrary postconditions on valid
entry/exit contexts. Quantified bodies instantiate into the actual syntax;
modal rule premises use semantic validity, rather than raw invalid environments.
This is a sound subcalculus of Definition 23: current-state path replacement
and full bounded-body instantiation are included; general existential logic,
two-state substitution, structural-support and arithmetic schemas remain
separate obligations. In
particular this file makes no completeness claim about proof search.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge HeapObservations
open Verification.TolerantFrames

/-- Meaning of a finite list of two-state premises. -/
def Premises (Γ : List Postcondition) (ρ ρ' : Env) (m : Nat) (s t : IndexedHeap) : Prop :=
  ∀ Q ∈ Γ, Q ρ ρ' m s t

/-- Semantic consequence of precisely these premises. -/
def Consequence (Γ : List Postcondition) (Q : Postcondition) : Prop :=
  ∀ ρ ρ' m s t, ValidContext ρ m s → ValidContext ρ' m t → Premises Γ ρ ρ' m s t → Q ρ ρ' m s t

/-- General finite logical derivations. Semantic inclusion, invariance and
rigidity are proof premises, and are not replaced by a finite case list. -/
inductive Derivation : List Postcondition → Postcondition → Prop where
  | assumption {Γ Q} : Q ∈ Γ → Derivation Γ Q
  | truth {Γ} : Derivation Γ (fun _ _ _ _ _ => True)
  | absurd {Γ Q} : Derivation Γ (fun _ _ _ _ _ => False) → Derivation Γ Q
  | cut {Γ Q R} : Derivation Γ Q → Derivation (Q :: Γ) R → Derivation Γ R
  | andIntro {Γ Q R} : Derivation Γ Q → Derivation Γ R → Derivation Γ (PostAnd Q R)
  | andLeft {Γ Q R} : Derivation Γ (PostAnd Q R) → Derivation Γ Q
  | andRight {Γ Q R} : Derivation Γ (PostAnd Q R) → Derivation Γ R
  | orLeft {Γ Q R} : Derivation Γ Q → Derivation Γ (PostOr Q R)
  | orRight {Γ Q R} : Derivation Γ R → Derivation Γ (PostOr Q R)
  | orElim {Γ Q R S} : Derivation Γ (PostOr Q R) → Derivation (Q :: Γ) S → Derivation (R :: Γ) S → Derivation Γ S
  | implication {Γ Q R} : Derivation Γ (PostImp Q R) → Derivation Γ Q → Derivation Γ R
  | indexInstance {Γ Q} : Derivation Γ (ForallIndex Q) → (i : Int) → Derivation Γ (Q i)
  | valueInstance {Γ Q} : Derivation Γ (ForallValue Q) → (v : Val) → isSourceVal v = true → Derivation Γ (Q v)
  | boxElim {Γ Φ} {F : Assertion} : Derivation Γ (Now (Box Φ F)) → Derivation Γ (Now F)
  | boxAnd {Γ Φ} {F G : Assertion} : Derivation Γ (PostAnd (Now (Box Φ F)) (Now (Box Φ G))) →
      Derivation Γ (Now (Box Φ (fun ρ m s => F ρ m s ∧ G ρ m s)))
  | boxLeft {Γ Φ} {F G : Assertion} : Derivation Γ (Now (Box Φ (fun ρ m s => F ρ m s ∧ G ρ m s))) →
      Derivation Γ (Now (Box Φ F))
  | boxRight {Γ Φ} {F G : Assertion} : Derivation Γ (Now (Box Φ (fun ρ m s => F ρ m s ∧ G ρ m s))) →
      Derivation Γ (Now (Box Φ G))
  | boxMono {Γ Φ} {F G : Assertion} : EntailsOn F G → Derivation Γ (Now (Box Φ F)) → Derivation Γ (Now (Box Φ G))
  | boxAnti {Γ Φ Ψ} {F : Assertion} : (∀ ρ m s t, ValidContext ρ m s → Action Φ ρ s t → Action Ψ ρ s t) →
      Derivation Γ (Now (Box Ψ F)) → Derivation Γ (Now (Box Φ F))
  | boxOr {Γ Φ} {F G : Assertion} : InvariantOn G → Derivation Γ (PostOr (Now G) (Now (Box Φ F))) →
      Derivation Γ (Now (Box Φ (fun ρ m s => G ρ m s ∨ F ρ m s)))
  | boxIdem {Γ Φ} {F : Assertion} : RigidOn Φ → Derivation Γ (Now (Box Φ F)) → Derivation Γ (Now (Box Φ (Box Φ F)))

  | replacePath {Γ p q F G} (types : DeclaredPaths) : F.WellFormed types → G.WellFormed types →
      FormulaReplacement false p q F G → Derivation Γ (Now (PathEquality p q).meaning) →
      Derivation Γ (Now F.meaning) → Derivation Γ (Now G.meaning)
  | replaceRigidPath {Γ p q F G} (types : DeclaredPaths) : F.WellFormed types → G.WellFormed types →
      FormulaReplacement true p q F G → Derivation Γ (Now (PathEquality p q).meaning) →
      Derivation Γ (Now (RigidFormula p).meaning) → Derivation Γ (Now (RigidFormula q).meaning) →
      Derivation Γ (Now F.meaning) → Derivation Γ (Now G.meaning)

  | everyInst {Γ z bound k body} : Derivation Γ (Now (Formula.atom (.every z bound body)).meaning) →
      Derivation Γ (Now (IndexBounds k bound).meaning) → Derivation Γ (Now (body.instantiate z k).meaning)
  | everyPrefix {Γ z bound smaller body} : Derivation Γ (Now (Formula.atom (.every z bound body)).meaning) →
      Derivation Γ (Now (Formula.atom (.le smaller bound)).meaning) →
      Derivation Γ (Now (Formula.atom (.every z smaller body)).meaning)
  | everyEmpty {Γ kind z bound body} : (kind = .length ∨ kind = .view) →
      Derivation Γ (Now (PathDefined kind z).meaning) →
      Derivation Γ (Now (Formula.atom (.le bound (.constant 0))).meaning) →
      Derivation Γ (Now (Formula.atom (.every z bound body)).meaning)

/-- Every represented derivation proves its semantic entailment. This does
not claim the omitted schemas have been represented. -/
theorem Derivation.sound {Γ Q} (d : Derivation Γ Q) : Consequence Γ Q := by
  intro ρ ρ' m s t _hv hvt hΓ
  induction d with
  | assumption hm => exact hΓ _ hm
  | truth => trivial
  | absurd _ ih => exact (ih hΓ).elim
  | cut _ _ ih₁ ih₂ =>
    exact ih₂ (fun F hF => by rcases List.mem_cons.mp hF with rfl | hm; exact ih₁ hΓ; exact hΓ F hm)
  | andIntro _ _ ih₁ ih₂ => exact ⟨ih₁ hΓ, ih₂ hΓ⟩
  | andLeft _ ih => exact (ih hΓ).1
  | andRight _ ih => exact (ih hΓ).2
  | orLeft _ ih => exact .inl (ih hΓ)
  | orRight _ ih => exact .inr (ih hΓ)
  | orElim _ _ _ ih ih₁ ih₂ =>
    rcases ih hΓ with hQ | hR
    · exact ih₁ (fun F hF => by rcases List.mem_cons.mp hF with rfl | hm; exact hQ; exact hΓ F hm)
    · exact ih₂ (fun F hF => by rcases List.mem_cons.mp hF with rfl | hm; exact hR; exact hΓ F hm)
  | implication _ _ ih₁ ih₂ => exact ih₁ hΓ (ih₂ hΓ)
  | indexInstance _ i ih => exact ih hΓ i
  | valueInstance _ v hv ih => exact ih hΓ v hv
  | boxElim _ ih => exact box_elim (ih hΓ)
  | boxAnd _ ih => exact box_and.mpr (ih hΓ)
  | boxLeft _ ih => exact (box_and.mp (ih hΓ)).1
  | boxRight _ ih => exact (box_and.mp (ih hΓ)).2
  | boxMono hfg _ ih => exact box_mono_on hfg ρ' m t hvt (ih hΓ)
  | boxAnti hΦ _ ih => exact box_anti (hΦ ρ' m t · hvt) (ih hΓ)
  | boxOr hG _ ih => exact box_or_on hG ρ' m t hvt (ih hΓ)
  | boxIdem hΦ _ ih => exact box_idem_on hΦ ρ' m t hvt (ih hΓ)

  | replacePath _ _ _ hr _ _ ihE ihF =>
    exact (hr.local (PathEquality.read_eq (ihE hΓ))).mp (ihF hΓ)
  | replaceRigidPath _ _ _ hr _ _ _ _ ihE ihP ihQ ihF =>
    exact (hr.rigid (RigidFormula.holds_iff.mp (ihP hΓ))
      (RigidFormula.holds_iff.mp (ihQ hΓ)) (ihE hΓ)).mp (ihF hΓ)

  | everyInst _ _ ihE ihK => exact inst_rule (ihE hΓ) (ihK hΓ)
  | everyPrefix _ _ ihE ihL => exact prefix_rule (m := m) (ihE hΓ) (ihL hΓ)
  | everyEmpty hkind _ _ ihD ihB => exact empty_rule hkind hvt (ihD hΓ) (ihB hΓ)

end Verification.Paper.TolerantFrames
