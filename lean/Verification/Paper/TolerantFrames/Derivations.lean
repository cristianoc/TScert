import Verification.Paper.TolerantFrames.Loops
import Verification.Paper.TolerantFrames.ModalReplacement
import Verification.Paper.TolerantFrames.Admission
import Verification.Paper.TolerantFrames.QuantifiedRules
import Verification.Paper.TolerantFrames.Existentials
import Verification.Paper.TolerantFrames.Arithmetic
import Verification.Paper.TolerantFrames.LiteralEquality

/-! # General logical derivations

The existing mechanism extended here is the sound finite `Parity.Derivation`.
This proof layer separates semantic rule premises from its serialized checker:
a derivation is a finite proof, and no constructor asserts an arbitrary semantic
entailment. The logic and modal laws below apply to arbitrary postconditions on valid
entry/exit contexts. Quantified bodies instantiate into the actual syntax;
modal rule premises use semantic validity, rather than raw invalid environments.
This is a sound subcalculus of Definition 23: current-state path replacement
and full bounded-body instantiation are included; literal existential substitution,
two-state substitution, the structural atom-support table and mixed-state arithmetic remain
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
  | valueToInteger {Γ p bits n} : SafeIntegers.SafeInt bits n →
      Derivation Γ (Now (NumberEquality p bits).meaning) → Derivation Γ (Now (IntegerEquality p n).meaning)
  | integerToValue {Γ p bits n} : SafeIntegers.SafeInt bits n → n ≠ 0 →
      Derivation Γ (Now (IntegerEquality p n).meaning) → Derivation Γ (Now (NumberEquality p bits).meaning)
  | integerZeroValues {Γ p} : Derivation Γ (Now (IntegerEquality p 0).meaning) →
      Derivation Γ (Now (ZeroValueEquality p).meaning)
  | arithmetic {Γ hypotheses goal} : IntegerConsequence hypotheses goal → GoalTermsDefined hypotheses goal →
      (∀ p ∈ hypotheses, Derivation Γ (Now (Formula.atom (.le p.1 p.2)).meaning)) →
      Derivation Γ (Now (Formula.atom (.le goal.1 goal.2)).meaning)
  | lengthRange {Γ t k} : t.ReadsKind k → (k = .length ∨ k = .view ∨ k = .strLength) →
      Derivation Γ (Now (TermDefined t).meaning) → Derivation Γ (Now (LengthBounds k t).meaning)
  | existsIntro {Γ F v} : Derivation Γ (Now (ValueInstantiation F v)) →
      Derivation Γ (Now (Formula.existsValue F).meaning)
  | existsElim {Γ F Q} : Derivation Γ (Now (Formula.existsValue F).meaning) →
      Derivation (Now F.meaning :: Γ.map ExitLift) (ExitLift Q) → Derivation Γ Q
  | oldMono {Γ} {F G : Assertion} : Derivation [Now F] (Now G) →
      Derivation Γ (Old F) → Derivation Γ (Old G)
  | frameAll {Γ} {K F : Formula} {Φ : Footprint} {q : SepQuery} : F.ModalityFree → respects q allKeep Φ = true →
      (∀ ρ m s, ValidContext ρ m s → K.Holds ρ m s → q.Sound ρ s.h) →
      Derivation Γ (Now K.meaning) → Derivation Γ (Now F.meaning) →
      Derivation Γ (Now (Box Φ F.meaning))
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
  induction d with
  | assumption hm =>
    intro ρ ρ' m s t hv hvt hΓ
    exact hΓ _ hm
  | truth =>
    intro ρ ρ' m s t hv hvt hΓ
    trivial
  | absurd _ ih =>
    intro ρ ρ' m s t hv hvt hΓ
    exact (ih ρ ρ' m s t hv hvt hΓ).elim
  | cut _ _ ih₁ ih₂ =>
    intro ρ ρ' m s t hv hvt hΓ
    exact ih₂ ρ ρ' m s t hv hvt (fun F hF => by rcases List.mem_cons.mp hF with rfl | hm; exact ih₁ ρ ρ' m s t hv hvt hΓ; exact hΓ F hm)
  | andIntro _ _ ih₁ ih₂ =>
    intro ρ ρ' m s t hv hvt hΓ
    exact ⟨ih₁ ρ ρ' m s t hv hvt hΓ, ih₂ ρ ρ' m s t hv hvt hΓ⟩
  | andLeft _ ih =>
    intro ρ ρ' m s t hv hvt hΓ
    exact (ih ρ ρ' m s t hv hvt hΓ).1
  | andRight _ ih =>
    intro ρ ρ' m s t hv hvt hΓ
    exact (ih ρ ρ' m s t hv hvt hΓ).2
  | orLeft _ ih =>
    intro ρ ρ' m s t hv hvt hΓ
    exact .inl (ih ρ ρ' m s t hv hvt hΓ)
  | orRight _ ih =>
    intro ρ ρ' m s t hv hvt hΓ
    exact .inr (ih ρ ρ' m s t hv hvt hΓ)
  | orElim _ _ _ ih ih₁ ih₂ =>
    intro ρ ρ' m s t hv hvt hΓ
    rcases ih ρ ρ' m s t hv hvt hΓ with hQ | hR
    · exact ih₁ ρ ρ' m s t hv hvt (fun F hF => by rcases List.mem_cons.mp hF with rfl | hm; exact hQ; exact hΓ F hm)
    · exact ih₂ ρ ρ' m s t hv hvt (fun F hF => by rcases List.mem_cons.mp hF with rfl | hm; exact hR; exact hΓ F hm)
  | implication _ _ ih₁ ih₂ =>
    intro ρ ρ' m s t hv hvt hΓ
    exact ih₁ ρ ρ' m s t hv hvt hΓ (ih₂ ρ ρ' m s t hv hvt hΓ)
  | indexInstance _ i ih =>
    intro ρ ρ' m s t hv hvt hΓ
    exact ih ρ ρ' m s t hv hvt hΓ i
  | valueInstance _ v hsv ih =>
    intro ρ ρ' m s t hv hvt hΓ
    exact ih ρ ρ' m s t hv hvt hΓ v hsv
  | valueToInteger hn _ ih =>
    intro ρ ρ' m s t hv hvt hΓ
    exact value_equality_to_integer hn (ih ρ ρ' m s t hv hvt hΓ)
  | integerToValue hn hn0 _ ih =>
    intro ρ ρ' m s t hv hvt hΓ
    exact integer_equality_to_value hn hn0 (ih ρ ρ' m s t hv hvt hΓ)
  | integerZeroValues _ ih =>
    intro ρ ρ' m s t hv hvt hΓ
    exact integer_zero_to_values (ih ρ ρ' m s t hv hvt hΓ)
  | arithmetic hc hd _ ih =>
    intro ρ ρ' m s t hv hvt hΓ
    exact integer_consequence hc hd (fun p hp => ih p hp ρ ρ' m s t hv hvt hΓ)
  | lengthRange hr hk _ ih =>
    intro ρ ρ' m s t hv hvt hΓ
    exact length_bounds hr hk (ih ρ ρ' m s t hv hvt hΓ)
  | existsIntro _ ih =>
    intro ρ ρ' m s t hv hvt hΓ
    exact exists_intro hvt (ih ρ ρ' m s t hv hvt hΓ)
  | @existsElim Γ F Q _ _ ihE ihBody =>
    intro ρ ρ' m s t hv hvt hΓ
    obtain ⟨v, hsv, hrv, hF⟩ := ihE ρ ρ' m s t hv hvt hΓ
    have hΓ' : Premises (Now F.meaning :: List.map ExitLift Γ) ρ (push v ρ') m s t := by
      intro R hR
      rcases List.mem_cons.mp hR with rfl | hR
      · exact hF
      · obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hR
        exact hΓ Q hQ
    exact ihBody ρ (push v ρ') m s t hv (hvt.push hsv hrv) hΓ'
  | oldMono _ _ ihFG ihF =>
    intro ρ ρ' m s t hv hvt hΓ
    apply ihFG ρ ρ m s s hv hv
    intro R hR
    have hR' : R = Now _ := List.mem_singleton.mp hR
    subst R
    exact ihF ρ ρ' m s t hv hvt hΓ
  | frameAll hn hc hq _ _ ihK ihF =>
    intro ρ ρ' m s t hv hvt hΓ
    exact tolerant_frame_unconditional (Formula.all_support hn) (respects_of_check hc hq)
      ρ' m t hvt ⟨ihK ρ ρ' m s t hv hvt hΓ, ihF ρ ρ' m s t hv hvt hΓ⟩
  | boxElim _ ih =>
    intro ρ ρ' m s t hv hvt hΓ
    exact box_elim (ih ρ ρ' m s t hv hvt hΓ)
  | boxAnd _ ih =>
    intro ρ ρ' m s t hv hvt hΓ
    exact box_and.mpr (ih ρ ρ' m s t hv hvt hΓ)
  | boxLeft _ ih =>
    intro ρ ρ' m s t hv hvt hΓ
    exact (box_and.mp (ih ρ ρ' m s t hv hvt hΓ)).1
  | boxRight _ ih =>
    intro ρ ρ' m s t hv hvt hΓ
    exact (box_and.mp (ih ρ ρ' m s t hv hvt hΓ)).2
  | boxMono hfg _ ih =>
    intro ρ ρ' m s t hv hvt hΓ
    exact box_mono_on hfg ρ' m t hvt (ih ρ ρ' m s t hv hvt hΓ)
  | boxAnti hΦ _ ih =>
    intro ρ ρ' m s t hv hvt hΓ
    exact box_anti (hΦ ρ' m t · hvt) (ih ρ ρ' m s t hv hvt hΓ)
  | boxOr hG _ ih =>
    intro ρ ρ' m s t hv hvt hΓ
    exact box_or_on hG ρ' m t hvt (ih ρ ρ' m s t hv hvt hΓ)
  | boxIdem hΦ _ ih =>
    intro ρ ρ' m s t hv hvt hΓ
    exact box_idem_on hΦ ρ' m t hvt (ih ρ ρ' m s t hv hvt hΓ)

  | replacePath _ _ _ hr _ _ ihE ihF =>
    intro ρ ρ' m s t hv hvt hΓ
    exact (hr.local (PathEquality.read_eq (ihE ρ ρ' m s t hv hvt hΓ))).mp (ihF ρ ρ' m s t hv hvt hΓ)
  | replaceRigidPath _ _ _ hr _ _ _ _ ihE ihP ihQ ihF =>
    intro ρ ρ' m s t hv hvt hΓ
    exact (hr.rigid (RigidFormula.holds_iff.mp (ihP ρ ρ' m s t hv hvt hΓ))
      (RigidFormula.holds_iff.mp (ihQ ρ ρ' m s t hv hvt hΓ)) (ihE ρ ρ' m s t hv hvt hΓ)).mp (ihF ρ ρ' m s t hv hvt hΓ)

  | everyInst _ _ ihE ihK =>
    intro ρ ρ' m s t hv hvt hΓ
    exact inst_rule (ihE ρ ρ' m s t hv hvt hΓ) (ihK ρ ρ' m s t hv hvt hΓ)
  | everyPrefix _ _ ihE ihL =>
    intro ρ ρ' m s t hv hvt hΓ
    exact prefix_rule (m := m) (ihE ρ ρ' m s t hv hvt hΓ) (ihL ρ ρ' m s t hv hvt hΓ)
  | everyEmpty hkind _ _ ihD ihB =>
    intro ρ ρ' m s t hv hvt hΓ
    exact empty_rule hkind hvt (ihD ρ ρ' m s t hv hvt hΓ) (ihB ρ ρ' m s t hv hvt hΓ)

end Verification.Paper.TolerantFrames
