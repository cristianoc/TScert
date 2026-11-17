import Verification.Paper.TolerantFrames.CommandRules
import Verification.Paper.TolerantFrames.Admission

/-! # Scope of a frame

The existing mechanism is named command bindings. Avoidance below is a structural
scope property, not a list of eligible statements or an assertion-preservation
check: a frame's free variables must not be bound by the command. Heap changes
are accounted for separately by the modality.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge HeapObservations
open Verification.TolerantFrames

/-- A command does not bind a variable used by the surrounding frame. -/
def Command.Avoids (x : Nat) : Command → Prop
  | .step (.bind y _) => x ≠ y
  | .step (.perform _) => True
  | .seq a b | .choice _ a b => a.Avoids x ∧ b.Avoids x
  | .loop b => b.Avoids x
  | .handle b y d => b.Avoids x ∧ x ≠ y ∧ d.Avoids x
  | .return_ _ | .throw_ _ | .break_ => True

private theorem primitive_preserves {host p ρ h n ρ' h' e} (hr : PrimitiveRun host p ρ h n ρ' h' e)
    {x : Nat} (hc : (Command.step p).Avoids x) : ρ' x = ρ x := by
  cases p with
  | bind y op => cases hr <;> simp_all [Primitive.bindResult, Command.Avoids, bindName]
  | perform op => cases hr <;> rfl

/-- Every binding on a completed run respects syntactic avoidance, including
the fresh caught name and every iteration of a loop. -/
theorem Executes.preserves_name {host c ρ h n ρ' h' e} (hr : Executes host c ρ h n ρ' h' e)
    {x : Nat} (hc : c.Avoids x) : ρ' x = ρ x := by
  induction hr with
  | step hp => exact primitive_preserves hp hc
  | seq _ _ ih₁ ih₂ => exact (ih₂ hc.2).trans (ih₁ hc.1)
  | seq_exit _ _ ih => exact ih hc.1
  | yes _ _ ih => exact ih hc.1
  | no _ _ ih => exact ih hc.2
  | loop_next _ _ ih₁ ih₂ => exact (ih₂ hc).trans (ih₁ hc)
  | loop_break _ ih => exact ih hc
  | loop_return _ ih => exact ih hc
  | loop_throw _ ih => exact ih hc
  | handle_catch _ _ ih₁ ih₂ =>
    have h₁ := ih₁ hc.1
    have h₂ := ih₂ hc.2.2
    simp only [bindName, if_neg hc.2.1] at h₂
    exact h₂.trans h₁
  | handle_exit _ _ ih => exact ih hc.1
  | return_ _ | throw_ _ | break_ => rfl

/-- Every outer lexical binding remains available after an admitted command. -/
theorem Command.WellScoped.preserves_input {Γ Δ c} (hc : Command.WellScoped Γ c Δ) : ∀ x, Γ x → Δ x := by
  induction hc with
  | bind => exact fun _ hx => .inr hx
  | perform => exact fun _ hx => hx
  | seq _ _ ih₁ ih₂ => exact fun x hx => ih₂ x (ih₁ x hx)
  | choice _ _ _ _ hkeep _ _ => exact hkeep
  | loop => exact fun _ hx => hx
  | handle _ _ _ _ hkeep _ _ _ => exact hkeep
  | return_ | throw_ | break_ => exact fun _ hx => hx

/-- A branch join may discard branch-local temporaries while retaining every
outer name. Its intersection obligations follow from input preservation. -/
theorem Command.WellScoped.choice_input {Γ Δ Θ test a b}
    (ht : Argument.Scoped Γ test) (ha : Command.WellScoped Γ a Δ) (hb : Command.WellScoped Γ b Θ) :
    Command.WellScoped Γ (.choice test a b) Γ :=
  .choice ht ha hb (fun x hx => ⟨ha.preserves_input x hx, hb.preserves_input x hx⟩) (fun _ hx => hx)

/-- An admitted command never overwrites an original input binding. -/
theorem Command.WellScoped.avoids_inputs {Γ Δ c} (hc : Command.WellScoped Γ c Δ) :
    ∀ x, Γ x → c.Avoids x := by
  induction hc with
  | bind hf _ _ =>
    intro x hx heq
    subst x
    exact hf hx
  | perform => exact fun _ _ => trivial
  | seq ha _ ih₁ ih₂ => exact fun x hx => ⟨ih₁ x hx, ih₂ x (ha.preserves_input x hx)⟩
  | choice _ _ _ _ _ ih₁ ih₂ => exact fun x hx => ⟨ih₁ x hx, ih₂ x hx⟩
  | loop _ ih => exact ih
  | handle hf _ _ _ _ _ ih₁ ih₂ =>
    intro x hx
    refine ⟨ih₁ x hx, ?_, ih₂ x (.inr hx)⟩
    intro heq
    subst x
    exact hf hx
  | return_ | throw_ | break_ => exact fun _ _ => trivial

/-- An assertion reads only these variables. This semantic scope definition
applies to complete assertions, including effects beneath modalities. -/
def DependsOn (F : Assertion) (variables : Nat → Prop) : Prop :=
  ∀ ρ ρ' m s, (∀ x, variables x → ρ x = ρ' x) → (F ρ m s ↔ F ρ' m s)

/-- The scope premises of Frame and Frame+ follow from fresh binding names,
for every formula, without an invariant-guard restriction. -/
theorem scope_stable_of_avoids {host c F variables}
    (hF : DependsOn F variables) (hc : ∀ x, variables x → c.Avoids x) : ScopeStable host c F := by
  intro ρ h n ρ' h' e hr m s
  exact hF ρ ρ' m s (fun x hx => (hr.preserves_name (hc x hx)).symm)

end Verification.Paper.TolerantFrames
