import Verification.Paper.TolerantFrames.CompilerControlSimulation

/-! # Real function-boundary sink execution

These proofs use full emitted expressions/continuations, not site metadata
alone. Matching retains the named environment before the graph frame is lost.
Standalone break remains distinct for the eventual function obligation.
-/
namespace Verification.Paper.TolerantFrames.Compiler
open Verification ControlFlow HeapObservations

theorem normal_sink {P nodes bound outer graph host a h h' term after}
    (steps : Steps a h .undef h' term)
    (leave : ControlFlow.Transition P h' (.eval term graph .ret none) h' after)
    (outside : OutsideEvaluation after) :
    NodeResult nodes bound outer host .normal graph h a h' after := by
  obtain ⟨rfl, rfl, rfl⟩ := steps_from_value rfl steps
  cases leave with
  | expr _ => cases outside
  | ret _ => exact ⟨0, .exit .normal [], restore bound outer graph, Nat.le_refl _, .refl, .normal⟩
  | raise raised => cases raised

theorem break_sink {P nodes bound outer graph host a h h' term after}
    (steps : Steps a h .undef h' term)
    (leave : ControlFlow.Transition P h' (.eval term graph .ret none) h' after)
    (outside : OutsideEvaluation after) :
    NodeResult nodes bound outer host .broken graph h a h' after := by
  obtain ⟨rfl, rfl, rfl⟩ := steps_from_value rfl steps
  cases leave with
  | expr _ => cases outside
  | ret _ => exact ⟨0, .exit .break [], restore bound outer graph, Nat.le_refl _, .refl, .broken⟩
  | raise raised => cases raised

theorem return_sink {P nodes bound outer graph host a h h' term after}
    (values : ∀ i, isVal (graph i) = true)
    (steps : Steps a h (instantiate 0 graph (.var (bound + 3))) h' term)
    (leave : ControlFlow.Transition P h' (.eval term graph .ret none) h' after)
    (outside : OutsideEvaluation after) :
    NodeResult nodes bound outer host .returned graph h a h' after := by
  change Steps a h (graph (bound + 3)) h' term at steps
  have hv := values (bound + 3)
  obtain ⟨rfl, rfl, rfl⟩ := steps_from_value hv steps
  generalize he : graph (bound + 3) = result at leave hv ⊢
  cases leave with
  | expr _ => cases outside
  | ret _ =>
    refine ⟨0, .exit (.returned result) [], restore bound outer graph, Nat.le_refl _, ?_, .returned⟩
    simp only [Site.control, he]
    exact .refl
  | raise raised => exact False.elim (by simpa [hv] using raises_not_val raised)

theorem throw_sink {P nodes bound outer graph host a h h' term after}
    (values : ∀ i, isVal (graph i) = true)
    (steps : Steps a h (instantiate 0 graph (.throw (.var (bound + 3)))) h' term)
    (leave : ControlFlow.Transition P h' (.eval term graph .ret none) h' after)
    (outside : OutsideEvaluation after) :
    NodeResult nodes bound outer host .thrown graph h a h' after := by
  change Steps a h (.throw (graph (bound + 3))) h' term at steps
  have hv := values (bound + 3)
  obtain ⟨rfl, rfl, rfl⟩ := throw_value_steps hv steps
  generalize he : graph (bound + 3) = result at leave hv ⊢
  cases leave with
  | expr _ => cases outside
  | ret bad => cases bad
  | raise raised =>
    cases raised with
    | throwV _ _ =>
      refine ⟨0, .exit (.thrown result) [], restore bound outer graph, Nat.le_refl _, ?_, .thrown⟩
      simp only [Site.control, he]
      exact .refl
    | throwC inner => exact False.elim (by simpa [hv] using raises_not_val inner)

end Verification.Paper.TolerantFrames.Compiler
