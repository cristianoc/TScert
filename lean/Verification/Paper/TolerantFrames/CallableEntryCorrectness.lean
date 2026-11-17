import Verification.Paper.TolerantFrames.CallableEntryCode

/-! # Completed fixed-arity invocations recover actual body execution

Cancel the proved three-step invocation prefix, then use the existing generated
body inversion in its ambient code. Exact counts give a strict decrease for
future recursion arguments. Source typing, signatures, rest allocation and
specification/old-anchor transport are not inferred from this raw theorem.
-/
namespace Verification.Paper.TolerantFrames.Compiler.Callable
open Verification ControlFlow HeapObservations

/-- Normal completion retains the actual body exit kind, including an escaping
break; it does not silently identify that break with valid function fallthrough. -/
theorem invocation_value {arity} {caps : List Tm} (c : Command) (layout : Layout arity caps.length)
    (fields : List (PropKey × Nat)) (identity : Nat) (receiver : Tm) (args : List Tm) (h : Heap)
    (hr : isVal receiver = true) (ha : CallArguments.Values args) (hc : CallArguments.Values caps)
    {n h' v} (run : Steps n h (invocation c layout fields identity receiver args) h' v)
    (value : isVal v = true) :
    ∃ q p ρ' e, n = 3 + q ∧ p ≤ q ∧ p < n ∧
      Executes layout.host c (layout.env receiver args (function c layout fields identity)) h p ρ' h' e ∧
      ControlFlow.State.done v = resultState e := by
  obtain ⟨q, count, bodyRun⟩ := steps_cancel_terminal (invocation_prefix c layout fields identity receiver args h hr ha)
    run (fun _ _ => value_no_step value)
  obtain ⟨state, graphRun, simulation⟩ := steps_back bodyRun GraphCode.Sim.goto
  have terminalState := value_state simulation value
  rw [terminalState] at graphRun
  obtain ⟨p, ρ', e, weight, body, result⟩ :=
    compiled_execution_agree c layout.host (layout.env receiver args (function c layout fields identity)) h
      (layout.env_values hr ha rfl hc) (layout.host_values hc) (code_agrees c layout) graphRun trivial
  exact ⟨q, p, ρ', e, count, weight, by omega, body, result⟩

/-- Exceptional completion recovers the same thrown value and the same heap. -/
theorem invocation_raise {arity} {caps : List Tm} (c : Command) (layout : Layout arity caps.length)
    (fields : List (PropKey × Nat)) (identity : Nat) (receiver : Tm) (args : List Tm) (h : Heap)
    (hr : isVal receiver = true) (ha : CallArguments.Values args) (hc : CallArguments.Values caps)
    {n h' term v} (run : Steps n h (invocation c layout fields identity receiver args) h' term)
    (raised : Raises term v) :
    ∃ q p ρ', n = 3 + q ∧ p ≤ q ∧ p < n ∧
      Executes layout.host c (layout.env receiver args (function c layout fields identity)) h p ρ' h' (.thrown v) := by
  obtain ⟨q, count, bodyRun⟩ := steps_cancel_terminal (invocation_prefix c layout fields identity receiver args h hr ha)
    run (fun _ _ => raises_no_step raised)
  obtain ⟨state, graphRun, simulation⟩ := steps_back bodyRun GraphCode.Sim.goto
  have terminalState := raised_state simulation raised
  rw [terminalState] at graphRun
  obtain ⟨p, ρ', e, weight, body, result⟩ :=
    compiled_execution_agree c layout.host (layout.env receiver args (function c layout fields identity)) h
      (layout.env_values hr ha rfl hc) (layout.host_values hc) (code_agrees c layout) graphRun trivial
  cases e with
  | normal | «break» | returned _ => cases result
  | thrown w => cases result; exact ⟨q, p, ρ', count, weight, by omega, body⟩

end Verification.Paper.TolerantFrames.Compiler.Callable
