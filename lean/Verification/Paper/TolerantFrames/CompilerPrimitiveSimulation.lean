import Verification.Paper.TolerantFrames.CompilerSimulation

/-! # Completed primitive nodes yield actual command steps

Fixed symbolic code is inverted at its terminal, then finite generated routes
handle the exit. Native host code and actual heaps are retained exactly.
-/
namespace Verification.Paper.TolerantFrames.Compiler
open Verification ControlFlow HeapObservations

private theorem operation_scope {bound p} (scope : (Command.step p).InFrame bound) :
    p.operation.Scoped (· < bound) := by cases p <;> first | exact scope.2 | exact scope

theorem primitive_value {bound outer graph host p a h h' term}
    (scope : (Command.step p).InFrame bound) (values : ∀ i, isVal (graph i) = true)
    (stable : (hostTemplate bound).close graph = host)
    (steps : Steps a h (instantiate 0 graph (p.operation.symbolic (hostTemplate bound))) h' term)
    (value : isVal term = true) :
    ∃ k, k ≤ a ∧ PrimitiveRun host p (restore bound outer graph) h k
      (p.bindResult (restore bound outer graph) term) h' .normal := by
  obtain ⟨admin, k, _, count, actual⟩ := Operation.symbolic_invert values steps (fun _ _ => value_no_step value)
  rw [stable, ← operation_restore (outer := outer) (operation_scope scope)] at actual
  exact ⟨k, by omega, .normal actual value⟩

theorem primitive_raise {bound outer graph host p a h h' term v}
    (scope : (Command.step p).InFrame bound) (values : ∀ i, isVal (graph i) = true)
    (stable : (hostTemplate bound).close graph = host)
    (steps : Steps a h (instantiate 0 graph (p.operation.symbolic (hostTemplate bound))) h' term)
    (raised : Raises term v) :
    ∃ k, k ≤ a ∧ PrimitiveRun host p (restore bound outer graph) h k
      (restore bound outer graph) h' (.thrown v) := by
  obtain ⟨admin, k, _, count, actual⟩ := Operation.symbolic_invert values steps (fun _ _ => raises_no_step raised)
  rw [stable, ← operation_restore (outer := outer) (operation_scope scope)] at actual
  exact ⟨k, by omega, .thrown actual raised⟩

/-- Exceptional primitive completion uses the actual thrown value and target
map; only the routing trace changes control after the primitive. -/
theorem primitive_exception {nodes bound outer graph host p stack next broken returned thrown a h h' term v}
    (scope : (Command.step p).InFrame bound) (values : ∀ i, isVal (graph i) = true)
    (stable : (hostTemplate bound).close graph = host)
    (routing : Routes nodes bound stack next broken returned thrown)
    (steps : Steps a h (instantiate 0 graph (p.operation.symbolic (hostTemplate bound))) h' term)
    (raised : Raises term v) :
    NodeResult nodes bound outer host (.command (.step p) stack) graph h a h'
      (.at thrown.label (targetEnv thrown v graph)) := by
  obtain ⟨k, hk, actual⟩ := primitive_raise (outer := outer) scope values stable steps raised
  obtain ⟨site, lookup, tail⟩ := routing.throw_trace host outer graph v h'
  refine ⟨k, site.control bound (targetEnv thrown v graph), restore bound outer (targetEnv thrown v graph), hk, ?_, ?_⟩
  · simpa only [Nat.add_zero, Site.control] using CommandMachine.Runs.next (CommandMachine.Step.primitive actual) tail
  · exact matches_at_site lookup (target_values (raises_val raised) values)
      ((routing.throw_host graph v).trans stable)

/-- Result binding is the real shared map, and its name is inside the source
frame. It cannot overwrite the reserved host or payload slots. -/
theorem primitive_bind_normal {nodes bound outer graph host x op stack next broken returned thrown a h h' term}
    (scope : (Command.step (.bind x op)).InFrame bound) (values : ∀ i, isVal (graph i) = true)
    (stable : (hostTemplate bound).close graph = host)
    (routing : Routes nodes bound stack next broken returned thrown)
    (steps : Steps a h (instantiate 0 graph (op.symbolic (hostTemplate bound))) h' term)
    (value : isVal term = true) :
    NodeResult nodes bound outer host (.command (.step (.bind x op)) stack) graph h a h'
      (.at next (targetEnv (resultTarget bound next x) term graph)) := by
  obtain ⟨k, hk, actual⟩ := primitive_value (outer := outer) scope values stable steps value
  let updated := targetEnv (resultTarget bound next x) term graph
  have envEq : restore bound outer updated = bindName (restore bound outer graph) x term :=
    restore_replace scope.1 outer graph term
  obtain ⟨site, lookup, tail⟩ := routing.normal_trace host outer updated h'
  have first : CommandMachine.Step host (.run (.step (.bind x op)) stack) (restore bound outer graph) h k
      (.exit .normal stack) (restore bound outer updated) h' := by
    rw [envEq]
    exact .primitive actual
  refine ⟨k, site.control bound updated, restore bound outer updated, hk, ?_, ?_⟩
  · simpa only [Nat.add_zero, Site.control] using CommandMachine.Runs.next first tail
  · exact matches_at_site lookup (target_values value values) ((host_replace scope.1 graph term).trans stable)

theorem primitive_perform_normal {nodes bound outer graph host op stack next broken returned thrown a h h' term}
    (scope : (Command.step (.perform op)).InFrame bound) (values : ∀ i, isVal (graph i) = true)
    (stable : (hostTemplate bound).close graph = host)
    (routing : Routes nodes bound stack next broken returned thrown)
    (steps : Steps a h (instantiate 0 graph (op.symbolic (hostTemplate bound))) h' term)
    (value : isVal term = true) :
    NodeResult nodes bound outer host (.command (.step (.perform op)) stack) graph h a h' (.at next graph) := by
  obtain ⟨k, hk, actual⟩ := primitive_value (outer := outer) scope values stable steps value
  obtain ⟨site, lookup, tail⟩ := routing.normal_trace host outer graph h'
  refine ⟨k, site.control bound graph, restore bound outer graph, hk, ?_, ?_⟩
  · simpa only [Nat.add_zero, Site.control] using CommandMachine.Runs.next (CommandMachine.Step.primitive actual) tail
  · exact matches_at_site lookup values stable

theorem primitive_node {P nodes bound outer graph host p stack next broken returned thrown a h h' term after}
    (scope : (Command.step p).InFrame bound) (values : ∀ i, isVal (graph i) = true)
    (stable : (hostTemplate bound).close graph = host)
    (routing : Routes nodes bound stack next broken returned thrown)
    (steps : Steps a h (instantiate 0 graph (p.operation.symbolic (hostTemplate bound))) h' term)
    (leave : ControlFlow.Transition P h'
      (.eval term graph (match p with
        | .bind x _ => .bind (resultTarget bound next x)
        | .perform _ => .effect (target next)) (some thrown)) h' after)
    (outside : OutsideEvaluation after) :
    NodeResult nodes bound outer host (.command (.step p) stack) graph h a h' after := by
  cases p with
  | bind x op =>
    cases leave with
    | expr _ => cases outside
    | bind value => exact primitive_bind_normal scope values stable routing steps value
    | handle raised => exact primitive_exception scope values stable routing steps raised
  | perform op =>
    cases leave with
    | expr _ => cases outside
    | effect value => exact primitive_perform_normal scope values stable routing steps value
    | handle raised => exact primitive_exception scope values stable routing steps raised

end Verification.Paper.TolerantFrames.Compiler
