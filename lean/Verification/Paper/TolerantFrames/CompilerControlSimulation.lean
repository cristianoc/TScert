import Verification.Paper.TolerantFrames.CompilerPrimitiveSimulation

/-! # Completed administrative/control nodes

The existing control machine handles branch/loop/return/throw/break. Each proof
uses the real graph expression and leave transition; no stuck expression is
silently admitted as a successful control operation.
-/
namespace Verification.Paper.TolerantFrames.Compiler
open Verification ControlFlow HeapObservations

theorem loop_node {P nodes bound outer graph host body stack next broken returned thrown bodyLabel a h h' term after}
    (values : ∀ i, isVal (graph i) = true) (stable : (hostTemplate bound).close graph = host)
    (_routing : Routes nodes bound stack next broken returned thrown)
    (bodySite : (nodes[bodyLabel]?).map AnnotatedNode.site = some (frontSite body (.loop body :: stack)))
    (steps : Steps a h .undef h' term)
    (leave : ControlFlow.Transition P h' (.eval term graph (.effect (target bodyLabel)) none) h' after)
    (outside : OutsideEvaluation after) :
    NodeResult nodes bound outer host (.command (.loop body) stack) graph h a h' after := by
  obtain ⟨rfl, rfl, rfl⟩ := steps_from_value rfl steps
  cases leave with
  | expr _ => cases outside
  | effect _ =>
    refine ⟨0, (frontSite body (.loop body :: stack)).control bound graph, restore bound outer graph,
      Nat.le_refl _, ?_, matches_at_site bodySite values stable⟩
    rw [frontSite_control]
    simpa only [Site.control] using
      CommandMachine.Runs.next CommandMachine.Step.loop (front_trace body (.loop body :: stack) host (restore bound outer graph) h')
  | raise raised => cases raised

theorem break_node {P nodes bound outer graph host stack next broken returned thrown a h h' term after}
    (values : ∀ i, isVal (graph i) = true) (stable : (hostTemplate bound).close graph = host)
    (routing : Routes nodes bound stack next broken returned thrown)
    (steps : Steps a h .undef h' term)
    (leave : ControlFlow.Transition P h' (.eval term graph (.effect (target broken)) none) h' after)
    (outside : OutsideEvaluation after) :
    NodeResult nodes bound outer host (.command .break_ stack) graph h a h' after := by
  obtain ⟨rfl, rfl, rfl⟩ := steps_from_value rfl steps
  cases leave with
  | expr _ => cases outside
  | effect _ =>
    obtain ⟨site, lookup, tail⟩ := routing.break_trace host outer graph h'
    refine ⟨0, site.control bound graph, restore bound outer graph, Nat.le_refl _, ?_, matches_at_site lookup values stable⟩
    simpa only [Site.control] using CommandMachine.Runs.next CommandMachine.Step.broken tail
  | raise raised => cases raised

theorem return_node {P nodes bound outer graph host value stack next broken returned thrown a h h' term after}
    (scope : value.Scoped (· < bound))
    (values : ∀ i, isVal (graph i) = true) (stable : (hostTemplate bound).close graph = host)
    (routing : Routes nodes bound stack next broken returned thrown)
    (steps : Steps a h (instantiate 0 graph (value.code 0)) h' term)
    (leave : ControlFlow.Transition P h' (.eval term graph (.bind (payloadTarget bound returned)) none) h' after)
    (outside : OutsideEvaluation after) :
    NodeResult nodes bound outer host (.command (.return_ value) stack) graph h a h' after := by
  rw [Argument.instantiate_code] at steps
  have hv : isVal (value.eval graph) = true := argument_value values
  obtain ⟨rfl, rfl, rfl⟩ := steps_from_value hv steps
  generalize he : value.eval graph = result at leave hv
  cases leave with
  | expr _ => cases outside
  | bind _ =>
    let updated := targetEnv (payloadTarget bound returned) result graph
    obtain ⟨lookup, tail⟩ := routing.return_trace host outer graph result h'
    have argEq : value.eval (restore bound outer graph) = result := (argument_restore scope).trans he
    have first : CommandMachine.Step host (.run (.return_ value) stack) (restore bound outer graph) h' 0
        (.exit (.returned result) stack) (restore bound outer graph) h' := by
      rw [← argEq]
      exact .returned (by rw [argEq]; exact hv)
    refine ⟨0, Site.returned.control bound updated, restore bound outer updated, Nat.le_refl _, ?_, ?_⟩
    · simpa only [Site.control] using CommandMachine.Runs.next first tail
    · exact matches_at_site lookup (target_values hv values) ((host_payload bound graph result).trans stable)
  | raise raised => exact False.elim (by simpa [hv] using raises_not_val raised)

theorem throw_node {P nodes bound outer graph host value stack next broken returned thrown a h h' term after}
    (scope : value.Scoped (· < bound))
    (values : ∀ i, isVal (graph i) = true) (stable : (hostTemplate bound).close graph = host)
    (routing : Routes nodes bound stack next broken returned thrown)
    (steps : Steps a h (instantiate 0 graph (.throw (value.code 0))) h' term)
    (leave : ControlFlow.Transition P h' (.eval term graph (.effect (target next)) (some thrown)) h' after)
    (outside : OutsideEvaluation after) :
    NodeResult nodes bound outer host (.command (.throw_ value) stack) graph h a h' after := by
  change Steps a h (.throw (instantiate 0 graph (value.code 0))) h' term at steps
  rw [Argument.instantiate_code] at steps
  have hv : isVal (value.eval graph) = true := argument_value values
  obtain ⟨rfl, rfl, rfl⟩ := throw_value_steps hv steps
  generalize he : value.eval graph = result at leave hv
  cases leave with
  | expr _ => cases outside
  | effect bad => cases bad
  | handle raised =>
    cases raised with
    | throwC inner => exact False.elim (by simpa [hv] using raises_not_val inner)
    | throwV _ _ =>
      obtain ⟨site, lookup, tail⟩ := routing.throw_trace host outer graph result h'
      have argEq : value.eval (restore bound outer graph) = result := (argument_restore scope).trans he
      have first : CommandMachine.Step host (.run (.throw_ value) stack) (restore bound outer graph) h' 0
          (.exit (.thrown result) stack) (restore bound outer graph) h' := by
        rw [← argEq]
        exact .thrown (by rw [argEq]; exact hv)
      refine ⟨0, site.control bound (targetEnv thrown result graph), restore bound outer (targetEnv thrown result graph),
        Nat.le_refl _, ?_, ?_⟩
      · simpa only [Site.control] using CommandMachine.Runs.next first tail
      · exact matches_at_site lookup (target_values hv values) ((routing.throw_host graph result).trans stable)

theorem choice_node {P nodes bound outer graph host test yes no stack yesLabel noLabel a h h' term after}
    (scope : test.Scoped (· < bound))
    (values : ∀ i, isVal (graph i) = true) (stable : (hostTemplate bound).close graph = host)
    (yesSite : (nodes[yesLabel]?).map AnnotatedNode.site = some (frontSite yes stack))
    (noSite : (nodes[noLabel]?).map AnnotatedNode.site = some (frontSite no stack))
    (steps : Steps a h (instantiate 0 graph (test.code 0)) h' term)
    (leave : ControlFlow.Transition P h' (.eval term graph
      (.tagBind .truthy ⟨yesLabel, dropMap (width bound)⟩ ⟨noLabel, dropMap (width bound)⟩) none) h' after)
    (outside : OutsideEvaluation after) :
    NodeResult nodes bound outer host (.command (.choice test yes no) stack) graph h a h' after := by
  rw [Argument.instantiate_code] at steps
  have hv : isVal (test.eval graph) = true := argument_value values
  obtain ⟨rfl, rfl, rfl⟩ := steps_from_value hv steps
  generalize he : test.eval graph = result at leave hv
  cases leave with
  | expr _ => cases outside
  | raise raised => exact False.elim (by simpa [hv] using raises_not_val raised)
  | tagBind _ =>
    have ht : tagHoldsIn h' .truthy result = tagHolds .truthy result := by cases result <;> rfl
    rw [ht]
    let updated := PointClaims.mapEnv (dropMap (width bound)) (push result graph)
    have envEq : restore bound outer updated = restore bound outer graph := restore_drop bound outer graph result
    have argEq : test.eval (restore bound outer graph) = result := (argument_restore scope).trans he
    cases hb : tagHolds .truthy result
    · refine ⟨0, (frontSite no stack).control bound updated, restore bound outer updated, Nat.le_refl _, ?_, ?_⟩
      · rw [frontSite_control, envEq]
        simpa only [Site.control] using CommandMachine.Runs.next
          (CommandMachine.Step.no (by rw [argEq]; exact hb))
          (front_trace no stack host (restore bound outer graph) h')
      · exact matches_at_site noSite
          (target_values (destination := ⟨noLabel, dropMap (width bound)⟩) hv values)
          ((host_drop bound graph result).trans stable)
    · refine ⟨0, (frontSite yes stack).control bound updated, restore bound outer updated, Nat.le_refl _, ?_, ?_⟩
      · rw [frontSite_control, envEq]
        simpa only [Site.control] using CommandMachine.Runs.next
          (CommandMachine.Step.yes (by rw [argEq]; exact hb))
          (front_trace yes stack host (restore bound outer graph) h')
      · exact matches_at_site yesSite
          (target_values (destination := ⟨yesLabel, dropMap (width bound)⟩) hv values)
          ((host_drop bound graph result).trans stable)

end Verification.Paper.TolerantFrames.Compiler
