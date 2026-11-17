import Verification.Paper.TolerantFrames.CompilerNodeSimulation

/-! # Whole generated-command graph inversion

Induction is on actual shared graph transitions. Each node contributes at most
its expression count to primitive weight; dispatch/leave steps make the suffix
strictly smaller even around zero-weight B loops. No body summary is assumed.
-/
namespace Verification.Paper.TolerantFrames.Compiler
open Verification ControlFlow HeapObservations

def graphProgram (nodes : List AnnotatedNode) : Program := GraphCode.program (expressions nodes) (continuations nodes)

def Terminal : ControlFlow.State → Prop
  | .done _ | .raised _ => True
  | _ => False

theorem terminal_outside {state : ControlFlow.State} (terminal : Terminal state) : OutsideEvaluation state := by
  cases state <;> first | exact terminal | trivial

def resultState : Exit → ControlFlow.State
  | .normal | .break => .done .undef
  | .returned v => .done v
  | .thrown v => .raised v

theorem Matches.terminal {nodes bound outer host state ctrl ρ}
    (matching : Matches nodes bound outer host state ctrl ρ) (terminal : Terminal state) :
    ∃ e, ctrl = .exit e [] ∧ state = resultState e := by
  cases matching with
  | «at» => cases terminal
  | normal => exact ⟨.normal, rfl, rfl⟩
  | broken => exact ⟨.break, rfl, rfl⟩
  | returned => exact ⟨.returned _, rfl, rfl⟩
  | thrown => exact ⟨.thrown _, rfl, rfl⟩

theorem machineRuns_append {host ctrl ρ h p middle ρ₁ h₁ q final ρ₂ h₂}
    (first : CommandMachine.Runs host ctrl ρ h p middle ρ₁ h₁)
    (second : CommandMachine.Runs host middle ρ₁ h₁ q final ρ₂ h₂) :
    CommandMachine.Runs host ctrl ρ h (p + q) final ρ₂ h₂ := by
  induction first with
  | refl => simpa using second
  | next step _ ih => simpa [Nat.add_assoc] using CommandMachine.Runs.next step (ih second)

/-- Every real terminating graph run yields a finite command trace, retaining
the final named environment before the graph sink discards its frame. -/
theorem graph_trace {nodes bound outer host}
    (origins : ∀ node ∈ nodes, Origin nodes bound node) :
    ∀ n {start ctrl ρ h h' final}, Matches nodes bound outer host start ctrl ρ →
      Execution (graphProgram nodes) n h start h' final → Terminal final →
      ∃ p finalControl finalEnv, p ≤ n ∧ CommandMachine.Runs host ctrl ρ h p finalControl finalEnv h' ∧
        Matches nodes bound outer host final finalControl finalEnv := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro start ctrl ρ h h' final matching run terminal
    cases matching with
    | «at» lookup values stable =>
      cases run with
      | refl => cases terminal
      | next first rest =>
        cases first with
        | enter actual =>
          have encoded := program_lookup_annotated lookup
          have same := Option.some.inj (encoded.symm.trans actual)
          cases same
          obtain ⟨a, middleHeap, middleTerm, next, q, count, expressionRun, leave, outside, suffixRun⟩ :=
            evaluation_segment rest (terminal_outside terminal)
          have origin := origins _ (List.mem_of_getElem? lookup)
          obtain ⟨p, middleControl, middleEnv, hp, trace, nextMatching⟩ :=
            origin.node_result (outer := outer) values stable expressionRun leave outside
          obtain ⟨r, finalControl, finalEnv, hr, remaining, finalMatching⟩ :=
            ih q (by omega) nextMatching suffixRun terminal
          exact ⟨p + r, finalControl, finalEnv, by omega, machineRuns_append trace remaining, finalMatching⟩
    | normal =>
      cases run with
      | refl => exact ⟨0, .exit .normal [], _, Nat.le_refl _, .refl, .normal⟩
      | next first _ => cases first
    | broken =>
      cases run with
      | refl => exact ⟨0, .exit .break [], _, Nat.le_refl _, .refl, .broken⟩
      | next first _ => cases first
    | returned =>
      cases run with
      | refl => exact ⟨0, .exit (.returned _) [], _, Nat.le_refl _, .refl, .returned⟩
      | next first _ => cases first
    | thrown =>
      cases run with
      | refl => exact ⟨0, .exit (.thrown _) [], _, Nat.le_refl _, .refl, .thrown⟩
      | next first _ => cases first

theorem envOf_values {L : List Tm} {d : Tm}
    (values : ∀ v ∈ L, isVal v = true) (default : isVal d = true) : ∀ i, isVal (envOf L d i) = true := by
  intro i
  rcases getD_mem_or L i d with member | same
  · exact values _ member
  · simpa only [envOf, same] using default

/-- Concrete generated graphs invert for EVERY finite raw command. A finite
frame bound and all routing/node evidence are generated, never external premises.
Host values are a representation condition, with no native safety inferred. -/
theorem compiled_execution (c : Command) (host : NativeCode) (ρ : Env) (h : Heap)
    (values : ∀ i, isVal (ρ i) = true)
    (hostValues : isVal host.viewRead = true ∧ isVal host.viewWrite = true ∧ isVal host.viewLength = true)
    {n h' final}
    (run : Execution (graphProgram (compile c.frameBound c)) n h
      (.at 4 (envOf (slots c.frameBound ρ host .undef) .undef)) h' final)
    (terminal : Terminal final) :
    ∃ p ρ' e, p ≤ n ∧ Executes host c ρ h p ρ' h' e ∧ final = resultState e := by
  let graph := envOf (slots c.frameBound ρ host .undef) .undef
  have graphValues : ∀ i, isVal (graph i) = true := envOf_values (slots_values values hostValues rfl) rfl
  have matching : Matches (compile c.frameBound c) c.frameBound ρ host (.at 4 graph)
      ((frontSite c []).control c.frameBound graph) (restore c.frameBound ρ graph) :=
    matches_at_site (compile_entry c.frameBound c) graphValues (slots_host _ _ _ _ _)
  obtain ⟨p, finalControl, finalEnv, count, trace, finalMatching⟩ :=
    graph_trace (compile_origins c) n matching run terminal
  obtain ⟨e, rfl, result⟩ := finalMatching.terminal terminal
  rw [frontSite_control] at trace
  have restored : restore c.frameBound ρ graph = ρ := restore_slots _ _ _ _ _
  rw [restored] at trace
  have whole := machineRuns_append (front_trace c [] host ρ h) trace
  exact ⟨p, finalEnv, e, count, CommandMachine.Runs.executes (by simpa only [Nat.zero_add] using whole), result⟩

/-- Code is fixed by c; the values occur only in its runtime frame. -/
def compiledEntry (c : Command) (host : NativeCode) (ρ : Env) : Tm :=
  let nodes := compile c.frameBound c
  .goto (expressions nodes) (continuations nodes) 4 (slots c.frameBound ρ host .undef) .undef

/-- Actual shared reductions to a value yield the original structured command
and distinguish normal fallthrough, returned value and an escaping break. -/
theorem compiled_value (c : Command) (host : NativeCode) (ρ : Env) (h : Heap)
    (values : ∀ i, isVal (ρ i) = true)
    (hostValues : isVal host.viewRead = true ∧ isVal host.viewWrite = true ∧ isVal host.viewLength = true)
    {n h' v} (run : Steps n h (compiledEntry c host ρ) h' v) (value : isVal v = true) :
    ∃ p ρ' e, p ≤ n ∧ Executes host c ρ h p ρ' h' e ∧ ControlFlow.State.done v = resultState e := by
  obtain ⟨state, graphRun, simulation⟩ := steps_back run GraphCode.Sim.goto
  have terminalState := value_state simulation value
  rw [terminalState] at graphRun
  exact compiled_execution c host ρ h values hostValues graphRun trivial

/-- Actual shared exceptional completion yields the very same thrown value;
internal values cannot be caught through a fabricated direct jump. -/
theorem compiled_raise (c : Command) (host : NativeCode) (ρ : Env) (h : Heap)
    (values : ∀ i, isVal (ρ i) = true)
    (hostValues : isVal host.viewRead = true ∧ isVal host.viewWrite = true ∧ isVal host.viewLength = true)
    {n h' term v} (run : Steps n h (compiledEntry c host ρ) h' term) (raised : Raises term v) :
    ∃ p ρ', p ≤ n ∧ Executes host c ρ h p ρ' h' (.thrown v) := by
  obtain ⟨state, graphRun, simulation⟩ := steps_back run GraphCode.Sim.goto
  have terminalState := raised_state simulation raised
  rw [terminalState] at graphRun
  obtain ⟨p, ρ', e, hp, commandRun, result⟩ := compiled_execution c host ρ h values hostValues graphRun trivial
  cases e with
  | normal | «break» | returned _ => cases result
  | thrown w => cases result; exact ⟨p, ρ', hp, commandRun⟩

end Verification.Paper.TolerantFrames.Compiler
