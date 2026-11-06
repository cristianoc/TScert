import Verification.Source.Claims.Linking
import Verification.Semantics.I64
import Verification.Source.PrimitiveBoundary

/-! # Conditional safety of a deployed linked program

Runtime machines use observation steps, which may group implementation steps.
The simulation premises include progress: a model step must have a matching
runtime step, or an already safe terminal runtime state. A relation that only
matches completed executions is insufficient. No compiler or engine simulation
is asserted here; each is a named premise of `end_to_end`.
-/
namespace Verification.LinkedRuntime
open PositiveGraphs PositiveRules Tower ProgramTyping ControlFlow
open SourceClaimJson SourceExtraction RequestJson

structure Machine where
  State : Nat → Type
  terminal : (n : Nat) → State n → Prop
  step : {n : Nat} → State (n + 1) → State n → Prop

@[nospecialize] def Machine.CanRun (M : Machine) : (n : Nat) → M.State n → Prop
  | 0, _ => True
  | n + 1, s => M.terminal (n + 1) s ∨ ∃ t, M.step s t ∧ M.CanRun n t

/-- Every transition preserves safety; a nonterminal state has a successor. -/
@[nospecialize] def Machine.Safe (M : Machine) : (n : Nat) → M.State n → Prop
  | 0, _ => True
  | n + 1, s => (M.terminal (n + 1) s ∨ ∃ t, M.step s t) ∧
      ∀ t, M.step s t → M.Safe n t

/-- Observation machines are deterministic and terminal states have no steps. -/
structure Machine.Deterministic (M : Machine) : Prop where
  unique : ∀ n (s : M.State (n + 1)) t u, M.step s t → M.step s u → t = u
  stopped : ∀ n (s : M.State (n + 1)) t, M.terminal (n + 1) s → ¬ M.step s t

theorem Machine.canRun_safe {M : Machine} (det : M.Deterministic) {n s}
    (safe : M.CanRun n s) : M.Safe n s := by
  induction n with
  | zero => trivial
  | succ n ih =>
    rcases safe with terminal | ⟨t, step, rest⟩
    · exact ⟨.inl terminal, fun t h => (det.stopped n s t terminal h).elim⟩
    · refine ⟨.inr ⟨t, step⟩, ?_⟩
      intro u hu
      have eq := det.unique n s t u step hu
      subst u
      exact ih rest

/-- Progress and result-contract preserving implementation correspondence.
The target's terminal predicate includes result types and permitted throws.
The relation may carry heap, glue-state, artifact and loading invariants. -/
structure Simulation (model runtime : Machine) where
  deterministic : runtime.Deterministic
  related : (n : Nat) → model.State n → runtime.State n → Prop
  terminal : ∀ n s t, related n s t → model.terminal n s → runtime.terminal n t
  step : ∀ n s t s', related (n + 1) s t → model.step s s' →
    runtime.terminal (n + 1) t ∨ ∃ t', runtime.step t t' ∧ related n s' t'

/-- Core graph states include their step-indexed world and shared heap. -/
structure GraphState (n : Nat) where
  world : WorldT n
  heap : Heap
  state : ControlFlow.State

@[nospecialize] def graphMachine (Ξ : Fam) (P : Program) (result : Fam) : Machine where
  State := GraphState
  terminal := fun n s =>
    (∃ v, s.state = .done v ∧ isVal v = true ∧ result n s.world v) ∨
    (∃ v, s.state = .raised v ∧ Scoped 0 v ∧ Ξ n s.world v)
  step := fun {n} s t =>
    WExt (trunc n (Nat.le_succ n) s.world) t.world ∧ WorldAdm t.world ∧
    Transition P s.heap s.state t.heap t.state ∧ HeapOk n t.world t.heap

theorem Simulation.canRun {M N : Machine} (sim : Simulation M N) {n s t}
    (related : sim.related n s t) (safe : M.CanRun n s) : N.CanRun n t := by
  induction n with
  | zero => trivial
  | succ n ih =>
    rcases safe with terminal | ⟨s', step, rest⟩
    · exact .inl (sim.terminal _ _ _ related terminal)
    · rcases sim.step n s t s' related step with terminal | ⟨t', step', related'⟩
      · exact .inl terminal
      · exact .inr ⟨t', step', ih related' rest⟩

theorem graph_safe {Ξ P result n W heap state}
    (safe : SafeGraph Ξ P result n W heap state) :
    (graphMachine Ξ P result).CanRun n ⟨W, heap, state⟩ := by
  induction n generalizing heap state with
  | zero => trivial
  | succ n ih =>
    rcases safe with terminal | ⟨U, h', s', ext, adm, step, heapOk, rest⟩
    · exact .inl terminal
    · exact .inr ⟨⟨U, h', s'⟩, ⟨ext, adm, step, heapOk⟩, ih rest⟩

/-- **Conditional linked TS/Rust/Wasm safety.** The finite export family has
certified invocation specifications and structural acyclic stable links.
The caller request is accepted (`RequestsSafe` from `checkUnitJson_safe`).
The assembled slots transport signatures, obtainable for the demo's closed
primitive signatures by `PrimitiveBoundary.transport` and graph attachments.
Entry separation, external contracts, admitted parameters, world and heap
invariants remain premises. Initialization is complete; exports are fixed;
cyclic imports, live-binding writes and re-exports are outside this scope.

Runtime premises, all explicit simulations with progress and result contracts
and deterministic targets whose terminal states have no outgoing transitions:
* `typescriptLowering`: faithful TypeScript lowering/extraction;
* `rustTranslation`: faithful Rust translation, including signed arithmetic
  and the wrapping bigint adapter (`I64`);
* `rustc`: the selected release compiler and Wasm backend;
* `wasmBindgen`: conversions, allocation, panic/trap and adapter-state behavior;
* `engine`: engine execution, module loading and the deployment's artifacts.
The initial related-state premises bind those simulations to this entry and
these artifacts. Adapter states must preserve invariants on throws or exclude
reuse after a trap. These premises are assumptions about implementations;
the theorem adds no axioms and proves no compiler correspondence itself. -/
theorem end_to_end {labels : Fin count → Type}
    {exports : (i : Fin count) → Linking.Export (labels i)}
    (linked : Linking.WellLinked exports) {F : EquationStore.Frozen}
    {rs : List (SourceRequest (EquationStore.Checked F.equations F.primitive)
      (EquationStore.CheckedLabel F.equations F.primitive))}
    {b : Bundle (EquationStore.CheckedLabel F.equations F.primitive)}
    (accepted : RequestsSafe F rs b) {r c} (member : (r, c) ∈ rs.zip b.functions)
    {η} (admitted : r.Admits η) {ρ : Env} (closed : ∀ k, Scoped 0 (ρ k))
    (slots : ∀ k A, r.inputs[k]? = some A →
      ((∀ j, ρ k ≠ (exports j).value) ∧
        ∀ n W, meaning (reassign F.equations.graph η) A n W (ρ k)) ∨
      ∃ j, ρ k = (exports j).value ∧ ∀ n W v,
        meaning (exports j).graph (exports j).signature n W v ↔
          meaning (reassign F.equations.graph η) A n W v)
    {n W heap} (separation : HeapSeparation.Holds r.entrySeparation ρ)
    (world : WorldAdm W) (heapOk : HeapOk n W heap)
    {ts rust wasm glue deployed : Machine}
    (typescriptLowering : Simulation
      (graphMachine (excOf (reassign F.equations.graph η)) r.program
        (GoalHolds (reassign F.equations.graph η) r.goal (r.goal.argument ρ))) ts)
    (rustTranslation : Simulation ts rust) (rustc : Simulation rust wasm)
    (wasmBindgen : Simulation wasm glue) (engine : Simulation glue deployed)
    {tsState rustState wasmState glueState deployedState}
    (tsInitial : typescriptLowering.related n ⟨W, heap, .at r.start ρ⟩ tsState)
    (rustInitial : rustTranslation.related n tsState rustState)
    (wasmInitial : rustc.related n rustState wasmState)
    (glueInitial : wasmBindgen.related n wasmState glueState)
    (deployment : engine.related n glueState deployedState) :
    deployed.Safe n deployedState := by
  have modeled := Linking.entries_safe linked accepted member admitted closed slots separation world heapOk
  apply Machine.canRun_safe engine.deterministic
  exact engine.canRun deployment (wasmBindgen.canRun glueInitial (rustc.canRun wasmInitial
    (rustTranslation.canRun rustInitial (typescriptLowering.canRun tsInitial (graph_safe modeled)))))

end Verification.LinkedRuntime
