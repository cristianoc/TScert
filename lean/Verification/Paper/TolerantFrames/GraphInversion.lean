import Verification.Paper.TolerantFrames.OwnFieldCode
import Verification.Programs.GraphCode

/-! # Inverting actual shared callable graph reductions

The existing GraphCode.Sim proof maps graph-machine transitions to shared
reductions. Its converse here maps every actual reduction, retaining exact
counts. This does not assume a graph summary or any node's safety contract.
-/
namespace Verification.Paper.TolerantFrames.Compiler
open Verification ControlFlow HeapObservations

theorem program_lookup {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)}
    {l : Nat} {expression : Tm} {continuation : ControlFlow.Continuation} {handler : Option ControlFlow.Target}
    (he : E[l]? = some expression) (hk : K[l]? = some (continuation, handler)) :
    (GraphCode.program E K)[l]? = some ⟨expression, continuation, handler⟩ := by
  simp only [GraphCode.program, List.getElem?_map]
  exact Option.map_eq_some_iff.mpr
    ⟨(expression, continuation, handler), List.getElem?_zip_eq_some.mpr ⟨he, hk⟩, rfl⟩

/-- Every actual shared graph reduction corresponds to one graph transition. -/
theorem step_back {E K term state h h' term'} (sim : GraphCode.Sim E K term state)
    (step : Verification.Step h term h' term') :
    ∃ state', ControlFlow.Transition (GraphCode.program E K) h state h' state' ∧
      GraphCode.Sim E K term' state' := by
  cases sim with
  | goto =>
    cases step with
    | gotoEnter he hk => exact ⟨_, .enter (program_lookup he hk), .frame⟩
  | frame =>
    cases step with
    | frameC st => exact ⟨_, .expr st, .frame⟩
    | frameRet hv => exact ⟨_, .ret hv, .done hv⟩
    | frameBind hv =>
      refine ⟨_, .bind hv, ?_⟩
      rw [GraphCode.push_envOf]
      exact GraphCode.sim_goto
    | frameEffect hv => exact ⟨_, .effect hv, GraphCode.sim_goto⟩
    | frameYes => exact ⟨_, .yes, GraphCode.sim_goto⟩
    | frameNo => exact ⟨_, .no, GraphCode.sim_goto⟩
    | frameYesBind =>
      refine ⟨_, .yesBind, ?_⟩
      rw [GraphCode.push_envOf]
      exact GraphCode.sim_goto
    | frameNoBind =>
      refine ⟨_, .noBind, ?_⟩
      rw [GraphCode.push_envOf]
      exact GraphCode.sim_goto
    | frameTag hv =>
      refine ⟨_, .tagBind hv, ?_⟩
      rw [GraphCode.push_envOf]
      exact GraphCode.sim_goto
    | frameHandle hr =>
      refine ⟨_, .handle hr, ?_⟩
      rw [GraphCode.push_envOf]
      exact GraphCode.sim_goto
    | frameRaise hr => exact ⟨_, .raise hr, .raised (raises_val hr) (raises_sourceVal hr)⟩
  | done hv => exact False.elim (value_no_step hv step)
  | raised hv hs => exact False.elim (raises_no_step (.throwV hv hs) step)

/-- All shared reductions of graph code invert, including expression steps,
handlers and terminal sinks, with exactly the same total count. -/
theorem steps_back {E K n h term h' term'} (run : Steps n h term h' term') :
    ∀ {state}, GraphCode.Sim E K term state →
      ∃ state', Execution (GraphCode.program E K) n h state h' state' ∧
        GraphCode.Sim E K term' state' := by
  induction run with
  | refl => intro state sim; exact ⟨state, .refl, sim⟩
  | next step _ ih =>
    intro state sim
    obtain ⟨middle, st, hm⟩ := step_back sim step
    obtain ⟨final, run, hf⟩ := ih hm
    exact ⟨final, .next st run, hf⟩

/-- A returned shared value is the graph's actual done state. -/
theorem value_state {E K v state} (sim : GraphCode.Sim E K v state) (hv : isVal v = true) :
    state = .done v := by
  cases sim with
  | goto | frame | raised => simp [isVal] at hv
  | done => rfl

/-- A raised shared terminal corresponds to the graph's exceptional sink. -/
theorem raised_state {E K term v state} (sim : GraphCode.Sim E K term state) (hr : Raises term v) :
    state = .raised v := by
  cases sim with
  | goto | frame => cases hr
  | done hv => exact False.elim (by simpa [hv] using raises_not_val hr)
  | raised hv _ =>
    cases hr with
    | throwV _ _ => rfl
    | throwC inner => exact False.elim (by simpa [hv] using raises_not_val inner)

end Verification.Paper.TolerantFrames.Compiler
