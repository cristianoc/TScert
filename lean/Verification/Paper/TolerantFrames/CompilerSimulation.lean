import Verification.Paper.TolerantFrames.CompilerOrigins
import Verification.Paper.TolerantFrames.GraphSegments
import Verification.Paper.TolerantFrames.PureOperations

/-! # Matching actual graph and command control states

The relation retains the named environment at terminal sinks. Machine values
and stable host code are representation invariants; source/world validity is
supplied separately by the body Triple, never inferred from arbitrary runs.
-/
namespace Verification.Paper.TolerantFrames.Compiler
open Verification ControlFlow HeapObservations

inductive Matches (nodes : List AnnotatedNode) (bound : Nat) (outer : Env) (host : NativeCode) :
    ControlFlow.State → CommandMachine.Control → Env → Prop where
  | at {label graph node} : nodes[label]? = some node →
      (∀ i, isVal (graph i) = true) → (hostTemplate bound).close graph = host →
      Matches nodes bound outer host (.at label graph) (node.site.control bound graph) (restore bound outer graph)
  | normal {ρ} : Matches nodes bound outer host (.done .undef) (.exit .normal []) ρ
  | broken {ρ} : Matches nodes bound outer host (.done .undef) (.exit .break []) ρ
  | returned {ρ v} : Matches nodes bound outer host (.done v) (.exit (.returned v) []) ρ
  | thrown {ρ v} : Matches nodes bound outer host (.raised v) (.exit (.thrown v) []) ρ

theorem matches_at_site {nodes bound outer host label site graph}
    (lookup : (nodes[label]?).map AnnotatedNode.site = some site)
    (values : ∀ i, isVal (graph i) = true) (stable : (hostTemplate bound).close graph = host) :
    Matches nodes bound outer host (.at label graph) (site.control bound graph) (restore bound outer graph) := by
  obtain ⟨node, nodeLookup, rfl⟩ := Option.map_eq_some_iff.mp lookup
  exact .at nodeLookup values stable

theorem target_values {destination : Target} {v : Tm} {graph : Env}
    (value : isVal v = true) (values : ∀ i, isVal (graph i) = true) :
    ∀ i, isVal (targetEnv destination v graph i) = true := by
  intro i
  unfold targetEnv PointClaims.mapEnv
  generalize PointClaims.slot destination.mapping i = j
  cases j with
  | zero => exact value
  | succ j => exact values j

theorem argument_value {a : Argument} {graph : Env} (values : ∀ i, isVal (graph i) = true) :
    isVal (a.eval graph) = true := by
  cases a with
  | «variable» i => exact values i
  | literal v => cases v <;> first | rfl | (rename_i b; cases b <;> rfl)

theorem argument_restore {a : Argument} {bound outer graph}
    (scope : a.Scoped (· < bound)) : a.eval (restore bound outer graph) = a.eval graph :=
  Argument.scoped_eval_eq scope (fun _ hi => by simp [restore, hi])

theorem restore_drop (bound : Nat) (outer graph : Env) (v : Tm) :
    restore bound outer (PointClaims.mapEnv (dropMap (width bound)) (push v graph)) =
      restore bound outer graph := by
  funext i
  by_cases hi : i < bound
  · simp only [restore, hi, ↓reduceIte]
    exact mapped_drop (by unfold width; omega) graph v
  · simp [restore, hi]

theorem host_drop (bound : Nat) (graph : Env) (v : Tm) :
    (hostTemplate bound).close (PointClaims.mapEnv (dropMap (width bound)) (push v graph)) =
      (hostTemplate bound).close graph := by
  simp only [hostTemplate, NativeCode.close, instantiate, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
  congr 1 <;> exact mapped_drop (by unfold width; omega) graph v

/-- Real throw expressions at value arguments make no further expression
step, even for an internal value which cannot be thrown as a source value. -/
theorem throw_value_steps {n h v h' term} (value : isVal v = true)
    (steps : Steps n h (.throw v) h' term) : n = 0 ∧ h' = h ∧ term = .throw v := by
  cases steps with
  | refl => exact ⟨rfl, rfl, rfl⟩
  | next first _ => cases first with | throwC step => exact False.elim (value_no_step value step)

/-- The proved outcome of one actually completed node. It is not a supplied
body summary: Origin plus the real expression/leave run will establish it. -/
def NodeResult (nodes : List AnnotatedNode) (bound : Nat) (outer : Env) (host : NativeCode)
    (site : Site) (graph : Env) (before : Heap) (expressionCount : Nat) (after : Heap)
    (next : ControlFlow.State) : Prop :=
  ∃ p ctrl ρ, p ≤ expressionCount ∧
    CommandMachine.Runs host (site.control bound graph) (restore bound outer graph) before p ctrl ρ after ∧
    Matches nodes bound outer host next ctrl ρ

end Verification.Paper.TolerantFrames.Compiler
