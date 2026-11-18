import Verification.Paper.TolerantFrames.OwnFieldCode

/-! # Fixed symbolic code for every paper operation

The existing Operation.code interpreter supplies closed terms. Symbolic code
uses the shared closing substitution and the own-field administrative prefix.
Host terms may be captured graph slots; they are closed by the SAME environment.
No hypothesis asserts the safety or specification of arbitrary native code.
-/
namespace Verification.Paper.TolerantFrames
open Verification HeapObservations

/-- A source argument under `depth` internal de Bruijn binders. -/
def Argument.code (depth : Nat) : Argument → Tm
  | .variable x => .var (x + depth)
  | .literal v => v.eval

theorem Argument.instantiate_code (d : Nat) (ρ : Env) (a : Argument) :
    instantiate d ρ (a.code d) = a.eval ρ := by
  cases a with
  | «variable» x => simp [Argument.code, Argument.eval, instantiate, Nat.not_lt_of_ge (Nat.le_add_left d x)]
  | literal v => cases v <;> first | rfl | (rename_i b; cases b <;> rfl)

/-- Native code is closed by the same graph environment as its operands. -/
def NativeCode.close (host : NativeCode) (ρ : Env) : NativeCode :=
  ⟨instantiate 0 ρ host.viewRead, instantiate 0 ρ host.viewWrite, instantiate 0 ρ host.viewLength⟩

/-- The fixed operation term. Element-write's returned operand is shifted
under the internal let, so it still denotes the original argument. -/
def Operation.symbolic (host : NativeCode) : Operation → Tm
  | .value a => a.code 0
  | .binary op a b => .arith op (a.code 0) (b.code 0)
  | .not a => .ite (.test .truthy (a.code 0)) .fls .tru
  | .and a b => .ite (.test .truthy (a.code 0)) (b.code 0) (a.code 0)
  | .or a b => .ite (.test .truthy (a.code 0)) (a.code 0) (b.code 0)
  | .fieldRead x f => ownFieldCode (.str f) (.var x)
  | .fieldWrite x f a => .writeAt (.str f) (.var x) (a.code 0)
  | .elementRead x i => .elemAt (.readAt arraySpineKey (.var x)) (i.code 0)
  | .elementWrite x i v => .letE (.writeAt arraySpineKey (.var x)
      (.setElem (.readAt arraySpineKey (.var x)) (i.code 0) (v.code 0))) (v.code 1)
  | .arrayLength x => .lenOf (.readAt arraySpineKey (.var x))
  | .viewRead x i => .invoke host.viewRead (.var x) [i.code 0]
  | .viewWrite x i v => .invoke host.viewWrite (.var x) [i.code 0, v.code 0]
  | .viewLength x => .invoke host.viewLength (.var x) []
  | .stringRead x i => .elemAt (.var x) (i.code 0)
  | .stringLength x => .lenOf (.var x)
  | .objectLiteral fs => .makeAt .absent (fs.map fun p => .str p.1) (fs.map fun p => p.2.code 0)
  | .arrayLiteral es => .makeAt .absent [arraySpineKey] [.arrLit (es.map (Argument.code 0))]
  | .nativeCall f receiver args => .invoke (.var f) (receiver.code 0) (args.map (Argument.code 0))
  | .methodCall x f args => .invoke (.readAt (.str f) (.var x)) (.var x) (args.map (Argument.code 0))
  | .call f args => .invoke (.var f) .undef (args.map (Argument.code 0))
  | .construct f args => .construct (.var f) (args.map (Argument.code 0))

/-- The own-field term after its variable is instantiated. -/
theorem instantiate_ownFieldCode (ρ : Env) (key : PropKey) (v : Tm) :
    instantiate 0 ρ (ownFieldCode key v) = ownFieldCode key (instantiate 0 ρ v) := rfl

/-- All operations have fixed symbolic code. Closing it realizes exactly the
original operation, with at most six pure reductions for an own-field read.
There is no per-input specialization of the compiled operation. -/
theorem Operation.symbolic_prefix (host : NativeCode) (ρ : Env) (op : Operation)
    (h : Heap) (hv : ∀ x, isVal (ρ x) = true) :
    ∃ a, a ≤ 6 ∧ Steps a h (instantiate 0 ρ (op.symbolic host)) h (op.code (host.close ρ) ρ) := by
  have args (as : List Argument) :
      instantiateArgs 0 ρ (as.map (Argument.code 0)) = as.map (Argument.eval ρ) := by
    simp only [instantiateArgs_eq_map, List.map_map, Function.comp_def, Argument.instantiate_code]
  cases op
  case fieldRead x f =>
    simpa only [Operation.symbolic, instantiate_ownFieldCode, instantiate, Nat.not_lt_zero,
      ↓reduceIte, Nat.sub_zero] using
      (Operation.fieldRead_prefix (host := host.close ρ) (h := h) (field := f) (hv x))
  all_goals
    refine ⟨0, by omega, ?_⟩
    suffices eq : instantiate 0 ρ (Operation.symbolic host _) = Operation.code (host.close ρ) ρ _ by
      rw [eq]; exact .refl
    simp only [Operation.symbolic, Operation.code, NativeCode.close, instantiate,
      Nat.not_lt_zero, Nat.sub_zero, ↓reduceIte, Argument.instantiate_code,
      instantiateArgs, args, instantiateArgs_eq_map, List.map_map, Function.comp_def]

/-- A terminal compiled run contains an actual operation run, with its exact
primitive count and a bounded extra administrative count. -/
theorem Operation.symbolic_invert {host ρ h n h' t} {op : Operation}
    (hv : ∀ x, isVal (ρ x) = true)
    (run : Steps n h (instantiate 0 ρ (op.symbolic host)) h' t)
    (terminal : ∀ h₂ t₂, ¬ Step h' t h₂ t₂) :
    ∃ a p, a ≤ 6 ∧ n = a + p ∧ Steps p h (op.code (host.close ρ) ρ) h' t := by
  obtain ⟨a, ha, initial⟩ := op.symbolic_prefix host ρ h hv
  obtain ⟨p, hn, hp⟩ := steps_cancel_terminal initial run terminal
  exact ⟨a, p, ha, hn, hp⟩

end Verification.Paper.TolerantFrames
