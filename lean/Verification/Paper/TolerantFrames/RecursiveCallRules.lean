import Verification.Paper.TolerantFrames.RecursiveFunctions
import Verification.Paper.TolerantFrames.PostconditionValuationScope
import Verification.Paper.TolerantFrames.MarkIndependence
import Verification.Paper.TolerantFrames.FormulaScopes

/-! # Concrete recursive calls use only smaller-count specifications

A direct call's code is exactly the represented callable invocation. This rule
uses the restricted induction hypothesis at its actual primitive count. Scope
transports the decoded formal environment to the caller, retaining both indexed
heaps; semantic mark independence is the displayed Call premise. Capture typing
and the input-layout equation are explicit embedding obligations. Renamed actuals
and freshness rebasing are supplied separately, not inferred here.
-/
namespace Verification.Paper.TolerantFrames.Compiler.Callable
open Verification Footprints TolerantFrames HeapObservations

/-- Encoding conditions on this identity-aligned call. They say nothing about
the behavior/specification of the callee. Its specification comes from the IH. -/
def RecursiveCallPre {arity} {caps : List Tm} (c : Command) (layout : Layout arity caps.length)
    (fields : List (PropKey × Nat)) (identity : Nat) (P : Assertion) (Γ : Nat → Prop)
    (f : Nat) (arguments : List Argument) : Assertion := fun ρ m s =>
  P ρ m s ∧ ρ f = function c layout fields identity ∧
  ValidContext (layout.env .undef (arguments.map (Argument.eval ρ)) (function c layout fields identity)) s.h.length s ∧
  ∀ x, Γ x → layout.env .undef (arguments.map (Argument.eval ρ)) (function c layout fields identity) x = ρ x

private theorem result_env_agrees {Γ : Nat → Prop} {ρ ρ' : Env} (agree : ∀ x, Γ x → ρ x = ρ' x)
    (y : Nat) (v : Val) : ∀ x, x = y ∨ Γ x → bindName ρ y v x = bindName ρ' y v x := by
  intro x hx
  by_cases he : x = y
  · simp only [bindName, if_pos he]
  · simp only [bindName, if_neg he]
    exact agree x (hx.resolve_left he)

private theorem call_exit {arity} {caps : List Tm} (c : Command) (layout : Layout arity caps.length)
    (fields : List (PropKey × Nat)) (identity : Nat) {N Γ y P Φ Φe host f J Ret}
    (arguments : List Argument) (Q Qe : TwoState.Post) (η : TwoState.LogicalEnv)
    (depends : DependsOn P Γ) (markPre : MarkIndependent P)
    (normalScope : Q.Scoped Γ (fun x => x = y ∨ Γ x) 0 0)
    (exceptionalScope : Qe.Scoped Γ Γ 0 0)
    (markNormal : PostMarkIndependent (Q.meaning η)) (markExceptional : PostMarkIndependent (Qe.meaning η))
    (normalEffects : EffectNames Γ Φ) (exceptionalEffects : EffectNames Γ Φe)
    (captures : CallArguments.Values caps)
    (oracle : ∀ k, k < N → InvocationSpecAt c layout fields identity P Q Qe η y Φ Φe k)
    {ρ m s n ρ' h' e} (valid : ValidContext ρ m s)
    (pre : RecursiveCallPre c layout fields identity P Γ f arguments ρ m s)
    (run : PrimitiveRun host (.bind y (.call f arguments)) ρ s.h n ρ' h' e)
    (budget : n < s.n) (limited : n < N) :
    ∃ t : IndexedHeap, Admissible s t ∧ t.h = h' ∧ t.n + n = s.n ∧
      ValidContext ρ' m t ∧ ExitValid e t ∧
      ExitPost (Q.meaning η) (Qe.meaning η) J Ret
        e ρ ρ' m s t ∧
      Footprints.Post (match e with | .thrown _ => Φe | _ => Φ) ρ s.h h' := by
  obtain ⟨pre, callee, decodedValid, agree⟩ := pre
  let decoded := layout.env .undef (arguments.map (Argument.eval ρ)) (function c layout fields identity)
  have values : CallArguments.Values (arguments.map (Argument.eval ρ)) := by
    intro v hv
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
    exact sourceVal_isVal (a.valid valid).1
  have decodedPre := (markPre _ s m s.h.length).mp ((depends _ ρ m s agree).mpr pre)
  have spec := oracle n limited .undef (arguments.map (Argument.eval ρ)) s rfl values captures decodedValid decodedPre
  have code : (Operation.call f arguments).code host ρ =
      invocation c layout fields identity .undef (arguments.map (Argument.eval ρ)) := by
    simp only [Operation.code, invocation, callee]
  cases run with
  | normal execution value =>
    rename_i v
    simp only [Primitive.operation] at execution
    rw [code] at execution
    obtain ⟨t, admissible, heap, steps, _, source, refs, post, effect⟩ := spec.1 _ _ execution value budget
    have converted := (Q.environment_agree normalScope (entry := ⟨decoded, s⟩) (focus := ⟨bindName decoded y v, t⟩)
      (entry' := ⟨ρ, s⟩) (focus' := ⟨bindName ρ y v, t⟩)
      ⟨rfl, agree⟩ ⟨rfl, result_env_agrees agree y v⟩ s.h.length η).mp post
    exact ⟨t, admissible, heap, steps, (valid.admissible admissible).bindName ⟨source, refs⟩,
      trivial, (markNormal _ _ s t s.h.length m).mp converted,
      (post_scope agree normalEffects s.h _).mp effect⟩
  | thrown execution raised =>
    simp only [Primitive.operation] at execution
    rw [code] at execution
    obtain ⟨t, admissible, heap, steps, _, source, refs, post, effect⟩ := spec.2 _ _ _ execution raised budget
    have converted := (Qe.environment_agree exceptionalScope (entry := ⟨decoded, s⟩) (focus := ⟨decoded, t⟩)
      (entry' := ⟨ρ, s⟩) (focus' := ⟨ρ, t⟩)
      ⟨rfl, agree⟩ ⟨rfl, agree⟩ s.h.length η).mp post
    exact ⟨t, admissible, heap, steps, valid.admissible admissible, ⟨source, refs⟩,
      (markExceptional _ _ s t s.h.length m).mp converted,
      (post_scope agree exceptionalEffects s.h _).mp effect⟩

/-- A positive bounded primitive premise for the relative body proof. The
recursive oracle is never promoted to an unrestricted self triple. -/
theorem recursive_call_rule {arity} {caps : List Tm} (c : Command) (layout : Layout arity caps.length)
    (fields : List (PropKey × Nat)) (identity : Nat) {N Γ y P Φ Φe host f J Ret}
    (arguments : List Argument) (Q Qe : TwoState.Post) (η : TwoState.LogicalEnv)
    (depends : DependsOn P Γ) (markPre : MarkIndependent P)
    (normalScope : Q.Scoped Γ (fun x => x = y ∨ Γ x) 0 0)
    (exceptionalScope : Qe.Scoped Γ Γ 0 0)
    (markNormal : PostMarkIndependent (Q.meaning η)) (markExceptional : PostMarkIndependent (Qe.meaning η))
    (normalEffects : EffectNames Γ Φ) (exceptionalEffects : EffectNames Γ Φe)
    (captures : CallArguments.Values caps)
    (oracle : ∀ k, k < N → InvocationSpecAt c layout fields identity P Q Qe η y Φ Φe k) :
    TripleBelow N host (RecursiveCallPre c layout fields identity P Γ f arguments)
      (.step (.bind y (.call f arguments))) (Q.meaning η) (Qe.meaning η)
      J Ret ∧
    EffectsBelow N host (RecursiveCallPre c layout fields identity P Γ f arguments)
      (.step (.bind y (.call f arguments))) Φ Φe := by
  constructor
  · intro ρ m s n ρ' h' e valid pre run budget limited
    cases run with
    | step primitive =>
      obtain ⟨t, admissible, heap, steps, valid', exit, post, _⟩ :=
        call_exit (J := J) (Ret := Ret) c layout fields identity arguments Q Qe η depends markPre normalScope exceptionalScope
          markNormal markExceptional normalEffects exceptionalEffects captures oracle valid pre primitive budget limited
      exact ⟨t, admissible, heap, steps, valid', exit, post⟩
  · intro ρ m s n ρ' h' e valid pre run budget limited
    cases run with
    | step primitive =>
      obtain ⟨_, _, _, _, _, _, _, effect⟩ :=
        call_exit (J := J) (Ret := Ret) c layout fields identity arguments Q Qe η depends markPre normalScope exceptionalScope
          markNormal markExceptional normalEffects exceptionalEffects captures oracle valid pre primitive budget limited
      cases e <;> exact effect

end Verification.Paper.TolerantFrames.Compiler.Callable
