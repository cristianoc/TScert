import Verification.Paper.TolerantFrames.CallableEntryCorrectness
import Verification.Paper.TolerantFrames.CallableReferences
import Verification.Paper.TolerantFrames.PostconditionEnvironmentScope
import Verification.Paper.TolerantFrames.BudgetTruncation
import Verification.Paper.TolerantFrames.Scopes

/-! # Actual invocation satisfies its proved body postconditions

Use the body triple at the original invocation entry, then restrict its chosen
exit to the residual *shared* reduction budget. The full syntactic postcondition
transport retains old and the entry mark. Lexical scope removes body locals;
only a normal result is bound in the current environment. Recursive discharge,
caller mark rebasing and function allocation/typing remain separate obligations.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints TolerantFrames HeapObservations

/-- Substitute an arbitrary result value in the current phase only. In
particular this also represents normal fallthrough by undefined. -/
def ResultPost (Q : TwoState.Post) (η : TwoState.LogicalEnv) (y : Nat) (v : Val) : Postcondition :=
  fun ρ ρ' m s t => Q.meaning η ρ (bindName ρ' y v) m s t

namespace Compiler.Callable

/-- Generated self is source-valued. Its reference guarantee follows from
object identity/field roles and captures, not from its specification. -/
theorem entry_valid_from_roles {arity} {caps : List Tm} (c : Command) (layout : Layout arity caps.length)
    (fields : List (PropKey × Nat)) (identity : Nat) {s : IndexedHeap} {receiver : Tm} {args : List Tm}
    (hr : isSourceVal receiver = true ∧ RefsOk s.W receiver)
    (ha : ∀ a ∈ args, isSourceVal a = true ∧ RefsOk s.W a)
    (ho : RefsOk s.W (.objAt fields .absent identity))
    (hrefs : ∀ v ∈ caps, RefsOk s.W v)
    (hsource : ∀ j : Fin caps.length, Selector.capture j ∈ layout.source →
      isSourceVal (caps.getD j.val .undef) = true) :
    ValidContext (layout.env receiver args (function c layout fields identity)) s.h.length s := by
  apply layout.entry_valid hr ha ⟨rfl, function_refs_ok c layout fields identity ho hrefs⟩
  intro j hj
  refine ⟨hsource j hj, ?_⟩
  simp only [List.getD_eq_getElem?_getD]
  cases found : caps[j.val]? with
  | none => exact RefsOk_undef
  | some v => exact hrefs v (List.mem_of_getElem? found)

/-- Exact body-premise transport. The output environment here is the original
input environment: body locals are not observable in a scoped specification.
Return is frozen at the same entry even when its local command entry differs. -/
theorem body_exit_specification {host P c Γ Δ y ρ s p ρ' h' e N}
    (Q Qe : TwoState.Post) (η : TwoState.LogicalEnv)
    (scope : c.WellScoped Γ Δ)
    (normalScope : Q.Scoped Γ (fun x => x = y ∨ Γ x) 0 0)
    (exceptionalScope : Qe.Scoped Γ Γ 0 0)
    (body : Triple host P c (ResultPost Q η y .undef) (Qe.meaning η) (fun _ _ _ _ _ => False)
      (FunctionReturn ρ s (ResultPost Q η y)))
    (valid : ValidContext ρ s.h.length s) (pre : P ρ s.h.length s)
    (run : Executes host c ρ s.h p ρ' h' e) (count : p ≤ N) (budget : N < s.n) :
    ∃ t : IndexedHeap, Admissible s t ∧ t.h = h' ∧ t.n + N = s.n ∧
      ValidContext ρ s.h.length t ∧ ExitValid e t ∧
      ExitPost (ResultPost Q η y .undef) (Qe.meaning η) (fun _ _ _ _ _ => False)
        (ResultPost Q η y) e ρ ρ s.h.length s t := by
  obtain ⟨t, admissible, heap, steps, valid', exitValid, post⟩ :=
    body ρ s.h.length s p ρ' h' e valid pre run (by omega)
  have positive : 0 < s.n - N := by omega
  have smaller : s.n - N ≤ t.n := by omega
  let u := truncateBudget t (s.n - N) positive smaller
  have reachable : Admissible s u := admissible.trans (truncateBudget_reachable t _ positive smaller)
  have agree : ∀ x, Γ x → ρ' x = ρ x := fun x hx => run.preserves_name (scope.avoids_inputs x hx)
  have normal (v : Val) (hp : ResultPost Q η y v ρ ρ' s.h.length s t) :
      ResultPost Q η y v ρ ρ s.h.length s u := by
    have hlow := (Q.current_truncate ⟨⟨ρ, s⟩, ⟨bindName ρ' y v, t⟩, s.h.length⟩ η
      (s.n - N) positive smaller admissible).mp hp
    apply (Q.current_env_agree normalScope (fun _ hx => .inr hx)
      ⟨⟨ρ, s⟩, ⟨bindName ρ' y v, u⟩, s.h.length⟩ (bindName ρ y v) η ?_).mp hlow
    intro x hx
    by_cases he : x = y
    · simp only [bindName, if_pos he]
    · simp only [bindName, if_neg he]
      exact agree x (hx.resolve_left he)
  refine ⟨u, reachable, heap, by change s.n - N + N = s.n; omega,
    valid.admissible reachable, exitValid.truncate_budget _ positive smaller, ?_⟩
  cases e with
  | normal => exact normal .undef post
  | «break» => exact post.elim
  | returned v => exact normal v post
  | thrown v =>
    have hlow := (Qe.current_truncate ⟨⟨ρ, s⟩, ⟨ρ', t⟩, s.h.length⟩ η
      (s.n - N) positive smaller admissible).mp post
    exact (Qe.current_env_agree exceptionalScope (fun _ hx => hx)
      ⟨⟨ρ, s⟩, ⟨ρ', u⟩, s.h.length⟩ ρ η agree).mp hlow

/-- Normal completion of the actual callable, including fallthrough and
explicit return. The effect and postcondition retain the original entry;
all administrative reductions are charged to the shared residual budget. -/
theorem invocation_value_specification {arity} {caps : List Tm} (c : Command)
    (layout : Layout arity caps.length) (fields : List (PropKey × Nat)) (identity : Nat)
    (receiver : Tm) (args : List Tm) (s : IndexedHeap) {Γ Δ y P Φ Φe}
    (Q Qe : TwoState.Post) (η : TwoState.LogicalEnv)
    (scope : c.WellScoped Γ Δ)
    (normalScope : Q.Scoped Γ (fun x => x = y ∨ Γ x) 0 0)
    (exceptionalScope : Qe.Scoped Γ Γ 0 0)
    (body : Triple layout.host P c (ResultPost Q η y .undef) (Qe.meaning η) (fun _ _ _ _ _ => False)
      (FunctionReturn (layout.env receiver args (function c layout fields identity)) s (ResultPost Q η y)))
    (effects : Effects layout.host P c Φ Φe)
    (valid : ValidContext (layout.env receiver args (function c layout fields identity)) s.h.length s)
    (pre : P (layout.env receiver args (function c layout fields identity)) s.h.length s)
    (hr : isVal receiver = true) (ha : CallArguments.Values args) (hc : CallArguments.Values caps)
    {n h' v} (run : Steps n s.h (invocation c layout fields identity receiver args) h' v)
    (value : isVal v = true) (budget : n < s.n) :
    let ρ := layout.env receiver args (function c layout fields identity)
    ∃ t : IndexedHeap, Admissible s t ∧ t.h = h' ∧ t.n + n = s.n ∧
      ValidContext (bindName ρ y v) s.h.length t ∧ isSourceVal v = true ∧ RefsOk t.W v ∧
      ResultPost Q η y v ρ ρ s.h.length s t ∧ Footprints.Post Φ ρ s.h h' := by
  obtain ⟨q, p, ρ', e, count, weight, less, execution, result⟩ :=
    invocation_value c layout fields identity receiver args s.h hr ha hc run value
  obtain ⟨t, admissible, heap, steps, valid', exitValid, post⟩ :=
    body_exit_specification Q Qe η scope normalScope exceptionalScope body valid pre execution
      (Nat.le_of_lt less) budget
  have effect := effects _ _ _ _ _ _ _ valid pre execution (by omega)
  cases e with
  | normal =>
    simp only [resultState] at result
    cases result
    exact ⟨t, admissible, heap, steps, valid'.bindName ⟨rfl, RefsOk_undef⟩,
      rfl, RefsOk_undef, post, effect⟩
  | «break» => exact post.elim
  | returned w =>
    simp only [resultState] at result
    cases result
    exact ⟨t, admissible, heap, steps, valid'.bindName exitValid,
      exitValid.1, exitValid.2, post, effect⟩
  | thrown w => cases result

/-- Exceptional completion of the actual callable. No normal-result binding
is observable; the exceptional postcondition and effect use the same entry. -/
theorem invocation_raise_specification {arity} {caps : List Tm} (c : Command)
    (layout : Layout arity caps.length) (fields : List (PropKey × Nat)) (identity : Nat)
    (receiver : Tm) (args : List Tm) (s : IndexedHeap) {Γ Δ y P Φ Φe}
    (Q Qe : TwoState.Post) (η : TwoState.LogicalEnv)
    (scope : c.WellScoped Γ Δ)
    (normalScope : Q.Scoped Γ (fun x => x = y ∨ Γ x) 0 0)
    (exceptionalScope : Qe.Scoped Γ Γ 0 0)
    (body : Triple layout.host P c (ResultPost Q η y .undef) (Qe.meaning η) (fun _ _ _ _ _ => False)
      (FunctionReturn (layout.env receiver args (function c layout fields identity)) s (ResultPost Q η y)))
    (effects : Effects layout.host P c Φ Φe)
    (valid : ValidContext (layout.env receiver args (function c layout fields identity)) s.h.length s)
    (pre : P (layout.env receiver args (function c layout fields identity)) s.h.length s)
    (hr : isVal receiver = true) (ha : CallArguments.Values args) (hc : CallArguments.Values caps)
    {n h' term v} (run : Steps n s.h (invocation c layout fields identity receiver args) h' term)
    (raised : Raises term v) (budget : n < s.n) :
    let ρ := layout.env receiver args (function c layout fields identity)
    ∃ t : IndexedHeap, Admissible s t ∧ t.h = h' ∧ t.n + n = s.n ∧
      ValidContext ρ s.h.length t ∧ isSourceVal v = true ∧ RefsOk t.W v ∧
      Qe.meaning η ρ ρ s.h.length s t ∧ Footprints.Post Φe ρ s.h h' := by
  obtain ⟨q, p, ρ', count, weight, less, execution⟩ :=
    invocation_raise c layout fields identity receiver args s.h hr ha hc run raised
  obtain ⟨t, admissible, heap, steps, valid', exitValid, post⟩ :=
    body_exit_specification Q Qe η scope normalScope exceptionalScope body valid pre execution
      (Nat.le_of_lt less) budget
  exact ⟨t, admissible, heap, steps, valid', exitValid.1, exitValid.2, post,
    effects _ _ _ _ _ _ _ valid pre execution (by omega)⟩

end Compiler.Callable
end Verification.Paper.TolerantFrames
