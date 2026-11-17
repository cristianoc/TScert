import Verification.Paper.TolerantFrames.CompilerLayout

/-! # Every finite command fits a finite graph frame

The existing lexical operand scopes are reused. Bounds include EVERY name,
including binders and caught names; they do not need a finite ambient scope.
Only names a command actually reads matter for code/environment agreement.
-/
namespace Verification.Paper.TolerantFrames
open Verification

def Argument.names : Argument → List Nat
  | .variable x => [x]
  | .literal _ => []

theorem Argument.scoped_names (a : Argument) (Γ : Scope) :
    a.Scoped Γ ↔ ∀ x ∈ a.names, Γ x := by cases a <;> simp [Argument.Scoped, Argument.names]

def Operation.names : Operation → List Nat
  | .value a | .not a => a.names
  | .binary _ a b | .and a b | .or a b => a.names ++ b.names
  | .fieldRead x _ | .arrayLength x | .viewLength x | .stringLength x => [x]
  | .fieldWrite x _ a | .elementRead x a | .viewRead x a | .stringRead x a => x :: a.names
  | .elementWrite x i v | .viewWrite x i v => x :: (i.names ++ v.names)
  | .objectLiteral fs => fs.flatMap fun p => p.2.names
  | .arrayLiteral args => args.flatMap Argument.names
  | .methodCall x _ args | .call x args | .construct x args => x :: args.flatMap Argument.names

theorem Operation.scoped_names (op : Operation) (Γ : Scope) :
    op.Scoped Γ ↔ ∀ x ∈ op.names, Γ x := by
  cases op <;> simp [Operation.Scoped, Operation.names, Argument.scoped_names, or_imp, forall_and] <;> grind

def Command.names : Command → List Nat
  | .step (.bind x op) => x :: op.names
  | .step (.perform op) => op.names
  | .seq a b => a.names ++ b.names
  | .choice test a b => test.names ++ a.names ++ b.names
  | .loop b => b.names
  | .handle b x d => b.names ++ x :: d.names
  | .return_ a | .throw_ a => a.names
  | .break_ => []

/-- Storage bounds, distinct from lexical order/freshness admission. -/
def Command.InFrame (bound : Nat) : Command → Prop
  | .step (.bind x op) => x < bound ∧ op.Scoped (· < bound)
  | .step (.perform op) => op.Scoped (· < bound)
  | .seq a b => a.InFrame bound ∧ b.InFrame bound
  | .choice test a b => test.Scoped (· < bound) ∧ a.InFrame bound ∧ b.InFrame bound
  | .loop b => b.InFrame bound
  | .handle b x d => b.InFrame bound ∧ x < bound ∧ d.InFrame bound
  | .return_ a | .throw_ a => a.Scoped (· < bound)
  | .break_ => True

theorem Command.inFrame_names (c : Command) (bound : Nat) :
    c.InFrame bound ↔ ∀ x ∈ c.names, x < bound := by
  induction c with
  | step p => cases p <;> simp [Command.InFrame, Command.names, Operation.scoped_names]
  | seq _ _ ih₁ ih₂ | choice _ _ _ ih₁ ih₂ | handle _ _ _ ih₁ ih₂ =>
    simp [Command.InFrame, Command.names, Argument.scoped_names, ih₁, ih₂, or_imp, forall_and] <;> grind
  | loop _ ih => exact ih
  | return_ _ | throw_ _ | break_ => simp [Command.InFrame, Command.names, Argument.scoped_names]

private theorem le_names_max {names : List Nat} {x : Nat} (hx : x ∈ names) :
    x ≤ names.foldr max 0 := by
  induction names with
  | nil => cases hx
  | cons y names ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hx) (Nat.le_max_right _ _)

def Command.frameBound (c : Command) : Nat := c.names.foldr max 0 + 1

theorem Command.inFrame (c : Command) : c.InFrame c.frameBound := by
  apply (c.inFrame_names _).mpr
  intro x hx
  have := le_names_max hx
  unfold Command.frameBound
  omega

theorem Argument.scoped_eval_eq {Γ : Scope} {ρ ρ' : Env} {a : Argument}
    (ha : a.Scoped Γ) (agree : ∀ x, Γ x → ρ x = ρ' x) : a.eval ρ = a.eval ρ' := by
  cases a with
  | «variable» x => exact agree x ha
  | literal _ => rfl

/-- Code ignores every program slot outside its actual operand scope. The
host terms are fixed separately, as proved by the frame's host invariants. -/
theorem Operation.scoped_code_eq {Γ : Scope} {ρ ρ' : Env} {op : Operation}
    (scope : op.Scoped Γ) (agree : ∀ x, Γ x → ρ x = ρ' x) (host : NativeCode) :
    op.code host ρ = op.code host ρ' := by
  have arg (a : Argument) (h : a.Scoped Γ) := Argument.scoped_eval_eq h agree
  have args (as : List Argument) (h : ∀ a ∈ as, a.Scoped Γ) :
      as.map (Argument.eval ρ) = as.map (Argument.eval ρ') :=
    List.map_congr_left fun a ha => arg a (h a ha)
  cases op with
  | value a | not a => simp only [Operation.code, arg a scope]
  | binary op a b | and a b | or a b => simp only [Operation.code, arg a scope.1, arg b scope.2]
  | fieldRead x f | arrayLength x | viewLength x | stringLength x =>
    simp only [Operation.code, agree x scope]
  | fieldWrite x f a | elementRead x a | viewRead x a | stringRead x a =>
    simp only [Operation.code, agree x scope.1, arg a scope.2]
  | elementWrite x i v | viewWrite x i v =>
    simp only [Operation.code, agree x scope.1, arg i scope.2.1, arg v scope.2.2]
  | objectLiteral fs =>
    simp only [Operation.code]
    congr 1
    exact List.map_congr_left fun p hp => arg p.2 (scope p hp)
  | arrayLiteral as => simp only [Operation.code, args as scope]
  | methodCall x f as | call x as | construct x as =>
    simp only [Operation.code, agree x scope.1, args as scope.2]

namespace Compiler

theorem operation_restore {bound outer graph host} {op : Operation}
    (scope : op.Scoped (· < bound)) :
    op.code host (restore bound outer graph) = op.code host graph :=
  Operation.scoped_code_eq scope (fun _ hi => by simp [restore, hi]) host

end Compiler
end Verification.Paper.TolerantFrames
