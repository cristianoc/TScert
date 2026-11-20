import Init
import Verification.Semantics.PointerEquality

/-! # Equality of shared immutable lists

Method and clause comparisons repeatedly visit identical lists of operands. Lean's
pointer-equality primitive recognizes shared lists and elements. Its kernel
definition checks structural equality, and an unequal pointer falls back to the
element's ordinary decision procedure. -/
namespace Verification
/-- Decide equality, ending at the first shared tail or unequal element. -/
def sharedListEq {α : Type u} [DecidableEq α] (xs ys : List α) : Decidable (xs = ys) :=
  withPtrEqDecEq sameObjectOr (fun _ _ _ _ => rfl) xs ys fun _ =>
    match xs, ys with
    | [], [] => .isTrue rfl
    | _ :: _, [] => .isFalse (by intro h; cases h)
    | [], _ :: _ => .isFalse (by intro h; cases h)
    | x :: xs, y :: ys =>
      match withPtrEqDecEq sameObjectOr (fun _ _ _ _ => rfl) x y (fun _ => decEq x y) with
      | .isFalse h => .isFalse (fun e => h (List.cons.inj e).1)
      | .isTrue h =>
        match sharedListEq xs ys with
        | .isFalse t => .isFalse (fun e => t (List.cons.inj e).2)
        | .isTrue t => .isTrue (by cases h; cases t; rfl)
termination_by structural xs

/-- The compiler may use the sharing-aware procedure at any list element type. -/
@[csimp] theorem listEq_eq_sharedListEq : @instDecidableEqList = @sharedListEq := by
  funext α d xs ys
  exact Subsingleton.elim _ _
end Verification
