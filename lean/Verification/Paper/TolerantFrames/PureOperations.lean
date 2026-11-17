import Verification.Paper.TolerantFrames.OperationCode
import Verification.Paper.TolerantFrames.BudgetTruncation
/-! # Exact rules for computed pure primitive results

Actual shared reductions determine every completed primitive run, chosen exit
world and empty effect. The computed result relation reads the entry state;
it is not assumed invariant under arbitrary world or budget changes.
-/
namespace Verification.Paper.TolerantFrames
open Verification HeapObservations Footprints TolerantFrames

theorem steps_from_value {n h v h' t} (hv : isVal v = true) (hs : Steps n h v h' t) :
    n = 0 ∧ h' = h ∧ t = v := by
  cases hs with
  | refl => exact ⟨rfl, rfl, rfl⟩
  | next first _ => exact False.elim (value_no_step hv first)

theorem PrimitiveRun.pure_result {host p ρ h k v n ρ' h' e}
    (known : Steps k h (p.operation.code host ρ) h v) (hv : isVal v = true)
    (run : PrimitiveRun host p ρ h n ρ' h' e) :
    n = k ∧ ρ' = p.bindResult ρ v ∧ h' = h ∧ e = .normal := by
  cases run with
  | normal actual hv' =>
    obtain ⟨j, hn, hs⟩ := steps_cancel_terminal known actual (fun _ _ => value_no_step hv')
    obtain ⟨rfl, rfl, rfl⟩ := steps_from_value hv hs
    exact ⟨by omega, rfl, rfl, rfl⟩
  | thrown actual raised =>
    obtain ⟨j, hn, hs⟩ := steps_cancel_terminal known actual (fun _ _ => raises_no_step raised)
    obtain ⟨_, rfl, rfl⟩ := steps_from_value hv hs
    have := raises_not_val raised
    simp [hv] at this

/-- A pure evaluation rule computes an actual shared reduction; it does not
assume a command summary or a native contract. -/
theorem triple_pure_bind {host P y op} {R : Env → IndexedHeap → Val → Prop}
    (compute : ∀ ρ m s, ValidContext ρ m s → P ρ m s →
      ∃ k v, Steps k s.h (op.code host ρ) s.h v ∧ isSourceVal v = true ∧
        RefsOk s.W v ∧ R ρ s v) :
    Triple host P (.step (.bind y op))
      (fun ρ ρ' _ s _ => ∃ v, ρ' = bindName ρ y v ∧ R ρ s v)
      (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False) (fun _ _ _ _ _ _ => False) := by
  intro ρ m s n ρ' h' e context pre run budget
  obtain ⟨k, v, known, source, refs, facts⟩ := compute ρ m s context pre
  cases run with
  | step primitive =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := primitive.pure_result known (sourceVal_isVal source)
    let t := truncateBudget s (s.n - n) (by omega) (by omega)
    refine ⟨t, truncateBudget_reachable s _ _ _, rfl, by dsimp [t, truncateBudget]; omega, ?_, trivial, ?_⟩
    · exact (context.truncate_budget _ _ _).bindName ⟨source, RefsOk_trunc _ refs⟩
    · exact ⟨v, rfl, facts⟩

theorem effects_pure {host P p}
    (compute : ∀ ρ m s, ValidContext ρ m s → P ρ m s →
      ∃ k v, Steps k s.h (p.operation.code host ρ) s.h v ∧ isVal v = true) :
    Effects host P (.step p) [] [] := by
  intro ρ m s n ρ' h' e context pre run budget
  obtain ⟨k, v, known, value⟩ := compute ρ m s context pre
  cases run with
  | step primitive =>
    obtain ⟨_, _, rfl, rfl⟩ := primitive.pure_result known value
    exact Post.refl _ _ _
end Verification.Paper.TolerantFrames
