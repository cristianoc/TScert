import Verification.Paper.TolerantFrames.GraphInversion

/-! # Actual entered-node execution segments

A completed graph run must eventually leave its current expression by an
actual continuation/handler step. Separating that segment preserves all shared
reduction counts and exposes the primitive terminal to operation inversion.
-/
namespace Verification.Paper.TolerantFrames.Compiler
open Verification ControlFlow HeapObservations

def OutsideEvaluation : ControlFlow.State → Prop
  | .eval .. => False
  | _ => True

/-- Expression steps precede one real continuation/handler transition. Its
heap is unchanged; only the expression prefix may change the heap. -/
theorem evaluation_segment {P : Program} : ∀ {n h term ρ continuation handler h' final},
    Execution P n h (.eval term ρ continuation handler) h' final → OutsideEvaluation final →
    ∃ a middleHeap middleTerm next q,
      n = a + 1 + q ∧ Steps a h term middleHeap middleTerm ∧
      ControlFlow.Transition P middleHeap (.eval middleTerm ρ continuation handler) middleHeap next ∧
      OutsideEvaluation next ∧ Execution P q middleHeap next h' final := by
  intro n
  induction n with
  | zero => intro h term ρ continuation handler h' final run outside; cases run; cases outside
  | succ n ih =>
    intro h term ρ continuation handler h' final run outside
    cases run with
    | next first rest =>
      cases first with
      | expr step =>
        obtain ⟨a, middleHeap, middleTerm, next, q, count, prefixRun, leave, hn, suffixRun⟩ := ih rest outside
        exact ⟨a + 1, middleHeap, middleTerm, next, q, by omega, .next step prefixRun, leave, hn, suffixRun⟩
      | ret hv => exact ⟨0, _, _, _, _, by omega, .refl, .ret hv, trivial, rest⟩
      | bind hv => exact ⟨0, _, _, _, _, by omega, .refl, .bind hv, trivial, rest⟩
      | effect hv => exact ⟨0, _, _, _, _, by omega, .refl, .effect hv, trivial, rest⟩
      | yes => exact ⟨0, _, _, _, _, by omega, .refl, .yes, trivial, rest⟩
      | no => exact ⟨0, _, _, _, _, by omega, .refl, .no, trivial, rest⟩
      | yesBind => exact ⟨0, _, _, _, _, by omega, .refl, .yesBind, trivial, rest⟩
      | noBind => exact ⟨0, _, _, _, _, by omega, .refl, .noBind, trivial, rest⟩
      | tagBind hv => exact ⟨0, _, _, _, _, by omega, .refl, .tagBind hv, trivial, rest⟩
      | handle raised => exact ⟨0, _, _, _, _, by omega, .refl, .handle raised, trivial, rest⟩
      | raise raised => exact ⟨0, _, _, _, _, by omega, .refl, .raise raised, trivial, rest⟩

/-- Leaving evaluation means its expression has really completed, normally
or exceptionally. Stuck nonvalues cannot be mistaken for primitive outcomes. -/
theorem evaluation_terminal {P h term ρ continuation handler h' next}
    (leave : ControlFlow.Transition P h (.eval term ρ continuation handler) h' next)
    (outside : OutsideEvaluation next) : isVal term = true ∨ ∃ v, Raises term v := by
  cases leave with
  | expr _ => cases outside
  | ret hv | bind hv | effect hv | tagBind hv => exact Or.inl hv
  | yes | no | yesBind | noBind => exact Or.inl rfl
  | handle raised | raise raised => exact Or.inr ⟨_, raised⟩

theorem evaluation_no_step {P h term ρ continuation handler h' next}
    (leave : ControlFlow.Transition P h (.eval term ρ continuation handler) h' next)
    (outside : OutsideEvaluation next) : ∀ h₂ term₂, ¬ Verification.Step h' term h₂ term₂ := by
  rcases evaluation_terminal leave outside with value | ⟨_, raised⟩
  · exact fun _ _ => value_no_step value
  · exact fun _ _ => raises_no_step raised

end Verification.Paper.TolerantFrames.Compiler
