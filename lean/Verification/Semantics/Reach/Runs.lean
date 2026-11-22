import Verification.Semantics.Reach.Scoped
import Verification.Semantics.SafeUnder

/-! # Runs of a value's evaluation

`ValRun` is an execution of a term recorded step by step, and the lemmas
about the locations it reaches along the way. -/

namespace Verification.TolerantFrames.Reach

open Verification

/-- **Every tag's code as outside code**: no tag is the package's. -/
def allC : ComponentTag → Bool := fun _ => false

/-- **A run of the calculus over heaps of values**: steps, each from a heap
whose every location holds a value. -/
inductive ValRun : Heap → Tm → Heap → Tm → Prop where
  | refl {h : Heap} {t : Tm} : ValRun h t h t
  | step {h h₁ h₂ : Heap} {t t₁ t₂ : Tm} : (∀ (l : Nat) (v : Val), h[l]? = some v → isVal v = true) →
      Step h t h₁ t₁ → ValRun h₁ t₁ h₂ t₂ → ValRun h t h₂ t₂

/-- A run only grows the heap (proved). -/
theorem ValRun.length_le {h h' : Heap} {t t' : Tm} (hr : ValRun h t h' t') : h.length ≤ h'.length := by
  induction hr with
  | refl => exact Nat.le_refl _
  | step _ hs _ ih => exact Nat.le_trans (Footprints.step_length_le hs) ih

variable {α : Type}

end Verification.TolerantFrames.Reach
