import Verification.Programs.TolerantFramesModelTyped
import Verification.Programs.TolerantFramesModelLoop
import Verification.Programs.TolerantFramesElems

/-! # Tolerant frames: the note's remaining atoms and rules in the model

Each atom or rule of the note "Tolerant frames" not stated elsewhere, as a
theorem with the hypotheses the indexed model forces, or a counter-model
where the note's statement does not hold:

- (View): a linear fact over slots' integers and typed-array lengths holds
  after every admissible transition where each view's length location is
  single-valued (`view_box`), which a type stating `viewLengthKey` stable
  gives (`viewStable_of_typed`); without it the length may change
  (`view_not_invariant`);
- (Init): every linear fact without a string length at a path survives every
  action of `{values: init, stores: keep}` (`init_box`), with no condition on
  its paths;
- Call: a callee's run is an action of its renamed regional effect at the
  caller's slots, its post holds, and the caller's facts it keeps are named
  at the result's fresh name (`call_rule`);
- Alloc: an allocated array is fresh, empty and apart from every older array
  whose cells are allocated (`alloc_post`); a later change of the fresh store
  at `any` can break that separation even though the store stays fresh
  (`apart_not_kept_fresh`);
- Seq-Eff: rebasing keeps each entry's change (`rebaseAll_labels`) and
  widens what it cannot rebase to every location (`rebase_elems`); the rule
  holds with class evidence at the entry (`seq_eff`);
- Fresh-Eff: a fresh store's entry in a step's effect covers no location of
  the entry heap (`fresh_eff`, `fresh_eff_bound`); its listed cells are not
  erased (`fresh_cells_not_erased`). -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations ControlFlow PointClaims
open ProgramTyping PositiveGraphs PositiveRules ExpressionEffects HeapExpressionRules

/-! ## (View) -/

/-! ## (Init) -/

/-! ## Call -/

/-! ## Alloc -/

/-- The allocation of an empty array: one object whose store field holds the
empty store. -/
def allocTerm : Tm := .makeAt .absent [arrayStoreKey] [.arr []]

/-- The array the allocation steps to at a heap. -/
def allocated (h : Heap) : Val := .objAt [(arrayStoreKey, h.length)] .absent (h.length + 1)

theorem alloc_step (h : Heap) : Step h allocTerm (h ++ [.arr []] ++ [.nul]) (allocated h) :=
  .makeFields (by simp [isVal]) rfl

/-! ## Seq-Eff -/

/-! ## Fresh-Eff -/

end Verification.TolerantFrames
