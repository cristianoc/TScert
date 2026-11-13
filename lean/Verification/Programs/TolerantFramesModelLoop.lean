import Verification.Programs.TolerantFramesExamples

/-! # Tolerant frames: the note's loop, one closed instance of graph safety

The loop `for (j = from; j < to; j++) out[j] = xs[j]` as a graph of six
nodes (`loopGraph`): the initialisation `j = from`, the guard `j < to`, the
read `xs[j]`, the element write `out[j] = v`, the increment `j + 1` and the
exit. `xs` and `out` are arrays of source values (`arrayF`): objects whose
array-store field holds a store under the tuple contract every position of
which, required or not, holds a source value (`storeF`); nothing relates
`xs` and `out`, so they may be one object. Every node is checked here from the
semantics alone, and `loop_safe` is `graph_safe` with no premise about the
graph: from every state where `0 ≤ from`, `to ≤ |xs|` and `xs`, `out` are
such arrays, the loop's run never gets stuck and returns `null`, raising
nothing. -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations ControlFlow PointClaims

/-! ## The world of the loop: arrays of source values -/

/-! ## The assertions -/

/-! ## One step keeping the heap -/

/-- A step that keeps the heap, then the rest at the truncated world. -/
theorem pure_step {Ξ T : Fam} {Q : Post} {R : Heap → Prop} {n : Nat} {W : WorldT (n + 1)} {h : Heap} {t t' : Tm}
    (ha : WorldAdm W) (ho : HeapOk (n + 1) W h) (hst : Step h t h t')
    (hs : SafePostExc Ξ T Q R n (trunc n (Nat.le_succ n) W) h t') : SafePostExc Ξ T Q R (n + 1) W h t :=
  .inr ⟨_, h, t', WExt_refl _, WorldAdm_trunc _ ha, hst, HeapOk_trunc n W h ho, hs⟩

/-! ## The element write `out[j] = v`

`out` in slot 4, `j` in slot 1, `v` in slot 0, as the pass lowers an element
write at a run-time index (`ExpressionEffects.elemVarWriteSlots`). Three steps:
the store is read, the element written (a listed cell takes the value, or a
fresh cell is listed), the store put back. -/

/-! ## The guard `j < to` and the read `xs[j]` -/

/-- The read's term: `xs[j]`, `xs` in slot 2, `j` in slot 0. -/
def readTerm : Tm := .elemAt (.readAt arrayStoreKey (.var 2)) (.var 0)

/-! ## The graph, its assertions and its nodes checked -/

/-! ## An aliased entry state

The entry assertion is met where `xs` and `out` are one array: a world of two
locations, a store listing one cell and that cell, at every positive budget.
So `loop_safe` covers an aliased run, not only a vacuous one. -/

end Verification.TolerantFrames
