import Verification.Programs.TolerantFramesMergeGraph

/-! # Tolerant frames: a merge's joined implications on the exits into it

The pass records each edge into a merge as `(Γe, atSlots, m)`
(`incomingEdges` in `SinglePass.run`): the edge's context as the source's
yields refine it, the implications the edge carries restated at the
source's slots (`atSlotsOf names carried`), the edge's mapping; the state the
edge carries is `edgeTransfer`'s, whose implications are `carried`
(`MergeEdgeRecorded`). A joined implication the merge keeps
(`joinedChecked`) holds at the target environment `mapEnv m ρs` of every
exit whose source environment `ρs` meets `Γe` and whose carried
implications hold at the source's valuation (`joined_of_exit`).

The joined implications are a property of the source environment through
`Γe`: an implication kept because the source's type of its target slot is
within it (`PromiseCalls.impliesFollows`, its second disjunct) is not stated
by the edge state, whose meaning (`StateHolds`) reads names, facts and
implications, not types. So they hold where the exit delivers them, not
wherever an edge state into the merge holds: an exit into a merge delivers
`edgePreJ` (the edge state and the joined implications at the target
environment), and the entries follow from it (`entries_of_traversedJ`, by
`entry_of_edge`). -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations
open ProgramTyping PositiveGraphs

section Joined
variable {ι : Type} [DecidableEq ι] [Hashable ι]

omit [Hashable ι] in
/-- **An exit establishes the merge's joined implications**: for an edge
recorded as `(Γe, atSlotsOf names carried, m)`, a source environment `ρs`
meeting `Γe` whose slots hold `names`' values at `η`, and the carried
implications holding at `η`, the kept joined implications hold at the
target environment `mapEnv m ρs` (`meetImplications_ok_of_check`,
`atSlots_ok`). -/
theorem joined_of_exit {G : NormalGraph ι} {context : List (Ty ι)}
    {edgesIn : List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {Γe : List (Ty ι)} {names : List Nat} {carried : List (PromiseCalls.Implication ι)} {m : PointClaims.Mapping}
    {ρs η : Env} {n : Nat} {W : WorldT n} (hin : (Γe, atSlotsOf names carried, m) ∈ edgesIn)
    (he : EnvOk G Γe ρs n W) (hss : SlotsNamed names ρs η) (hcar : PromiseCalls.ImpliesOk G carried η n W) :
    PromiseCalls.ImpliesOk G (joinedChecked G context edgesIn) (PointClaims.mapEnv m ρs) n W :=
  meetImplications_ok_of_check hin he (atSlots_ok hss hcar)

/-- **What an exit into a node delivers, at a merge with its joined
implications**: an edge state into `t` holds, and where `t` is a merge the
implications it keeps (`joinedChecked`) hold at the target environment. -/
def edgePreJ (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ε : HeapKnowledge.EntryState) (given : Nat → Bool)
    (ctx : Nat → List (Ty ι))
    (edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)) :
    Nat → Assertion :=
  fun t ρ m s => edgePre G w startNames ε t ρ m s ∧
    (given t = false → 2 ≤ (w.incoming t).length →
      PromiseCalls.ImpliesOk G (joinedChecked G (ctx t) (edgesIn t)) ρ s.n s.W)

/-- **Entry states hold where the exits into them deliver** (`edgePreJ`),
from the walk's construction, the heads entered and `LinearNearFuelEq`
(`entry_of_edge`): the merges' joined implications come with the exit. -/
theorem entries_of_traversedJ {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat} 
    {given : Nat → Bool} {ctx : Nat → List (Ty ι)}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {fresh : Nat → Nat} {m : Nat} (hT : Traversed G w startNames given ctx edgesIn fresh)
    (hheads : HeadsEntered G w startNames ε given m) (hnear : LinearNearFuelEq) :
    ∀ t ρ (s : IndexedHeap), edgePreJ G w startNames ε given ctx edgesIn t ρ m s →
      passPre G w startNames ε t ρ m s :=
  fun _ _ _ h => entry_of_edge hT hheads hnear h.1 h.2

end Joined

end Verification.TolerantFrames
