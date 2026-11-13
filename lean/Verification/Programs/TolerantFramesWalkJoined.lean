import Verification.Programs.TolerantFramesWalkReassignWalk
import Verification.Programs.TolerantFramesMergeWritten

/-! # Tolerant frames: the exits into a merge deliver its joined implications

The pass keeps a joined implication at a merge only where every incoming
edge passes `PromiseCalls.impliesCheck` over the edge's context as the
source's yields refine it (`joinedChecked`, 5382cf4a on the pass lane). That
check reads the source's types, which the edge state's meaning
(`StateHolds`) does not state, so the joined implications are delivered by
the exit, at its source environment (`joined_of_exit`), not by the edge
state. `ExitsJoined` is that delivery at each exit and the handler of a
node (`joinedAt`); with the node's meaning (`NodeMeaning`, the targets'
`edgePreA`) it gives the node's meaning at `edgePreAJ`
(`NodeMeaning.withJoined`), and the checked nodes at the node assertion
stating the written assertions follow from the walk's construction with the
written facts (`nodesChecked_of_walkJ`). -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules

section Joined
variable {ι : Type} [DecidableEq ι] [Hashable ι]

/-- **The joined implications at a target**: at a merge (no given facts,
at least two incoming states), the implications it keeps hold at the
environment. -/
def joinedAt (G : NormalGraph ι) (w : Walk ι) (given : Nat → Bool) (ctx : Nat → List (Ty ι))
    (edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)) :
    Nat → Assertion :=
  fun t ρ _ s => given t = false → 2 ≤ (w.incoming t).length →
    PromiseCalls.ImpliesOk G (joinedChecked G (ctx t) (edgesIn t)) ρ s.n s.W

/-- **A node's exits deliver the joined implications of the merges they
enter** (`joinedAt`): each normal exit from the state after the step at the
pushed environment, and the handler from the throw state, as `NodeMeaning`
states the exits' other obligations. -/
structure ExitsJoined (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ε : HeapKnowledge.EntryState) (ctx : Nat → List (Ty ι))
    (given : Nat → Bool)
    (edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping))
    (m : Nat) (l : Nat) (node : Node) (c : PointClaim ι) (entry : SinglePass.State) (st : Stepped ι) : Prop where
  exits : ∀ t pushed observed promote, Exit.normal t pushed observed promote ∈ Exit.ofNode node → ∀ ρ,
    ExitDelivers (joinedAt G w given ctx edgesIn) G c.type c.context
      (StateHolds G ⟨st.result :: entry.names, st.store, entry.fresh⟩ (w.implies l) startNames ε) ρ m t
      pushed observed promote
  handler : ∀ t, node.handler = some t → ∀ ρ (s' : IndexedHeap) e,
    StateHolds G ⟨entry.names, entry.store.dropHeap (fun _ => false), entry.fresh⟩ (w.implies l) startNames ε
      ρ m s' →
    EnvOk G c.context ρ s'.n s'.W → Scoped 0 e → excOf G s'.n s'.W e →
    joinedAt G w given ctx edgesIn t.label (PointClaims.mapEnv t.mapping (push e ρ)) m s'

omit [Hashable ι] in
/-- **A node's meaning with its exits' joined implications** is its meaning
at `edgePreAJ`. -/
theorem NodeMeaning.withJoined {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat} 
    {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge} {given : Nat → Bool}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {Tres : Fam} {m l : Nat} {node : Node} {c : PointClaim ι} {entry : SinglePass.State} {st : Stepped ι}
    (hm : NodeMeaning G w startNames ε ctx stated Tres m l node c entry st)
    (hj : ExitsJoined G w startNames ε ctx given edgesIn m l node c entry st) :
    NodeMeaningAt (edgePreAJ G w startNames ε ctx stated given edgesIn) G w startNames ε ctx Tres m l node c entry st
    where
  entered := hm.entered
  shape := hm.shape
  ret := hm.ret
  exits t p o q hmem ρ s' v hv hF he ho := ⟨hm.exits t p o q hmem ρ s' v hv hF he ho, hj.exits t p o q hmem ρ s' v hv hF he ho⟩
  handler t ht ρ s' e h1 h2 h3 h4 := ⟨hm.handler t ht ρ s' e h1 h2 h3 h4, hj.handler t ht ρ s' e h1 h2 h3 h4⟩

/-- **The walk checks every node at the node assertion stating the
written assertions**, from the walk's construction with the written facts
(`TraversedA`), each node's step and exits delivering `edgePreAJ`, the
heads entered and `LinearNearFuelEq` (`passPreA_of_edgeAJ`). -/
theorem nodesChecked_of_walkJ {P : ControlFlow.Program} {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat}
    {given : Nat → Bool} {ctx : Nat → List (Ty ι)}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {fresh : Nat → Nat} {Ξres Tres : Fam} {m : Nat} {stated : Nat → Option HeapKnowledge.Knowledge}
    (hT : TraversedA G w startNames given ctx edgesIn fresh stated)
    (hstep : StepEdgesSoundMarked (edgePreAJ G w startNames ε ctx stated given edgesIn) P G w startNames ε ctx Ξres
      Tres (fun _ => True) (fun _ => True) m)
    (hheads : HeadsEntered G w startNames ε given m) (hnear : LinearNearFuelEq) :
    NodesChecked P (marked (passPreA G w startNames ε ctx stated)) Ξres Tres (fun _ => True) (fun _ => True) m := by
  intro l ρ s ⟨hp, hm⟩
  obtain ⟨node, hn, Ξ, T, cn, ce, Qn, Qe, hsafe, ho⟩ := hstep l ρ s hp.1 hm
  exact ⟨node, hn, Ξ, T, cn, ce, Qn, Qe, hsafe,
    nodeObligations_marked hm (nodeObligations_mono (fun _ _ _ h => passPreA_of_edgeAJ hT hheads hnear h) ho)⟩

end Joined

end Verification.TolerantFrames
