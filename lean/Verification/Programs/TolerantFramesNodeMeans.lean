import Verification.Programs.TolerantFramesRunSound
import Verification.Programs.TolerantFramesComposeShape

/-! # Tolerant frames: a checked node's entry and shapes

`NodeMeaning` states five things of a visited node: its entry state holding
where the node assertion does (`entered`), the claim type giving each
continuation's shape (`shape`), a return's result type (`ret`), each normal
exit (`exits`) and the handler (`handler`) delivering the target's
assertion. The first two are the pass's own checks at the node, which
`NodeChecked` records: the step starts from the label's recorded entry
(`hentry`) and `run`'s shape check accepts the claim type (`hshape`,
`passShapeCheck'`). `NodeDelivers` is the other three. Proved:

- `NodeChecked.meaning`: `NodeChecked` ∧ `NodeDelivers` ⟹ `NodeMeaning`
  (`entered` from `hentry`, `shape` by `nodeShape_of`);
- `nodesMean_of_delivers`: `NodesDeliver` (`NodeDelivers` at every visited
  node of every recorded walk at every admitted reassigned graph) ⟹
  `NodesMean`, the checked node carried to the reassigned graph by
  `nodeChecked_reassign`. -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules LabelStore

section Delivers
variable {ι : Type} [DecidableEq ι] [Hashable ι]

/-- **What a node's step delivers at a graph** beyond the pass's checks at
the node: a return's result type and each normal exit and the handler
delivering the target's typed and written assertion (`edgePreA`), as
`NodeMeaning` states them. -/
structure NodeDelivers (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ρ0 : Env)
    (ctx : Nat → List (Ty ι)) (stated : Nat → Option HeapKnowledge.Knowledge) (Tres : Fam) (m : Nat) (l : Nat)
    (node : Node) (c : PointClaim ι) (entry : SinglePass.State) (st : Stepped ι) : Prop where
  ret : node.continuation = .ret → ∀ n (W : WorldT n) v, meaning G c.type n W v → Tres n W v
  exits : ∀ t pushed observed promote, Exit.normal t pushed observed promote ∈ Exit.ofNode node → ∀ ρ,
    ExitDelivers (edgePreA G w startNames ρ0 ctx stated) G c.type c.context
      (StateHolds G ⟨st.result :: entry.names, st.store, entry.fresh⟩ (w.implies l) startNames ρ0) ρ m t
      pushed observed promote
  handler : ∀ t, node.handler = some t → ∀ ρ (s' : IndexedHeap) e,
    StateHolds G ⟨entry.names, entry.store.dropHeap (fun _ => false), entry.fresh⟩ (w.implies l) startNames ρ0
      ρ m s' →
    EnvOk G c.context ρ s'.n s'.W → Scoped 0 e → excOf G s'.n s'.W e →
    edgePreA G w startNames ρ0 ctx stated t.label (PointClaims.mapEnv t.mapping (push e ρ)) m s'

/-- **A checked node means what it states** where it delivers: the entry
state from the recorded entry (`hentry`), the shapes from `run`'s shape
check (`hshape`, `nodeShape_of`), the rest from `NodeDelivers`. -/
theorem NodeChecked.meaning [Instantiates ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {codes : CodeEntry ι → Bool} {pc : PassChecker G images} {P : ControlFlow.Program} {w : Walk ι}
    {startNames : List Nat} {ρ0 : Env} {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge}
    {Tres : Fam} {m l : Nat} (x : NodeChecked G images codes pc P w startNames ctx l)
    (hd : NodeDelivers G w startNames ρ0 ctx stated Tres m l x.node x.c x.entry x.st) :
    NodeMeaning G w startNames ρ0 ctx stated Tres m l x.node x.c x.entry x.st where
  entered _ _ hp := x.hentry ▸ hp.1.2
  shape _ _ _ hv := nodeShape_of x.hshape hv
  ret := hd.ret
  exits := hd.exits
  handler := hd.handler

end Delivers

section Run
variable {ι : Type} [Labels ι]

variable (ι) in
/-- **(Named hypothesis) Each checked node delivers** at every admitted
reassigned graph: a return's result type, each exit's and the handler's
target assertion (`NodeDelivers`), what `NodesMean` states beyond the
pass's checks at the node. -/
def NodesDeliver : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) after admits,
    RunPremises G I c after admits → ∀ r : RunWalkA G I c, ∀ η, admits η → ∀ ρ0 m l (hl : r.w.visited l),
      NodeDelivers (reassign G η) r.w (List.range c.inputs.length) ρ0 r.ctx r.stated
        (GoalHolds (reassign G η) c.goal (c.goal.argument ρ0)) m l (r.node l hl).node (r.node l hl).c
        (r.node l hl).entry (r.node l hl).st

/-- **The nodes mean what they state where they deliver** (`NodesMean`):
each visited node carried to the reassigned graph (`nodeChecked_reassign`),
its entry and shapes from the pass's checks there (`NodeChecked.meaning`). -/
theorem nodesMean_of_delivers (h : NodesDeliver ι) : NodesMean ι := by
  intro G I c after admits hp r η hη ρ0 m l hl
  obtain ⟨pc', hpc⟩ := scope_reassign hp.2.1 hη
  exact (nodeChecked_reassign hpc (r.node l hl)).meaning (h G I c after admits hp r η hη ρ0 m l hl)

end Run

end Verification.TolerantFrames
