import Verification.Programs.TolerantFramesWalkReassignChecks
import Verification.Programs.TolerantFramesNodeWalk
import Verification.Programs.TolerantFramesNodeAsserts

/-! # Tolerant frames: a visited node's run at a reassignment

`NodeAccepted` holds what the pass computed at a node (`NodeRan`: the step,
the store's well-formedness, the names below the counter, the width, the
summary table checked) and what follows of it at the graph's meaning
(`NodeMeaning`: the stated assertion, the shapes, the return type, the exits,
the handler). The first is data and checks, carried to `reassign G η` with
the searches as oracles (`NodeChecked`, `nodeChecked_reassign`). The second
reads the graph's meaning at its own assignment, so it is established at
`reassign G η` by the theorems that give it at every graph from the checks
there (the exit lemmas of `TolerantFramesNodeWalk`). -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules

variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

/-- **What a node's step means at a graph, its exits delivering `pre`**:
about the node `node` at `l`, its claim `c`, its entry state `entry` and its
step's result `st`: the entry state holding where the node assertion does,
the claim's type giving each continuation's shape and a return's result
type, and each normal exit and the handler delivering the target's `pre`. -/
structure NodeMeaningAt (pre : Nat → Assertion) (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ε : HeapKnowledge.EntryState)
    (ctx : Nat → List (Ty ι)) (Tres : Fam) (m : Nat) (l : Nat) (node : Node)
    (c : PointClaim ι) (entry : SinglePass.State) (st : Stepped ι) : Prop where
  entered : ∀ ρ (s : IndexedHeap), passPreT G w startNames ε ctx l ρ m s →
    StateHolds G entry (w.implies l) startNames ε ρ m s
  shape : ∀ n (W : WorldT n) v, meaning G c.type n W v → ShapeOk v node.continuation
  ret : node.continuation = .ret → ∀ n (W : WorldT n) v, meaning G c.type n W v → Tres n W v
  exits : ∀ t pushed observed promote, Exit.normal t pushed observed promote ∈ Exit.ofNode node → ∀ ρ,
    ExitDelivers pre G c.type c.context
      (StateHolds G ⟨st.result :: entry.names, st.store, entry.fresh⟩ (w.implies l) startNames ε) ρ m t
      pushed observed promote
  handler : ∀ t, node.handler = some t → ∀ ρ (s' : IndexedHeap) e,
    StateHolds G ⟨entry.names, entry.store.dropHeap (fun _ => false), entry.fresh⟩ (w.implies l) startNames ε
      ρ m s' →
    EnvOk G c.context ρ s'.n s'.W → Scoped 0 e → excOf G s'.n s'.W e →
    pre t.label (PointClaims.mapEnv t.mapping (push e ρ)) m s'

/-- **What a node's step means at a graph**: `NodeMeaningAt` with each
normal exit and the handler delivering the target's typed assertion with
its written assertion (`edgePreA`), the written assertions `stated`. -/
abbrev NodeMeaning (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ε : HeapKnowledge.EntryState) (ctx : Nat → List (Ty ι))
    (stated : Nat → Option HeapKnowledge.Knowledge) (Tres : Fam) (m : Nat) (l : Nat) (node : Node)
    (c : PointClaim ι) (entry : SinglePass.State) (st : Stepped ι) : Prop :=
  NodeMeaningAt (edgePreA G w startNames ε ctx stated) G w startNames ε ctx Tres m l node c entry st

section Split
variable {G : NormalGraph ι} {images : InstanceImageCheck G} {pool : List (Ty ι)} {fuel : Nat}
  {suggestions : List (Sequent ι)} {index : KnownIndex ι} {codes : CodeEntry ι → Bool} {aliases : List (ι × ι)}
  {pc : PassChecker G images} {undefTy : Option (Ty ι)} {P : ControlFlow.Program} {w : Walk ι}
  {startNames : List Nat} {ctx : Nat → List (Ty ι)} {Tres : Fam} {m : Nat} {l : Nat}

end Split

end Verification.TolerantFrames
