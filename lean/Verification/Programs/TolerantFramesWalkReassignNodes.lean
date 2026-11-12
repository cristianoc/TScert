import Verification.Programs.TolerantFramesWalkReassignChecks
import Verification.Programs.TolerantFramesNodeWalk

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

/-- **What the pass computed at a visited node**: the fields of
`NodeAccepted` that are the pass's values and checks. -/
structure NodeRan (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) (fuel : Nat)
    (suggestions : List (Sequent ι)) (index : KnownIndex ι) (codes : CodeEntry ι → Bool) (aliases : List (ι × ι))
    (pc : PassChecker G images) (undefTy : Option (Ty ι)) (P : ControlFlow.Program) (w : Walk ι)
    (startNames : List Nat) (ctx : Nat → List (Ty ι)) (l : Nat) where
  node : Node
  hP : P[l]? = some node
  c : PointClaim ι
  hctx : ctx l = c.context
  entry : SinglePass.State
  ms : List Nat
  fresh : Nat
  answers : Answered G
  st : Stepped ι
  stats : StepStats
  ans : Answered G
  hstep : checkedStep G images pool fuel suggestions index codes aliases pc undefTy l node c entry ms fresh answers =
    (Except.ok st, stats, ans)
  wf : StoreWF entry.store
  below : NamesBelow entry (w.implies l) startNames fresh
  width : entry.names.length ≤ c.context.length
  sums : SummariesSound G images answers.summaries.toList

/-- **What a node's step means at a graph**: the fields of `NodeAccepted`
that read the graph's meaning, about the node `node` at `l`, its claim `c`,
its entry state `entry` and its step's result `st`. -/
structure NodeMeaning (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ρ0 : Env) (ctx : Nat → List (Ty ι))
    (Tres : Fam) (m : Nat) (l : Nat) (node : Node) (c : PointClaim ι) (entry : SinglePass.State) (st : Stepped ι) :
    Prop where
  stated : ∀ ρ (s : IndexedHeap), passPreT G w startNames ρ0 ctx l ρ m s →
    StateHolds G entry (w.implies l) startNames ρ0 ρ m s
  shape : ∀ n (W : WorldT n) v, meaning G c.type n W v → ShapeOk v node.continuation
  ret : node.continuation = .ret → ∀ n (W : WorldT n) v, meaning G c.type n W v → Tres n W v
  exits : ∀ t pushed observed promote, Exit.normal t pushed observed promote ∈ Exit.ofNode node → ∀ ρ,
    ExitDelivers (edgePreT G w startNames ρ0 ctx) G c.type c.context
      (StateHolds G ⟨st.result :: entry.names, st.store, entry.fresh⟩ (w.implies l) startNames ρ0) ρ m t
      pushed observed promote
  handler : ∀ t, node.handler = some t → ∀ ρ (s' : IndexedHeap) e,
    StateHolds G ⟨entry.names, entry.store.dropHeap (fun _ => false), entry.fresh⟩ (w.implies l) startNames ρ0
      ρ m s' →
    EnvOk G c.context ρ s'.n s'.W → Scoped 0 e → excOf G s'.n s'.W e →
    edgePreT G w startNames ρ0 ctx t.label (PointClaims.mapEnv t.mapping (push e ρ)) m s'

section Split
variable {G : NormalGraph ι} {images : InstanceImageCheck G} {pool : List (Ty ι)} {fuel : Nat}
  {suggestions : List (Sequent ι)} {index : KnownIndex ι} {codes : CodeEntry ι → Bool} {aliases : List (ι × ι)}
  {pc : PassChecker G images} {undefTy : Option (Ty ι)} {P : ControlFlow.Program} {w : Walk ι}
  {startNames : List Nat} {ρ0 : Env} {ctx : Nat → List (Ty ι)} {Tres : Fam} {m : Nat} {l : Nat}

/-- The pass's values and checks at an accepted node. -/
def NodeAccepted.ran (na : NodeAccepted G images pool fuel suggestions index codes aliases pc undefTy P w startNames ρ0
    ctx Tres m l) : NodeRan G images pool fuel suggestions index codes aliases pc undefTy P w startNames ctx l :=
  ⟨na.node, na.hP, na.c, na.hctx, na.entry, na.ms, na.fresh, na.answers, na.st, na.stats, na.ans, na.hstep, na.wf,
    na.below, na.width, na.sums⟩

/-- An accepted node's meaning at its graph. -/
theorem NodeAccepted.meaning (na : NodeAccepted G images pool fuel suggestions index codes aliases pc undefTy P w
    startNames ρ0 ctx Tres m l) : NodeMeaning G w startNames ρ0 ctx Tres m l na.node na.c na.entry na.st :=
  ⟨na.stated, na.shape, na.ret, na.exits, na.handler⟩

/-- **A node is accepted where it ran and its run means what it states.** -/
def NodeAccepted.ofRan (r : NodeRan G images pool fuel suggestions index codes aliases pc undefTy P w startNames ctx l)
    (h : NodeMeaning G w startNames ρ0 ctx Tres m l r.node r.c r.entry r.st) :
    NodeAccepted G images pool fuel suggestions index codes aliases pc undefTy P w startNames ρ0 ctx Tres m l :=
  ⟨r.node, r.hP, r.c, r.hctx, r.entry, h.stated, r.ms, r.fresh, r.answers, r.st, r.stats, r.ans, r.hstep, r.wf,
    r.below, r.width, r.sums, h.shape, h.ret, h.exits, h.handler⟩

end Split

end Verification.TolerantFrames
