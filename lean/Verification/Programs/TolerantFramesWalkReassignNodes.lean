import Verification.Programs.TolerantFramesWalkReassignChecks
import Verification.Programs.TolerantFramesNodeWalk

/-! # Tolerant frames: a visited node's run at a reassignment

`NodeAccepted` holds what the pass computed at a node (`NodeRan`: the step,
the store's well-formedness, the names below the counter, the width, the
summary table checked) and what follows of it at the graph's meaning
(`NodeMeaning`: the stated assertion, the shapes, the return type, the exits,
the handler). The first is data and checks: it is carried to `reassign G η`
by the invariance of the pass's functions (`nodeRan_reassign`, from
`CheckedStepReassign`). The second reads the graph's meaning at its own
assignment, so it is established at `reassign G η` by the theorems that give
it at every graph from the checks there (the exit lemmas of
`TolerantFramesNodeWalk`), which is what `run_traversed` composes. -/
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

/-- **What a node's run means at a graph**: the fields of `NodeAccepted`
that read the graph's meaning, about the run `r`. -/
structure NodeMeaning {G : NormalGraph ι} {images : InstanceImageCheck G} {pool : List (Ty ι)} {fuel : Nat}
    {suggestions : List (Sequent ι)} {index : KnownIndex ι} {codes : CodeEntry ι → Bool} {aliases : List (ι × ι)}
    {pc : PassChecker G images} {undefTy : Option (Ty ι)} {P : ControlFlow.Program} {w : Walk ι}
    {startNames : List Nat} {ctx : Nat → List (Ty ι)} {l : Nat}
    (r : NodeRan G images pool fuel suggestions index codes aliases pc undefTy P w startNames ctx l)
    (ρ0 : Env) (Tres : Fam) (m : Nat) : Prop where
  stated : ∀ ρ (s : IndexedHeap), passPreT G w startNames ρ0 ctx l ρ m s →
    StateHolds G r.entry (w.implies l) startNames ρ0 ρ m s
  shape : ∀ n (W : WorldT n) v, meaning G r.c.type n W v → ShapeOk v r.node.continuation
  ret : r.node.continuation = .ret → ∀ n (W : WorldT n) v, meaning G r.c.type n W v → Tres n W v
  exits : ∀ t pushed observed promote, Exit.normal t pushed observed promote ∈ Exit.ofNode r.node → ∀ ρ,
    ExitDelivers (edgePreT G w startNames ρ0 ctx) G r.c.type r.c.context
      (StateHolds G ⟨r.st.result :: r.entry.names, r.st.store, r.entry.fresh⟩ (w.implies l) startNames ρ0) ρ m t
      pushed observed promote
  handler : ∀ t, r.node.handler = some t → ∀ ρ (s' : IndexedHeap) e,
    StateHolds G ⟨r.entry.names, r.entry.store.dropHeap (fun _ => false), r.entry.fresh⟩ (w.implies l) startNames ρ0
      ρ m s' →
    EnvOk G r.c.context ρ s'.n s'.W → Scoped 0 e → excOf G s'.n s'.W e →
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
    startNames ρ0 ctx Tres m l) : NodeMeaning na.ran ρ0 Tres m :=
  ⟨na.stated, na.shape, na.ret, na.exits, na.handler⟩

/-- **A node is accepted where it ran and its run means what it states.** -/
def NodeAccepted.ofRan (r : NodeRan G images pool fuel suggestions index codes aliases pc undefTy P w startNames ctx l)
    (h : NodeMeaning r ρ0 Tres m) :
    NodeAccepted G images pool fuel suggestions index codes aliases pc undefTy P w startNames ρ0 ctx Tres m l :=
  ⟨r.node, r.hP, r.c, r.hctx, r.entry, h.stated, r.ms, r.fresh, r.answers, r.st, r.stats, r.ans, r.hstep, r.wf,
    r.below, r.width, r.sums, h.shape, h.ret, h.exits, h.handler⟩

end Split

/-- **The step at a reassigned graph** (a named hypothesis): `checkedStep`
at `reassign G η`, with the reassigned image check, the checker `pc'` and
the answers reassigned, returns what it returns at `G`, its answers
reassigned. Its proof lacks the invariance of the functions `checkedStep`
calls that are not proved invariant here: `directCall` (its `for` loops
over the signatures and operands, threading the answers), the search
`expressionEffectUsing`, and the checker's `select` at the reassigned graph
(`pc'` the reassignment of `pc`: `ordinary` for `ordinary`; for a qualified
body, a `BodySubtyping (reassign G η)`, which exists where the body's check
is sound at `η`, the scope `q.Admits η`). The tree check, `requiresTree`,
`subtypeUsing` and the call layers it calls are invariant
(`Parametricity.checkTree_reassign`, `Parametricity.requiresTree_reassign`,
`subtypeUsing_reassign`, `Parametricity.elementsCall_reassign`,
`Parametricity.requiresCall_reassign`, `Parametricity.freshCall_reassign`,
`Parametricity.ownCall_reassign`, `Parametricity.keepsCall_reassign`). -/
def CheckedStepReassign (G : NormalGraph ι) (η : MixedAssignment ι) (images : InstanceImageCheck G)
    (pool : List (Ty ι)) (fuel : Nat) (suggestions : List (Sequent ι)) (index : KnownIndex ι)
    (codes : CodeEntry ι → Bool) (aliases : List (ι × ι)) (pc : PassChecker G images)
    (pc' : PassChecker (reassign G η) (images.reassign η)) (undefTy : Option (Ty ι)) : Prop :=
  ∀ l node c entry ms fresh (answers : Answered G),
    checkedStep (reassign G η) (images.reassign η) pool fuel suggestions index codes aliases pc' undefTy l node c entry
        ms fresh (Answered.reassign answers η) =
      ((checkedStep G images pool fuel suggestions index codes aliases pc undefTy l node c entry ms fresh answers).1,
        (checkedStep G images pool fuel suggestions index codes aliases pc undefTy l node c entry ms fresh answers).2.1,
        Answered.reassign
          (checkedStep G images pool fuel suggestions index codes aliases pc undefTy l node c entry ms fresh answers).2.2 η)

/-- **A node's run at a reassignment**: where the step is invariant
(`CheckedStepReassign`), what the pass computed at a node of `G` it computes
at `reassign G η`, the answers reassigned; the summary table stays checked
(`Parametricity.summariesSound_reassign`). -/
def nodeRan_reassign {G : NormalGraph ι} {η : MixedAssignment ι} {images : InstanceImageCheck G}
    {pool : List (Ty ι)} {fuel : Nat} {suggestions : List (Sequent ι)} {index : KnownIndex ι}
    {codes : CodeEntry ι → Bool} {aliases : List (ι × ι)} {pc : PassChecker G images}
    {pc' : PassChecker (reassign G η) (images.reassign η)} {undefTy : Option (Ty ι)} {P : ControlFlow.Program}
    {w : Walk ι} {startNames : List Nat} {ctx : Nat → List (Ty ι)} {l : Nat}
    (hs : CheckedStepReassign G η images pool fuel suggestions index codes aliases pc pc' undefTy)
    (r : NodeRan G images pool fuel suggestions index codes aliases pc undefTy P w startNames ctx l) :
    NodeRan (reassign G η) (images.reassign η) pool fuel suggestions index codes aliases pc' undefTy P w startNames ctx
      l where
  node := r.node
  hP := r.hP
  c := r.c
  hctx := r.hctx
  entry := r.entry
  ms := r.ms
  fresh := r.fresh
  answers := Answered.reassign r.answers η
  st := r.st
  stats := r.stats
  ans := Answered.reassign r.ans η
  hstep := by rw [hs, r.hstep]
  wf := r.wf
  below := r.below
  width := r.width
  sums := Parametricity.summariesSound_reassign G η images r.sums

/-- **An accepted node at a reassignment**: where the step is invariant, a
node the pass accepted at `G` is accepted at `reassign G η` given its run's
meaning there (`NodeMeaning` of the reassigned run, which the exit lemmas
give at every graph from the checks). -/
def nodeAccepted_reassign {G : NormalGraph ι} {η : MixedAssignment ι} {images : InstanceImageCheck G}
    {pool : List (Ty ι)} {fuel : Nat} {suggestions : List (Sequent ι)} {index : KnownIndex ι}
    {codes : CodeEntry ι → Bool} {aliases : List (ι × ι)} {pc : PassChecker G images}
    {pc' : PassChecker (reassign G η) (images.reassign η)} {undefTy : Option (Ty ι)} {P : ControlFlow.Program}
    {w : Walk ι} {startNames : List Nat} {ρ0 : Env} {ctx : Nat → List (Ty ι)} {Tres : Fam} {m : Nat} {l : Nat}
    (hs : CheckedStepReassign G η images pool fuel suggestions index codes aliases pc pc' undefTy)
    (na : NodeAccepted G images pool fuel suggestions index codes aliases pc undefTy P w startNames ρ0 ctx Tres m l)
    (hm : NodeMeaning (nodeRan_reassign hs na.ran) ρ0 Tres m) :
    NodeAccepted (reassign G η) (images.reassign η) pool fuel suggestions index codes aliases pc' undefTy P w startNames
      ρ0 ctx Tres m l :=
  NodeAccepted.ofRan (nodeRan_reassign hs na.ran) hm

/-- **The guarantee from one run at `G`**: where the pass's run at `G`
computed every visited node (`NodeRan`), the step is invariant at every
admitted assignment for some checker `pc'` there (`hinv`, a named
hypothesis: `CheckedStepReassign`; for a qualified body `pc'` exists at the
scope's admitted assignments), and the run's nodes at `reassign G η` give
the walk predicates there (`hwalk`, `run_traversed`'s statement at the
reassigned graph, whose proof is uniform in the graph), the run guarantees
every field of `GraphGuarantee`. -/
theorem run_guarantee_of_run {G : NormalGraph ι} {admits : MixedAssignment ι → Prop} {P : Program} {start : Nat}
    {goal : Goal ι} {inputs : List (Ty ι)} {sep : HeapSeparation.Separation} {idx : List HeapKnowledge.IndexAtom}
    {assertions : List (Nat × HeapKnowledge.Knowledge)} {bound : Option (Footprints.Closed × Bool × Bool)}
    {ensures : List HeapKnowledge.IndexFact}
    {regional : Option (Footprints.Closed × List Footprints.ArgumentStoreRegion × Bool)}
    {images : InstanceImageCheck G} {pool : List (Ty ι)} {fuel : Nat} {suggestions : List (Sequent ι)}
    {index : KnownIndex ι} {codes : CodeEntry ι → Bool} {aliases : List (ι × ι)} {pc : PassChecker G images}
    {undefTy : Option (Ty ι)} {w : Walk ι} {ctx : Nat → List (Ty ι)}
    (hran : ∀ l, w.visited l → Nonempty (NodeRan G images pool fuel suggestions index codes aliases pc undefTy P w
      (List.range inputs.length) ctx l))
    (hinv : ∀ η, admits η → ∃ pc' : PassChecker (reassign G η) (images.reassign η),
      CheckedStepReassign G η images pool fuel suggestions index codes aliases pc pc' undefTy)
    (hwalk : ∀ η, admits η → ∀ pc' : PassChecker (reassign G η) (images.reassign η),
      (∀ l, w.visited l → Nonempty (NodeRan (reassign G η) (images.reassign η) pool fuel suggestions index codes
        aliases pc' undefTy P w (List.range inputs.length) ctx l)) →
      ∃ (given : Nat → Bool)
        (edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping))
        (fresh : Nat → Nat),
        PassWalkSound (reassign G η) P start goal inputs sep idx assertions bound ensures regional w given ctx
          edgesIn fresh) :
    GraphGuarantee G admits P start goal inputs sep idx assertions bound ensures regional :=
  run_guarantee fun η hη => by
    obtain ⟨pc', hs⟩ := hinv η hη
    obtain ⟨given, edgesIn, fresh, h⟩ := hwalk η hη pc' fun l hl => let ⟨r⟩ := hran l hl; ⟨nodeRan_reassign hs r⟩
    exact ⟨w, given, ctx, edgesIn, fresh, h⟩

end Verification.TolerantFrames
