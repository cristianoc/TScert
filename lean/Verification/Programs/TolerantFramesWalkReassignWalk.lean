import Verification.Programs.TolerantFramesWalkReassignStep
import Verification.Programs.TolerantFramesNodeWalk

/-! # Tolerant frames: a node checked with its searches as oracles

`NodeChecked` is `NodeRan` with the step's equation replaced by the step's
conditions (`StepChecked`), so that a node's step at `reassign G η` is
stated without the searches run there; `nodeChecked_reassign` carries a
node checked at `G` to `reassign G η`, and `stepEdgesSound_of_checked`
gives the typed node obligations from the checked nodes and their meaning
(`NodeMeaning`) at a graph. -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules


section Nodes
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

/-- **A node's step checked, its searches as oracles**: `NodeRan` with the
step's equation replaced by `StepChecked`. -/
structure NodeChecked (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (pc : PassChecker G images) (P : ControlFlow.Program) (w : Walk ι) (startNames : List Nat)
    (ctx : Nat → List (Ty ι)) (l : Nat) where
  node : Node
  hP : P[l]? = some node
  c : PointClaim ι
  hctx : ctx l = c.context
  entry : SinglePass.State
  ms : List Nat
  fresh : Nat
  answers : Answered G
  st : Stepped ι
  ans : Answered G
  hstep : StepChecked G images pc codes c node entry ms fresh answers ans st
  wf : StoreWF entry.store
  below : NamesBelow entry (w.implies l) startNames fresh
  width : entry.names.length ≤ c.context.length
  sums : SummariesSound G images answers.summaries.toList
  /-- The step starts from the label's recorded entry. -/
  hentry : entry = w.entry l
  /-- `run`'s shape check accepts the claim type (`passShapeCheck'`). -/
  hshape : SinglePass.passShapeCheck' G c.type node.continuation = true

/-- A node's run is checked with its searches as oracles, where the direct
call and the search keep the summary table checked. -/
def NodeRan.checked {G : NormalGraph ι} {images : InstanceImageCheck G} {pool : List (Ty ι)} {fuel : Nat}
    {suggestions : List (Sequent ι)} {index : KnownIndex ι} {codes : CodeEntry ι → Bool} {aliases : List (ι × ι)}
    {pc : PassChecker G images} {undefTy : Option (Ty ι)} {P : ControlFlow.Program} {w : Walk ι}
    {startNames : List Nat} {ctx : Nat → List (Ty ι)} {l : Nat}
    (hdir : DirectKeepsSummaries G images undefTy)
    (hsrch : SearchKeepsSummaries G images pool fuel suggestions index codes aliases pc.checker)
    (r : NodeRan G images pool fuel suggestions index codes aliases pc undefTy P w startNames ctx l)
    (hentry : r.entry = w.entry l) (hshape : SinglePass.passShapeCheck' G r.c.type r.node.continuation = true) :
    NodeChecked G images codes pc P w startNames ctx l :=
  ⟨r.node, r.hP, r.c, r.hctx, r.entry, r.ms, r.fresh, r.answers, r.st, r.ans,
    stepChecked_of_step r.hstep hdir hsrch, r.wf, r.below, r.width, r.sums, hentry, hshape⟩

omit [Hashable ι] [Instantiates ι] in
/-- **The shape check at a reassigned graph** is the check at the graph. -/
theorem passShapeCheck'_reassign (G : NormalGraph ι) (η : MixedAssignment ι) (A : Ty ι)
    (k : Continuation) :
    SinglePass.passShapeCheck' (reassign G η) A k = SinglePass.passShapeCheck' G A k := by
  cases k <;> rfl

omit [Instantiates ι] in
/-- **A checked node at a reassignment**: a node checked at `G` is checked
at `reassign G η` with a checker whose `select` is the same result there,
the answers reassigned, the summary table checked
(`Parametricity.summariesSound_reassign`). -/
def nodeChecked_reassign {G : NormalGraph ι} {η : MixedAssignment ι} {images : InstanceImageCheck G}
    {codes : CodeEntry ι → Bool} {pc : PassChecker G images} {pc' : PassChecker (reassign G η) (images.reassign η)}
    {P : ControlFlow.Program} {w : Walk ι} {startNames : List Nat} {ctx : Nat → List (Ty ι)} {l : Nat}
    (hpc : PassCheckerReassign G η images pc pc') (r : NodeChecked G images codes pc P w startNames ctx l) :
    NodeChecked (reassign G η) (images.reassign η) codes pc' P w startNames ctx l :=
  ⟨r.node, r.hP, r.c, r.hctx, r.entry, r.ms, r.fresh, Answered.reassign r.answers η, r.st,
    Answered.reassign r.ans η, stepChecked_reassign hpc r.hstep r.sums, r.wf, r.below, r.width,
    Parametricity.summariesSound_reassign G η images r.sums, r.hentry,
    (passShapeCheck'_reassign G η r.c.type r.node.continuation).trans r.hshape⟩

omit [Hashable ι] [Instantiates ι] in
/-- **A qualified body's checker at an admitted instance**: where the
body's check is the lexical body check (`verify_qualified_safe_at`'s
`bodyCheck`), at an assignment `assign η source.binders As` the scheme
admits within its bounds, the lexical body subtyping of the reassigned
graph (`lexicalBodySubtyping`) has the same check, so the checker there
exists (`passCheckerReassign_qualified`). -/
theorem passCheckerReassign_lexical {G : NormalGraph ι} {images : InstanceImageCheck G} (source : SchemeRow ι)
    {N : Fam} {C : ResolutionDescriptors.Capabilities (excOf G) N}
    (domain : G.domain = ResolutionDescriptors.descriptorDomain C)
    (aliases : List (ι × ι)) (aliasesSound : AliasesSound G source aliases)
    (body : BodySubtyping G) (bodyCheck : body.check = lexicalBodyCheck G images source aliases)
    (ord : ∀ {A B p}, checkUsing G images A B p = true → body.check A B p = true)
    (η : MixedAssignment ι) (As : List MixedFamily) (length : As.length = source.binders.length)
    (allowed : G.domain.allowed source As) (bounded : ∀ m, Bounded (mixedMeaning G) η source As m) :
    ∃ pc' : PassChecker (reassign G (assign η source.binders As)) (images.reassign (assign η source.binders As)),
      PassCheckerReassign G (assign η source.binders As) images (.qualified body ord) pc' :=
  ⟨_, passCheckerReassign_qualified G _ images body
    (lexicalBodySubtyping G images source domain aliases aliasesSound η As length allowed bounded)
    bodyCheck.symm ord⟩

omit [DecidableEq ι] [Hashable ι] [Instantiates ι] in
/-- **Each visited node's step and edges deliver `pre`**: from the typed
node assertion, the node's local judgment and every exit `pre` of its
target (`StepEdgesSoundA` at `pre`). -/
def StepEdgesSoundAt (pre : Nat → Assertion) (P : ControlFlow.Program) (G : NormalGraph ι) (w : Walk ι)
    (startNames : List Nat) (ρ0 : Env) (ctx : Nat → List (Ty ι)) (Ξres Tres : Fam) (Qres Rres : Heap → Prop)
    (m : Nat) : Prop :=
  ∀ l ρ (s : IndexedHeap), passPreT G w startNames ρ0 ctx l ρ m s → ∃ node, P[l]? = some node ∧
    ∃ (Ξ T : Fam) (cn ce : Footprints.Closed) (Qn : Post) (Qe : Heap → Prop),
      SafePostExc Ξ T (fun h' v => cn.Holds s.h h' ∧ Qn h' v) (fun h' => ce.Holds s.h h' ∧ Qe h')
        s.n s.W s.h (instantiate 0 ρ node.expression) ∧
      NodeObligations pre Ξres Tres Qres Rres Ξ T cn ce Qn Qe ρ m s node.continuation node.handler

omit [Instantiates ι] in
/-- **Every checked node of the pass delivers `pre`** (`StepEdgesSoundAt`):
where every visited node is checked with its searches as oracles
(`NodeChecked`) and that node's step means at the graph what it states
with its exits delivering `pre` (`NodeMeaningAt`), the codes are sound,
each visited node's step and exits meet the typed node obligations at
`pre`, with the exception family `excOf G`, the result type `Tres` and no
post on the heap at the graph's exits (`stepChecked_parts` in place of
`checkedStep_parts` in `stepEdgesSound_of`). -/
theorem stepEdgesSound_of_checkedAt {pre : Nat → Assertion} {G : NormalGraph ι} {images : InstanceImageCheck G}
    {codes : CodeEntry ι → Bool}
    {pc : PassChecker G images} {P : ControlFlow.Program} {w : Walk ι} {startNames : List Nat} {ρ0 : Env}
    {ctx : Nat → List (Ty ι)} {Tres : Fam} {m : Nat}
    (hacc : ∀ l, w.visited l → ∃ r : NodeChecked G images codes pc P w startNames ctx l,
      NodeMeaningAt pre G w startNames ρ0 ctx Tres m l r.node r.c r.entry r.st)
    (hcodes : CodesSound G codes) :
    StepEdgesSoundAt pre P G w startNames ρ0 ctx (excOf G) Tres (fun _ => True) (fun _ => True) m := by
  intro l ρ s hp
  obtain ⟨na, hm⟩ := hacc l hp.1.1
  have hS := hm.entered ρ s hp
  have he : EnvOk G na.c.context ρ s.n s.W := na.hctx ▸ hp.2
  obtain ⟨-, -, -, cn, ce, hparts⟩ := stepChecked_parts na.hstep hS na.wf na.below na.width he hcodes na.sums
  obtain ⟨hj, ho⟩ := nodeObligations_of_parts (pre := pre) (Ξres := excOf G)
    (Tres := Tres) (Qres := fun _ => True) (Rres := fun _ => True) (x := na.node.handler) hparts he
    (fun j U v hv => hm.shape (j + 1) U v hv)
    (fun s' v _ hv hF he' _ => normalTarget_of_exits (fun t p o q hmem => hm.exits t p o q hmem ρ) hm.ret
      (fun _ => trivial) s' v hv hF he' (hm.shape _ _ v (he'.2 0 _ rfl)))
    (fun s' e _ hFe he' hsc hx => by
      cases hh : na.node.handler with
      | none => exact ⟨hx, trivial⟩
      | some t => exact hm.handler t hh ρ s' e hFe he' hsc hx)
  exact ⟨na.node, na.hP, _, _, cn, ce, _, _, hj, ho⟩

omit [Instantiates ι] in
/-- **Every checked node of the pass delivers** (`StepEdgesSoundA`):
`stepEdgesSound_of_checkedAt` at `edgePreA`, the targets' typed and written
assertions. -/
theorem stepEdgesSound_of_checked {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {pc : PassChecker G images} {P : ControlFlow.Program} {w : Walk ι} {startNames : List Nat} {ρ0 : Env}
    {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge} {Tres : Fam} {m : Nat}
    (hacc : ∀ l, w.visited l → ∃ r : NodeChecked G images codes pc P w startNames ctx l,
      NodeMeaning G w startNames ρ0 ctx stated Tres m l r.node r.c r.entry r.st)
    (hcodes : CodesSound G codes) :
    StepEdgesSoundA P G w startNames ρ0 ctx stated (excOf G) Tres (fun _ => True) (fun _ => True) m :=
  stepEdgesSound_of_checkedAt hacc hcodes

end Nodes

section Queries
variable {ι : Type} [DecidableEq ι] (G : NormalGraph ι) (η : MixedAssignment ι) (images : InstanceImageCheck G)

/-- **The head query at a reassignment** (`SinglePass.run`, an edge into a
loop head): the given facts `req` checked over the edge's facts `k` with
the facts the edge's context `Γ` states of the cells and links they read,
in the target's context `Δ`, is the same check at `reassign G η`. -/
theorem headQuery_reassign (Δ Γ : List (Ty ι)) (req k : HeapKnowledge.Knowledge) (m : PointClaims.Mapping) :
    KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf (reassign G η) Δ)
        (HeapKnowledge.withTypedLinks (reassign G η) Γ (ControlFlow.withTypedCells (reassign G η) Γ req m k)) req m =
      KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G Δ)
        (HeapKnowledge.withTypedLinks G Γ (ControlFlow.withTypedCells G Γ req m k)) req m := by
  rw [Parametricity.withTypedCells_reassign]
  rfl

/-- **The assertion query at a reassignment** (`SinglePass.run`, an edge
into a node stating an assertion): the edge's facts with what its context
states of the cells it reads, observed where the edge observes the result,
checked against the assertion, is the same check at `reassign G η`. -/
theorem assertionQuery_reassign (Δ Γ : List (Ty ι)) (req k : HeapKnowledge.Knowledge) (m : PointClaims.Mapping)
    (observed : Option BranchRefinement.Observation) :
    KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf (reassign G η) Δ)
        (match observed with
          | some o => HeapKnowledge.observeTyped (reassign G η) Γ (ControlFlow.withTypedCells (reassign G η) Γ req m k) 0 o
          | none => HeapKnowledge.withTypedLinks (reassign G η) Γ (ControlFlow.withTypedCells (reassign G η) Γ req m k))
        req m =
      KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G Δ)
        (match observed with
          | some o => HeapKnowledge.observeTyped G Γ (ControlFlow.withTypedCells G Γ req m k) 0 o
          | none => HeapKnowledge.withTypedLinks G Γ (ControlFlow.withTypedCells G Γ req m k))
        req m := by
  rw [Parametricity.withTypedCells_reassign]
  cases observed <;> rfl

/-- **An edge's evidence check at a reassignment** (`edgeEvidenceChecked`,
which the pass applies to the evidence the edge search returns): the same
check at `reassign G η`, so the edge search is an oracle as the step's
search is. -/
theorem edgeEvidenceChecked_reassign (Γ Δ : List (Ty ι)) (t : Target)
    (observed : Option BranchRefinement.Observation) (fields optionals : List (Nat × PropKey))
    (cells : HeapFacts.Facts) (p : PointClaims.EdgeEvidence ι) :
    edgeEvidenceChecked (reassign G η) (images.reassign η) Γ Δ t observed fields optionals cells p =
      edgeEvidenceChecked G images Γ Δ t observed fields optionals cells p := by
  unfold edgeEvidenceChecked
  cases observed <;>
    simp only [Parametricity.unsatisfiable_reassign, Parametricity.checkMapped_reassign,
      Parametricity.checkObserved_reassign]

end Queries

end Verification.TolerantFrames
