-- Claims/Wire.lean defines the strict claim document wire and decoder.
import Verification.Source.Claims.Wire
-- Claims/Diagnostics.lean writes located source and quantified-call diagnostics.
import Verification.Source.Claims.Diagnostics
-- Claims/Schemes.lean prepares schemes, generic instances and binder rows.
import Verification.Source.Claims.Schemes
-- Claims/Sites.lean checks claim sites and module initialization order.
import Verification.Source.Claims.Sites
-- Claims/Preparation.lean lowers source annotations and claims into their equations.
import Verification.Source.Claims.Preparation
-- Claims/Plans.lean owns the exhaustive certification boundary and frozen plans.
import Verification.Source.Claims.Plans
-- Claims/Extraction.lean coordinates source units and reconstructs graph requests.
import Verification.Source.Claims.Extraction
-- Claims/Imports.lean plans certified imports: the module runs and the qualified reads.
import Verification.Source.Claims.Imports
-- EvidenceWire.lean reads and writes the evidence document's tables and references.
import Verification.Source.EvidenceWire

/-! Source claim validation, evidence production and the theorem relating
exact accepted plans to modeled graph safety. -/
namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore
open EquationGraphs (Tree)

/-- A unit stating a postcondition whose return does not establish it:
refused at that return, at a node whose edge loses a slot holding an input
the facts name, or at the definition where the unit is qualified. -/
def ensuresRefusal {σ ι : Type} [Labels ι] [StoreView σ ι] (name : String) (namePos : Span)
    (r : SourceRequest σ ι) (c : Response ι) : Option String :=
  if r.ensures.isEmpty || (ensuresResult r c).accepted then none else
  let G := RequestJson.graph r.toRequest
  let T := GraphCode.trackTable r.program c.certificate r.start (GraphCode.namedInputs r.ensures)
  let bad := (List.range r.program.length).find? fun l =>
    match r.program[l]?, c.certificate[l]? with
    | some node, some n => !(GraphCode.edgesTrack T l node &&
        GraphCode.returnOk G n node.continuation (GraphCode.trackedAt T l) r.ensures)
    | _, _ => false
  let pos := ((bad.bind fun l => (r.sourceMap[l]?).bind id).map (·.pos)).getD namePos
  -- Whether the node at fault loses a slot holding an input the facts name
  -- along an edge, or is a return not entailing them.
  let losing := bad.any fun l => match r.program[l]? with
    | some node => !GraphCode.edgesTrack T l node
    | none => false
  if losing then
    some s!"source ensures refusal at [{pos.1},{pos.2}): an edge in '{name}' loses the slot holding a parameter named by its postcondition"
  else
    some s!"source ensures refusal at [{pos.1},{pos.2}): a return of '{name}' does not establish the postcondition stated by its declaration"

/-- The located refusal of a footprint a unit claims for its declaration, or
for a closure of its code, that its graph and certificate do not establish:
at the first node the node-by-node bound check refuses, else at the
closure's region, else at the declaration. Search and checking report it
alike. A check that ran out of search rounds is no refusal: it is left to the
exhaustion diagnostic. -/
def footprintRefusal {σ ι : Type} [Labels ι] [StoreView σ ι] (name : String) (namePos : Span)
    (r : SourceRequest σ ι) (c : Response ι) : Option String :=
  let G := RequestJson.graph r.toRequest
  let images := StoreView.images r.types
  let firstBad (Φ : Footprints.Closed) (ret exc : Bool) (start : Nat) (P : Program) (C : Certificate ι)
      (sourceMap : SourceMap) : Option SourceMapEntry :=
    let facts := GraphCode.inferFresh G images c.readSummaries P C start
    let dead := GraphCode.inferDead G P C exc
    ((P.zip C).zipIdx.find? fun ((node, point), l) =>
      !GraphCode.nodeChecked G images c.readSummaries Φ facts dead ret exc l node point).bind fun (_, l) => (sourceMap[l]?).bind id
  let refuse (what : String) (pos : Span) :=
    s!"source effect refusal at [{pos.1},{pos.2}): the footprint claimed for {what} is not established by its body"
  -- An async definition's footprint is `top` whatever its body does
  -- (`RequestJson.asyncEffects`): refused at the definition.
  let refuseAsync (what : String) (pos : Span) :=
    s!"source effect refusal at [{pos.1},{pos.2}): the footprint claimed for {what} is not `top`, and an async definition's is"
  if !RequestJson.asyncEffects r.async r.footprint then some (refuseAsync s!"'{name}'" namePos) else
  -- A stated declaration's claim lies within its statement
  -- (`RequestJson.statedWithin`): refused at the definition.
  if !RequestJson.statedWithin r.async r.footprint r.onThrow r.fresh r.stated then
    some s!"source effect refusal at [{namePos.1},{namePos.2}): the footprint claimed for '{name}' is not within the effect its result annotation states" else
  let asyncCode := (r.toRequest.codes.zipIdx.find? fun (q, _) =>
    !RequestJson.asyncEffects q.async q.entry.row.effect.footprint).map fun (_, i) =>
      refuseAsync s!"a closure in '{name}'"
        ((((r.codeSources[i]?).bind fun code => sourceMapRegion code.sourceMap).map (·.pos)).getD namePos)
  if asyncCode.isSome then asyncCode else
  let unit := effectResult r c
  if !unit.accepted then
    if unit.exhaustion.isSome then none else
    some (refuse s!"'{name}'" (((firstBad r.footprint r.fresh r.onThrow r.start r.program c.certificate r.sourceMap).map (·.pos)).getD namePos))
  else
  -- A statement with store regions: at the first node the regional check
  -- refuses (`regionalResult`), else at the declaration.
  if !(regionalResult r c).accepted then
    let fieldsOk := (r.regional.map fun (_, regions) =>
      GraphCode.ArgumentPathTracking.checkEntryFields G r.inputs regions).getD true
    let place := r.regional.bind fun (Φ, regions) =>
      let P := GraphCode.program (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))
      let table := regionTable P c.certificate r.start regions
      let ft := freshTables G images c.readSummaries Φ P c.certificate r.start
      (GraphCode.ArgumentRegionGraph.firstRefusedNode G images c.readSummaries Φ regions table ft
        (r.stated.any (·.onThrow)) P c.certificate).bind fun (_, l) => (r.sourceMap[l]?).bind id
    let pos := (place.map (·.pos)).getD namePos
    if !fieldsOk then
      some s!"source effect refusal at [{namePos.1},{namePos.2}): the frame stated for '{name}' reads a store region through a field that is no present stable field of its parameter's type, or through more than one field"
    else
    some s!"source effect refusal at [{pos.1},{pos.2}): the frame stated for '{name}' is not established by its body: a step changes a location outside its store regions beyond the statement's bound"
  else
    (r.toRequest.codes.zip c.codes).zipIdx.findSome? fun ((q, C), i) =>
      let code := GraphCode.effectCheckedResult G images c.readSummaries q.entry C
      if code.accepted || code.exhaustion.isSome then none else
        let sourceMap := ((r.codeSources[i]?).map (·.sourceMap)).getD []
        let place := firstBad q.entry.row.effect.footprint q.entry.row.effect.fresh q.entry.row.effect.onThrow
            q.entry.start
            (GraphCode.program q.entry.exprs q.entry.conts) C sourceMap <|>
          sourceMapRegion sourceMap
        some (refuse s!"a closure in '{name}'" ((place.map (·.pos)).getD namePos))

/-- Where evidence fails a node's check: the first node of the unit's graph,
or of a closure's code, whose certificate the node-by-node check refuses, at
its source position. A diagnostic only: acceptance is `checkRequestsResult`. -/
private def nodeRefusal {σ ι : Type} [Labels ι] [StoreView σ ι] (r : SourceRequest σ ι) (c : Response ι) :
    Option String :=
  let G := RequestJson.graph r.toRequest
  let images := StoreView.images r.types
  let firstBad (Φ : Footprints.Closed) (exc : Bool) (start : Nat) (P : Program) (C : Certificate ι)
      (sourceMap : SourceMap) : Option SourceMapEntry :=
    let facts := GraphCode.inferFresh G images c.readSummaries P C start
    let dead := GraphCode.inferDead G P C exc
    ((P.zip C).zipIdx.find? fun ((node, point), l) =>
      !GraphCode.nodeChecked G images c.readSummaries Φ facts dead false exc l node point).bind fun (_, l) => (sourceMap[l]?).bind id
  let refuse (pos : Span) :=
    s!"source evidence refusal at [{pos.1},{pos.2}): the evidence does not establish this node's claim"
  ((firstBad r.footprint r.onThrow r.start r.program c.certificate r.sourceMap).map (refuse ·.pos)) <|>
    (r.toRequest.codes.zip c.codes).zipIdx.findSome? fun ((q, C), i) =>
      let sourceMap := ((r.codeSources[i]?).map (·.sourceMap)).getD []
      (firstBad q.entry.row.effect.footprint q.entry.row.effect.onThrow q.entry.start
        (GraphCode.program q.entry.exprs q.entry.conts) C sourceMap).map (refuse ·.pos)

/-- Where evidence fails a node's typing: the first node of the unit's graph
whose node check (`ControlFlow.checkNodeUsing`: its claim, its yields, its
edges) refuses the certificate, at its source position. A diagnostic only. -/
private def typingRefusal {σ ι : Type} [Labels ι] [StoreView σ ι] (r : SourceRequest σ ι) (c : Response ι) :
    Option String :=
  let G := RequestJson.graph r.toRequest
  let codes := match codeTable r.toRequest c with
    | some table => GraphCode.admits table
    | none => fun _ => false
  ((r.program.zip c.certificate).zipIdx.find? fun ((node, e), _) =>
      !checkNodeUsing (checker := r.checker) (sums := c.readSummaries) G (StoreView.images r.types) r.goal r.program
        c.certificate node e codes).bind
    fun (_, l) => ((r.sourceMap[l]?).bind id).map fun m =>
      s!"source evidence refusal at [{m.pos.1},{m.pos.2}): the evidence does not establish this node's typing"

/-- Where evidence fails an expression obligation: the first whose evidence
the check refuses, at its source position. A diagnostic only. -/
private def obligationRefusal {σ ι : Type} [Labels ι] [StoreView σ ι] (r : SourceRequest σ ι) (c : Response ι)
    (es : List (ProgramCertificates.Evidence ι)) : Option String :=
  let G := RequestJson.graph r.toRequest
  let codes := match codeTable r.toRequest c with
    | some table => GraphCode.admits table
    | none => fun _ => false
  ((r.obligations.zip es).find? fun (q, e) =>
    !(ExpressionClaims.checkResult G (StoreView.images r.types) (StoreView.valid r.types) q.sequent e codes
      c.readSummaries).accepted).map
    fun (q, _) => s!"source evidence refusal at [{q.pos.1},{q.pos.2}): the evidence does not establish this obligation's claim"

/-- Where evidence states another claim than the unit's: the first node of
the unit's graph whose evidence is for another claim, at its source position.
A diagnostic only. -/
private def claimRefusal {σ ι : Type} [Labels ι] [StoreView σ ι] (r : SourceRequest σ ι) (c : Response ι) :
    Option String :=
  ((c.certificate.zip r.claims).zipIdx.find? fun ((e, q), _) =>
      !decide (CertificateProducer.signature e = q)).bind fun (_, l) =>
    ((r.sourceMap[l]?).bind id).map fun m =>
      s!"source evidence refusal at [{m.pos.1},{m.pos.2}): the evidence does not establish this node's claim"

/-- The destination of a failed incoming type or heap-knowledge obligation.
Claim agreement is checked before this diagnostic is selected. -/
@[nospecialize] private def edgeRefusal {σ ι : Type} [Labels ι] [StoreView σ ι]
    (r : SourceRequest σ ι) (c : Response ι) : Option String := Id.run do
  let G := RequestJson.graph r.toRequest
  let images := StoreView.images r.types
  let codes := match codeTable r.toRequest c with
    | some table => GraphCode.admits table
    | none => fun _ => false
  -- A bad expression or yield can also make a later edge fail. Report that
  -- local typing failure before blaming an incoming interface.
  if (r.program.zip c.certificate).any (fun (node, e) =>
      !((ProgramCertificates.claim e.expression).term == node.expression &&
        ProgramCertificates.checkScope (entry e).length node.expression &&
        (r.checker.run (ProgramCertificates.claim e.expression) (entryFacts G e)
          (e.effect.getD (.ordinary e.expression)) codes c.readSummaries).value.any (outputFits G e) &&
        checkYields G images e codes c.readSummaries)) then return none
  for ((node, e), label) in (r.program.zip c.certificate).zipIdx do
    if let (some target, some (T, proof)) := (node.handler, e.handler) then
      if let some destination := c.certificate[target.label]? then
        let typed := PointClaims.checkMappedUsing G images (T :: entry e) (entry destination) target.mapping proof
        let linked := KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G (entry destination)) (handlerFacts (entryFacts G e))
          destination.knowledge target.mapping
        if !typed || !linked then
          if let some m := (r.sourceMap[target.label]?).bind id then
            return some s!"source incoming edge obligation at [{m.pos.1},{m.pos.2}): evidence fails {if !typed then "type coverage" else "heap knowledge"} from node {label}, handler edge"
    for (target, index) in (CertificateProducer.successors node.continuation).zipIdx do
      let some destination := c.certificate[target.label]? | continue
      let some proof := e.edges[index]? | continue
      let Γ := CertificateProducer.edgeContextOf G e node.continuation index
      let facts := CertificateProducer.edgeImplicationsOf.edgeFactsOf (ControlFlow.outFacts G e) node.continuation
      let observed := match node.continuation with
        | .branchBind .. => some (BranchRefinement.Observation.boolean (index == 0))
        | .tagBind tag .. => some (BranchRefinement.Observation.tag tag (index == 0))
        | _ => none
      let typed := match observed with
        | none => PointClaims.checkMappedUsing G images Γ (entry destination) target.mapping proof
        | some o => BranchRefinement.checkObservedUsing G images Γ (entry destination) 0 o target.mapping proof
            (readFields facts 0) (optionalFields facts 0) (HeapKnowledge.aliasCells (HeapKnowledge.observeTyped G Γ facts 0 o))
      -- The source knowledge the checker reads (`ControlFlow.withTypedCells`).
      let typedFacts := ControlFlow.withTypedCells G Γ destination.knowledge target.mapping facts
      let knowledge := match observed with
        | none => HeapKnowledge.withTypedLinks G Γ typedFacts
        | some o => HeapKnowledge.observeTyped G Γ typedFacts 0 o
      let linked := KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G (entry destination)) knowledge destination.knowledge target.mapping
      if !typed || !linked then
        if let some m := (r.sourceMap[target.label]?).bind id then
          return some s!"source incoming edge obligation at [{m.pos.1},{m.pos.2}): evidence fails {if !typed then "type coverage" else "heap knowledge"} from node {label}, edge {index}"
  return none

/-- The located refusal of requests a bundle does not justify. -/
def requestsRefusal {σ ι : Type} [Labels ι] [StoreView σ ι] (certified : List (CertifiedPlan σ ι)) (b : Bundle ι)
    (checked : ProgramCertificates.CheckResult ι Unit) : String :=
  let rs := CertifiedPlan.requests certified
  -- An exhausted search is reported as such; a footprint the graph does not
  -- establish is located, then a node or an obligation whose evidence the
  -- check refuses; any other failure is the generic refusal.
  let fallback := validationFailure rs checked "source evidence does not justify the extracted program and exact claims"
  if checked.exhaustion.isSome then fallback else
    (((certified.zip b.functions).findSome? fun (plan, c) => match plan with
      | .graph name namePos r => footprintRefusal name namePos r c <|> ensuresRefusal name namePos r c) <|>
     (((certified.zip b.functions).zip b.obligations).findSome? fun ((plan, c), es) => match plan with
      | .graph _ _ r => obligationRefusal r c es <|> claimRefusal r c <|> edgeRefusal r c <|> nodeRefusal r c <|>
          typingRefusal r c)).getD fallback

/-- Check extracted plans at their evidence: freeze them, cross the
exhaustive certification boundary, decode the evidence and check every
request. -/
def checkPlans (T : EquationStore.State) (plans : List (FunctionPlan EquationStore.State Tree))
    (evidence : Json) : Except String Unit := do
  let ⟨F, frozen⟩ ← freezePlans T plans
  let certified ← certifyPlans frozen
  let rs := CertifiedPlan.requests certified
  let b : Bundle (EquationStore.CheckedLabel F.equations F.primitive) ← EvidenceWire.decode evidence
  let checked := checkRequestsResult rs b
  if checked.accepted then return ()
  throw (requestsRefusal certified b checked)

def checkDocument (ast claims : Json) (fileKey : String) (evidence : Json)
    (budget : PositiveCertificates.SearchBudget := {})
    (qualified : List (String × Footprints.Closed × Bool × Footprints.Closed) := []) : Except String Unit := do
  let (T, plans) ← extractPlans ast claims fileKey budget qualified
  checkPlans T plans evidence

private def codeJson {ι : Type} [ToJson ι] (c : CodeEntry ι) : Json :=
  Json.mkObj [("arity", toJson c.arity), ("start", toJson c.start),
    ("program", toJson ((c.exprs.zip c.conts).map fun (e, k, h) => (⟨e, k, h⟩ : Node)))]

/-- The program graph each unit lowers to, with the graph code it creates, for
inspection: per unit its name, entry node and nodes, and per code its arity,
entry node and nodes. -/
def lowerJson (ast claims : Json) (fileKey : String) : Except String Json := do
  let p ← planImports ast claims
  let (T, plans) ← extractPlans p.ast p.claims fileKey {} p.qualified
  let ⟨_, frozen⟩ ← freezePlans T plans
  return toJson (frozen.map fun
    | .graph name _ r => Json.mkObj [("name", toJson name), ("start", toJson r.toRequest.start),
        ("program", toJson r.toRequest.program),
        ("codes", toJson (r.toRequest.codes.map fun (c : CodeRequest _) => codeJson c.entry))])

/-- What requests a bundle justifies give: the check accepts them, each is
safe, within its footprint where it claims one, returning a fresh array
where it promises one, returning values meeting
its postcondition where it states one, within its statement's bound off the
stores its stated regions hold at entry where it states them, and its stated
assertions are entailed by its certificate, as `checkRequests_safe_at`,
`checkRequests_footprint_at`, `checkRequests_ensures_at`,
`checkRequests_regional_at` and `checkRequests_assertions_at` state; each for
an environment meeting what the request assumes of its inputs, their types,
their separation and the index facts of its precondition
(`entryIndices`). -/
def RequestsSafe (F : EquationStore.Frozen)
    (rs : List (SourceRequest (EquationStore.Checked F.equations F.primitive)
      (EquationStore.CheckedLabel F.equations F.primitive)))
    (b : Bundle (EquationStore.CheckedLabel F.equations F.primitive)) : Prop :=
      checkRequests rs b = true ∧
      (∀ r c, (r,c) ∈ rs.zip b.functions →
        ∀ η, r.Admits η → ∀ n W heap ρ, EnvOk (reassign F.equations.graph η) r.inputs ρ n W →
          HeapSeparation.Holds r.entrySeparation ρ → HeapKnowledge.IndexHolds r.entryIndices ρ heap →
          WorldAdm W → HeapOk n W heap →
          SafeGraph (excOf (reassign F.equations.graph η)) r.program
            (ControlFlow.GoalHolds (reassign F.equations.graph η) r.goal (r.goal.argument ρ))
            n W heap (.at r.start ρ)) ∧
      (∀ r c, (r,c) ∈ rs.zip b.functions →
        r.footprint ≠ .top ∨ r.onThrow = true ∨ r.fresh = true →
        ∀ η n W heap (L : List Tm) (d : Tm),
          EnvOk (reassign F.equations.graph η) r.inputs (envOf L d) n W →
          HeapSeparation.Holds r.entrySeparation (envOf L d) →
          HeapKnowledge.IndexHolds r.entryIndices (envOf L d) heap →
          WorldAdm W → HeapOk n W heap → (∀ v ∈ L, isVal v = true) → isVal d = true →
          HeapObservations.SafePostExc (excOf (reassign F.equations.graph η))
            (ControlFlow.GoalHolds (reassign F.equations.graph η) r.goal (r.goal.argument (envOf L d)))
            (fun h' v => r.footprint.Holds heap h' ∧ (r.fresh = true → Footprints.FreshAt heap.length v))
            (fun h' => r.onThrow = true → r.footprint.Holds heap h')
            n W heap
            (.goto (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))
              r.start L d)) ∧
      (∀ r c, (r,c) ∈ rs.zip b.functions → r.ensures ≠ [] →
        ∀ η n W heap (L : List Tm) (d : Tm),
          EnvOk (reassign F.equations.graph η) r.inputs (envOf L d) n W →
          HeapSeparation.Holds r.entrySeparation (envOf L d) →
          HeapKnowledge.IndexHolds r.entryIndices (envOf L d) heap →
          WorldAdm W → HeapOk n W heap →
          HeapObservations.SafePost (excOf (reassign F.equations.graph η))
            (ControlFlow.GoalHolds (reassign F.equations.graph η) r.goal (r.goal.argument (envOf L d)))
            (fun h' v => GraphCode.EnsuresAt r.ensures h' (push v (envOf L d))) n W heap
            (.goto (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))
              r.start L d)) ∧
      (∀ r c, (r,c) ∈ rs.zip b.functions → ∀ Φ regions, r.regional = some (Φ, regions) →
        ∀ η n W heap (L : List Tm) (d : Tm),
          EnvOk (reassign F.equations.graph η) r.inputs (envOf L d) n W →
          HeapSeparation.Holds r.entrySeparation (envOf L d) →
          HeapKnowledge.IndexHolds r.entryIndices (envOf L d) heap →
          WorldAdm W → HeapOk n W heap →
          HeapObservations.SafePostExc (excOf (reassign F.equations.graph η))
            (ControlFlow.GoalHolds (reassign F.equations.graph η) r.goal (r.goal.argument (envOf L d)))
            (fun h' _ => Footprints.ArgumentStoreRegionsWithin Φ regions (envOf L d) heap h')
            (fun h' => r.stated.any (·.onThrow) = true →
              Footprints.ArgumentStoreRegionsWithin Φ regions (envOf L d) heap h')
            n W heap
            (.goto (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))
              r.start L d)) ∧
      (∀ r c, (r,c) ∈ rs.zip b.functions → RequestAssertionsEntailed r c)

theorem requestsSafe_of_check {F : EquationStore.Frozen}
    {rs : List (SourceRequest (EquationStore.Checked F.equations F.primitive)
      (EquationStore.CheckedLabel F.equations F.primitive))}
    {b : Bundle (EquationStore.CheckedLabel F.equations F.primitive)}
    (hx : (checkRequestsResult rs b).accepted = true) : RequestsSafe F rs b := by
  have hc : checkRequests rs b = true := hx
  refine ⟨hc, ?_, ?_, ?_, ?_, fun r c hm => checkRequests_assertions_at hc hm⟩
  · intro r c hm η admitted n W heap ρ he hsep hidx hw hh
    exact checkRequests_safe_at hc hm η admitted n W heap ρ he hw hh hsep hidx
  · intro r c hm heffect η n W heap L d he hsep hidx hw hh hvalues hd
    exact checkRequests_footprint_at hc hm heffect η n W heap L d he hw hh hvalues hd hsep hidx
  · intro r c hm hens η n W heap L d he hsep hidx hw hh
    exact checkRequests_ensures_at hc hm hens η n W heap L d he hw hh hsep hidx
  · intro r c hm Φ regions hr η n W heap L d he hsep hidx hw hh
    exact checkRequests_regional_at hc hm hr η n W heap L d he hw hh hsep hidx

/-- What a successful check of extracted plans gives: they cross the
exhaustive certification boundary, and their requests are safe at the
evidence (`RequestsSafe`). -/
def PlansSafe (T : EquationStore.State) (plans : List (FunctionPlan EquationStore.State Tree))
    (evidence : Json) : Prop :=
    ∃ F : EquationStore.Frozen, ∃ frozen certified b,
      freezePlans T plans = .ok ⟨F, frozen⟩ ∧
      certifyPlans frozen = .ok certified ∧
      EvidenceWire.decode evidence = .ok b ∧
      RequestsSafe F (CertifiedPlan.requests certified) b

/-- What a document's successful check gives: its plans, and what checking
them gives (`PlansSafe`). -/
def DocumentSafe (ast claims : Json) (fileKey : String) (evidence : Json)
    (budget : PositiveCertificates.SearchBudget) (qualified : List (String × Footprints.Closed × Bool × Footprints.Closed)) : Prop :=
    ∃ T plans, extractPlans ast claims fileKey budget qualified = .ok (T, plans) ∧ PlansSafe T plans evidence

/-- Every extracted plan crosses the exhaustive certification boundary, and its
graph request proves the enclosing execution safe at every assignment admitted
by its source signature, including its descriptor contract when qualified. A
unit whose declaration claims a footprint other than the one letting every
location change, run as the code its graph describes, also returns with a heap
its footprint relates to its entry heap, and a value meeting its goal (a
guard's or an assertion function's promise included).
The graph is `Equations.graph` of the equations the extracted store presents,
validated by `Equations.ofRaw` (`freezePlans`). -/
theorem checkPlans_safe {T : EquationStore.State} {plans : List (FunctionPlan EquationStore.State Tree)}
    {evidence : Json} (h : checkPlans T plans evidence = .ok ()) : PlansSafe T plans evidence := by
  unfold PlansSafe
  unfold checkPlans at h
  cases hf : freezePlans T plans with
  | error e => rw [hf] at h; contradiction
  | ok Ff =>
    obtain ⟨F, frozen⟩ := Ff
    rw [hf] at h
    simp only [Bind.bind, Except.bind] at h
    cases hc : certifyPlans frozen with
    | error e => rw [hc] at h; contradiction
    | ok certified =>
      rw [hc] at h
      cases hb : (EvidenceWire.decode evidence : Except String
          (Bundle (EquationStore.CheckedLabel F.equations F.primitive))) with
      | error e => rw [hb] at h; contradiction
      | ok b =>
        rw [hb] at h
        by_cases hx : (checkRequestsResult (CertifiedPlan.requests certified) b).accepted = true
        · exact ⟨F, frozen, certified, b, rfl, hc, hb, requestsSafe_of_check hx⟩
        · simp [hx] at h

theorem checkDocument_safe {ast claims evidence : Json} {fileKey : String}
    {budget : PositiveCertificates.SearchBudget} {qualified : List (String × Footprints.Closed × Bool × Footprints.Closed)}
    (h : checkDocument ast claims fileKey evidence budget qualified = .ok ()) :
    DocumentSafe ast claims fileKey evidence budget qualified := by
  unfold DocumentSafe
  unfold checkDocument at h
  cases he : extractPlans ast claims fileKey budget qualified with
  | error e => rw [he] at h; contradiction
  | ok tp =>
    obtain ⟨T, plans⟩ := tp
    rw [he] at h
    simp only [Bind.bind, Except.bind] at h
    exact ⟨T, plans, rfl, checkPlans_safe h⟩

/-! ### A file's units, checked each on its own over one front -/

/-- A unit member's name as a selection names it: a function's name, or
`:init` for the module's initialization. -/
def memberName (member : String) : String :=
  if member == "init" then ":init" else (member.splitOn "@").headD member

/-- The units of a file a selection names: each group with a member it
names, or every group. -/
def Front.selected (fr : Front) (names : Option (List String)) : List Nat :=
  fr.leaders.filter fun i => match names with
    | none => true
    | some ns => (fr.group i).any fun j => ns.contains (memberName (fr.unitId j))

/-- Every unit's plan, extracted from the front in turn, one store grown
through them; a unit whose extraction fails keeps its refusal and leaves the
store as it was. -/
def Front.extractAll (fr : Front) :
    EquationStore.State × List (Except String (FunctionPlan EquationStore.State Tree)) :=
  fr.units.foldl (init := (fr.d.types, [])) fun (T, plans) u =>
    match extractMember fr T u with
    | .ok (next, plan) => (next, plans ++ [.ok plan])
    | .error reason => (T, plans ++ [.error reason])

/-- A file's plans over one frozen store: the import plan, the front, the
frozen store, and each unit's plan or refusal, in the front's order. -/
structure FilePlans where
  p : ImportPlan
  fr : Front
  F : EquationStore.Frozen
  plans : List (Except String (FunctionPlan (EquationStore.Checked F.equations F.primitive)
    (EquationStore.CheckedLabel F.equations F.primitive)))

def filePlans (ast claims : Json) (fileKey : String) (budget : PositiveCertificates.SearchBudget) :
    Except String FilePlans := do
  let p ← planImports ast claims
  let fr ← fileFront p.ast p.claims fileKey budget p.qualified
  let (T, plans) := fr.extractAll
  let F ← EquationStore.freeze T
  return ⟨p, fr, F, plans.map fun e => e.bind (FunctionPlan.over F)⟩

/-- The plans of a group, by its members' indices, crossing the exhaustive
certification boundary. -/
def FilePlans.certified (f : FilePlans) (group : List Nat) :
    Except String (List (CertifiedPlan (EquationStore.Checked f.F.equations f.F.primitive)
      (EquationStore.CheckedLabel f.F.equations f.F.primitive))) := do
  let plans ← group.mapM fun i => (f.plans[i]?).getD (.error s!"no unit {i}")
  certifyPlans plans

/-- A group's dependencies on the wire: the groups its members reach and, where
its code names a qualified read, the module runs. -/
def FilePlans.dependencies (f : FilePlans) (group : List Nat) : List String :=
  (f.fr.dependencies group).map f.fr.unitId ++
    (if f.fr.readsQualified group then f.p.modules.map ("module:" ++ ·.location) else [])

/-- A group's evidence, decoded: one response and one obligation list per
member, in the group's order. -/
def FilePlans.groupEvidence (f : FilePlans) (group : List Nat) (evidence : Json) :
    Except String (Bundle (EquationStore.CheckedLabel f.F.equations f.F.primitive)) := do
  let b : Bundle (EquationStore.CheckedLabel f.F.equations f.F.primitive) ← EvidenceWire.decode evidence
  if b.functions.length != group.length || b.obligations.length != group.length then
    throw "evidence for another set of units"
  return b

/-- **The verdict of a unit** at its evidence: the group's plans, certified,
checked at the group's evidence. Accepted, its dependencies. A module run is
checked as its own document (`moduleVerdict`). -/
def unitVerdict (f : FilePlans) (_budget : PositiveCertificates.SearchBudget) (unit : String) (evidence : Json) :
    Except String (List String) := do
  let some i := (List.range f.fr.units.length).find? (f.fr.unitId · == unit) | throw s!"no unit {unit}"
  let group := f.fr.group i
  let certified ← f.certified group
  let b ← f.groupEvidence group evidence
  let checked := checkRequestsResult (CertifiedPlan.requests certified) b
  if checked.accepted then return f.dependencies group
  throw (requestsRefusal certified b checked)

/-- What a unit's accepted verdict at its evidence gives: its group's plans
crossing the exhaustive certification boundary and every certified request
safe, and within its footprint where it claims one (`RequestsSafe`). -/
def UnitSafe (f : FilePlans) (_budget : PositiveCertificates.SearchBudget) (unit : String) (evidence : Json) :
    Prop :=
  ∃ i certified b, f.fr.unitId i = unit ∧ f.certified (f.fr.group i) = .ok certified ∧
    f.groupEvidence (f.fr.group i) evidence = .ok b ∧ RequestsSafe f.F (CertifiedPlan.requests certified) b

theorem unitVerdict_safe {f : FilePlans} {budget : PositiveCertificates.SearchBudget} {unit : String}
    {evidence : Json} {deps : List String} (h : unitVerdict f budget unit evidence = .ok deps) :
    UnitSafe f budget unit evidence := by
  unfold unitVerdict at h
  · cases hi : (List.range f.fr.units.length).find? (f.fr.unitId · == unit) with
    | none => simp [hi] at h
    | some i =>
      simp only [hi] at h
      have hid : f.fr.unitId i = unit := by simpa using List.find?_some hi
      cases hc : f.certified (f.fr.group i) with
      | error err => simp [hc, Bind.bind, Except.bind] at h
      | ok certified =>
        simp only [hc, Bind.bind, Except.bind] at h
        cases hb : f.groupEvidence (f.fr.group i) evidence with
        | error err => simp [hb] at h
        | ok b =>
          simp only [hb] at h
          by_cases hx : (checkRequestsResult (CertifiedPlan.requests certified) b).accepted = true
          · exact ⟨i, certified, b, hid, hc, hb, requestsSafe_of_check hx⟩
          · simp [hx] at h

/-- The first extraction refusal among the groups `names` selects: a check
reports it before any refusal at the evidence. -/
def FilePlans.extractionRefusal (f : FilePlans) (names : Option (List String)) : Option String :=
  ((f.fr.selected names).flatMap f.fr.group).findSome? fun i =>
    match (f.plans[i]?).getD (.error "no unit") with
    | Except.error reason => some reason
    | Except.ok _ => none

/-- Search evidence for one group: each member's request searched in turn,
the search's memo kept within the group only; the group's evidence, and its
refusal: the first member's search refused, or the group's check of that
evidence refused, as the checker checks it; and the account of the candidate
search over the members searched to the end (`CertificateProducer.Answered`):
its passes, the most over one graph, and the candidates it left out. -/
def FilePlans.produceGroup (f : FilePlans) (fuel : Nat) (group : List Nat) :
    Json × Option String × Nat × Nat × Nat := Id.run do
  let G : NormalGraph (EquationStore.CheckedLabel f.F.equations f.F.primitive) := StoreView.graph f.F.store
  let I : PositiveCertificates.InstanceImageCheck G := StoreView.images f.F.store
  let mut answers : CertificateProducer.Answered G := {}
  let mut cs := #[]
  let mut es := #[]
  let mut failed : Option String := none
  for i in group do
    let searched : Except String (Response _ × List (ProgramCertificates.Evidence _) × CertificateProducer.Answered G) :=
      do
      let .graph name namePos r ← (f.plans[i]?).getD (.error s!"no unit {i}")
      let labels := r.searchLabels
      let (e, next) ← ExpressionClaims.produceUsing G I labels (StoreView.valid r.types)
        (StoreView.projection r.types) fuel r.obligations { answers with summaries := #[], summaryAnswers := {} }
      let (rendered, next) := ExpressionClaims.renderKnownUsing G I labels (StoreView.valid r.types)
        r.nodePlans next
      let known := e ++ rendered
      -- A qualified body's checker is stated over the request's own image
      -- check: its search keeps that check, and the request's summaries.
      let (c, kept) ← if r.qualification.isNone then
          RequestJson.produceResponseUsing G I (HeapExpressionRules.Checker.ordinary G I) r.toRequest
            fuel [] known r.sourceMap (some labels) r.assertions r.cuts r.candidates r.codeHints r.checker r.aliases next
            (searched := true) (recheck := some (HeapExpressionRules.Checker.ordinary G))
        else do
          let (c, own) ← RequestJson.produceResponseUsing (RequestJson.graph r.toRequest) (StoreView.images r.types)
            r.checker r.toRequest fuel [] known r.sourceMap (some labels) r.assertions r.cuts r.candidates
            r.codeHints r.checker r.aliases { summaries := next.summaries, summaryAnswers := next.summaryAnswers }
            (searched := true)
          pure (c, { next with
            candidatePasses := next.candidatePasses + own.candidatePasses
            candidatePassesMax := max next.candidatePassesMax own.candidatePassesMax
            candidatesLeftOut := next.candidatesLeftOut + own.candidatesLeftOut })
      if let some refusal := footprintRefusal name namePos r c then throw refusal
      return (c, e, kept)
    match searched with
    | .ok (c, e, next) =>
      answers := next
      cs := cs.push c
      es := es.push e
    | .error reason =>
      if failed.isNone then failed := some reason
      cs := cs.push { certificate := [] }
      es := es.push []
  let evidence := EvidenceWire.encode (Bundle.mk cs.toList es.toList)
  let account := (answers.candidatePasses, answers.candidatePassesMax, answers.candidatesLeftOut)
  if failed.isSome then return (evidence, failed, account)
  -- Not refused by its search, the group is checked as the checker checks it,
  -- so a refusal is the search's.
  let refusal : Except String Unit := do
    let certified ← f.certified group
    let b ← f.groupEvidence group evidence
    let checked := checkRequestsResult (CertifiedPlan.requests certified) b
    if !checked.accepted then throw (requestsRefusal certified b checked)
  return (evidence, match refusal with | .ok () => none | .error reason => some reason, account)

/-- A module run on the wire: its location, its restricted document and
claims, and its own qualified reads with their footprints and on-throw
flags. -/
def ModuleRun.wire (m : ModuleRun) : Json :=
  Json.mkObj [("location", toJson m.location), ("ast", m.ast), ("claims", m.claims),
    ("qualified", toJson (m.qualified.map fun (name, footprint, onThrow, result) =>
      Json.mkObj [("name", toJson name), ("footprint", toJson footprint), ("onThrow", toJson onThrow),
        ("resultFootprint", toJson result)]))]

/-- A module run read from the wire, field by field. -/
def ModuleRun.decode (j : Json) : Except String ModuleRun := do
  fieldsExactly j ["location", "ast", "claims", "qualified"]
  let qualified ← (← jArr j "qualified").mapM fun q => do
    fieldsExactly q ["name", "footprint", "onThrow", "resultFootprint"]
    let footprint : Footprints.Closed ← fromJson? (← jField q "footprint")
    let onThrow : Bool ← fromJson? (← jField q "onThrow")
    let result : Footprints.Closed ← fromJson? (← jField q "resultFootprint")
    return (← jStr (← jField q "name"), footprint, onThrow, result)
  return ⟨← jStr (← jField j "location"), ← jField j "ast", ← jField j "claims", qualified⟩

/-- **The verdict of a module run** at its evidence: its restricted document
checked at its claims and qualified reads (`checkDocument`). -/
def moduleVerdict (m : ModuleRun) (budget : PositiveCertificates.SearchBudget) (evidence : Json) :
    Except String Unit :=
  (checkDocument m.ast m.claims m.location evidence budget m.qualified).mapError (s!"module {m.location}: " ++ ·)

/-- A unit's line of an evidence document: the unit, and its evidence. -/
def unitLine (unit : String) (evidence : Json) : Json :=
  Json.mkObj [("unit", toJson unit), ("evidence", evidence)]

/-- A line of an evidence document, read: the unit and its evidence. -/
def readUnitLine (line : Json) : Except String (String × Json) := do
  fieldsExactly line ["unit", "evidence"]
  return (← jStr (← jField line "unit"), ← jField line "evidence")

end Verification.SourceClaimJson
