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
import Verification.Programs.SinglePass
import Verification.Programs.SinglePassStats

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

/-- Whether the evidence's certificates line up with the unit's graph and its
codes' graphs: one certificate per code, one node's evidence per node. -/
private def certificatesAligned {σ ι : Type} [Labels ι] [StoreView σ ι] (r : SourceRequest σ ι) (c : Response ι) :
    Bool :=
  c.certificate.length == r.program.length && c.codes.length == r.toRequest.codes.length &&
    (r.toRequest.codes.zip c.codes).all fun (q, C) => C.length == q.entry.exprs.length

/-- Where evidence that does not line up with the graph fails: an expression
obligation whose evidence the check refuses, else the first node of the
unit's graph, else of a closure's code, whose evidence is for another claim,
at its source position. Reported before the footprint check, which reads
each node at its evidence. A diagnostic only. -/
private def misalignedRefusal {σ ι : Type} [Labels ι] [StoreView σ ι] (r : SourceRequest σ ι) (c : Response ι)
    (es : List (ProgramCertificates.Evidence ι)) : Option String :=
  if certificatesAligned r c then none else
  obligationRefusal r c es <|> claimRefusal r c <|>
    (r.toRequest.codes.zip c.codes).zipIdx.findSome? fun ((q, C), i) =>
      let sourceMap := ((r.codeSources[i]?).map (·.sourceMap)).getD []
      ((C.zip q.claims).zipIdx.find? fun ((e, p), _) => !decide (CertificateProducer.signature e = p)).bind
        fun (_, l) => ((sourceMap[l]?).bind id).map fun m =>
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
  -- An exhausted search is reported as such; evidence that does not line up
  -- with the graph is located at the first node whose claim it does not
  -- state; a footprint the graph does not establish is located, then a node
  -- or an obligation whose evidence the check refuses; any other failure is
  -- the generic refusal.
  let fallback := validationFailure rs checked "source evidence does not justify the extracted program and exact claims"
  if checked.exhaustion.isSome then fallback else
    ((((certified.zip b.functions).zip b.obligations).findSome? fun ((plan, c), es) => match plan with
      | .graph name namePos r => misalignedRefusal r c es <|> footprintRefusal name namePos r c <|>
          ensuresRefusal name namePos r c) <|>
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

/-- `extractAll` over the units `wanted` names, by index, only: another
unit's plan is a refusal no check of the wanted units reads. -/
def Front.extractSome (fr : Front) (wanted : Std.HashSet Nat) (retype : Option Retype := none)
    (instances : Option Instances := none) :
    EquationStore.State × List (Except String (FunctionPlan EquationStore.State Tree)) :=
  (fr.units.zipIdx.foldl (init := (fr.d.types, #[])) fun (T, plans) (u, i) =>
    if !wanted.contains i then (T, plans.push (.error "not extracted")) else
    match extractMember fr T u retype instances with
    | .ok (next, plan) => (next, plans.push (.ok plan))
    | .error reason => (T, plans.push (.error reason))).map id (·.toList)

/-- A file's plans over one frozen store: the import plan, the front, the
frozen store, and each unit's plan or refusal, in the front's order. -/
structure FilePlans where
  p : ImportPlan
  fr : Front
  F : EquationStore.Frozen
  plans : List (Except String (FunctionPlan (EquationStore.Checked F.equations F.primitive)
    (EquationStore.CheckedLabel F.equations F.primitive)))

def filePlans (ast claims : Json) (fileKey : String) (budget : PositiveCertificates.SearchBudget)
    (only : Option (Option (List String)) := none) :
    Except String FilePlans := do
  -- Each phase's time is measured (`SinglePass.timedKind`).
  let p ← SinglePass.timedKind "lower: planImports" fun _ => planImports ast claims
  let fr ← SinglePass.timedKind "lower: fileFront" fun _ => fileFront p.ast p.claims fileKey budget p.qualified
  let (T, plans) := SinglePass.timedKind "lower: extractAll" fun _ => match only with
    | none => fr.extractAll
    | some names => fr.extractSome (((fr.selected names).flatMap fr.group).foldl (·.insert ·) {})
  let F ← SinglePass.timedKind "lower: freeze" fun _ => EquationStore.freeze T
  let plans := SinglePass.timedKind "lower: plans over the store" fun _ => plans.map fun e => e.bind (FunctionPlan.over F)
  return ⟨p, fr, F, plans⟩

/-- A function's claims with only what another unit reads of them: its
identity, signature, footprints and on-throw flag, its point claims and
storage contracts left empty. -/
def signatureClaims (f : Json) : Json :=
  let f := (f.setObjVal! "entries" (Json.arr #[])).setObjVal! "expressions" (Json.arr #[])
  let f := f.setObjVal! "contracts" (Json.arr #[])
  -- No arrows is spelled by leaving the field out (the decoder refuses a
  -- default spelled out).
  match f with
  | .obj kvs => .obj (kvs.erase "arrows")
  | f => f

/-- A claims document whose functions outside `keep` (by name and name
position) hold their signature claims alone (`signatureClaims`). -/
def keepClaims (claims : Json) (keep : String → Span → Bool) : Json :=
  match claims.getObjVal? "functions" with
  | .ok (.arr fs) => claims.setObjVal! "functions" (Json.arr (fs.map fun f =>
      match (f.getObjValAs? String "name").toOption, (f.getObjValAs? Span "namePos").toOption with
      | some n, some p => if keep n p then f else signatureClaims f
      | _, _ => f))
  | _ => claims

/-- **A selected unit's plans**: `filePlans` over what the selected units'
groups read. The groups are read off a front of the file whose functions'
claims are their signatures alone; the import plan holds the qualified reads
whose names the groups' code mentions (`planImports` with `uses`); the front
holds the groups' functions' claims whole and every other function's
signature claims. A refusal of a read or a claim no group reads is no
refusal of the selected units. -/
def unitPlans (ast claims : Json) (fileKey : String) (budget : PositiveCertificates.SearchBudget)
    (names : Option (List String)) (retype : Option Retype := none) : Except String FilePlans := do
  let bare := (claims.setObjVal! "modules" (Json.arr #[])).setObjVal! "functions"
    (Json.arr ((claims.getObjValAs? (Array Json) "functions").toOption.getD #[] |>.map signatureClaims))
  let outline ← SinglePass.timedKind "lower: groups" fun _ =>
    fileFront (ast.setObjVal! "modules" (Json.arr #[])) bare fileKey budget
  let wanted := (outline.selected names).flatMap outline.group
  let mentioned : Std.HashSet String := (wanted.flatMap outline.mentions).foldl (·.insert ·) {}
  let members : List (String × Span) := wanted.filterMap fun i => match outline.units[i]? with
    | some (f, _, none) => some (f.name, f.namePos)
    | _ => none
  let p ← SinglePass.timedKind "lower: planImports" fun _ => planImports ast claims (some mentioned.contains)
  let fr ← SinglePass.timedKind "lower: fileFront" fun _ =>
    fileFront p.ast (keepClaims p.claims fun n pos => members.contains (n, pos)) fileKey budget p.qualified
  let (T, plans) := SinglePass.timedKind "lower: extractAll" fun _ =>
    fr.extractSome (wanted.foldl (·.insert ·) {}) retype
  let F ← SinglePass.timedKind "lower: freeze" fun _ => EquationStore.freeze T
  let plans := SinglePass.timedKind "lower: plans over the store" fun _ => plans.map fun e => e.bind (FunctionPlan.over F)
  return ⟨p, fr, F, plans⟩

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
refusal: the first member's search refused, or the checker's refusal of
what the searches left unchecked; and the account of the candidate
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
  let b := Bundle.mk cs.toList es.toList
  let evidence := EvidenceWire.encode b
  let account := (answers.candidatePasses, answers.candidatePassesMax, answers.candidatesLeftOut)
  if failed.isSome then return (evidence, failed, account)
  -- Not refused by its search, the group's requests are checked for what
  -- their searches left unchecked (`searchedRequestsResult`), so a refusal
  -- the checker would give there is the search's.
  let refusal : Except String Unit := do
    let certified ← f.certified group
    let checked := searchedRequestsResult (CertifiedPlan.requests certified) b
    if !checked.accepted then throw (requestsRefusal certified b checked)
  return (evidence, match refusal with | .ok () => none | .error reason => some reason, account)

/-- `produceGroup` and the check of its bundle, nothing encoded (`unchecked`: the
search leaves the graph's check to that check). Search evidence for one group: each member's request searched in turn,
the search's memo kept within the group only; the group's evidence, and its
refusal: the first member's search refused, or the checker's refusal of
what the searches left unchecked; and the account of the candidate
search over the members searched to the end (`CertificateProducer.Answered`):
its passes, the most over one graph, and the candidates it left out. -/
def FilePlans.searchGroup (f : FilePlans) (fuel : Nat) (group : List Nat) (unchecked : Bool) :
    Except String (Bundle (EquationStore.CheckedLabel f.F.equations f.F.primitive)) := Id.run do
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
            (searched := true) (recheck := some (HeapExpressionRules.Checker.ordinary G)) (unchecked := unchecked)
        else do
          let (c, own) ← RequestJson.produceResponseUsing (RequestJson.graph r.toRequest) (StoreView.images r.types)
            r.checker r.toRequest fuel [] known r.sourceMap (some labels) r.assertions r.cuts r.candidates
            r.codeHints r.checker r.aliases { summaries := next.summaries, summaryAnswers := next.summaryAnswers }
            (searched := true) (unchecked := unchecked)
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
  if let some reason := failed then return .error reason
  return .ok (Bundle.mk cs.toList es.toList)

/-- The check of a group's searched bundle: the group's dependencies where
it is accepted (`checkRequestsResult`), else its refusal. -/
def FilePlans.checkGroup (f : FilePlans) (group : List Nat)
    (b : Bundle (EquationStore.CheckedLabel f.F.equations f.F.primitive)) : Except String (List String) := do
  let certified ← f.certified group
  let checked := checkRequestsResult (CertifiedPlan.requests certified) b
  if checked.accepted then return f.dependencies group
  throw (requestsRefusal certified b checked)

/-- The single forward pass over a group's members (`SinglePass`). -/
def FilePlans.passStats (f : FilePlans) (group : List Nat) (node : Nat) : List String :=
  group.filterMap fun i =>
    let line : Except String String := do
      let .graph name _ r ← (f.plans[i]?).getD (.error s!"no unit {i}")
      return s!"{name}: {SinglePassStats.stats r.program r.claims r.cuts r.assertions}\n{SinglePassStats.trace r.program r.claims r.cuts node 40}"
    line.toOption

/-- What a graph's statement entries are given beyond their written
assertions and the claims' facts, by label: the implications they hold,
the slots holding a promise goal's input, and the slots holding an input's
entry value a postcondition names. An input of the single pass. -/
structure GivenHeads (ι : Type) where
  implies : Array (List (PromiseCalls.Implication ι)) := #[]
  args : Array (List Nat) := #[]
  inputs : Array (List (Nat × Nat)) := #[]

section
variable {ι : Type} [Labels ι]

/-- The given facts a certificate holds at the statement entries `cuts`. -/
def GivenHeads.ofCertificate (C : ControlFlow.Certificate ι) (cuts : List Nat) (P : ControlFlow.Program)
    (start : Nat) (ensures : List HeapKnowledge.IndexFact) : GivenHeads ι :=
  { implies := (C.zipIdx.map fun (c, l) => if cuts.contains l then c.implies else []).toArray
    args := (C.zipIdx.map fun (c, l) => if cuts.contains l then c.arguments else []).toArray
    inputs := if ensures.isEmpty then #[] else
      ((GraphCode.trackTable P C start (GraphCode.namedInputs ensures)).zipIdx.map fun (t, l) =>
        if cuts.contains l then t.getD [] else []).toArray }

def GivenHeads.toJson (g : GivenHeads ι) : Json :=
  Json.arr ((List.range (max g.implies.size (max g.args.size g.inputs.size))).filterMap fun l =>
    let xs := (g.implies[l]?).getD []
    let as := (g.args[l]?).getD []
    let ins := (g.inputs[l]?).getD []
    if xs.isEmpty && as.isEmpty && ins.isEmpty then none else
    some (Json.mkObj [("label", Lean.toJson l),
      ("implies", Json.arr (xs.map fun x => Json.mkObj [("test", Lean.toJson x.test),
        ("target", Lean.toJson x.target), ("type", Lean.toJson x.type)]).toArray),
      ("arguments", Lean.toJson as), ("inputs", Lean.toJson (ins.map fun (a, b) => [a, b]))])).toArray

def GivenHeads.fromJson (n : Nat) (j : Json) : Except String (GivenHeads ι) := do
  let entries ← j.getArr?
  let mut g : GivenHeads ι := ⟨Array.replicate n [], Array.replicate n [], Array.replicate n []⟩
  for e in entries do
    let l ← e.getObjValAs? Nat "label"
    let xs ← (← e.getObjVal? "implies").getArr?
    let implies ← xs.toList.mapM fun x => do
      pure (⟨← x.getObjValAs? Nat "test", ← x.getObjValAs? Nat "target", ← x.getObjValAs? (Ty ι) "type"⟩ :
        PromiseCalls.Implication ι)
    let args ← e.getObjValAs? (List Nat) "arguments"
    let inputs ← e.getObjValAs? (List (List Nat)) "inputs"
    if l < n then
      g := ⟨g.implies.set! l implies, g.args.set! l args,
        g.inputs.set! l (inputs.filterMap fun p => match p with | [a, b] => some (a, b) | _ => none)⟩
  return g

end

/-- A regional check's given facts (`SinglePass.Regional`), read from the
existing search's certificate: its tables (`SourceExtraction.regionTable`,
`freshTables`) at the statement entries `cuts`, and the field names. -/
def regionalGiven {σ ι : Type} [Labels ι] [StoreView σ ι] (r : SourceExtraction.SourceRequest σ ι)
    (resp : RequestJson.Response ι) (Φ : Footprints.Closed) (regions : List Footprints.ArgumentStoreRegion) : Json :=
  let P := GraphCode.program (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))
  let table := SourceExtraction.regionTable P resp.certificate r.start regions
  let ft := SourceExtraction.freshTables (RequestJson.graph r.toRequest) (StoreView.images r.types) resp.readSummaries Φ P
    resp.certificate r.start
  Json.mkObj [("names", Lean.toJson ft.names), ("heads", Json.arr (r.cuts.map fun l => Json.mkObj [
    ("label", Lean.toJson l),
    ("facts", Lean.toJson ((GraphCode.ArgumentPathTracking.atLabel table l).map fun f => (f.slot, f.region.position, f.region.path))),
    ("values", Lean.toJson (GraphCode.factsAt ft.values l)), ("cells", Lean.toJson (GraphCode.factsAt ft.cells l)),
    ("fields", Lean.toJson (GraphCode.ArgumentRegionGraph.fieldsAt ft.fields l))]).toArray)]

/-- A regional check's given facts read back (`regionalGiven`). -/
def regionalFromJson (n : Nat) (j : Json) : Except String (List String × Array (Option SinglePass.RegionState)) := do
  let names ← j.getObjValAs? (List String) "names"
  let mut heads : Array (Option SinglePass.RegionState) := Array.replicate n none
  for e in (← (← j.getObjVal? "heads").getArr?) do
    let l ← e.getObjValAs? Nat "label"
    let facts ← e.getObjValAs? (List (Nat × Nat × List String)) "facts"
    let st : SinglePass.RegionState := ⟨facts.map fun (sl, pos, path) => ⟨sl, ⟨pos, path⟩⟩,
      ← e.getObjValAs? (List Nat) "values", ← e.getObjValAs? (List Nat) "cells",
      ← e.getObjValAs? (List (Nat × String)) "fields"⟩
    if l < n then heads := heads.set! l (some st)
  return (names, heads)

/-- A graph's loop-head facts the claims state (its candidates at its loop
heads, `SinglePass.loopHeads`, and its start), each at its label with its
statement's start: a given file's `headFacts`. -/
def headFacts (P : ControlFlow.Program) (start : Nat) (sourceMap : SourceMap)
    (candidates : List (Nat × List HeapKnowledge.IndexAtom)) (others : Bool := false) : Json :=
  let heads := (SinglePass.loopHeads P.toArray start).1
  Json.arr ((candidates.filter fun (l, _) => (l == start || heads.getD l false) != others).map fun (l, atoms) => Json.mkObj [("label", Lean.toJson l),
    ("start", Lean.toJson (((sourceMap[l]?).bind id).map (·.pos.1))),
    ("width", Lean.toJson (((sourceMap[l]?).bind id).map (·.context.length))), ("atoms", Lean.toJson atoms)]).toArray

/-- A given file's loop-head facts read back (`headFacts`), each at the
statement entries of `cuts` that start where the given one does and hold as
many slots (a `for`'s head and its declarations' entry share a start): a
graph lowered over other types numbers its nodes otherwise. -/
def headFactsFromJson (sourceMap : SourceMap) (cuts : List Nat) (j : Json) : List (Nat × List HeapKnowledge.IndexAtom) :=
  let startOf := fun (l : Nat) => ((sourceMap[l]?).bind id).map (·.pos.1)
  ((j.getArr?).toOption.getD #[]).toList.flatMap fun e => match do
      let start ← (e.getObjValAs? (Option Nat) "start").toOption
      let width ← (e.getObjValAs? (Option Nat) "width").toOption
      let atoms ← (e.getObjValAs? (List HeapKnowledge.IndexAtom) "atoms").toOption
      pure (start, width, atoms) with
    | some (start, width, atoms) =>
      (cuts.filter fun l => startOf l == start && (((sourceMap[l]?).bind id).map (·.context.length)) == width).map (·, atoms)
    | none => []

/-- Each selected unit's given statement-entry facts, read from the existing
search's certificate (`GivenHeads.ofCertificate`), its own and each code
request's, as a line (`dev/single-pass-given.mts` writes the file). With
`facts`, also the loop-head facts the claims state (`headFacts`), its own and
each code request's: the claims-free pass's given invariants. -/
def FilePlans.givenLines (f : FilePlans) (fuel : Nat) (group : List Nat) (facts : Bool := false)
    (entries : Bool := false) : List Json :=
  group.filterMap fun i => do
    let .ok (.graph name _ r) := (f.plans[i]?).getD (.error "") | none
    let .ok b := f.searchGroup fuel [i] true | none
    let resp ← b.functions.head?
    let main := GivenHeads.ofCertificate resp.certificate r.cuts r.program r.start r.ensures
    let codes := (r.codes.zipIdx.map fun (q, ci) =>
      let hints := (r.codeHints[ci]?).getD {}
      let rq := q.asRequest r.toRequest
      (GivenHeads.ofCertificate ((resp.codes[ci]?).getD []) hints.cuts rq.program rq.start [] :
        GivenHeads _).toJson).toArray
    -- The regional checks' given facts: the unit's store regions, and its
    -- footprint's regional fallback (`effectResult`).
    let regional := match r.regional with
      | some (Φ, regions) => [("regional", regionalGiven r resp Φ regions)]
      | none => []
    let fallback := if !r.fresh && r.footprint != .top then [("footprintRegional", regionalGiven r resp r.footprint [])] else []
    let heads := if !facts then [] else
      [("headFacts", headFacts r.program r.start r.sourceMap r.candidates),
       ("headFactsOfCodes", Json.arr ((r.codes.zip r.codeHints).map fun (q, h) =>
        let rq := q.asRequest r.toRequest
        headFacts rq.program rq.start h.sourceMap h.candidates).toArray)] ++
      -- With `entries`, the claims' facts at the other statement entries:
      -- the search's cuts, which the referee (mode 9) reads.
      (if !entries then [] else
        [("entryFacts", headFacts r.program r.start r.sourceMap r.candidates true),
         ("entryFactsOfCodes", Json.arr ((r.codes.zip r.codeHints).map fun (q, h) =>
          let rq := q.asRequest r.toRequest
          headFacts rq.program rq.start h.sourceMap h.candidates true).toArray)])
    pure (Json.mkObj ([("unit", Lean.toJson (f.fr.unitId i)), ("name", Lean.toJson name),
      ("graph", main.toJson), ("codes", Json.arr codes)] ++ regional ++ fallback ++ heads))

/-- A member's counts, and where asked (`counting`) also as a JSON line. -/
def countsLine (counting : Bool) (name : String) (c : SinglePass.Counts) : String :=
  if counting then s!"{c}\ncounts: {name} {c.json}" else toString c

/-- The single forward pass over each member of a group (`SinglePass.run`),
no certificate built: per member its outcome and counts; the group's
verdict, the first member's refusal or construct not handled. -/
def FilePlans.passGroup (f : FilePlans) (fuel : Nat) (group : List Nat) (compare : Bool := false) (debugNode : Nat := 1000000000) (repeats : Nat := 1) (given : Option (Std.HashMap String Json) := none)
    (observe : Option String := none) (counting : Bool := false) :
    List String × Except String (List String) := Id.run do
  let G : NormalGraph (EquationStore.CheckedLabel f.F.equations f.F.primitive) := StoreView.graph f.F.store
  let I : PositiveCertificates.InstanceImageCheck G := StoreView.images f.F.store
  let mut answers : CertificateProducer.Answered G := {}
  let mut lines : List String := []
  let mut failed : Option String := none
  for i in group do
    let outcome : Except String (String × String × SinglePass.Outcome _) := do
      let .graph name _ r ← (f.plans[i]?).getD (.error s!"no unit {i}")
      -- The request's own checks over its whole certificate the pass does
      -- not make: the graph is passed, and its verdict is not handled.
      -- A footprint (`effectResult`): its request-level conditions here, its
      -- graph's bound at each node in the pass (`GraphCode.compositionalChecked`),
      -- a pure program's shortcut first.
      let bounded := !(r.footprint == .top && !r.onThrow && !r.fresh) &&
        !(!r.fresh && r.program.all fun n => Purity.pureTerm n.expression)
      if !(RequestJson.asyncEffects r.async r.footprint && (!r.async || !r.fresh) &&
          RequestJson.statedWithin r.async r.footprint r.onThrow r.fresh r.stated) then
        return (name, "", .refused "the declared effect")
      if bounded && !(r.footprint != .top || r.fresh) then return (name, "", .refused "the declared effect")
      let bound := if bounded then some (r.footprint, r.fresh, r.onThrow) else none
      -- A postcondition (`ensuresResult`): checked at each return in the pass.
      if !r.ensures.isEmpty && r.qualification.isSome then return (name, "", .refused "a postcondition")
      let unchecked : List String := []
      let labels := SinglePass.timedKind "outside: search labels" fun _ => r.searchLabels
      let (e, next) ← SinglePass.timedKind "outside: expression claims searched" fun _ =>
        ExpressionClaims.produceUsing G I labels (StoreView.valid r.types)
        (StoreView.projection r.types) fuel r.obligations { answers with summaries := #[], summaryAnswers := {} }
      let (rendered, next) := SinglePass.timedKind "outside: node plans rendered" fun _ =>
        ExpressionClaims.renderKnownUsing G I labels (StoreView.valid r.types) r.nodePlans next
      let pool := SinglePass.timedKind "outside: vocabulary" fun _ => CertificateProducer.vocabulary G labels r.claims r.inputs
      let reference : Array HeapKnowledge.Knowledge := if !compare then #[] else
        match f.searchGroup fuel [i] true with
        | .ok b => match b.functions.head? with
          | some resp => (resp.certificate.map (·.knowledge)).toArray
          | none => #[]
        | .error _ => #[]
      -- Supplied, where asked: the implications the existing search's
      -- certificate holds at the unit's statement entries, as their given
      -- invariants' (`supply`); the pass computes none.
      -- The statement entries' given facts beyond the written ones and the
      -- claims': read from the given file's line of this unit, where given.
      let line := given.bind fun m => m.get? (f.fr.unitId i)
      let main : GivenHeads _ := match line with
        | some l => match (l.getObjVal? "graph").bind (GivenHeads.fromJson r.program.length) with
          | Except.ok g => g
          | Except.error _ => {}
        | none => {}
      let givenImplies := main.implies
      let givenArgs := main.args
      let givenInputs := main.inputs
      -- A qualified body (`SourceRequest.checker`): the walk over the
      -- request's own graph and image check, at its checker and aliases;
      -- the request-level conditions a qualified body meets
      -- (`effectResult`, `regionalResult`, `ensuresResult`).
      if let some q := r.qualification then
        if !(r.footprint == .top && !r.onThrow && !r.fresh) then return (name, "", .refused "the declared effect")
        if r.regional.isSome then return (name, "", .refused "store regions of a qualified body")
        if !r.codes.isEmpty then return (name, "", .notHandled "codes of a qualified body")
        let G' := RequestJson.graph r.toRequest
        let I' := StoreView.images r.types
        let pool' := CertificateProducer.vocabulary G' labels r.claims r.inputs
        let (o, counts, after, _) := CertificateProducer.timed SinglePass.passNanos fun _ =>
          SinglePass.run G' I' pool' fuel r.program r.claims r.start r.goal r.assertions r.cuts r.candidates
            r.entryIndices [] (e ++ rendered) (GraphCode.admits []) r.aliases q.checker
            { summaries := next.summaries, summaryAnswers := next.summaryAnswers } #[] debugNode none
            givenImplies givenArgs r.ensures givenInputs r.entrySeparation none false false true
        let sums := after.summaries.toList
        let sumsOk := sums.all (RequestJson.validSummary (StoreView.valid r.types)) &&
          (ProgramCertificates.checkReadSummariesResult G' I' sums).accepted
        let obligations := ExpressionClaims.checkAllResult G' I' (StoreView.valid r.types) r.obligations e
          (GraphCode.admits []) sums
        let o : SinglePass.Outcome _ := match o with
          | .accepted => if !sumsOk then .refused "a read summary"
            else if !obligations.accepted then .refused "an expression claim" else .accepted
          | .refused w => .refused w
          | .notHandled w => .notHandled w
          | .observed _ => .notHandled "observing a qualified body"
        return (name, countsLine counting name counts, o)
      -- Each code request, in order, passed over its own graph with the codes
      -- admitted before it (`produceResponseUsing`'s loop, `codeCheckedResult`):
      -- its signature's conditions, its graph against its goal and frame, its
      -- effect's bound; then the unit's graph over the admitted table.
      let mut table : List (CodeEntry _) := []
      let mut codeOutcome : Option (SinglePass.Outcome _) := none
      -- The read summaries the searches add, kept from run to run: the
      -- unit's are checked once (`checkReadSummariesResult`).
      let mut sumsAnswers := next
      for (q, ci) in r.codes.zipIdx do
        let hints := (r.codeHints[ci]?).getD {}
        let rq := q.asRequest r.toRequest
        let eff := q.entry.row.effect
        let conditions := decide (q.entry.arity ≤ q.entry.row.arguments.length) && eff.below q.entry.arity &&
          !eff.freshObject && eff.requires.isNone && eff.elements.isNone && !eff.receiverGrows && eff.elementWrite.isNone
        if !conditions then
          codeOutcome := codeOutcome.orElse fun _ => some (.refused s!"code {ci}: its signature")
          break
        let codeBound := if eff.footprint == .top && !eff.fresh && !eff.onThrow then none
          else if !eff.fresh && q.entry.exprs.all Purity.pureTerm then none
          else some (eff.footprint, eff.fresh, eff.onThrow)
        let codePool := CertificateProducer.vocabulary G labels rq.claims rq.inputs
        let codeGiven : GivenHeads _ := match line with
          | some l => match (l.getObjVal? "codes").bind fun cs => do
              let arr ← cs.getArr?
              GivenHeads.fromJson rq.program.length ((arr[ci]?).getD (Json.arr #[])) with
            | Except.ok g => g
            | Except.error _ => {}
          | none => {}
        let codeImplies := codeGiven.implies
        let codeArgs := codeGiven.args
        let (o, _, a, _) := SinglePass.run G I codePool fuel rq.program rq.claims rq.start q.entry.goal hints.requirements
          hints.cuts hints.candidates rq.entryIndices [] (e ++ rendered) (GraphCode.admits table) r.aliases
          (HeapExpressionRules.Checker.ordinary G I) sumsAnswers #[] 1000000000 codeBound codeImplies codeArgs
        sumsAnswers := a
        -- A refusal observed in a code request: its obligation, the facts
        -- over its names and those it lacks, as for the unit's own graph.
        if let .refused w := o then
          if observe == some "refusal" then
            let (_, _, _, trace) := SinglePass.run G I codePool fuel rq.program rq.claims rq.start q.entry.goal hints.requirements
              hints.cuts hints.candidates rq.entryIndices [] (e ++ rendered) (GraphCode.admits table) r.aliases
              (HeapExpressionRules.Checker.ordinary G I) sumsAnswers #[] 1000000000 codeBound codeImplies codeArgs [] #[] {}
              (some 1000000000) true
            let l := trace.node
            let mentioned := ((rq.claims[l]?).map RequestJson.PointClaim.mentions).getD []
            let p := StoreView.projection r.types mentioned.eraseDups
            let width := trace.names.length
            let slotOf := fun (x : Nat) => trace.names.idxOf? x
            let shown := fun (as : List SinglePass.Atom) =>
              toJson (SinglePass.ofAtoms (as.filterMap fun a => a.rename slotOf) width)
            let here := (trace.afters[l]?).join.orElse fun _ => (trace.entries[l]?).join
            let focus := (here.map fun st => st.store.connected trace.focus).getD []
            let facts := (here.map fun st => st.store.toList.filter fun a => a.names.any focus.contains).getD []
            let place := fun l => [("label", toJson l), ("sourceMap", toJson ((hints.sourceMap[l]?).bind id))]
            let missingJson := trace.missing.map fun a => Json.mkObj [("fact", shown [a]),
              ("where", Json.arr ((trace.locate l a 3 false).map fun (q, why) => Json.mkObj (place q ++ [("why", toJson why)])).toArray)]
            let record := Json.mkObj ([("refusal", toJson s!"code {ci}: {w}"), ("observed", Json.mkObj (place l)),
              ("node", toJson rq.program[l]?),
              ("claim", toJson ((rq.claims[l]?).map (RequestJson.PointClaim.shown p))),
              ("facts", shown facts), ("missing", Json.arr missingJson.toArray)] ++ p.fields)
            return (name, "refusal-observation: " ++ record.compress, .refused s!"code {ci}: {w}")
        match o with
        | .accepted => table := table ++ [q.entry]
        | .refused w => codeOutcome := codeOutcome.orElse fun _ => some (.refused s!"code {ci}: {w}"); break
        | .notHandled w => codeOutcome := codeOutcome.orElse fun _ => some (.notHandled s!"{w} (in code {ci})"); break
        | .observed _ => break
      if let some o := codeOutcome then return (name, "", o)
      let codes := GraphCode.admits table
      -- Observing (`observe`): the node of that label (`node:L`), or the
      -- innermost node whose source span holds that offset (`offset:K`).
      let observed : Option Nat := observe.bind fun w =>
        if w == "refusal" then some 1000000000 else
        if w.startsWith "node:" then (w.drop 5).toString.toNat? else
        if w.startsWith "offset:" then (w.drop 7).toString.toNat?.bind fun k =>
          let holding := r.sourceMap.zipIdx.filterMap fun (e, l) => e.bind fun e =>
            if e.pos.1 ≤ k && k < e.pos.2 then some (e.pos.2 - e.pos.1, l) else none
          (holding.foldl (fun (b : Option (Nat × Nat)) x => match b with
            | some y => if x.1 < y.1 then some x else some y
            | none => some x) none).map (·.2)
        else none
      if observe.isSome && observed.isNone then return (name, "", .notHandled "no node to observe")
      -- Profiling: the pass run `repeats` times, the last run's result kept.
      for k in List.range (repeats - 1) do
        let (o, _, _, _) := SinglePass.run G I pool fuel r.program r.claims r.start r.goal r.assertions r.cuts r.candidates
          r.entryIndices [] (e ++ rendered) codes r.aliases (HeapExpressionRules.Checker.ordinary G I) sumsAnswers #[] (debugNode + k)
        if let .notHandled w := o then throw w
      let tracing := observe == some "refusal"
      -- The regional checks (`regionalChecked`), made in the walk: the
      -- unit's store regions, and its footprint's regional fallback
      -- (`effectResult`); each loop head's given regional facts read from
      -- the given line. Their entry conditions (`checkEntryFields`, the
      -- regions' own conditions) are checked here.
      let regionalOf := fun (key : String) (Φ : Footprints.Closed) (regions : List Footprints.ArgumentStoreRegion) (exc : Bool) =>
        let (names, heads) := match line.bind fun l => (l.getObjVal? key).toOption with
          | some j => (regionalFromJson r.program.length j).toOption.getD ([], #[])
          | none => ([], #[])
        ({ Φ, regions, exc, names, heads } : SinglePass.Regional)
      let regional := r.regional.map fun (Φ, regions) => regionalOf "regional" Φ regions (r.stated.any (·.onThrow))
      if let some (_, regions) := r.regional then
        if r.async || r.fresh || !GraphCode.ArgumentPathTracking.checkEntryFields (RequestJson.graph r.toRequest) r.inputs regions then
          return (name, "", .refused "store regions")
      let walk := fun (bound : Option (Footprints.Closed × Bool × Bool)) (regional : Option SinglePass.Regional) =>
        SinglePass.run G I pool fuel r.program r.claims r.start r.goal r.assertions r.cuts r.candidates
          r.entryIndices [] (e ++ rendered) codes r.aliases (HeapExpressionRules.Checker.ordinary G I) sumsAnswers reference debugNode bound
          givenImplies givenArgs r.ensures givenInputs r.entrySeparation observed tracing false false regional
      let (o, counts, after, trace) := CertificateProducer.timed SinglePass.passNanos fun _ => walk bound regional
      -- A footprint the walk refuses node by node, checked regionally with no
      -- regions where the result is not fresh; then the unit's own regions.
      let (o, counts, after, trace) := match o with
        | .refused w => if w.startsWith "footprint at node" && !r.fresh then
            let fallback := regionalOf "footprintRegional" r.footprint [] r.onThrow
            match walk none (some fallback) with
            | (.accepted, c, a, t) => match regional with
              | some rg => walk none (some rg)
              | none => (.accepted, c, a, t)
            | (.refused w', c, a, t) => (.refused s!"footprint by store regions: {w'} (after {w})", c, a, t)
            | x => x
          else (o, counts, after, trace)
        | _ => (o, counts, after, trace)
      -- The unit's own expression claims, as the check reads them.
      let obligations := SinglePass.timedKind "outside: expression claims checked" fun _ => ExpressionClaims.checkAllResult (RequestJson.graph r.toRequest) (StoreView.images r.types)
        (StoreView.valid r.types) r.obligations e codes after.summaries.toList
      -- A graph the bound refuses may still be within it by its store
      -- regions (`regionalChecked`), which the pass does not decide.
      -- The read summaries every step's check read, checked as a
      -- response's are (`validSummary`, `checkReadSummariesResult`).
      let sums := after.summaries.toList
      let sumsOk := sums.all (RequestJson.validSummary (StoreView.valid r.types)) &&
        (ProgramCertificates.checkReadSummariesResult (RequestJson.graph r.toRequest) (StoreView.images r.types) sums).accepted
      let o : SinglePass.Outcome _ := match o with
        | .accepted => if !sumsOk then .refused "a read summary" else if !obligations.accepted then .refused "an expression claim"
          else match unchecked with
            | [] => .accepted
            | w :: _ => .notHandled s!"{w} (the graph passed)"
        | o => o
      -- A node observed whose step is refused, or that is not reached past
      -- the refusal: the walk again, stopping on its entry.
      let o : SinglePass.Outcome _ := match o, observed with
        | .refused _, some _ => if tracing then o else
          (SinglePass.run G I pool fuel r.program r.claims r.start r.goal r.assertions r.cuts r.candidates
            r.entryIndices [] (e ++ rendered) codes r.aliases (HeapExpressionRules.Checker.ordinary G I) sumsAnswers #[] debugNode bound
            givenImplies givenArgs r.ensures givenInputs r.entrySeparation observed false true).1
        | o, _ => o
      -- A refusal observed: its obligation's facts, the facts it lacks, and
      -- each fact over its names an earlier state held, where last present
      -- and what removed it (`Trace.locate`, `Trace.lost`).
      if let .refused w := o then
        if tracing then
          let l := trace.node
          let mentioned := ((r.claims[l]?).map RequestJson.PointClaim.mentions).getD []
          let p := StoreView.projection r.types mentioned.eraseDups
          let width := trace.names.length
          let slotOf := fun (x : Nat) => trace.names.idxOf? x
          let shown := fun (as : List SinglePass.Atom) =>
            toJson (SinglePass.ofAtoms (as.filterMap fun a => a.rename slotOf) width)
          let here := (trace.afters[l]?).join.orElse fun _ => (trace.entries[l]?).join
          let focus := (here.map fun st => st.store.connected trace.focus).getD []
          let facts := (here.map fun st => st.store.toList.filter fun a => a.names.any focus.contains).getD []
          let place := fun l => [("label", toJson l), ("sourceMap", toJson ((r.sourceMap[l]?).bind id))]
          let lostJson := (trace.lost.map fun (a, ws) => Json.mkObj [("fact", shown [a]),
            ("where", Json.arr (ws.map fun (q, why) => Json.mkObj (place q ++ [("why", toJson why)])).toArray)])
          let missingJson := trace.missing.map fun a => Json.mkObj [("fact", shown [a]),
            ("where", Json.arr ((trace.locate l a 3 false).map fun (q, why) => Json.mkObj (place q ++ [("why", toJson why)])).toArray)]
          let record := Json.mkObj ([("refusal", toJson w), ("observed", Json.mkObj (place l)),
            ("edge", toJson (trace.edge.map fun t => Json.mkObj (place t))),
            ("node", toJson r.program[l]?),
            ("claim", toJson ((r.claims[l]?).map (RequestJson.PointClaim.shown p))),
            ("facts", shown facts), ("missing", Json.arr missingJson.toArray), ("lost", Json.arr lostJson.toArray)] ++ p.fields)
          return (name, "refusal-observation: " ++ record.compress, o)
      if let .observed ob := o then
        let claimAt := fun l => (r.claims[l]? : Option (CertificateProducer.PointClaim _))
        let mentioned := ((claimAt ob.label).map RequestJson.PointClaim.mentions).getD [] ++
          ob.implies.flatMap (·.type)
        let p := StoreView.projection r.types mentioned.eraseDups
        let place := fun l => [("label", toJson l), ("sourceMap", toJson ((r.sourceMap[l]?).bind id))]
        let record := Json.mkObj ([("observed", Json.mkObj (place ob.label)),
          ("node", toJson r.program[ob.label]?),
          ("claim", toJson ((claimAt ob.label).map (RequestJson.PointClaim.shown p))),
          ("before", toJson ob.before), ("after", toJson ob.after), ("slotNames", toJson ob.names),
          ("implies", Json.arr (ob.implies.map fun x => Json.mkObj [("test", toJson x.test),
            ("target", toJson x.target), ("type", toJson (p.shown x.type))]).toArray),
          ("preds", Json.arr (ob.preds.map fun (pl, k) => Json.mkObj (place pl ++ [("knowledge", toJson k)])).toArray)] ++ p.fields)
        return (name, "observation: " ++ record.compress, .notHandled "observed")
      return (name, countsLine counting name counts, o)
    match outcome with
    | .ok (name, counts, o) =>
      lines := lines ++ [s!"{name}: {o}; {counts}"]
      match o with
      | .accepted => pure ()
      | .observed _ => pure ()
      | .refused w | .notHandled w => if failed.isNone then failed := some s!"single pass: {o} ({w.length})"
    | .error reason =>
      lines := lines ++ [s!"refused before the pass: {reason.take 200}"]
      if failed.isNone then failed := some reason
  return (lines, match failed with
    | some reason => .error reason
    | none => .ok (f.dependencies group))

/-- `searchGroup`, then `checkGroup`. -/
def FilePlans.verifyGroup (f : FilePlans) (fuel : Nat) (group : List Nat) (unchecked : Bool) :
    Except String (List String) := do
  f.checkGroup group (← f.searchGroup fuel group unchecked)

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
