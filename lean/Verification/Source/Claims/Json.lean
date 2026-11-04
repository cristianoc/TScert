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
  if !RequestJson.statedWithin r.async r.footprint r.onThrow r.stated then
    some s!"source effect refusal at [{namePos.1},{namePos.2}): the footprint claimed for '{name}' is not within the effect its result annotation states" else
  let asyncCode := (r.toRequest.codes.zipIdx.find? fun (q, _) =>
    !RequestJson.asyncEffects q.async q.entry.row.effect.footprint).map fun (_, i) =>
      refuseAsync s!"a closure in '{name}'"
        ((((r.codeSources[i]?).bind fun code => sourceMapRegion code.sourceMap).map (·.pos)).getD namePos)
  if asyncCode.isSome then asyncCode else
  let unit := effectResult r c
  if !unit.accepted then
    if unit.exhaustion.isSome then none else
    some (refuse s!"'{name}'" (((firstBad r.footprint false r.onThrow r.start r.program c.certificate r.sourceMap).map (·.pos)).getD namePos))
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
      let knowledge := match observed with
        | none => HeapKnowledge.withTypedLinks G Γ facts
        | some o => HeapKnowledge.observeTyped G Γ facts 0 o
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
      | .graph name namePos r => footprintRefusal name namePos r c) <|>
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
    (qualified : List (String × Footprints.Closed × Bool) := []) : Except String Unit := do
  let (T, plans) ← extractPlans ast claims fileKey budget qualified
  checkPlans T plans evidence

/-- Search and check supplied frozen plans. This returns evidence only; the
ordinary acceptance path independently extracts and certifies its source. -/
def produceFrozenPlans (F : EquationStore.Frozen)
    (frozen : List (FunctionPlan (EquationStore.Checked F.equations F.primitive)
      (EquationStore.CheckedLabel F.equations F.primitive))) (fuel : Nat) : Except String Json := do
  let rs := FunctionPlan.requests frozen
  -- One graph and one image check for the document's search: every request
  -- holds the frozen store (`SourceRequest.over`), whose graph is the
  -- equations' (`Checked.graph_eq`) and whose image check reads only the
  -- equations, its variances and its budget (`Checked.images_eq`).
  let G : NormalGraph (EquationStore.CheckedLabel F.equations F.primitive) := StoreView.graph F.store
  let I : PositiveCertificates.InstanceImageCheck G := StoreView.images F.store
  -- The answered requests of the document's graph and image check, threaded
  -- through every search in them; a qualified body's search, in its own
  -- image check, starts its own.
  let mut answers : CertificateProducer.Answered G := {}
  let mut proofLists := #[]
  -- Each request's read summaries, a table of its own scope: its
  -- obligations', then its nodes' and codes'.
  let mut scopes := #[]
  -- Each request's search vocabulary, read by its three searches.
  let vocabularies := rs.map (·.searchLabels)
  for (r, labels) in rs.zip vocabularies do
    let (e, next) ← ExpressionClaims.produceUsing G I labels (StoreView.valid r.types)
      (StoreView.projection r.types) fuel r.obligations { answers with summaries := #[], summaryAnswers := {} }
    answers := next
    proofLists := proofLists.push e
    scopes := scopes.push (next.summaries, next.summaryAnswers)
  let mut responses := #[]
  for (((r, labels), proofs), (summaries, summaryAnswers)) in
      ((rs.zip vocabularies).zip proofLists.toList).zip scopes.toList do
    let (rendered, next) := ExpressionClaims.renderKnownUsing G I labels (StoreView.valid r.types)
      r.nodePlans { answers with summaries, summaryAnswers }
    answers := next
    let known := proofs ++ rendered
    -- A qualified body's checker is stated over the request's own image
    -- check: its search keeps that check, and the request's summaries.
    if r.qualification.isNone then
      let (c, next) ← RequestJson.produceResponseUsing G I (HeapExpressionRules.Checker.ordinary G I) r.toRequest
        fuel [] known r.sourceMap (some labels) r.assertions r.cuts r.codeHints r.checker r.aliases answers
        (searched := true) (recheck := some (HeapExpressionRules.Checker.ordinary G))
      answers := next
      responses := responses.push c
    else
      let (c, _) ← RequestJson.produceResponseUsing (RequestJson.graph r.toRequest) (StoreView.images r.types)
        r.checker r.toRequest fuel [] known r.sourceMap (some labels) r.assertions r.cuts
        r.codeHints r.checker r.aliases { summaries := next.summaries, summaryAnswers := next.summaryAnswers }
        (searched := true)
      responses := responses.push c
  let es := proofLists.toList
  let cs := responses.toList
  for (plan, c) in frozen.zip cs do
    let .graph name namePos r := plan
    if let some refusal := footprintRefusal name namePos r c then throw refusal
  let evidence := EvidenceWire.encode (Bundle.mk cs es)
  let b : Bundle (EquationStore.CheckedLabel F.equations F.primitive) ← EvidenceWire.decode evidence
  let checked := checkRequestsResult rs b
  if !checked.accepted then
    throw (validationFailure rs checked "source evidence does not justify the extracted graph requests")
  return evidence

def produceDocument (ast claims : Json) (fileKey : String) (fuel : Nat)
    (budget : PositiveCertificates.SearchBudget := {})
    (qualified : List (String × Footprints.Closed × Bool) := []) : Except String Json := do
  let (T, plans) ← extractPlans ast claims fileKey budget qualified
  let ⟨F, frozen⟩ ← freezePlans T plans
  produceFrozenPlans F frozen fuel

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

/-- The evidence of a document with certified imports: the importer's, and
each module run's, by the module's identity. -/
def evidenceParts (evidence : Json) (p : ImportPlan) : Except String (List Json) := do
  fieldsExactly evidence ["main", "modules"]
  let modules ← jArr evidence "modules"
  if modules.length != p.modules.length then throw "evidence for another set of module runs"
  (p.modules.zip modules).mapM fun (m, e) => do
    fieldsExactly e ["location", "evidence"]
    if (← jStr (← jField e "location")) != m.location then throw "evidence for another module run"
    jField e "evidence"

/-- What requests a bundle justifies give: the check accepts them, and each
is safe, and within its footprint where it claims one, as
`checkRequests_safe_at` and `checkRequests_footprint_at` state. -/
def RequestsSafe (F : EquationStore.Frozen)
    (rs : List (SourceRequest (EquationStore.Checked F.equations F.primitive)
      (EquationStore.CheckedLabel F.equations F.primitive)))
    (b : Bundle (EquationStore.CheckedLabel F.equations F.primitive)) : Prop :=
      checkRequests rs b = true ∧
      (∀ r c, (r,c) ∈ rs.zip b.functions →
        ∀ η, r.Admits η → ∀ n W heap ρ, EnvOk (reassign F.equations.graph η) r.inputs ρ n W →
          WorldAdm W → HeapOk n W heap →
          SafeGraph (excOf (reassign F.equations.graph η)) r.program
            (ControlFlow.GoalHolds (reassign F.equations.graph η) r.goal (r.goal.argument ρ))
            n W heap (.at r.start ρ)) ∧
      (∀ r c, (r,c) ∈ rs.zip b.functions →
        r.footprint ≠ .top ∨ r.onThrow = true →
        ∀ η n W heap (L : List Tm) (d : Tm),
          EnvOk (reassign F.equations.graph η) r.inputs (envOf L d) n W →
          WorldAdm W → HeapOk n W heap → (∀ v ∈ L, isVal v = true) → isVal d = true →
          HeapObservations.SafePostExc (excOf (reassign F.equations.graph η))
            (ControlFlow.GoalHolds (reassign F.equations.graph η) r.goal (r.goal.argument (envOf L d)))
            (fun h' _ => r.footprint.Holds heap h') (fun h' => r.onThrow = true → r.footprint.Holds heap h')
            n W heap
            (.goto (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))
              r.start L d))

theorem requestsSafe_of_check {F : EquationStore.Frozen}
    {rs : List (SourceRequest (EquationStore.Checked F.equations F.primitive)
      (EquationStore.CheckedLabel F.equations F.primitive))}
    {b : Bundle (EquationStore.CheckedLabel F.equations F.primitive)}
    (hx : (checkRequestsResult rs b).accepted = true) : RequestsSafe F rs b := by
  have hc : checkRequests rs b = true := hx
  refine ⟨hc, ?_, ?_⟩
  · intro r c hm η admitted n W heap ρ he hw hh
    exact checkRequests_safe_at hc hm η admitted n W heap ρ he hw hh
  · intro r c hm heffect η n W heap L d he hw hh hvalues hd
    exact checkRequests_footprint_at hc hm heffect η n W heap L d he hw hh hvalues hd

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
    (budget : PositiveCertificates.SearchBudget) (qualified : List (String × Footprints.Closed × Bool)) : Prop :=
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
    {budget : PositiveCertificates.SearchBudget} {qualified : List (String × Footprints.Closed × Bool)}
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

/-- A bundle's entries of the given units. -/
def bundleOf {ι : Type} (b : Bundle ι) (group : List Nat) : Bundle ι :=
  ⟨group.filterMap (b.functions[·]?), group.filterMap (b.obligations[·]?)⟩

/-- A group's dependencies on the wire: the groups its members reach and, where
its code names a qualified read, the module runs. -/
def FilePlans.dependencies (f : FilePlans) (group : List Nat) : List String :=
  (f.fr.dependencies group).map f.fr.unitId ++
    (if f.fr.readsQualified group then f.p.modules.map ("module:" ++ ·.location) else [])

/-- A file's plans and its decoded evidence: the importer's bundle, one
response per unit in the front's order, and each module run's evidence. -/
structure FileEvidence extends FilePlans where
  /-- The importer's bundle, one response per unit in the front's order, or why the evidence is none. -/
  b : Except String (Bundle (EquationStore.CheckedLabel F.equations F.primitive))
  /-- Each module run with its evidence, or why the evidence has none. -/
  modules : Except String (List (ModuleRun × Json))

/-- A file's plans and its evidence, decoded. A unit whose extraction
failed is refused for that, whatever the evidence. -/
def fileEvidence (ast claims : Json) (fileKey : String) (evidence : Json)
    (budget : PositiveCertificates.SearchBudget) : Except String FileEvidence := do
  let f ← filePlans ast claims fileKey budget
  let b : Except String (Bundle (EquationStore.CheckedLabel f.F.equations f.F.primitive)) := do
    let b : Bundle (EquationStore.CheckedLabel f.F.equations f.F.primitive) ←
      EvidenceWire.decode (evidence.getObjValD "main")
    if b.functions.length != f.fr.units.length || b.obligations.length != f.fr.units.length then
      throw "evidence for another set of units"
    return b
  return { f with b, modules := (evidenceParts evidence f.p).map (f.p.modules.zip ·) }

/-- **The verdict of a unit.** A module run is checked as its document; a
group's plans, certified, are checked at their entries of the file's
evidence. Accepted, its dependencies. -/
def unitVerdict (e : FileEvidence) (budget : PositiveCertificates.SearchBudget) (unit : String) :
    Except String (List String) :=
  match e.p.modules.filter (fun m => "module:" ++ m.location == unit) with
  | m :: _ => do
    let parts ← e.modules
    match parts.filter (fun x => x.1.location == m.location) with
    | (m, evidence) :: _ =>
      (checkDocument m.ast m.claims m.location evidence budget m.qualified).mapError (s!"module {m.location}: " ++ ·)
      return []
    | [] => throw s!"no evidence for module run {m.location}"
  | [] => do
    let some i := (List.range e.fr.units.length).find? (e.fr.unitId · == unit) | throw s!"no unit {unit}"
    let group := e.fr.group i
    let certified ← e.certified group
    let b ← e.b
    let checked := checkRequestsResult (CertifiedPlan.requests certified) (bundleOf b group)
    if checked.accepted then return e.dependencies group
    throw (requestsRefusal certified (bundleOf b group) checked)

/-- What a unit's accepted verdict gives: for a module run, its document's
check (`DocumentSafe`); for a group, its plans crossing the exhaustive
certification boundary and every certified request safe, and within its
footprint where it claims one (`RequestsSafe`). -/
def UnitSafe (e : FileEvidence) (budget : PositiveCertificates.SearchBudget) (unit : String) : Prop :=
  (∃ parts m evidence, e.modules = .ok parts ∧ (m, evidence) ∈ parts ∧ "module:" ++ m.location = unit ∧
    DocumentSafe m.ast m.claims m.location evidence budget m.qualified) ∨
  (∃ i certified b, e.fr.unitId i = unit ∧ e.certified (e.fr.group i) = .ok certified ∧ e.b = .ok b ∧
    RequestsSafe e.F (CertifiedPlan.requests certified) (bundleOf b (e.fr.group i)))

theorem unitVerdict_safe {e : FileEvidence} {budget : PositiveCertificates.SearchBudget} {unit : String}
    {deps : List String} (h : unitVerdict e budget unit = .ok deps) : UnitSafe e budget unit := by
  unfold unitVerdict at h
  split at h
  · left
    cases hp : e.modules with
    | error err => simp [hp, Bind.bind, Except.bind] at h
    | ok parts =>
      simp only [hp, Bind.bind, Except.bind] at h
      split at h
      · rename_i m0 tail hm0 _ m' evidence rest hfilter
        have hin : (m', evidence) ∈ parts.filter (fun x => x.1.location == m0.location) := by
          rw [hfilter]; exact List.mem_cons_self
        obtain ⟨hmem, hloc⟩ := List.mem_filter.mp hin
        have hin0 : m0 ∈ e.p.modules.filter (fun m => "module:" ++ m.location == unit) := by
          rw [hm0]; exact List.mem_cons_self
        have hunit : "module:" ++ m0.location = unit := by simpa using (List.mem_filter.mp hin0).2
        have hsame : m'.location = m0.location := by simpa using hloc
        cases hd : checkDocument m'.ast m'.claims m'.location evidence budget m'.qualified with
        | error err => simp [hd, Except.mapError] at h
        | ok u => exact ⟨parts, m', evidence, rfl, hmem, by rw [hsame]; exact hunit, checkDocument_safe hd⟩
      · simp at h
  · right
    cases hi : (List.range e.fr.units.length).find? (e.fr.unitId · == unit) with
    | none => simp [hi] at h
    | some i =>
      simp only [hi] at h
      have hid : e.fr.unitId i = unit := by simpa using List.find?_some hi
      cases hc : e.certified (e.fr.group i) with
      | error err => simp [hc, Bind.bind, Except.bind] at h
      | ok certified =>
        simp only [hc, Bind.bind, Except.bind] at h
        cases hb : e.b with
        | error err => simp [hb] at h
        | ok b =>
          simp only [hb] at h
          by_cases hx : (checkRequestsResult (CertifiedPlan.requests certified) (bundleOf b (e.fr.group i))).accepted = true
          · exact ⟨i, certified, b, hid, hc, rfl, requestsSafe_of_check hx⟩
          · simp [hx] at h

/-- **The check of a file's units.** Each selected unit's verdict over the
file's one front and evidence: a group with a member `names` names (every
group, without a selection), and every module run. -/
def checkUnitsJson (ast claims : Json) (fileKey : String) (evidence : Json)
    (budget : PositiveCertificates.SearchBudget := {}) (names : Option (List String) := none) :
    Except String (List (String × List String × Except String (List String)) × Option String) := do
  let e ← fileEvidence ast claims fileKey evidence budget
  let groups := (e.fr.selected names).map fun i => (e.fr.unitId i, (e.fr.group i).map e.fr.unitId)
  let runs := e.p.modules.map fun m => ("module:" ++ m.location, [])
  let verdicts := (groups ++ runs).map fun (u, members) => (u, members, unitVerdict e budget u)
  -- The file's refusal, in the order the check meets them: a selected unit's
  -- extraction, then the evidence, then the first unit refused.
  let extraction := ((e.fr.selected names).flatMap e.fr.group).findSome? fun i =>
    match (e.plans[i]?).getD (.error "no unit") with
    | Except.error reason => some reason
    | Except.ok _ => none
  let refusal := verdicts.findSome? fun (_, _, v) => match v with
    | .error reason => some reason
    | .ok _ => none
  return (verdicts, if refusal.isNone then none else
    extraction <|> (match e.b with | .error reason => some reason | .ok _ => none) <|> refusal)

/-- **The acceptance theorem.** A unit the CLI check of a file's units
accepts is safe as `UnitSafe` states, over the file's one front and
evidence: its certified requests safe under `EnvOk` of their inputs (the
file's module values at their claimed signatures and effects, its qualified
reads and every imported, ambient and host value among them), and within
their footprints where they claim one. -/
theorem checkUnitJson_safe {ast claims evidence : Json} {fileKey : String}
    {budget : PositiveCertificates.SearchBudget} {names : Option (List String)}
    {verdicts : List (String × List String × Except String (List String))} {first : Option String} {unit : String}
    {members deps : List String}
    (h : checkUnitsJson ast claims fileKey evidence budget names = .ok (verdicts, first))
    (hm : (unit, members, .ok deps) ∈ verdicts) :
    ∃ e, fileEvidence ast claims fileKey evidence budget = .ok e ∧ UnitSafe e budget unit := by
  unfold checkUnitsJson at h
  cases he : fileEvidence ast claims fileKey evidence budget with
  | error err => simp [he, Bind.bind, Except.bind] at h
  | ok e =>
    simp only [he, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hv, _⟩ := h
    subst hv
    obtain ⟨⟨u, ms⟩, _, heq⟩ := List.mem_map.mp hm
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, _, hv⟩ := heq
    exact ⟨e, rfl, unitVerdict_safe hv⟩

/-- Search evidence for a file's units: the selected groups' requests, each
searched on its own, every other unit's entry left empty, and every module
run; the evidence, and each refused unit with its refusal. -/
def produceUnitsJson (ast claims : Json) (fileKey : String) (fuel : Nat)
    (budget : PositiveCertificates.SearchBudget := {}) (names : Option (List String) := none) :
    Except String (Json × List (String × String)) := do
  let f ← filePlans ast claims fileKey budget
  let chosen := (f.fr.selected names).flatMap f.fr.group
  let G : NormalGraph (EquationStore.CheckedLabel f.F.equations f.F.primitive) := StoreView.graph f.F.store
  let I : PositiveCertificates.InstanceImageCheck G := StoreView.images f.F.store
  let mut answers : CertificateProducer.Answered G := {}
  let mut cs := #[]
  let mut es := #[]
  let mut failed : List (Nat × String) := []
  for (plan, i) in f.plans.zipIdx do
    let searched : Except String (Response _ × List (ProgramCertificates.Evidence _) × CertificateProducer.Answered G) :=
      if !chosen.contains i then .error "" else do
      let .graph name namePos r ← plan
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
            fuel [] known r.sourceMap (some labels) r.assertions r.cuts r.codeHints r.checker r.aliases next
            (searched := true) (recheck := some (HeapExpressionRules.Checker.ordinary G))
        else do
          let (c, _) ← RequestJson.produceResponseUsing (RequestJson.graph r.toRequest) (StoreView.images r.types)
            r.checker r.toRequest fuel [] known r.sourceMap (some labels) r.assertions r.cuts
            r.codeHints r.checker r.aliases { summaries := next.summaries, summaryAnswers := next.summaryAnswers }
            (searched := true)
          pure (c, next)
      if let some refusal := footprintRefusal name namePos r c then throw refusal
      return (c, e, kept)
    match searched with
    | .ok (c, e, next) =>
      answers := next
      cs := cs.push c
      es := es.push e
    | .error reason =>
      if chosen.contains i then failed := failed ++ [(i, reason)]
      cs := cs.push { certificate := [] }
      es := es.push []
  let main := EvidenceWire.encode (Bundle.mk cs.toList es.toList)
  -- Each chosen group not refused by its search is checked as the checker
  -- checks it, so a refusal is the search's.
  let b : Bundle (EquationStore.CheckedLabel f.F.equations f.F.primitive) ← EvidenceWire.decode main
  let mut refusals : List (String × String) := []
  for i in f.fr.selected names do
    let group := f.fr.group i
    if let some (_, reason) := failed.find? (group.contains ·.1) then
      refusals := refusals ++ [(f.fr.unitId i, reason)]
    else
      match f.certified group with
      | .error reason => refusals := refusals ++ [(f.fr.unitId i, reason)]
      | .ok certified =>
        let checked := checkRequestsResult (CertifiedPlan.requests certified) (bundleOf b group)
        if !checked.accepted then
          refusals := refusals ++ [(f.fr.unitId i, requestsRefusal certified (bundleOf b group) checked)]
  let mut modules := #[]
  for m in f.p.modules do
    match produceDocument m.ast m.claims m.location fuel budget m.qualified with
    | .ok e => modules := modules.push (Json.mkObj [("location", toJson m.location), ("evidence", e)])
    | .error reason =>
      refusals := refusals ++ [("module:" ++ m.location, s!"module {m.location}: " ++ reason)]
      modules := modules.push (Json.mkObj [("location", toJson m.location), ("evidence", Json.null)])
  return (Json.mkObj [("main", main), ("modules", Json.arr modules)], refusals)

/-- A file's units, one per line: each selected group by its first member,
with its members and dependencies, then each module run. -/
def unitsJson (ast claims : Json) (fileKey : String) (budget : PositiveCertificates.SearchBudget := {})
    (names : Option (List String) := none) : Except String (List Json) := do
  let p ← planImports ast claims
  let fr ← fileFront p.ast p.claims fileKey budget p.qualified
  let runs := p.modules.map ("module:" ++ ·.location)
  let groups := (fr.selected names).map fun i =>
    let group := fr.group i
    Json.mkObj [("unit", toJson (fr.unitId i)), ("members", toJson (group.map fr.unitId)),
      ("depends", toJson ((fr.dependencies group).map fr.unitId ++ (if fr.readsQualified group then runs else [])))]
  let modules := p.modules.map fun m =>
    Json.mkObj [("unit", toJson ("module:" ++ m.location)), ("members", toJson ([] : List String)),
      ("depends", toJson (if m.qualified.isEmpty then [] else runs.filter (· != "module:" ++ m.location)))]
  return groups ++ modules

end Verification.SourceClaimJson
