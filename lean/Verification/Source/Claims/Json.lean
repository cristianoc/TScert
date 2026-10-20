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
private def footprintRefusal {σ ι : Type} [Labels ι] [StoreView σ ι] (name : String) (namePos : Span)
    (r : SourceRequest σ ι) (c : Response ι) : Option String :=
  let G := RequestJson.graph r.toRequest
  let images := StoreView.images r.types
  let firstBad (Φ : Footprints.Closed) (ret exc : Bool) (start : Nat) (P : Program) (C : Certificate ι)
      (sourceMap : SourceMap) : Option SourceMapEntry :=
    let facts := GraphCode.inferFresh G images P C start
    ((P.zip C).zipIdx.find? fun ((node, point), l) =>
      !GraphCode.nodeChecked G images Φ facts ret exc l node point).bind fun (_, l) => (sourceMap[l]?).bind id
  let refuse (what : String) (pos : Span) :=
    s!"source effect refusal at [{pos.1},{pos.2}): the footprint claimed for {what} is not established by its body"
  let unit := effectResult r c
  if !unit.accepted then
    if unit.exhaustion.isSome then none else
    some (refuse s!"'{name}'" (((firstBad r.footprint false r.onThrow r.start r.program c.certificate r.sourceMap).map (·.pos)).getD namePos))
  else
    (r.toRequest.codes.zip c.codes).zipIdx.findSome? fun ((q, C), i) =>
      let code := GraphCode.effectCheckedResult G images q.entry C
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
    let facts := GraphCode.inferFresh G images P C start
    ((P.zip C).zipIdx.find? fun ((node, point), l) =>
      !GraphCode.nodeChecked G images Φ facts false exc l node point).bind fun (_, l) => (sourceMap[l]?).bind id
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
      !checkNodeUsing (checker := r.checker) G (StoreView.images r.types) r.goal r.program c.certificate node e codes).bind
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
    !(ExpressionClaims.checkResult G (StoreView.images r.types) (StoreView.valid r.types) q.sequent e codes).accepted).map
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
        ((r.checker.run (ProgramCertificates.claim e.expression) e.knowledge
          (e.effect.getD (.ordinary e.expression)) codes).expect e.output).accepted &&
        checkYields G images e codes)) then return none
  for ((node, e), label) in (r.program.zip c.certificate).zipIdx do
    if let (some target, some (T, proof)) := (node.handler, e.handler) then
      if let some destination := c.certificate[target.label]? then
        let typed := PointClaims.checkMappedUsing G images (T :: entry e) (entry destination) target.mapping proof
        let linked := HeapKnowledge.check (handlerFacts e.knowledge) destination.knowledge target.mapping
        if !typed || !linked then
          if let some m := (r.sourceMap[target.label]?).bind id then
            return some s!"source incoming edge obligation at [{m.pos.1},{m.pos.2}): evidence fails {if !typed then "type coverage" else "heap knowledge"} from node {label}, handler edge"
    for (target, index) in (CertificateProducer.successors node.continuation).zipIdx do
      let some destination := c.certificate[target.label]? | continue
      let some proof := e.edges[index]? | continue
      let Γ := CertificateProducer.edgeContextOf G e node.continuation index
      let facts := CertificateProducer.edgeImplicationsOf.edgeFactsOf e node.continuation
      let observed := match node.continuation with
        | .branchBind .. => some (BranchRefinement.Observation.boolean (index == 0))
        | .tagBind tag .. => some (BranchRefinement.Observation.tag tag (index == 0))
        | _ => none
      let typed := match observed with
        | none => PointClaims.checkMappedUsing G images Γ (entry destination) target.mapping proof
        | some o => BranchRefinement.checkObservedUsing G images Γ (entry destination) 0 o target.mapping proof
            (readFields facts 0) (optionalFields facts 0) (HeapKnowledge.observeTyped G Γ facts 0 o).cells
      let knowledge := match observed with
        | none => facts
        | some o => HeapKnowledge.observeTyped G Γ facts 0 o
      let linked := HeapKnowledge.check knowledge destination.knowledge target.mapping
      if !typed || !linked then
        if let some m := (r.sourceMap[target.label]?).bind id then
          return some s!"source incoming edge obligation at [{m.pos.1},{m.pos.2}): evidence fails {if !typed then "type coverage" else "heap knowledge"} from node {label}, edge {index}"
  return none

def checkDocument (ast claims : Json) (fileKey : String) (evidence : Json)
    (budget : PositiveCertificates.SearchBudget := {})
    (qualified : List (String × Footprints.Closed × Bool) := []) : Except String Unit := do
  let (T, plans) ← extractPlans ast claims fileKey budget qualified
  let ⟨F, frozen⟩ ← freezePlans T plans
  let certified ← certifyPlans frozen
  let rs := CertifiedPlan.requests certified
  let b : Bundle (EquationStore.CheckedLabel F.equations F.primitive) ← decodeStrict evidence
  let checked := checkRequestsResult rs b
  if checked.accepted then return ()
  -- An exhausted search is reported as such; a footprint the graph does not
  -- establish is located, then a node or an obligation whose evidence the
  -- check refuses; any other failure is the generic refusal.
  let fallback := validationFailure rs checked "source evidence does not justify the extracted program and exact claims"
  throw (if checked.exhaustion.isSome then fallback else
    (((certified.zip b.functions).findSome? fun (plan, c) => match plan with
      | .graph name namePos r => footprintRefusal name namePos r c) <|>
     (((certified.zip b.functions).zip b.obligations).findSome? fun ((plan, c), es) => match plan with
      | .graph _ _ r => nodeRefusal r c <|> obligationRefusal r c es <|> claimRefusal r c <|> edgeRefusal r c <|> typingRefusal r c)).getD fallback)

def produceDocument (ast claims : Json) (fileKey : String) (fuel : Nat)
    (budget : PositiveCertificates.SearchBudget := {})
    (qualified : List (String × Footprints.Closed × Bool) := []) : Except String Json := do
  let (T, plans) ← extractPlans ast claims fileKey budget qualified
  let ⟨F, frozen⟩ ← freezePlans T plans
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
  let mut answers : CertificateProducer.Answered (EquationStore.CheckedLabel F.equations F.primitive) := {}
  let mut proofLists := #[]
  for r in rs do
    let (e, next) ← ExpressionClaims.produceUsing G I r.searchLabels (StoreView.valid r.types)
      (StoreView.projection r.types) fuel r.obligations answers
    answers := next
    proofLists := proofLists.push e
  let mut responses := #[]
  for (r, proofs) in rs.zip proofLists.toList do
    let (rendered, next) := ExpressionClaims.renderKnownUsing G I r.searchLabels (StoreView.valid r.types)
      r.nodePlans answers
    answers := next
    let known := proofs ++ rendered
    -- A qualified body's checker is stated over the request's own image
    -- check: its search keeps that check.
    if r.qualification.isNone then
      let (c, next) ← RequestJson.produceResponseUsing G I (HeapExpressionRules.Checker.ordinary G I) r.toRequest
        fuel [] known r.sourceMap (some r.searchLabels) r.assertions r.cuts r.codeHints r.checker r.aliases answers
      answers := next
      responses := responses.push c
    else
      let (c, _) ← RequestJson.produceResponseUsing (RequestJson.graph r.toRequest) (StoreView.images r.types)
        r.checker r.toRequest fuel [] known r.sourceMap (some r.searchLabels) r.assertions r.cuts
        r.codeHints r.checker r.aliases
      responses := responses.push c
  let es := proofLists.toList
  let cs := responses.toList
  for (plan, c) in frozen.zip cs do
    let .graph name namePos r := plan
    if let some refusal := footprintRefusal name namePos r c then throw refusal
  let evidence := toJson (Bundle.mk cs es)
  let b : Bundle (EquationStore.CheckedLabel F.equations F.primitive) ← decodeStrict evidence
  let checked := checkRequestsResult rs b
  if !checked.accepted then
    throw (validationFailure rs checked "source evidence does not justify the extracted graph requests")
  return evidence

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

/-- Search evidence for the importer at its qualified reads, then for every
module run. -/
def produceJson (ast claims : Json) (fileKey : String) (fuel : Nat)
    (budget : PositiveCertificates.SearchBudget := {}) : Except String Json := do
  let p ← planImports ast claims
  let main ← produceDocument p.ast p.claims fileKey fuel budget p.qualified
  let modules ← p.modules.mapM fun m => do
    let e ← (produceDocument m.ast m.claims m.location fuel budget m.qualified).mapError
      (s!"module {m.location}: " ++ ·)
    return Json.mkObj [("location", toJson m.location), ("evidence", e)]
  return Json.mkObj [("main", main), ("modules", Json.arr modules.toArray)]

/-- Each module run checked as a document of its own, at its evidence. -/
def checkModules : List (ModuleRun × Json) → PositiveCertificates.SearchBudget → Except String Unit
  | [], _ => pure ()
  | (m, e) :: rest, budget => do
    (checkDocument m.ast m.claims m.location e budget m.qualified).mapError (s!"module {m.location}: " ++ ·)
    checkModules rest budget

theorem checkModules_each {runs : List (ModuleRun × Json)} {budget : PositiveCertificates.SearchBudget}
    (h : checkModules runs budget = .ok ()) :
    ∀ m e, (m, e) ∈ runs → checkDocument m.ast m.claims m.location e budget m.qualified = .ok () := by
  induction runs with
  | nil => intro m e hm; cases hm
  | cons x rest ih =>
    obtain ⟨m', e'⟩ := x
    unfold checkModules at h
    cases hd : checkDocument m'.ast m'.claims m'.location e' budget m'.qualified with
    | error err => rw [hd] at h; contradiction
    | ok u =>
      rw [hd] at h
      simp only [Bind.bind, Except.bind] at h
      intro m e hm
      rcases List.mem_cons.mp hm with he | hr
      · cases he; cases u; exact hd
      · exact ih h m e hr

/-- **The check.** The importer at its qualified reads, then every module
run, each a document of its own over its own store: one call, so the
evidence certifying a unit's effect is checked with the importer's. -/
def checkJson (ast claims : Json) (fileKey : String) (evidence : Json)
    (budget : PositiveCertificates.SearchBudget := {}) : Except String Unit := do
  let p ← planImports ast claims
  checkDocument p.ast p.claims fileKey (evidence.getObjValD "main") budget p.qualified
  let parts ← evidenceParts evidence p
  checkModules (p.modules.zip parts) budget

/-- What a document's successful check gives: its plans cross the
exhaustive certification boundary, and every certified request is safe, and
within its footprint where it claims one, as `checkDocument_safe` states. -/
def DocumentSafe (ast claims : Json) (fileKey : String) (evidence : Json)
    (budget : PositiveCertificates.SearchBudget) (qualified : List (String × Footprints.Closed × Bool)) : Prop :=
    ∃ T plans, extractPlans ast claims fileKey budget qualified = .ok (T, plans) ∧
      ∃ F : EquationStore.Frozen, ∃ frozen certified b,
      freezePlans T plans = .ok ⟨F, frozen⟩ ∧
      certifyPlans frozen = .ok certified ∧
      decodeStrict evidence = .ok b ∧
      checkRequests (CertifiedPlan.requests certified) b = true ∧
      (∀ r c, (r,c) ∈ (CertifiedPlan.requests certified).zip b.functions →
        ∀ η, r.Admits η → ∀ n W heap ρ, EnvOk (reassign F.equations.graph η) r.inputs ρ n W →
          WorldAdm W → HeapOk n W heap →
          SafeGraph (excOf (reassign F.equations.graph η)) r.program
            (ControlFlow.GoalHolds (reassign F.equations.graph η) r.goal (r.goal.argument ρ))
            n W heap (.at r.start ρ)) ∧
      (∀ r c, (r,c) ∈ (CertifiedPlan.requests certified).zip b.functions →
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

/-- Every extracted plan crosses the exhaustive certification boundary, and its
graph request proves the enclosing execution safe at every assignment admitted
by its source signature, including its descriptor contract when qualified. A
unit whose declaration claims a footprint other than the one letting every
location change, run as the code its graph describes, also returns with a heap
its footprint relates to its entry heap, and a value meeting its goal (a
guard's or an assertion function's promise included).
The graph is `Equations.graph` of the equations the extracted store presents,
validated by `Equations.ofRaw` (`freezePlans`). -/
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
    cases hf : freezePlans T plans with
    | error e => rw [hf] at h; contradiction
    | ok Ff =>
      obtain ⟨F, frozen⟩ := Ff
      rw [hf] at h
      simp only at h
      cases hc : certifyPlans frozen with
      | error e => rw [hc] at h; contradiction
      | ok certified =>
        rw [hc] at h
        cases hb : (decodeStrict evidence : Except String
            (Bundle (EquationStore.CheckedLabel F.equations F.primitive))) with
        | error e => rw [hb] at h; contradiction
        | ok b =>
          rw [hb] at h
          by_cases hx : checkRequests (CertifiedPlan.requests certified) b = true
          · refine ⟨T, plans, rfl, F, frozen, certified, b, hf, hc, hb, hx, ?_, ?_⟩
            · intro r c hm η admitted n W heap ρ he hw hh
              exact checkRequests_safe_at hx hm η admitted n W heap ρ he hw hh
            · intro r c hm heffect η n W heap L d he hw hh hvalues hd
              exact checkRequests_footprint_at hx hm heffect η n W heap L d he hw hh hvalues hd
          · simp only [checkRequests] at hx
            simp [hx] at h

/-- **The acceptance theorem.** A successful CLI check gives, for the
importer, what a document's check gives (`DocumentSafe`), its qualified
reads among its inputs, and the same for each module run certifying a
qualified unit, its own qualified reads among its inputs, each over its own
store. -/
theorem checkJson_safe {ast claims evidence : Json} {fileKey : String}
    {budget : PositiveCertificates.SearchBudget}
    (h : checkJson ast claims fileKey evidence budget = .ok ()) :
    ∃ p parts, planImports ast claims = .ok p ∧ evidenceParts evidence p = .ok parts ∧
      DocumentSafe p.ast p.claims fileKey (evidence.getObjValD "main") budget p.qualified ∧
      ∀ m e, (m, e) ∈ p.modules.zip parts → DocumentSafe m.ast m.claims m.location e budget m.qualified := by
  unfold checkJson at h
  cases hp : planImports ast claims with
  | error err => rw [hp] at h; contradiction
  | ok p =>
    rw [hp] at h
    simp only [Bind.bind, Except.bind] at h
    cases hd : checkDocument p.ast p.claims fileKey (evidence.getObjValD "main") budget p.qualified with
    | error err => rw [hd] at h; contradiction
    | ok u =>
      rw [hd] at h
      simp only at h
      cases he : evidenceParts evidence p with
      | error err => rw [he] at h; contradiction
      | ok parts =>
        rw [he] at h
        simp only at h
        cases u
        refine ⟨p, parts, rfl, he, checkDocument_safe hd, fun m e hme => ?_⟩
        exact checkDocument_safe (checkModules_each h m e hme)

end Verification.SourceClaimJson
