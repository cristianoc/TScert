import Verification.Source.Claims.Json

/-! Diagnostic traversal produces an inventory, with no evidence output and
no conversion to the acceptance result. Local node attempts assume their
supplied interfaces and forget predecessor-derived heap facts. -/
namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs LabelStore

private def occurrence (layer : String) (pos : Span) (reason : String)
    (conditional : Bool := false) : Json :=
  Json.mkObj [("layer", toJson layer), ("pos", toJson pos),
    ("reason", toJson ((reason.splitOn "\n").headD "")), ("conditional", toJson conditional)]

/-- Inspect every extracted expression obligation and graph node. Failure of
shared equation preparation leaves the entire document unexamined. Failure
of one unit's extraction leaves that unit unexamined and retains its siblings.
No successful local attempt establishes a source safety judgment. -/
def diagnoseJson (ast claims : Json) (fileKey : String) (fuel : Nat)
    (budget : PositiveCertificates.SearchBudget := {}) : Json :=
  -- A complete derivation of the retained program discharges every local
  -- obligation. Only a refusal needs the less precise local traversal.
  match produceDocument ast claims fileKey fuel budget with
  | .ok _ => Json.mkObj [("status", toJson "diagnostic"), ("attempted", toJson (0 : Nat)),
      ("completed", toJson true), ("occurrences", toJson ([] : List Json)),
      ("unexamined", toJson ([] : List Json))]
  | .error aggregate => Id.run do
    let mut failures : List Json := [occurrence "aggregate" (0, 0) aggregate]
    let mut unexamined : List Json := [occurrence "check" (0, 0) "aggregate checking stops at a refusal"]
    let mut attempted := 0
    let result : Except String ((F : EquationStore.Frozen) ×
        List (FunctionPlan (EquationStore.Checked F.equations F.primitive)
          (EquationStore.CheckedLabel F.equations F.primitive)) × List (Span × String)) := do
      let (T, plans, refusals) ← diagnosticPlans ast claims fileKey budget
      let ⟨F, frozen⟩ ← freezePlans T plans
      pure ⟨F, frozen, refusals⟩
    match result with
    | .error reason =>
      failures := [occurrence "extraction" (0, 0) reason]
      unexamined := [occurrence "extraction" (0, 0) "shared extraction failed"]
    | .ok ⟨_, plans, refusals⟩ =>
      for (pos, reason) in refusals do
        failures := failures ++ [occurrence "extraction" pos reason]
        unexamined := unexamined ++ [occurrence "extraction" pos "unit extraction failed"]
      for plan in plans do
        let .graph _ namePos r := plan
        let G := StoreView.graph r.types
        let I := StoreView.images r.types
        let labels := r.searchLabels
        let mut known := []
        let mut answers : CertificateProducer.Answered G := {}
        for obligation in r.obligations do
          attempted := attempted + 1
          match ExpressionClaims.produceUsing G I labels (StoreView.valid r.types)
              (StoreView.projection r.types) fuel [obligation] answers with
          | .error reason => failures := failures ++ [occurrence "search" obligation.pos reason]
          | .ok (proofs, next) =>
            known := known ++ proofs
            answers := next
        -- Each sibling's complete graph and effect checks can reveal an
        -- obligation beyond the first refusing unit of the document.
        match RequestJson.produceResponseUsing G I r.checker r.toRequest fuel [] known
            r.sourceMap (some labels) r.assertions r.cuts r.codeHints r.checker r.aliases answers
            (searched := true) with
        | .error reason => failures := failures ++ [occurrence "search" namePos reason]
        | .ok (response, _) =>
          if let some reason := footprintRefusal "diagnostic unit" namePos r response then
            failures := failures ++ [occurrence "check" namePos reason]
        let requests := (r.toRequest, r.sourceMap, r.assertions) ::
          (r.toRequest.codes.zipIdx.map fun (q, i) =>
            (q.asRequest r.toRequest, ((r.codeHints[i]?).getD {}).sourceMap,
              ((r.codeHints[i]?).getD {}).requirements))
        for (request, origins, requirements) in requests do
          attempted := attempted + request.program.length
          let errors := CertificateProducer.diagnoseUsing G I labels fuel
            request.program request.claims requirements known (fun _ => true) r.checker r.aliases request.goal
          for error in errors do
            let reason := match error with
              | .expression l => s!"node {l}: expression evidence search failed at supplied interface"
              | .exhaustedExpression l _ => s!"node {l}: expression subtype search exhausted"
              | .edge source target index => s!"node {source}: edge {index} to node {target} does not establish its claims"
              | .exhaustedEdge source target index _ => s!"node {source}: edge {index} to node {target} subtype search exhausted"
              | .promise l .. => s!"node {l}: return promise not established"
              | .claimCount => "graph claim count mismatch"
              | .rejected => "graph certificate rejected"
            let pos := match error with
              | .expression l | .exhaustedExpression l _ | .promise l .. =>
                (((origins[l]?).bind id).map (·.pos)).getD namePos
              | .edge _ l _ | .exhaustedEdge _ l _ _ =>
                (((origins[l]?).bind id).map (·.pos)).getD namePos
              | _ => namePos
            failures := failures ++ [occurrence "search" pos reason true]
            unexamined := unexamined ++ [occurrence "check" pos
              "remaining obligations of a failed node; aggregate certificate and footprint checks" true]
    return Json.mkObj [("status", toJson "diagnostic"), ("attempted", toJson attempted), ("completed", toJson false),
      ("occurrences", toJson failures), ("unexamined", toJson unexamined)]

end Verification.SourceClaimJson
