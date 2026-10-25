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

private abbrev GraphShape := Nat × List Tm × List (Continuation × Option Target) × Nat

mutual
private partial def graphShapes : Tm → List GraphShape
  | .objAt _ code _ => codeShapes code
  | .makeAt code _ args => codeShapes code ++ args.flatMap graphShapes
  | .invoke f r args => graphShapes f ++ graphShapes r ++ args.flatMap graphShapes
  | .construct f args => graphShapes f ++ args.flatMap graphShapes
  | .letE a b | .indexAt a b | .writeAt _ a b | .arith _ a b | .elemAt a b |
      .merge _ a b | .makeKey a b => graphShapes a ++ graphShapes b
  | .readAt _ a | .test _ a | .lenOf a | .spread a | .throw a => graphShapes a
  | .ite a b c | .setElem a b c => graphShapes a ++ graphShapes b ++ graphShapes c
  | .arrLit args => args.flatMap graphShapes
  | .goto es _ _ env d => (es ++ env ++ [d]).flatMap graphShapes
  | .frame es _ t env d _ _ => (es ++ env ++ [t, d]).flatMap graphShapes
  | .var _ | .nul | .undef | .tru | .fls | .num _ | .str _ | .bigint _ | .sym _ | .arr _ => []
private partial def codeShapes : CallCode → List GraphShape
  | .absent => []
  | .bound f r args => (f :: r :: args).flatMap graphShapes
  | .graph a es ks start caps _ _ => (a, es, ks, start) :: (es ++ caps).flatMap graphShapes
end

/-- Opaque expressions read fresh assumed inputs at their stated result types.
Appending slots preserves every original variable index. Each transfer carries
those inputs past the original destination mapping. The result is used only
inside diagnostic checking and cannot become a source acceptance result. -/
@[nospecialize] private def assumeNodes {σ ι : Type} [Labels ι] [StoreView σ ι]
    (r : SourceRequest σ ι) (holes : List Nat) (obligations : List Span)
    (edges : List (Nat × Nat × Nat)) : SourceRequest σ ι := Id.run do
  let holes := holes.eraseDups.filter fun label =>
    (r.claims[label]?).any fun c => !ControlFlow.unsatisfiable (StoreView.graph r.types) [c.type]
  let regions :=  holes.filterMap fun l => ((r.sourceMap[l]?).bind id).map (·.pos)
  let supplied := holes.map fun label => ((r.claims[label]?).map (·.type)).getD []
  let edgeSlots := edges.map fun (source, index, destination) => Id.run do
    let some node := r.program[source]? | return []
    let some claim := r.claims[source]? | return []
    let normal := CertificateProducer.successors node.continuation
    let some edge := (normal[index]?) <|> node.handler | return []
    let available := if index == normal.length then
        none :: claim.context.map some
      else match node.continuation with
        | .bind _ | .branchBind .. | .tagBind .. => (claim.type :: claim.context).map some
        | .ret | .effect _ | .branch .. => claim.context.map some
    let context := ((r.claims[destination]?).map (·.context)).getD []
    return context.zipIdx.filter fun (A, slot) =>
      ((available[PointClaims.slot edge.mapping slot]?).bind id) != some A
  let edgeInputs := edgeSlots.map fun slots => slots.map (·.1)
  let expressionInputs := supplied.length
  let supplied := supplied ++ edgeInputs.flatten
  let target (label index size : Nat) (t : Target) : Target :=
    match edges.findIdx? (fun (source, edge, _) => source == label && edge == index) with
    | some i =>
      let offset := expressionInputs + (edgeInputs.take i).flatten.length
      let slots := (edgeSlots[i]?).getD []
      { t with mapping := some ((List.range (((r.claims[t.label]?).map (·.context.length)).getD 0)).map
          (fun slot => match slots.findIdx? (fun (_, j) => j == slot) with
            | some j => size + offset + j
            | none => PointClaims.slot t.mapping slot) ++ (List.range supplied.length).map (size + ·)) }
    | none =>
      let count := ((r.claims[t.label]?).map (·.context.length)).getD 0
      { t with mapping := some ((List.range count).map (PointClaims.slot t.mapping) ++
        (List.range supplied.length).map (size + ·)) }
  let program := r.program.zipIdx.map fun (node, label) =>
    let size := ((r.claims[label]?).map (·.context.length)).getD 0
    let continuation := match node.continuation with
      | .ret => .ret
      | .bind t => .bind (target label 0 (size + 1) t)
      | .effect t => .effect (target label 0 size t)
      | .branch a b => .branch (target label 0 size a) (target label 1 size b)
      | .branchBind a b => .branchBind (target label 0 (size + 1) a) (target label 1 (size + 1) b)
      | .tagBind tag a b => .tagBind tag (target label 0 (size + 1) a) (target label 1 (size + 1) b)
    let expression := match holes.idxOf? label with
      | some i => Tm.var (size + i)
      | none => node.expression
    { node with expression, continuation, handler := node.handler.map (target label (CertificateProducer.successors node.continuation).length (size + 1)) }
  let shapes := program.flatMap fun node => graphShapes node.expression
  let retained := r.codes.zipIdx.filter fun (q, _) =>
    shapes.contains (q.entry.arity, q.entry.exprs, q.entry.conts, q.entry.start)
  return { r with
    program := program
    codes := retained.map (·.1)
    codeSources := retained.map fun (_, i) => (r.codeSources[i]?).getD {}
    inputs := r.inputs ++ supplied
    claims := r.claims.map (fun c => { c with context := c.context ++ supplied }),
    nodePlans := [],
    assertions := r.assertions.filter fun (label, _) => !edges.any (fun (_, _, destination) => destination == label),
    obligations := (r.obligations.filter fun o => !obligations.contains o.pos &&
      !regions.any (fun p => p.1 ≤ o.pos.1 && o.pos.2 ≤ p.2)).map fun o =>
      { o with sequent := { o.sequent with context := o.sequent.context ++ supplied } } }

/-- Structured failures locate either an expression or a nested closure body.
A promise or incoming edge can make the enclosing closure opaque, while the
same obligation in the unit's own graph remains required. -/
private def failedRegion (reason : String) : Option (Span × Bool) := do
  if reason.startsWith "source effect refusal at [" &&
      reason.endsWith "is not established by its body" then
    let location ← (reason.splitOn "[")[1]?
    let bounds := ((location.splitOn ")").headD "").splitOn ","
    let start ← (← bounds[0]?).toNat?
    let stop ← (← bounds[1]?).toNat?
    if start < stop then return ((start, stop), true) else none
  else do
    let raw ← (reason.splitOn "\nobligation-diagnostic: ")[1]?
    let record ← (Json.parse raw).toOption
    let kind ← (record.getObjValAs? String "kind").toOption
    let expression := kind == "expression-claim"
    let origin ← if kind == "node-typing" then do
        let source ← (record.getObjVal? "source").toOption
        (source.getObjVal? "sourceMap").toOption
      else if kind == "edge-coverage" then do
        let destination ← (record.getObjVal? "destination").toOption
        (destination.getObjVal? "sourceMap").toOption
      else if kind == "expression-claim" || kind == "direct-obligation" then
        (record.getObjVal? "sourceMap").toOption
      else none
    pure (← (jSpan origin "pos").toOption, expression)

/-- A closure is selected by its own source map and retained code shape.
Source containment alone can also name scaffolding around the closure. -/
@[nospecialize] private def containsClosureAt {σ ι : Type} [Labels ι] [StoreView σ ι]
    (r : SourceRequest σ ι) (node : Node) (pos : Span) : Bool :=
  let shapes := graphShapes node.expression
  r.codes.zipIdx.any fun (q, i) =>
    shapes.contains (q.entry.arity, q.entry.exprs, q.entry.conts, q.entry.start) &&
    ((r.codeSources[i]?).getD {}).sourceMap.any fun entry =>
      entry.any fun e => e.pos.1 ≤ pos.1 && pos.2 ≤ e.pos.2

/-- Prefer the failing node itself when the diagnostic names this exact graph.
A closure's node can share a label or span with a surrounding expression. -/
private def failedLabel (reason : String) (program : Program) : Option Nat := do
  let raw ← (reason.splitOn "\nobligation-diagnostic: ")[1]?
  let record ← (Json.parse raw).toOption
  if (record.getObjValAs? String "kind").toOption != some "node-typing" then none else do
    let source ← (record.getObjVal? "source").toOption
    let label ← (source.getObjValAs? Nat "label").toOption
    let node ← (source.getObjVal? "node").toOption
    if (program[label]?).any (fun n => toJson n == node) then some label else none

/-- An edge retry uses the structured source and destination, including their
positions, so a nested closure's labels cannot select the enclosing graph. -/
private def failedEdge (reason : String) (program : Program) : Option (Nat × Nat × Nat × Span × Span) := do
  let raw ← (reason.splitOn "\nobligation-diagnostic: ")[1]?
  let record ← (Json.parse raw).toOption
  if (record.getObjValAs? String "kind").toOption != some "edge-coverage" then none else do
    let source ← (record.getObjVal? "source").toOption
    let destination ← (record.getObjVal? "destination").toOption
    let label ← (source.getObjValAs? Nat "label").toOption
    let target ← (destination.getObjValAs? Nat "label").toOption
    let index ← (record.getObjValAs? Nat "edgeIndex").toOption
    let sourceNode ← (source.getObjVal? "node").toOption
    let destinationNode ← (destination.getObjVal? "node").toOption
    if !(program[label]?).any (fun n => toJson n == sourceNode) ||
        !(program[target]?).any (fun n => toJson n == destinationNode) then none else do
      let origin ← (source.getObjVal? "sourceMap").toOption
      let to ← (destination.getObjVal? "sourceMap").toOption
      pure (label, index, target, ← (jSpan origin "pos").toOption, ← (jSpan to "pos").toOption)

/-- Inspect every extracted expression obligation and graph node. Failure of
shared equation preparation leaves the entire document unexamined. Failure
of one unit's extraction leaves that unit unexamined and retains its siblings.
No successful local attempt establishes a source safety judgment. -/
def diagnoseJson (ast claims : Json) (fileKey : String) (fuel : Nat)
    (budget : PositiveCertificates.SearchBudget := {}) (complete : Bool := true) : Json :=
  -- A complete derivation of the retained program discharges every local
  -- obligation. Only a refusal needs the less precise local traversal.
  match produceDocument ast claims fileKey fuel budget with
  | .ok _ => Json.mkObj [("status", toJson "diagnostic"), ("attempted", toJson (0 : Nat)),
      ("completed", toJson true), ("occurrences", toJson ([] : List Json)),
      ("unexamined", toJson ([] : List Json))]
  | .error aggregate => Id.run do
    let mut failures : List Json := [occurrence "aggregate" (0, 0) aggregate]
    let mut unexamined : List Json := []
    let mut completed := false
    let mut attempted := 0
    let result : Except String ((F : EquationStore.Frozen) ×
        List (FunctionPlan (EquationStore.Checked F.equations F.primitive)
          (EquationStore.CheckedLabel F.equations F.primitive)) × List (Span × String × Bool)) := do
      let (T, plans, refusals) ← diagnosticPlans ast claims fileKey budget
      let ⟨F, frozen⟩ ← freezePlans T plans
      pure ⟨F, frozen, refusals⟩
    match result with
    | .error reason =>
      failures := [occurrence "extraction" (0, 0) reason]
      unexamined := [occurrence "extraction" (0, 0) "shared extraction failed"]
    | .ok ⟨F, plans, refusals⟩ =>
      let mut allChecked := !plans.isEmpty && refusals.all (·.2.2)
      for (pos, reason, recovered) in refusals do
        failures := failures ++ [occurrence "extraction" pos reason]
        unexamined := unexamined ++ [occurrence "extraction" pos
          (if recovered then "opaque typed operation or contract" else "unit extraction failed")]
      for plan in plans do
        let .graph name namePos r := plan
        -- Check every recovered unit, retaining siblings after a refusal.
        if complete then
          match produceFrozenPlans F [plan] fuel with
          | .ok _ => continue
          | .error reason =>
            failures := failures ++ [occurrence "aggregate" namePos reason]
        let beforeLocal := unexamined
        let mut assumed : List Nat := []
        let mut assumedObligations : List Span := []
        let mut assumedEdges : List (Nat × Nat × Nat) := []
        let mut assumedRegions : List Json := []

        let G := StoreView.graph r.types
        let I := StoreView.images r.types
        let labels := r.searchLabels
        let mut known := []
        let mut answers : CertificateProducer.Answered G := {}
        for obligation in r.obligations do
          attempted := attempted + 1
          match ExpressionClaims.produceUsing G I labels (StoreView.valid r.types)
              (StoreView.projection r.types) fuel [obligation] answers with
          | .error reason =>
            failures := failures ++ [occurrence "search" obligation.pos reason]
            assumedObligations := assumedObligations ++ [obligation.pos]
            assumedRegions := assumedRegions ++ [occurrence "search" obligation.pos "opaque expression obligation"]
          | .ok (proofs, next) =>
            known := known ++ proofs
            answers := next
        if !RequestJson.asyncEffects r.async r.footprint ||
            !RequestJson.statedWithin r.async r.footprint r.onThrow r.stated then
          failures := failures ++ [occurrence "check" namePos "the unit's claimed effect is outside its source contract"]
        let requests := (r.toRequest, r.sourceMap, r.assertions, r.footprint, false, r.onThrow) ::
          (r.toRequest.codes.zipIdx.map fun (q, i) =>
            (q.asRequest r.toRequest, ((r.codeHints[i]?).getD {}).sourceMap,
              ((r.codeHints[i]?).getD {}).requirements,
              q.entry.row.effect.footprint, q.entry.row.effect.fresh, q.entry.row.effect.onThrow))
        for ((request, origins, requirements, footprint, fresh, onThrow), requestIndex) in requests.zipIdx do
          attempted := attempted + request.program.length
          let holeLabels := origins.zipIdx.filterMap fun (entry, label) =>
            if entry.any (fun e => e.role.startsWith "diagnostic-") then some label else none
          let inspected := CertificateProducer.inspectUsing G I labels fuel
            request.program request.claims requirements known (fun _ => true) r.checker r.aliases request.goal request.start holeLabels
          if requestIndex == 0 then
            assumed := holeLabels ++ inspected.failures.filterMap fun
              | .expression l | .exhaustedExpression l _ => some l
              | _ => none
            for label in assumed.eraseDups do
              let pos := (((origins[label]?).bind id).map (·.pos)).getD namePos
              assumedRegions := assumedRegions ++ [occurrence "search" pos "opaque expression supplied as a fresh input"]
          -- Effects are inspected independently of safety and of earlier nodes.
          if footprint != .top || fresh || onThrow then
            if fresh || !request.program.all (fun node => Purity.pureTerm node.expression) then
              let facts := GraphCode.inferFresh G I [] request.program inspected.nodes request.start
              for ((node, evidence), label) in (request.program.zip inspected.nodes).zipIdx do
                if !GraphCode.nodeChecked G I [] footprint facts fresh onThrow label node evidence then
                  let pos := (((origins[label]?).bind id).map (·.pos)).getD namePos
                  failures := failures ++ [occurrence "check" pos
                    s!"node {label}: footprint not established at supplied interface" true]
          for error in inspected.failures do
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
              "aggregate certificate checks" true]
        if !complete then
          allChecked := false
        else
          let mut checked := false
          -- Each retry replaces one expression or one of at most three
          -- outgoing edges per node (two normal destinations and a handler).
          for _ in List.range (r.program.length * 4 + 1) do
            let approximation := assumeNodes r assumed assumedObligations assumedEdges
            match produceFrozenPlans F [.graph name namePos approximation] fuel with
            | .ok _ =>
              checked := true
              break
            | .error reason =>
              failures := failures ++ [occurrence "aggregate" namePos reason true]
              if let some (source, index, destination, origin, to) := failedEdge reason approximation.program then
                let edge := (source, index, destination)
                let originsAgree := ((r.sourceMap[source]?).bind id).any (·.pos == origin) &&
                  ((r.sourceMap[destination]?).bind id).any (·.pos == to)
                let inhabited := (r.claims[destination]?).any fun c =>
                  c.context.all fun A => !ControlFlow.unsatisfiable G [A]
                if originsAgree && inhabited && !assumedEdges.contains edge then
                  assumedEdges := assumedEdges ++ [edge]
                  assumedRegions := assumedRegions ++ [
                    occurrence "search" origin "opaque edge supplies destination values from fresh inputs",
                    occurrence "search" to "opaque incoming interface supplied by fresh inputs"]
                  continue
              let some (pos, expressionFailure) := failedRegion reason | break
              let exactLabel := failedLabel reason approximation.program
              let candidates := r.sourceMap.zipIdx.filter fun (entry, label) =>
                !assumed.contains label && entry.any (fun e => e.pos.1 ≤ pos.1 && pos.2 ≤ e.pos.2) &&
                (expressionFailure || exactLabel == some label ||
                  (r.program[label]?).any (fun node => containsClosureAt r node pos)) &&
                (r.claims[label]?).any (fun c => !ControlFlow.unsatisfiable G [c.type])
              let exact := exactLabel.bind fun label =>
                candidates.find? (fun (_, i) => i == label)
              let candidate := exact <|> candidates.foldl (fun best next => match best, next.1 with
                | none, some _ => some next
                | some (some previous, _), some current =>
                  if current.pos.2 - current.pos.1 < previous.pos.2 - previous.pos.1 then some next else best
                | _, _ => best) none
              let some (some origin, label) := candidate | break
              assumed := assumed ++ [label]
              assumedRegions := assumedRegions ++ [occurrence "search" origin.pos
                "opaque aggregate expression supplied as a fresh input"]
          if checked then unexamined := beforeLocal ++ assumedRegions
          else
            allChecked := false
            unexamined := unexamined ++ assumedRegions
      completed := allChecked
    return Json.mkObj [("status", toJson "diagnostic"), ("attempted", toJson attempted), ("completed", toJson completed),
      ("occurrences", toJson failures), ("unexamined", toJson unexamined)]

end Verification.SourceClaimJson
