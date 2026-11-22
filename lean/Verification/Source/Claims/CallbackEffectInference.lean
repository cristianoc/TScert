import Verification.Source.Claims.PassProposals
import Verification.Source.Claims.CallbackPreservation
import Verification.Source.Claims.CallbackEffectFlow

/-! Experimental location-sensitive closure effect proposals. The ordinary
pass checks the code first. This analysis reads its step certificates and
rebases their effects into the closure entry frame, including its captures. -/
namespace Verification.SourceClaimJson.CallbackEffectInference
open Footprints CallEffects ControlFlow ProgramTyping RequestJson SourceElaboration
open PositiveGraphs PositiveCertificates LabelStore CertificateProducer

private def join (old new : Option Footprint) : Option Footprint :=
  match old, new with
  | none, a | a, none => a
  | some a, some b => some ((a ++ b).eraseDups)

private def sequence (before after : Option Footprint) : Option Footprint :=
  match before, after with
  | some a, some b => some ((a ++ b).eraseDups)
  | _, _ => none

/-- Join per-exit effects over the same normal and exceptional edges that the
single pass walks. An absent local summary identifies an unvisited node. -/
private def proposeFlow (nodes : List Node) (start : Nat) (locals : Array (Option Summary)) :
    Option (Entries × Summary) :=
  let graph := (nodes.map (·, ())).zipIdx
  let entry := (Array.replicate nodes.length none).setIfInBounds start (some [])
  let limit := locals.foldl (init := 2) fun n s =>
    n + ((s.bind (·.normal)).getD []).length + ((s.bind (·.exceptional)).getD []).length
  let transfer := fun (((node, _), label) : (Node × Unit) × Nat)
      ((entry, out) : Array (Option Footprint) × Summary) => Id.run do
    let some previous := entry.getD label none | return (entry, out)
    let some localSummary := locals.getD label none | return (entry, out)
    let normal := sequence (some previous) localSummary.normal
    let raised := sequence (some previous) localSummary.exceptional
    let mut entry := entry
    let mut out := out
    if node.continuation == .ret then out := { out with normal := join out.normal normal }
    for target in CertificateProducer.successors node.continuation do
      entry := entry.modify target.label (join · normal)
    match node.handler with
    | some target => entry := entry.modify target.label (join · raised)
    | none => out := { out with exceptional := join out.exceptional raised }
    return (entry, out)
  graphWorklist graph transfer (fun state l => state.1.getD l none)
    limit (entry, ⟨none, none⟩)

/-- Check the proposed node entries and both graph exits. A failed worklist
and a proposed table missing an effect have different diagnostics. -/
def composeChecked (nodes : List Node) (start : Nat) (locals : Array (Option Summary)) : Except String Summary := do
  let some (entries, result) := proposeFlow nodes start locals
    | throw "closure effect inference did not settle"
  if checkFlow nodes start locals entries result then return result
  throw "closure effect flow certificate does not cover every reached node and exit"

private def rebaseStep (facts : List GraphCode.ArgumentPathTracking.Fact)
    (slots : Nat → Option Nat) (frame : Footprint) : Footprint :=
  let link := fun p => do
    let slot ← slots p
    let fact ← facts.find? (·.slot == slot)
    return (fact.region.position, fact.region.path)
  rebaseAll { link, agree := fun _ _ => false } (frame.filter (·.2 != .keep))

section
variable {ι : Type} [DecidableEq ι]

/-- Keep the selected signature's location-specific effects for calls. A
typed own-field write uses the existing regional rule for that operation.
All other effects use the certificate's class bounds or an unrestricted bound. -/
def step (G : NormalGraph ι) (node : Node) (claim : PointClaim ι)
    (facts : List GraphCode.ArgumentPathTracking.Fact) (q : SinglePass.StepCertificate) : Summary := Id.run do
  let top := Footprints.Closed.top.fp
  if !q.scope then return ⟨some top, some top⟩
  let frames : Exits Footprint := ⟨(q.normal.head?.map (·.frame)).getD top,
    (q.exceptional.head?.map (·.frame)).getD top⟩
  let slots := PromiseCalls.actualSlot node.expression
  let normal := if ExpressionEffects.emptyType G claim.type then none else
    some (rebaseStep facts slots frames.normal)
  match ExpressionEffects.fieldWriteStep G claim.context node.expression with
  | some (receiver, key) =>
    return ⟨normal.map fun _ => rebaseStep facts some (ExpressionEffects.fieldWriteFrame receiver key), some []⟩
  | none => return ⟨normal, some (rebaseStep facts slots frames.exceptional)⟩

/-- Infer effects in closure entry slots. The code frame places the receiver
and ordinary arguments before the captures. Two different captures retain
two positions, even if a caller passes aliases for them. -/
def inferChecked (G : NormalGraph ι) (q : CodeRequest ι) (records : Array SinglePass.VisitRecord) : Except String Summary := do
  let nodes := GraphCode.program q.entry.exprs q.entry.conts
  let inputs := codeFrame q.entry.arity q.entry.row q.entry.captures q.entry.spine
  let origins := (List.range inputs.length).map fun slot =>
    ({ position := slot, path := [] } : ArgumentSpineRegion)
  let entries := q.claims.map fun c => ({ sequent := some ⟨c.context, .undef, c.type⟩, edges := [] } : NodeEvidence ι)
  let facts := regionTable nodes entries q.entry.start origins |>.toArray
  let ns := nodes.toArray
  let claims := q.claims.toArray
  let locals ← records.foldlM (init := Array.replicate ns.size none) fun acc record => do
    let some node := ns[record.label]? | throw "closure effect record has no graph node"
    let some claim := claims[record.label]? | throw "closure effect record has no point claim"
    let frame := step G node claim (facts.getD record.label []) record.certificate
    let combined := match acc.getD record.label none with
      | none => frame
      | some old => ⟨join old.normal frame.normal, join old.exceptional frame.exceptional⟩
    return acc.setIfInBounds record.label (some combined)
  composeChecked nodes q.entry.start locals

end

/-- Consume an inferred proposal at the proof-rule boundary. The supplied
actuals map the closure frame's ordinary and captured slots to caller slots. -/
def Summary.callback (summary : Summary) (actuals : Nat → Option Nat) :
    CallbackPreservation.Callback :=
  ⟨summary.map (·.getD []), actuals⟩


structure CheckedCode (ι : Type) where
  entry : CodeEntry ι
  summary : Summary

/-- Check the code requests in their usual dependency order and infer their
effects using the accepted walks. The parent graph can consume these without
walking closure source a second time. -/
def inferCodes {σ ι : Type} [Labels ι] [StoreView σ ι]
    [CertificateProducer.Instantiates ι] (r : SourceRequest σ ι) (fuel : Nat) :
    Except String (Array (CheckedCode ι) × List (ProgramCertificates.Evidence ι) ×
      CertificateProducer.Answered (RequestJson.graph r.toRequest)) := do
  if r.qualification.isSome then throw "regional closure inference needs an ordinary graph"
  let G := RequestJson.graph r.toRequest
  let images := StoreView.images r.types
  let labels := r.searchLabels
  let valid := StoreView.valid r.types
  let (known, answers) ← match ExpressionClaims.produceUsing G images labels valid
      (StoreView.projection r.types) fuel r.obligations {} with
    | .ok result => pure result
    | .error _ => throw "the member's expression obligations did not pass"
  let (rendered, answers) := ExpressionClaims.renderKnownUsing G images labels valid r.nodePlans answers
  let known := known ++ rendered
  let mut answers := answers
  let mut table := #[]
  let mut accepted := []
  for (q, code) in r.codes.zipIdx do
    if !codeConditions q.entry || !asyncAdmits q.async q.entry.row.effect then
      throw s!"closure {code} did not meet its signature conditions"
    let rq := q.asRequest r.toRequest
    let hints := (r.codeHints[code]?).getD {}
    let pool := CertificateProducer.vocabulary G labels rq.claims rq.inputs
    let (outcome, counts, next, _) := SinglePass.run G images pool fuel rq.program rq.claims rq.start
      rq.inputs q.entry.goal hints.requirements hints.cuts hints.candidates rq.entryIndices
      [] known (GraphCode.admits accepted) r.aliases .ordinary answers
      (bound := codeBound q.entry) (grading := true)
    let .accepted := outcome | throw s!"closure {code} was refused: {outcome}"
    answers := next
    accepted := accepted ++ [q.entry]
    let summary : Summary ← if q.async then
      pure ⟨some Footprints.Closed.top.fp, some Footprints.Closed.top.fp⟩
      else (inferChecked G q counts.grades).mapError fun msg => s!"closure {code}: {msg}"
    table := table.push ⟨q.entry, summary⟩
  return (table, known, answers)

end Verification.SourceClaimJson.CallbackEffectInference
