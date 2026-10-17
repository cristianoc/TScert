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

/-! Source claim validation, evidence production and the theorem relating
exact accepted plans to modeled graph safety. -/
namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore
open EquationGraphs (Tree)

def checkJson (ast claims : Json) (fileKey : String) (evidence : Json)
    (budget : PositiveCertificates.SearchBudget := {}) : Except String Unit := do
  let (T, plans) ← extractPlans ast claims fileKey budget
  let ⟨F, frozen⟩ ← freezePlans T plans
  let certified ← certifyPlans frozen
  let rs := CertifiedPlan.requests certified
  let b : Bundle (EquationStore.CheckedLabel F.equations F.primitive) ← decodeStrict evidence
  let checked := checkRequestsResult rs b
  if checked.accepted then return ()
  throw (validationFailure rs checked "source evidence does not justify the extracted program and exact claims")

def produceJson (ast claims : Json) (fileKey : String) (fuel : Nat)
    (budget : PositiveCertificates.SearchBudget := {}) : Except String Json := do
  let (T, plans) ← extractPlans ast claims fileKey budget
  let ⟨F, frozen⟩ ← freezePlans T plans
  let rs := FunctionPlan.requests frozen
  let es ← rs.mapM fun r => ExpressionClaims.produceUsing (RequestJson.graph r.toRequest)
    (StoreView.images r.types) r.searchLabels (StoreView.valid r.types)
    (StoreView.projection r.types) fuel r.obligations
  let cs ← (rs.zip es).mapM fun (r,proofs) => do
    let known := proofs ++ ExpressionClaims.renderKnownUsing (RequestJson.graph r.toRequest)
      (StoreView.images r.types) r.searchLabels (StoreView.valid r.types) r.nodePlans
    RequestJson.produceResponse r.toRequest fuel [] known r.sourceMap (some r.searchLabels) r.assertions
      r.cuts r.codeHints r.checker r.aliases
  -- A declaration's claimed effect its graph does not establish is located at
  -- the first node that does not preserve the heap, or at the declaration.
  for (plan, c) in frozen.zip cs do
    let .graph name namePos r := plan
    if !(effectResult r c).accepted then
      let G := RequestJson.graph r.toRequest
      let images := StoreView.images r.types
      let bad := ((r.program.zip c.certificate).zipIdx.find? fun ((node, point), _) =>
        !GraphCode.compositionalChecked G images [node] [point]).bind fun (_, l) =>
          (r.sourceMap[l]?).bind id
      let pos := (bad.map (·.pos)).getD namePos
      throw s!"source effect refusal at [{pos.1},{pos.2}): the heap preservation claimed for '{name}' is not established by its body"
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
  let (T, plans) ← extractPlans ast claims fileKey {}
  let ⟨_, frozen⟩ ← freezePlans T plans
  return toJson (frozen.map fun
    | .graph name _ r => Json.mkObj [("name", toJson name), ("start", toJson r.toRequest.start),
        ("program", toJson r.toRequest.program),
        ("codes", toJson (r.toRequest.codes.map fun (c : CodeRequest _) => codeJson c.entry))])

/-- Every extracted plan crosses the exhaustive certification boundary, and its
graph request proves the enclosing execution safe at every assignment admitted
by its source signature, including its descriptor contract when qualified. A
unit whose declaration claims heap preservation, run as the code its graph
describes, also leaves its entry heap a prefix of the heap it returns with.
The graph is `Equations.graph` of the equations the extracted store presents,
validated by `Equations.ofRaw` (`freezePlans`). -/
theorem checkJson_safe {ast claims evidence : Json} {fileKey : String}
    {budget : PositiveCertificates.SearchBudget}
    (h : checkJson ast claims fileKey evidence budget = .ok ()) :
    ∃ T plans, extractPlans ast claims fileKey budget = .ok (T, plans) ∧
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
        r.effect = .preservesInputHeap →
        ∀ η n W heap (L : List Tm) (d : Tm),
          EnvOk (reassign F.equations.graph η) r.inputs (envOf L d) n W →
          WorldAdm W → HeapOk n W heap → (∀ v ∈ L, isVal v = true) → isVal d = true →
          HeapObservations.SafePost (excOf (reassign F.equations.graph η))
            (meaning (reassign F.equations.graph η) r.result)
            (CallEffects.Effect.preservesInputHeap.post heap) n W heap
            (.goto (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))
              r.start L d)) := by
  unfold checkJson at h
  cases he : extractPlans ast claims fileKey budget with
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
              exact checkRequests_preserving_at hx hm heffect η n W heap L d he hw hh hvalues hd
          · simp only [checkRequests] at hx
            simp [hx] at h

end Verification.SourceClaimJson
