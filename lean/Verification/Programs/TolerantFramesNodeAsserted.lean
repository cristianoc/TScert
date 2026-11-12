import Verification.Programs.TolerantFramesEdge

/-! # Tolerant frames: a written assertion established on an edge

`run` checks a node's written assertion `req` on every edge into a node
other than a loop head (`SinglePass.run`, "A target's assertion established
on the edge"): `KnowledgeExpand.checkIn` of `req` over the edge's
materialized facts, with the facts the edge's context `Γe` states of the
cells and links it reads, and under the edge's observation of the result
where it has one. `assertion_query_sound` proves that check gives `req` at
the target's environment, as `head_query_sound` proves the head query. -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules

section Asserted
variable {ι : Type} [DecidableEq ι]

/-- The facts the assertion check reads on an edge: under the edge's
observation of the result, the observed facts; otherwise the typed links,
each over the typed cells of the assertion (`run`'s `k`). -/
def assertionSource (G : NormalGraph ι) (Γe : List (Ty ι)) (req k : HeapKnowledge.Knowledge)
    (θ : PointClaims.Mapping) (observed : Option BranchRefinement.Observation) : HeapKnowledge.Knowledge :=
  match observed with
  | some o => HeapKnowledge.observeTyped G Γe (ControlFlow.withTypedCells G Γe req θ k) 0 o
  | none => HeapKnowledge.withTypedLinks G Γe (ControlFlow.withTypedCells G Γe req θ k)

/-- **The assertion check on an edge is sound**: where the edge's facts `k`
hold at the source environment `ρ`, typed by the edge's context `Γe`, the
observation (where the edge has one) holds of the result at slot 0, and the
target's context `Δ` types the mapped environment, the written assertion
`req` the check accepts holds at the target's environment. -/
theorem assertion_query_sound {G : NormalGraph ι} {Γe Δ : List (Ty ι)} {req k : HeapKnowledge.Knowledge}
    {θ : PointClaims.Mapping} {observed : Option BranchRefinement.Observation} {ρ : Env} {n : Nat}
    {W : WorldT (n + 1)} {h : Heap}
    (hq : KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G Δ) (assertionSource G Γe req k θ observed) req θ = true)
    (hk : HeapKnowledge.Holds k ρ h) (he : EnvOk G Γe ρ (n + 1) W) (hh : HeapOk (n + 1) W h)
    (ho : ∀ o, observed = some o → o.holds (ρ 0))
    (htc : EnvOk G Δ (PointClaims.mapEnv θ ρ) (n + 1) W) : HeapKnowledge.Holds req (PointClaims.mapEnv θ ρ) h := by
  have hc := withTypedCells_holds (k := req) (m := θ) (fun _ => HeapExpressionRules.typedCells_holds he hh)
    (fun _ _ hr => HeapExpressionRules.typeValues_sound hr he) hk
  refine KnowledgeExpand.checkIn_sound hq (KnowledgeExpand.ctxOf_ok htc) ?_
  unfold assertionSource
  cases observed with
  | some o => exact HeapKnowledge.observeTyped_holds he hc (ho o rfl)
  | none => exact HeapKnowledge.withTypedLinks_holds he hc

end Asserted

end Verification.TolerantFrames
