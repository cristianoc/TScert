import Verification.Programs.TolerantFramesRegionalHeld

/-! # Regional typing from the derivation's checked requirements -/
namespace Verification.TolerantFrames
open Verification SinglePass ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open ProgramTyping PositiveRules HeapObservations LabelStore GraphCode GraphCode.ArgumentRegionGraph
variable {ι : Type} [Labels ι]

/-- The regional evidence supplies the facts read by the step's requirements check. -/
def RegionalStepFacts (G : NormalGraph ι) (ev : NodeEvidence ι) (stepK : HeapKnowledge.Knowledge) : Prop :=
  ∀ ρ h, HeapKnowledge.Holds (entryFacts G ev) ρ h → HeapKnowledge.Holds stepK ρ h

/-- The requirements branch gives regional typing when the regional entry supplies the step facts. -/
theorem regionalTyped_of_requires {G : NormalGraph ι} {I : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} {c : PointClaim ι} {node : Node} {d : ProgramCertificates.Evidence ι}
    {se : Option (HeapExpressionRules.StepEvidence ι)} {kHere stepK : HeapKnowledge.Knowledge}
    (hd : regionalDerivChecked G I codes sums c node stepK (some d) = true)
    (hr : PromiseCalls.requiresTree G I stepK codes sums d = true)
    (hk : RegionalStepFacts G (passRegionalEvidence c node (some d) se kHere) stepK)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G I sums) :
    ControlFlow.entry (passRegionalEvidence c node (some d) se kHere) = c.context ∧
      RegionalTyped G (passRegionalEvidence c node (some d) se kHere) node := by
  simp only [regionalDerivChecked, derivChecked, Bool.and_eq_true, beq_iff_eq] at hd
  obtain ⟨⟨hterm, hctx⟩, -⟩ := hd
  refine ⟨by simpa [ControlFlow.entry, passRegionalEvidence, NodeEvidence.expression] using hctx, ?_⟩
  intro n W h ρ he _ hf hw hh
  obtain ⟨_, _, hs⟩ := PromiseCalls.requiresTree_sound hcodes hsums d hr
  have hs := erase (hs (by simpa [ControlFlow.entry, passRegionalEvidence, NodeEvidence.expression] using he)
    (hk ρ h hf) hw hh)
  rw [hterm] at hs
  have hs' : Safe (excOf G) (fun k U u => meaning G (result (passRegionalEvidence c node (some d) se kHere)) k U u ∧
      PromiseCalls.YieldsOk G (passRegionalEvidence c node (some d) se kHere).yields ρ k U u) n W h
      (instantiate 0 ρ node.expression) :=
    Safe_mono n (fun _ _ _ v hv => ⟨by simpa [result, passRegionalEvidence, NodeEvidence.expression] using hv,
      fun y hy => by simp [passRegionalEvidence] at hy⟩) W h _ hs
  exact of_value_property (fun _ _ _ v _ => outFacts_holds he (HeapKnowledge.empty _ _)) hs'

/-- Both branches of the regional derivation check give typing under the step-facts bridge. -/
theorem regionalTyped_of_derivation {G : NormalGraph ι} {I : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} {c : PointClaim ι} {node : Node} {d : ProgramCertificates.Evidence ι}
    {se : Option (HeapExpressionRules.StepEvidence ι)} {kHere stepK : HeapKnowledge.Knowledge}
    (hd : regionalDerivChecked G I codes sums c node stepK (some d) = true)
    (hk : RegionalStepFacts G (passRegionalEvidence c node (some d) se kHere) stepK)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G I sums) :
    ControlFlow.entry (passRegionalEvidence c node (some d) se kHere) = c.context ∧
      RegionalTyped G (passRegionalEvidence c node (some d) se kHere) node := by
  have hc := hd
  simp only [regionalDerivChecked, derivChecked, Bool.and_eq_true, Bool.or_eq_true] at hc
  rcases hc.2 with ht | hr
  · exact regionalTyped_of_tree hd ht hcodes hsums
  · exact regionalTyped_of_requires hd hr hk hcodes hsums

end Verification.TolerantFrames
