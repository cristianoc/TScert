import Verification.Programs.TolerantFramesExitExecution

/-! # Assembly of checked exits into the graph's exit obligation -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules LabelStore

section Assembly
variable {ι : Type} [Labels ι]

/-- The exit obligation from reassignment-stable checks at each recorded
node. The check-extraction premise is local to the original graph; codes,
summary soundness, freshness and reassignment are supplied here. -/
theorem exitsYield_of_checks
    (checks : ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I)
      (r : RunWalkA G I c), WalkChecked c r → ∀ l (hl : r.w.visited l),
      ∃ here outFresh ysA thrown TT,
        NodeExitsChecked G I r.w (List.range c.inputs.length) r.ctx r.stated r.given r.edgesIn l
          (r.node l hl).node (r.node l hl).c (r.node l hl).entry (r.node l hl).st (r.node l hl).ys
          here outFresh ysA thrown TT ∧
        outFresh = passOutFreshChecked G I c.codes (r.node l hl).ans.summaries.toList
          (r.node l hl).c (r.node l hl).node (r.node l hl).entry (r.node l hl).st.stepK
          (SinglePass.derivOf (r.node l hl).c (r.node l hl).node (r.node l hl).st)) :
    ExitsYield ι := by
  intro G I c after admits hp r hchecked η _ ρ0 m l hl
  have hchecks := checks G I c r hchecked l hl
  obtain ⟨here, outFresh, ysA, thrown, TT, hc, hf⟩ := hchecks
  have hsums := (r.node l hl).hstep.summaries (r.node l hl).sums
  have hcodes := codesSound_reassign hp.2.2.1 η
  exact nodeExitsY_of_checks hc hf (r.node l hl).hshape (r.node l hl).wf
    (r.node l hl).width List.nodup_range η (subtypeAnswersAll _ _) hcodes
    (Parametricity.summariesSound_reassign G η I hsums) m

end Assembly
end Verification.TolerantFrames
