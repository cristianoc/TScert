import Verification.Programs.TolerantFramesExitChecks
import Verification.Programs.TolerantFramesExitAux

/-! # Exit delivery from the checked step's execution

The normal exit assertion retains an execution within the initial budget
and the entry mark's bound. The checked freshness flag therefore supplies
`AfterStep`'s freshness premise.
-/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules LabelStore

section Execution
variable {ι : Type} [Labels ι]

/-- Checked exits deliver from an actual step execution, including the
freshness of a newly allocated result. -/
theorem nodeExitsY_of_checks {G : NormalGraph ι} {images : InstanceImageCheck G} {w : Walk ι}
    {startNames : List Nat} {ρ0 : Env} {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge}
    {given : Nat → Bool}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {l : Nat} {node : Node} {c : PointClaim ι} {entry : SinglePass.State} {st : Stepped ι}
    {ys : List (PromiseCalls.Yield ι)} {here outFresh : Bool} {ysA : List (PromiseCalls.Yield ι)} {thrown : Nat}
    {TT : Ty ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} {deriv : ProgramCertificates.Evidence ι}
    (η : MixedAssignment ι)
    (hc : NodeExitsChecked (reassign G η) (images.reassign η) w startNames ctx stated given edgesIn l node c entry st ys
      here outFresh ysA thrown TT)
    (hf : outFresh = passOutFreshChecked G images codes sums c node entry st.stepK deriv)
    (hshape : SinglePass.passShapeCheck' G c.type node.continuation = true) (wf : StoreWF entry.store)
    (hwidth : entry.names.length ≤ c.context.length) (hnd : startNames.Nodup)
    (hsub : SubtypeAnswersSound (reassign G η) (images.reassign η))
    (hcodes : CodesSound (reassign G η) codes) (hsums : SummariesSound (reassign G η) (images.reassign η) sums)
    (m : Nat) :
    NodeExitsY (reassign G η) w startNames ρ0 ctx stated given edgesIn m l node c entry st ys := by
  have hshape' : SinglePass.passShapeCheck' (reassign G η) c.type node.continuation = true := by
    rw [passShapeCheck'_reassign]; exact hshape
  have hd := nodeExitsYF_of_checks hc hshape' wf hnd hsub (ρ0 := ρ0) m
  refine ⟨?_, hd.handler⟩
  intro t pushed observed promote hmem ρ s hS he hkS hm s' v hv hF he' ho
  obtain ⟨hS', hy, hout, k, hk, hrun⟩ := hF
  apply hd.exits t pushed observed promote hmem ρ s' v hv _ he' ho
  refine ⟨hS', hy, hout, fun hfr _ => ?_⟩
  have hfr' : passOutFreshChecked (reassign G η) (images.reassign η) codes sums c node entry st.stepK deriv = true := by
    rw [passOutFreshChecked_reassign, ← hf]
    exact hfr
  exact passOutFreshChecked_fresh hfr' hcodes hsums hS he hwidth hm hkS hk hrun hv

end Execution
end Verification.TolerantFrames
