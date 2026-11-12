import Verification.Programs.TolerantFramesComposeRunSound

/-! # Tolerant frames: the visit's footprint check read as `BoundChecked`

The visit's step computes whether its footprint check passes (`bounded`
in `SinglePass.visitStep`): under no bound, it passes; under the bound
$`(\Phi, \mathit{ret}, \mathit{exc})`$, at a label of the no-return region
`deadArr` it is `deadNode` with no throw bound, elsewhere `footprintCheck`
at the step's values with the fresh receiver slots, the live handler and
`outFresh` as the step computes them. `passBounded` is that expression
over its values. Proved: (`boundChecked_of_bounded`) where it passes at a
checked node's own values, the node meets `BoundChecked` under the bound
in the region `deadArr.toList`; with the return check's refusal `none`,
`NodePassChecked` (`nodePassChecked_of`). -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules LabelStore

section Bounded
variable {ι : Type} [Labels ι]

/-- **The visit's footprint check** (`SinglePass.visitStep`'s `bounded`)
over its values: the bound, the no-return region `deadArr`, the label,
its node, claim and entry state, the read summaries after the step, the
step's facts and its derivation. -/
def passBounded (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (bound : Option (Footprints.Closed × Bool × Bool)) (deadArr : Array Bool) (l : Nat) (node : Node)
    (c : PointClaim ι) (entry : SinglePass.State) (sums : List (ReadSummary ι)) (stepK : HeapKnowledge.Knowledge)
    (deriv : ProgramCertificates.Evidence ι) : Bool :=
  match bound with
  | none => true
  | some (Φ, ret, exc) =>
    if deadArr.getD l false then
      GraphCode.deadNode G deadArr.toList node (passDeadEvidence c node) && !exc
    else
      footprintCheck G images codes sums Φ (passRecvFresh node entry) c node stepK deriv
        (match node.handler with
          | some t => !deadArr.getD t.label false
          | none => false) exc ret
        (passOutFreshChecked G images codes sums c node entry stepK deriv)

omit [Labels ι] in
theorem passLiveHandler_toList (a : Array Bool) (node : Node) :
    passLiveHandler a.toList node = (match node.handler with
      | some t => !a.getD t.label false
      | none => false) := by
  unfold passLiveHandler
  cases node.handler <;> simp [deadAt_toList]

/-- **The visit's footprint check gives `BoundChecked`**: where
`passBounded` passes at a checked node's own values (its entry, the
answers after its step, its step's facts and derivation), the node meets
`BoundChecked` under every bound `bound` states, in the region
`deadArr.toList`. -/
theorem boundChecked_of_bounded {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {pc : SinglePass.PassChecker G images} {P : ControlFlow.Program} {w : Walk ι} {startNames : List Nat}
    {ctx : Nat → List (Ty ι)} {l : Nat} (r : NodeChecked G images codes pc P w startNames ctx l)
    {bound : Option (Footprints.Closed × Bool × Bool)} {deadArr : Array Bool}
    (hb : passBounded G images codes bound deadArr l r.node r.c r.entry r.ans.summaries.toList r.st.stepK
      (passDerivOf r.c r.node r.st) = true) :
    ∀ Φ fr ex, bound = some (Φ, fr, ex) → BoundChecked r Φ deadArr.toList fr ex := by
  intro Φ fr ex hbd
  subst hbd
  simp only [passBounded] at hb
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · rw [deadAt_toList] at hd
    rw [if_pos hd] at hb
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hb
    exact hb
  · rw [deadAt_toList] at hd
    rw [if_neg (by simp [hd])] at hb
    rw [passLiveHandler_toList]
    exact hb

/-- **The visit's checks give `NodePassChecked`**: the footprint check
passing at the node's own values under the call's bound
(`boundChecked_of_bounded`), and where the call states a postcondition,
the return check at the node's values, and the yields it kept checked. -/
theorem nodePassChecked_of {G : NormalGraph ι} {I : InstanceImageCheck G} {c : Target.RunCall G I}
    {w : Walk ι} {ctx : Nat → List (Ty ι)} {l : Nat}
    (r : NodeChecked G I c.codes c.passChecker c.P w (List.range c.inputs.length) ctx l) {deadArr : Array Bool}
    (hb : passBounded G I c.codes c.bound deadArr l r.node r.c r.entry r.ans.summaries.toList r.st.stepK
      (passDerivOf r.c r.node r.st) = true)
    (hret : c.ensures ≠ [] → ReturnChecked r c.goal c.ensures)
    (hys : ∃ sums : List (ReadSummary ι), SummariesSound G I sums ∧
      NodeYieldChecks G I c.codes sums w (List.range c.inputs.length) c.goal c.ensures l r.node r.c r.entry r.st r.ys) :
    NodePassChecked c deadArr.toList r :=
  ⟨boundChecked_of_bounded r hb, hret, hys⟩

end Bounded

end Verification.TolerantFrames
