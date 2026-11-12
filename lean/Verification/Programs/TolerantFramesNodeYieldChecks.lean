import Verification.Programs.TolerantFramesNodeRefined
import Verification.Programs.TolerantFramesNodeReturns

/-! # Tolerant frames: a node's yield checks at every reassignment

`run` keeps a node's yields only where `checkedYields` keeps them (at a
promise call behind `promiseDerivChecked`), and at a return checks them
with `returnCheck`. What it checks is stated over the pass's functions at
`G` (`NodeYieldChecks`); the graph theorem reads it at every reassigned
graph, where the same functions give the same results
(`derivChecked_reassign`, `promiseDerivChecked_reassign`,
`checkedYields_reassign`, `returnCheck_reassign`), so the checks hold there
too (`NodeYieldChecks.reassign`). -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules

section Reassign
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι] (G : NormalGraph ι) (η : MixedAssignment ι)
  (images : InstanceImageCheck G)

omit [Hashable ι] [Instantiates ι] in
/-- **The derivation check at a reassignment.** -/
theorem derivChecked_reassign (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) (c : PointClaim ι)
    (node : Node) (stepK : HeapKnowledge.Knowledge) (deriv : ProgramCertificates.Evidence ι) :
    derivChecked (reassign G η) (images.reassign η) codes sums c node stepK deriv =
      derivChecked G images codes sums c node stepK deriv := by
  simp only [derivChecked, Parametricity.checkTree_reassign, Parametricity.requiresTree_reassign]

omit [Hashable ι] [Instantiates ι] in
/-- **The promise check at a reassignment.** -/
theorem promiseDerivChecked_reassign (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι))
    (c : PointClaim ι) (node : Node) (stepK : HeapKnowledge.Knowledge) (deriv : ProgramCertificates.Evidence ι) :
    promiseDerivChecked (reassign G η) (images.reassign η) codes sums c node stepK deriv =
      promiseDerivChecked G images codes sums c node stepK deriv := by
  simp only [promiseDerivChecked, derivChecked_reassign]

omit [Hashable ι] [Instantiates ι] in
/-- **The kept yields at a reassignment** (`checkedYields`, its promise
check given). -/
theorem checkedYields_reassign (Γ : List (Ty ι)) (A : Ty ι) (xs : List (PromiseCalls.Implication ι))
    (k out : HeapKnowledge.Knowledge) (e : ProgramCertificates.Evidence ι) (t : Tm) (pc : Unit → Bool)
    (ys : List (PromiseCalls.Yield ι)) :
    checkedYields (reassign G η) (images.reassign η) Γ A xs k out e t pc ys =
      checkedYields G images Γ A xs k out e t pc ys := by
  simp only [checkedYields, Parametricity.promiseOf_reassign, Parametricity.yieldFollows_reassign,
    Parametricity.withStable_reassign]
  rfl

end Reassign

section Checks
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

/-- **What `run` checks of a node's kept yields and its return** (read off
the visit): the yields `ys` none, or those `checkedYields` keeps at the
implications `slotImplOf entry.names xs` for `xs` among the label's, the
step's facts and output, a derivation `deriv` and the pass's promise check
(`SinglePass.promiseDerivChecked`) over a summary table `sums'` within
`sums`; at a return, `returnCheck` refusing nothing at `ys`, with the
promised argument's name the start name of the goal's slot. -/
structure NodeYieldChecks (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) (w : Walk ι) (startNames : List Nat) (goal : Goal ι)
    (ensures : List HeapKnowledge.IndexFact) (l : Nat) (node : Node) (c : PointClaim ι) (entry : SinglePass.State)
    (st : Stepped ι) (ys : List (PromiseCalls.Yield ι)) : Prop where
  kept : ys = [] ∨ ∃ (xs : List (PromiseCalls.Implication ι)) (deriv : ProgramCertificates.Evidence ι)
    (ys0 : List (PromiseCalls.Yield ι)) (sums' : List (ReadSummary ι)), (∀ x ∈ xs, x ∈ w.implies l) ∧
    (∀ s ∈ sums', s ∈ sums) ∧
    ys = checkedYields G images c.context c.type (slotImplOf entry.names xs) st.stepK st.stepOut deriv
      node.expression (fun _ => SinglePass.promiseDerivChecked G images codes sums' c node st.stepK deriv) ys0
  ret : node.continuation = .ret → ∃ start argName debugNode answers,
    (returnCheck G images goal ensures c l entry st.store st.result start startNames argName ys debugNode
      answers).1 = none ∧ argName = goal.slot.bind (startNames[·]?)

/-- **The yield checks at a reassignment**: the same yields kept and the
return check refusing nothing there, its answers reassigned. -/
theorem NodeYieldChecks.reassign {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} {w : Walk ι} {startNames : List Nat} {goal : Goal ι}
    {ensures : List HeapKnowledge.IndexFact} {l : Nat} {node : Node} {c : PointClaim ι} {entry : SinglePass.State}
    {st : Stepped ι} {ys : List (PromiseCalls.Yield ι)}
    (h : NodeYieldChecks G images codes sums w startNames goal ensures l node c entry st ys) (η : MixedAssignment ι) :
    NodeYieldChecks (reassign G η) (images.reassign η) codes sums w startNames goal ensures l node c entry st ys where
  kept := by
    rcases h.kept with h0 | ⟨xs, deriv, ys0, sums', hx, hs, rfl⟩
    · exact .inl h0
    · refine .inr ⟨xs, deriv, ys0, sums', hx, hs, ?_⟩
      simp only [promiseDerivChecked_reassign, checkedYields_reassign]
  ret hk := by
    obtain ⟨start, argName, debugNode, answers, hr, harg⟩ := h.ret hk
    refine ⟨start, argName, debugNode, Answered.reassign answers η, ?_, harg⟩
    rw [returnCheck_reassign]
    exact hr

end Checks

end Verification.TolerantFrames
