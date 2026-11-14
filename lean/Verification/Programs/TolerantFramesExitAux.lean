import Verification.Programs.TolerantFramesDriverSettle
import Verification.Programs.TolerantFramesExitVacuity

/-! # Names and freshness used by the exit interpretation -/
namespace Verification.TolerantFrames
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification Footprints HeapObservations PositiveRules HeapExpressionRules
open Verification ControlFlow PositiveGraphs PositiveCertificates LabelStore ProgramTyping ProgramCertificates
open CertificateProducer SinglePass

section Aux
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

omit [Labels ι] in
/-- Restating yields at aliases preserves their meaning. -/
theorem yieldsAtSlots_ok {names : List Nat} {ys : List (PromiseCalls.Yield ι)} {ρ η : Env}
    (hn : SlotsNamed names ρ η) {n W v} (hy : PromiseCalls.YieldsOk G ys ρ n W v) :
    PromiseCalls.YieldsOk G (SinglePass.yieldsAtSlots names ys) ρ n W v := by
  intro y hy' ht hf
  obtain ⟨z, hz, hyz⟩ := List.mem_flatMap.mp hy'
  cases hnm : names[z.target]? with
  | none =>
    simp only [hnm, List.mem_singleton] at hyz
    subst y
    exact hy z hz ht hf
  | some nm =>
    simp only [hnm] at hyz
    obtain ⟨⟨x, j⟩, hj, rfl⟩ := List.mem_map.mp hyz
    obtain ⟨hj, hx⟩ := List.mem_filter.mp hj
    have hget : names[j]? = some x := by
      exact List.mem_zipIdx_iff_getElem?.mp hj
    have he : ρ j = ρ z.target := by
      rw [hn j x hget, hn z.target nm hnm]
      exact congrArg η (beq_iff_eq.mp hx)
    simpa only [he] using hy z hz ht hf

/-- The visit's freshness flag is exactly the checked freshness test. -/
theorem visitStep_outFresh {env : SinglePass.WalkEnv ι G I} {σ : SinglePass.WalkState ι G} {l : Nat}
    {en : SinglePass.Entered ι} {sd : SinglePass.StepDone ι G}
    (h : SinglePass.visitStep G I env σ l en = .ok sd) :
    sd.outFresh = passOutFreshChecked G I env.codes sd.steppedAnswers.summaries.toList env.claimed[l]!
      env.nodes[l]! en.entry sd.st.stepK (SinglePass.derivOf env.claimed[l]! env.nodes[l]! sd.st) := by
  unfold SinglePass.visitStep at h
  repeat' (first | split at h | extract_lets at h)
  all_goals first | cases h | skip
  all_goals rfl

/-- The step's next-name counter is at least its initial counter. -/
theorem StepChecked.fresh_le {pc : PassChecker G I} {codes : CodeEntry ι → Bool}
    {c : PointClaim ι} {node : Node} {entry : SinglePass.State} {ms : List Nat} {fresh : Nat}
    {answers ans : Answered G} {st : Stepped ι}
    (h : StepChecked G I pc codes c node entry ms fresh answers ans st) : fresh ≤ st.fresh := by
  rcases h with ⟨_, _, _, _, hf, _⟩ | ⟨_, _, _, ha, _⟩
  · exact Nat.le_of_eq hf.symm
  · obtain ⟨_, _, _, _, _, hf, _⟩ := ha
    rcases resultOf_cases node.expression entry.names fresh with ⟨_, _, _, hr⟩ | ⟨_, hr⟩
    · exact Nat.le_of_eq (hf.trans hr).symm
    · rw [hf, hr]
      exact Nat.le_succ _

/-- The checked freshness flag guarantees freshness for an actual normal
execution, relative to a mark below its initial heap. -/
theorem passOutFreshChecked_fresh {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    {c : CertificateProducer.PointClaim ι} {node : Node} {entry : SinglePass.State}
    {stepK : HeapKnowledge.Knowledge} {deriv : ProgramCertificates.Evidence ι}
    (hf : passOutFreshChecked G I codes sums c node entry stepK deriv = true)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G I sums)
    {imp : List (PromiseCalls.Implication ι)} {start : List Nat} {ρ : Env} {m : Nat} {s : IndexedHeap}
    (hS : StateHolds G entry imp start ε ρ m s) (he : EnvOk G c.context ρ s.n s.W)
    (hwidth : entry.names.length ≤ c.context.length) (hm : m ≤ s.h.length)
    (hkS : HeapKnowledge.Holds stepK ε ρ s.h) (href : RefsOk s.W (instantiate 0 ρ node.expression))
    {k : Nat} {h' : Heap} {v : Tm}
    (hk : k < s.n) (hst : Steps k s.h (instantiate 0 ρ node.expression) h' v)
    (hv : isVal v = true) : FreshAt m v := by
  rcases passOutFreshChecked_cases hf with hc | ⟨hcf, hdc⟩
  · exact copyFresh hS he hwidth hc hst
  · exact callFresh_of_checked hcf hdc hcodes hsums hm he hkS href k h' v hk hst hv


end Aux
end Verification.TolerantFrames
