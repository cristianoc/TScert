import Verification.Programs.TolerantFramesDriverSettle

/-! # Names and freshness used by the exit interpretation -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations PositiveRules HeapExpressionRules
open Verification ControlFlow PositiveGraphs PositiveCertificates LabelStore ProgramTyping ProgramCertificates

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

/-- The checked freshness flag guarantees freshness for an actual normal
execution, relative to a mark below its initial heap. -/
theorem passOutFreshChecked_fresh {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    {c : CertificateProducer.PointClaim ι} {node : Node} {entry : SinglePass.State}
    {stepK : HeapKnowledge.Knowledge} {deriv : ProgramCertificates.Evidence ι}
    (hf : passOutFreshChecked G I codes sums c node entry stepK deriv = true)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G I sums)
    {imp : List (PromiseCalls.Implication ι)} {start : List Nat} {E ρ : Env} {m : Nat} {s : IndexedHeap}
    (hS : StateHolds G entry imp start E ρ m s) (he : EnvOk G c.context ρ s.n s.W)
    (hwidth : entry.names.length ≤ c.context.length) (hm : m ≤ s.h.length)
    (hkS : HeapKnowledge.Holds stepK ρ s.h) {k : Nat} {h' : Heap} {v : Tm}
    (hk : k < s.n) (hst : Steps k s.h (instantiate 0 ρ node.expression) h' v)
    (hv : isVal v = true) : FreshAt m v := by
  rcases passOutFreshChecked_cases hf with hc | ⟨hcf, hdc⟩
  · exact copyFresh hS he hwidth hc hst
  · exact callFresh_of_checked hcf hdc hcodes hsums hm he hkS k h' v hk hst hv

/-- A successful entry exposes exactly the cached unsatisfiability answer it uses. -/
theorem visitEntry_here {env : SinglePass.WalkEnv ι G I} {σ : SinglePass.WalkState ι G} {l : Nat}
    {en : SinglePass.Entered ι} (h : SinglePass.visitEntry G I env σ l = .ok en) :
    en.here = (σ.unsat[l]!).getD (ControlFlow.unsatisfiable G (env.claimed[l]!).context) := by
  unfold SinglePass.visitEntry at h
  repeat' (first | split at h | extract_lets at h)
  all_goals first | cases h | skip
  all_goals simp_all only [Option.getD_some, Option.getD_none] <;> rfl

end Aux
end Verification.TolerantFrames
