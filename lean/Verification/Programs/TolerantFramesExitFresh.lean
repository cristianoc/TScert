import Verification.Programs.TolerantFramesExitAux

/-! # Tolerant frames: a run's values meet what every terminating run's value meets

`passOutFreshChecked_fresh` states the step's result fresh for every
normal run of the node's term within the step index; the exits read that
freshness from the state after the step. Proved
(`SafePostExc.and_steps`): a safe run whose every terminating run ends in a
value meeting `P` is safe with each returned value also meeting `P`; so the
step's judgment carries the result's freshness (`stepFresh_judgment`). -/
namespace Verification.TolerantFrames
open Verification HeapObservations PositiveRules

/-- **A property of every terminating run's value joins the returned
value's type**: `SafePostExc` with `T` strengthened by `P`, where every run
of fewer steps than the index ending in a value meets `P`. -/
theorem SafePostExc.and_steps {Ξ T : Fam} {Q : Post} {R : Heap → Prop} {P : Tm → Prop} :
    ∀ {n W h t}, SafePostExc Ξ T Q R n W h t →
      (∀ k h' v, k < n → Steps k h t h' v → isVal v = true → P v) →
      SafePostExc Ξ (fun j U u => T j U u ∧ P u) Q R n W h t := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ p ih =>
    intro W h t hs hP
    rcases hs with ((⟨hv, hT, hQ⟩ | ⟨hr, hR⟩) | ⟨U, h', t', hx, hu, hst, hok, hc⟩)
    · exact .inl (.inl ⟨hv, ⟨hT, hP 0 h t (Nat.succ_pos _) .refl hv⟩, hQ⟩)
    · exact .inl (.inr ⟨hr, hR⟩)
    · exact .inr ⟨U, h', t', hx, hu, hst, hok,
        ih hc fun k h'' v hk hs hv => hP (k + 1) h'' v (Nat.succ_lt_succ hk) (.next hst hs) hv⟩

section Fresh
open Footprints HeapExpressionRules ControlFlow PositiveGraphs PositiveCertificates LabelStore ProgramTyping ProgramCertificates CertificateProducer
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

/-- **The step's judgment with its result's freshness**: where the step's
freshness test passes (`passOutFreshChecked`, the visit's `outFresh` by
`visitStep_outFresh`), every value the node's term returns is fresh at a
mark below the heap (`passOutFreshChecked_fresh`). -/
theorem stepFresh_judgment {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    {c : CertificateProducer.PointClaim ι} {node : Node} {entry : SinglePass.State}
    {stepK : HeapKnowledge.Knowledge} {deriv : ProgramCertificates.Evidence ι}
    (hf : passOutFreshChecked G I codes sums c node entry stepK deriv = true)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G I sums)
    {imp : List (PromiseCalls.Implication ι)} {start : List Nat} {E ρ : Env} {m : Nat} {s : IndexedHeap}
    (hS : StateHolds G entry imp start E ρ m s) (he : EnvOk G c.context ρ s.n s.W)
    (hwidth : entry.names.length ≤ c.context.length) (hm : m ≤ s.h.length)
    (hkS : HeapKnowledge.Holds stepK ρ s.h) {T : Fam} {Q : Post} {R : Heap → Prop}
    (hj : SafePostExc (excOf G) T Q R s.n s.W s.h (instantiate 0 ρ node.expression)) :
    SafePostExc (excOf G) (fun j U u => T j U u ∧ FreshAt m u) Q R s.n s.W s.h (instantiate 0 ρ node.expression) :=
  SafePostExc.and_steps hj fun _ _ _ hk hst hv => passOutFreshChecked_fresh hf hcodes hsums hS he hwidth hm hkS hk hst hv

end Fresh

end Verification.TolerantFrames
