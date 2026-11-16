import Verification.Programs.TolerantFramesNamed

/-! # Tolerant frames: both exits of a step of empty normal effect

The pass applies a step's output with the frame of the facts it was not
handed (`applyDelta … true`) where the step's normal effect, as the rule
deciding it states it (`Checker.normal`, proved by `Checker.normal_sound`), is
`{values: keep, spines: keep}`: the tolerant frame at the support `all` keeps
every fact there (`named_keep_box`). This module states both exits of such a
step: the action, the residual budget, the type, the rule's output, and the
store's facts at the name valuation (`preserving_step_frame`). -/
namespace Verification.TolerantFrames
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification Footprints HeapObservations
open Verification.SinglePass (Atom)

section Steps
variable {ι : Type} [DecidableEq ι]
open ProgramTyping PositiveCertificates ProgramCertificates PositiveGraphs PositiveRules HeapExpressionRules

/-! ## Both exits of a preserving step -/

/-- **The selective frame at a preserving step, both exits.** A step whose
normal exit keeps the heap (`KeepsPost`) and whose checker's `run` accepted
it with output `out`, from the facts `k` handed to its rule and the store's
facts `S` at the name valuation `η`: a normal return is an action of
`{values: keep, spines: keep}` with the residual budget, the result's type,
the rule's output, and every fact of `S`, handed or not, at `η[r ↦ v]`; a
throw is an action of `{values: any, spines: any}` with the raised value
closed and of the exception family and the facts of `S` reading no heap. -/
theorem preserving_step_frame {G : NormalGraph ι} {images : InstanceImageCheck G} (checker : Checker G images)
    {j : Sequent ι} {kn out : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)}
    (hr : (checker.run j kn e codes sums).value = some out)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ η : Env} {r m : Nat} {s : IndexedHeap} {S : List Atom}
    (he : EnvOk G j.context ρ s.n s.W) (hkn : HeapKnowledge.Holds kn ε ρ s.h) (hρ : RootsOk s.W ρ)
    (hkeep : KeepsPost G j ρ s.n s.W s.h)
    (hS : Named ε S η ρ m s) (hfr : ∀ a ∈ S, r ∉ a.names)
    {k : Nat} {h' : Heap} {t' : Tm} (hst : Steps k s.h (instantiate 0 ρ j.term) h' t') (hk : k < s.n) :
    (isVal t' = true → ∃ s' : IndexedHeap, Action Footprints.Closed.empty.fp ρ s s' ∧ s'.h = h' ∧
        s'.n + k = s.n ∧ meaning G j.type s'.n s'.W t' ∧
        HeapKnowledge.Holds out ε (push t' ρ) h' ∧ Named ε S (Env.set η r t') ρ m s') ∧
      (∀ x, Raises t' x → ∃ s' : IndexedHeap, Action Footprints.Closed.top.fp ρ s s' ∧ s'.h = h' ∧
        s'.n + k = s.n ∧ Scoped 0 x ∧ excOf G s'.n s'.W x ∧ Named ε (S.filter (·.heapFree)) η ρ m s') := by
  have hout := checker.sound hr hcodes hsums he hkn s.adm s.ok (SafePostW.refs hkeep) hρ
  have hboth := cross_upto s.n (fun _ _ _ _ _ _ _ _ hb _ => hb) s.W s.W s.h _ s.ok s.ok hkeep hout
  have hj : SafePost (excOf G) (meaning G j.type)
      (fun h' v => Footprints.Closed.empty.Holds s.h h' ∧ HeapKnowledge.Holds out ε (push v ρ) h') s.n s.W s.h
      (instantiate 0 ρ j.term) := weaken (fun _ _ hq => ⟨hq.1.1, hq.2⟩) hboth
  refine ⟨fun hv => ?_, fun x hx => preserving_throw hj hst hx hk hS⟩
  obtain ⟨s', ha, he', hn, hT, hq, hS'⟩ := preserving_normal (Footprints.Closed.empty_le _) hj hst hv hk hS hfr
  exact ⟨s', ha, he', hn, hT, hq, hS'⟩

end Steps

end Verification.TolerantFrames
