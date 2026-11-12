import Verification.Programs.TolerantFramesEdge

/-! # Tolerant frames: the pass's return and footprint checks at a step

What `SinglePass.run`'s checks at a node give, read off the step theorem's
exits (`checkedStep_sound`):

- the return check (`SinglePass.lean` 1668–1681): a plain goal's type
  (`plain_return`), and `ensures` over the inputs' entry values from the
  state after the step (`pass_return_ensures`);
- the footprint check (lines 1596–1631): the node's exits within the
  invocation's bound from the invocation's entry heap, normal and
  exceptional (`pass_footprint_exits`). -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules

section Returns
variable {ι : Type}

/-! ## The return check -/

/-- **A plain goal's return** (line 1681): the claim's type is the goal's,
or no value has it. -/
theorem plain_return [DecidableEq ι] {G : NormalGraph ι} {A R : Ty ι} {n : Nat} {W : WorldT n} {v : Tm}
    (hc : (A == R || A.isEmpty) = true) (hv : meaning G A n W v) : meaning G R n W v := by
  simp only [Bool.or_eq_true, beq_iff_eq, List.isEmpty_iff] at hc
  rcases hc with rfl | rfl
  · exact hv
  · obtain ⟨a, ha, -⟩ := hv; exact absurd ha (List.not_mem_nil)

/-- The context at the pushed slots (`setsCtx … 1`, line 1676) holds of the
pushed environment where the node's context types the node's. -/
theorem setsCtx_push_ok {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ : Env} {n : Nat} {W : WorldT n}
    (he : EnvOk G Γ ρ n W) (v : Tm) :
    KnowledgeNormal.CtxOk (HeapKnowledge.setsCtx (HeapKnowledge.typeSets G Γ) 1) (push v ρ) := by
  intro i C hC
  simp only [HeapKnowledge.setsCtx] at hC
  split at hC
  · cases hC
  · rename_i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hC
    simpa [push] using HeapKnowledge.typeSets_mem he hC

/-- **`ensures` at a return** (lines 1668–1679): where `returnEntails`
accepts the output's facts over the result and the tracked slots, each
tracked slot `j` holding the name of the start's input `q`, the state after
the step gives `ensures` at the result and the invocation's entry values `E`. -/
theorem pass_return_ensures {G : NormalGraph ι} {Γ : List (Ty ι)} {entry : SinglePass.State} {store : Store}
    {result width : Nat} {tracked : GraphCode.Tracked} {ens : List HeapKnowledge.IndexFact}
    {I : List (PromiseCalls.Implication ι)} {startNames : List Nat} {E ρ : Env} {v : Tm} {m : Nat}
    {s : IndexedHeap}
    (hS : StateHolds G ⟨result :: entry.names, store, entry.fresh⟩ I startNames E (push v ρ) m s)
    (he : EnvOk G Γ ρ s.n s.W)
    (htr : ∀ p ∈ tracked, ∃ nm, startNames[p.2]? = some nm ∧ entry.names[p.1]? = some nm)
    (hc : GraphCode.returnEntails (KnowledgeExpand.expandLinks
      (HeapKnowledge.setsCtx (HeapKnowledge.typeSets G Γ) 1)
      (materialize ⟨result :: entry.names, store, []⟩ (width + 1) (0 :: tracked.map (·.1 + 1)) false).1)
      tracked ens = true) :
    GraphCode.EnsuresAt ens s.h (push v E) := by
  have hk := stateHolds_materialize (stateHolds_noFresh hS) (width + 1) (0 :: tracked.map (·.1 + 1)) true
  obtain ⟨η, hn, -, -, -, hst⟩ := hS
  refine GraphCode.returnEntails_sound hc (KnowledgeExpand.expandLinks_holds (setsCtx_push_ok he v) hk) ?_
  intro p hp
  obtain ⟨nm, hq, hj⟩ := htr p hp
  rw [← hst p.2 nm hq]
  simpa [push] using hn (p.1 + 1) nm (by simpa using hj)

/-! ## The footprint check -/

/-- **The footprint check composes the invocation's bound** (lines
1596–1631): where the pass's `within` and `throws` hold at the node (with the
fresh receiver slots `F` holding stores allocated at or past the invocation's
entry `h₀`, and the selected signature's claim at the node's context), the
node's local safety and a bound `Φ` from `h₀` to the node's entry heap give,
on each exit of a run with budget left, `Φ` from `h₀` to the exit's heap. -/
theorem pass_footprint_exits [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} {j : Sequent ι} {kS : HeapKnowledge.Knowledge} {Φ : Footprints.Closed}
    {F : List Nat} {d : ProgramCertificates.Evidence ι}
    (hwi : passWithin G images codes sums j kS Φ F d = true)
    (hth : passThrows G images codes sums j kS Φ F d = true)
    (hctx : GraphCode.selectedWithinAt Φ F d = true → DerivContext j d)
    (hscope : checkScope j.context.length j.term = true)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ : Env} {s : IndexedHeap} {h₀ : Heap} (hF : GraphCode.FreshOk F h₀.length ρ)
    (he : EnvOk G j.context ρ s.n s.W) (hkS : HeapKnowledge.Holds kS ρ s.h)
    (hsafe : Safe (excOf G) (meaning G j.type) s.n s.W s.h (instantiate 0 ρ j.term))
    (h₁ : Φ.Holds h₀ s.h) {k : Nat} {h' : Heap} {t' : Tm}
    (hst : Steps k s.h (instantiate 0 ρ j.term) h' t') (hk : k < s.n) :
    (isVal t' = true → Φ.Holds h₀ h') ∧ (∀ x, Raises t' x → Φ.Holds h₀ h') := by
  refine ⟨fun hv => ?_, fun x hx => ?_⟩
  · have hn := pass_within_normal hwi hctx hscope hcodes hsums hF he hkS s.adm s.ok hsafe
    obtain ⟨s', -, hh, -, -, hq⟩ := run_normal (SafePostExc.of_post (R := fun _ => True) (fun _ => trivial) hn) hst hv hk
    exact pass_within_entry h₁ (hh ▸ hq)
  · have ht := pass_within_throw hth hctx hscope hcodes hsums hF he hkS s.adm s.ok hsafe
    obtain ⟨s', -, hh, -, -, hq⟩ := run_throw ht hst hx hk
    exact pass_within_entry h₁ (hh ▸ hq)

end Returns

end Verification.TolerantFrames
