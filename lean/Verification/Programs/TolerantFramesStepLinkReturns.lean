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
entry `h₀`), the
node's local safety and a bound `Φ` from `h₀` to the node's entry heap give,
on each exit of a run with budget left, `Φ` from `h₀` to the exit's heap. -/
theorem pass_footprint_exits [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} {j : Sequent ι} {kS : HeapKnowledge.Knowledge} {Φ : Footprints.Closed}
    {F : List Nat} {d : ProgramCertificates.Evidence ι}
    (hwi : passWithin G images codes sums j kS Φ F d = true)
    (hth : passThrows G images codes sums j kS Φ F d = true)
    (hscope : checkScope j.context.length j.term = true)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ : Env} {s : IndexedHeap} {h₀ : Heap} (hF : GraphCode.FreshOk F h₀.length ρ)
    (he : EnvOk G j.context ρ s.n s.W) (hkS : HeapKnowledge.Holds kS ρ s.h)
    (hsafe : Safe (excOf G) (meaning G j.type) s.n s.W s.h (instantiate 0 ρ j.term))
    (h₁ : Φ.Holds h₀ s.h) {k : Nat} {h' : Heap} {t' : Tm}
    (hst : Steps k s.h (instantiate 0 ρ j.term) h' t') (hk : k < s.n) :
    (isVal t' = true → Φ.Holds h₀ h') ∧ (∀ x, Raises t' x → Φ.Holds h₀ h') := by
  refine ⟨fun hv => ?_, fun x hx => ?_⟩
  · have hn := pass_within_normal hwi hscope hcodes hsums hF he hkS s.adm s.ok hsafe
    obtain ⟨s', -, hh, -, -, hq⟩ := run_normal (SafePostExc.of_post (R := fun _ => True) (fun _ => trivial) hn) hst hv hk
    exact pass_within_entry h₁ (hh ▸ hq)
  · have ht := pass_within_throw hth hscope hcodes hsums hF he hkS s.adm s.ok hsafe
    obtain ⟨s', -, hh, -, -, hq⟩ := run_throw ht hst hx hk
    exact pass_within_entry h₁ (hh ▸ hq)

/-- **The pass's footprint check read as its conditions** (`SinglePass.footprintCheck`,
by unfolding): at the node's sequent `j`, `within`, `throws` where a live
handler catches the throw or the bound covers throws, a return's freshness
where the bound requires it, and the term's scope. -/
theorem footprintCheck_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} {Φ : Footprints.Closed} {F : List Nat}
    {c : PointClaim ι} {node : Node} {kS : HeapKnowledge.Knowledge} {d : ProgramCertificates.Evidence ι}
    {liveHandler exc ret outFresh : Bool}
    (h : footprintCheck G images codes sums Φ F c node kS d liveHandler exc ret outFresh = true) :
    passWithin G images codes sums ⟨c.context, node.expression, c.type⟩ kS Φ F d = true ∧
    ((liveHandler || exc) = true → passThrows G images codes sums ⟨c.context, node.expression, c.type⟩ kS Φ F d = true) ∧
    (node.continuation = .ret → ret = true → outFresh = true) ∧
    checkScope c.context.length node.expression = true := by
  have tg : ∀ f : Unit → Bool, (Thunk.mk f).get = f () := fun _ => rfl
  simp only [footprintCheck, tg, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hw, ht⟩, hr⟩, hs⟩ := h
  refine ⟨?_, fun hl => ?_, fun hk hret => ?_, hs⟩
  · simpa [passWithin, passWrites, passDerivChecked, Bool.or_assoc, Bool.and_assoc] using hw
  · rw [hl] at ht
    simp only [passThrows, passWrites, passDerivChecked]
    cases hse : ExpressionEffects.selectedEffect d <;> simp only [hse] at ht ⊢ <;>
      simpa [Bool.or_assoc, Bool.and_assoc] using ht
  · rw [hk] at hr; simpa [hret] using hr

/-- **The footprint check composes the invocation's bound**, from the pass's
function: where `footprintCheck` accepts the node, the fresh receiver slots
`F` hold stores allocated at or past the invocation's entry `h₀`, and the
node's local safety and a bound `Φ` from `h₀` to its entry heap hold, each
run with budget left keeps `Φ` from `h₀` to the heap of its normal exit, and of
its throw where a live handler catches it or the bound covers throws. -/
theorem footprint_exits [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} {Φ : Footprints.Closed} {F : List Nat}
    {c : PointClaim ι} {node : Node} {kS : HeapKnowledge.Knowledge} {d : ProgramCertificates.Evidence ι}
    {liveHandler exc ret outFresh : Bool}
    (hfc : footprintCheck G images codes sums Φ F c node kS d liveHandler exc ret outFresh = true)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ : Env} {s : IndexedHeap} {h₀ : Heap} (hF : GraphCode.FreshOk F h₀.length ρ)
    (he : EnvOk G c.context ρ s.n s.W) (hkS : HeapKnowledge.Holds kS ρ s.h)
    (hsafe : Safe (excOf G) (meaning G c.type) s.n s.W s.h (instantiate 0 ρ node.expression))
    (h₁ : Φ.Holds h₀ s.h) {k : Nat} {h' : Heap} {t' : Tm}
    (hst : Steps k s.h (instantiate 0 ρ node.expression) h' t') (hk : k < s.n) :
    (isVal t' = true → Φ.Holds h₀ h') ∧ ((liveHandler || exc) = true → ∀ x, Raises t' x → Φ.Holds h₀ h') := by
  obtain ⟨hwi, hth, -, hscope⟩ := footprintCheck_sound hfc
  refine ⟨fun hv => ?_, fun hl x hx => ?_⟩
  · have hn := pass_within_normal (j := ⟨c.context, node.expression, c.type⟩) hwi hscope hcodes hsums hF he hkS
      s.adm s.ok hsafe
    obtain ⟨s', -, hh, -, -, hq⟩ := run_normal (SafePostExc.of_post (R := fun _ => True) (fun _ => trivial) hn) hst hv hk
    exact pass_within_entry h₁ (hh ▸ hq)
  · have ht := pass_within_throw (j := ⟨c.context, node.expression, c.type⟩) (hth hl) hscope hcodes hsums hF he hkS
      s.adm s.ok hsafe
    obtain ⟨s', -, hh, -, -, hq⟩ := run_throw ht hst hx hk
    exact pass_within_entry h₁ (hh ▸ hq)

/-- **A plain return's check** (`SinglePass.returnCheck`, by unfolding): where
it refuses nothing, the claim's type is the goal's or empty, so a returned
value of the claim's type is of the goal's (`plain_return`). -/
theorem returnCheck_plain [DecidableEq ι] [Hashable ι] [Instantiates ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {R : Ty ι}
    {a : Tm} {ensures : List HeapKnowledge.IndexFact} {c : PointClaim ι} {l : Nat} {entry : SinglePass.State}
    {store : Store} {result start : Nat} {startNames : List Nat} {argName : Option Nat}
    {yields : List (PromiseCalls.Yield ι)} {debugNode : Nat} {answers : Answered G}
    (h : (returnCheck G images (.plain R) ensures c l entry store result start startNames argName yields debugNode
      answers).1 = none) {n : Nat} {W : WorldT n} {v : Tm} (hv : meaning G c.type n W v) :
    GoalHolds G (.plain R) a n W v := by
  refine plain_return ?_ hv
  unfold returnCheck at h
  dsimp only at h
  generalize (@ite (Option (Option String × Nat))
    ((!ensures.isEmpty && !(ExpressionEffects.emptyType G c.type || c.context.any (ExpressionEffects.emptyType G ·))) = true)
    _ _ none) = post at h
  simp only [Bool.or_eq_true, beq_iff_eq, List.isEmpty_iff]
  by_cases hc : c.type = R
  · exact .inl hc
  · right
    rcases post with _ | ⟨_ | why, _⟩ <;> simp_all

end Returns

end Verification.TolerantFrames
