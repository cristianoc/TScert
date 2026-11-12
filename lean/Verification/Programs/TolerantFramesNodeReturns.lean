import Verification.Programs.TolerantFramesNodeBound
import Verification.Programs.TolerantFramesWalkReassignWalk

/-! # Tolerant frames: the return check kept along a run

`ReturnsEnsured` (`TolerantFramesGuarantee`) asks, at every node entry where
the pass's typed assertion holds, that every run of the node's term with
budget left to a value at a return meets `ensures` at the value and the
entry values `ρ0`. The pass's return check (`SinglePass.returnCheck`, at a
node whose continuation is a return) accepts where the postcondition is
empty, the claim's type or a context slot's is empty, or `returnEntails`
accepts the output's facts over the result and the tracked inputs
(`returnCheck_ensures`). `returnsEnsured_of` composes it with the step
theorem's normal exit at a checked node (`stepChecked_parts`) and
`pass_return_ensures`; `ReturnChecked.reassign` carries the check to every
reassigned graph. -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules

section Returns
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

/-- The inputs a return's postcondition tracks (`returnCheck`'s `tracked`):
each named input's start name at a slot of the entry's names. -/
def passTracked (ensures : List HeapKnowledge.IndexFact) (entry : SinglePass.State) (startNames : List Nat) :
    GraphCode.Tracked :=
  (GraphCode.namedInputs ensures).filterMap fun (_, q) => do
    let nm ← startNames[q]?
    let j ← entry.names.idxOf? nm
    pure (j, q)

omit [DecidableEq ι] [Hashable ι] [Instantiates ι] in
/-- Each tracked slot holds the start name of the input it tracks. -/
theorem passTracked_names {ensures : List HeapKnowledge.IndexFact} {entry : SinglePass.State}
    {startNames : List Nat} :
    ∀ p ∈ passTracked ensures entry startNames, ∃ nm, startNames[p.2]? = some nm ∧ entry.names[p.1]? = some nm := by
  intro p hp
  simp only [passTracked, List.mem_filterMap] at hp
  obtain ⟨⟨_, q⟩, -, hq⟩ := hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hq
  obtain ⟨nm, hnm, j, hj, rfl⟩ := hq
  obtain ⟨hlt, heq, -⟩ := List.idxOf?_eq_some_iff.mp hj
  exact ⟨nm, hnm, by simp [List.getElem?_eq_getElem hlt, heq]⟩

/-- **The return check read for the postcondition** (`SinglePass.returnCheck`,
by unfolding): where it refuses nothing, the postcondition is empty, the
claim's type or a context slot's is empty, or `returnEntails` accepts the
output's facts over the result and the tracked inputs. -/
theorem returnCheck_ensures {G : NormalGraph ι} {images : InstanceImageCheck G} {goal : Goal ι}
    {ensures : List HeapKnowledge.IndexFact} {c : PointClaim ι} {l : Nat} {entry : SinglePass.State}
    {store : Store} {result start : Nat} {startNames : List Nat} {argName : Option Nat}
    {yields : List (PromiseCalls.Yield ι)} {debugNode : Nat} {answers : Answered G}
    (h : (returnCheck G images goal ensures c l entry store result start startNames argName yields debugNode
      answers).1 = none) :
    ensures = [] ∨ ExpressionEffects.emptyType G c.type = true ∨
      c.context.any (ExpressionEffects.emptyType G ·) = true ∨
      GraphCode.returnEntails (KnowledgeExpand.expandLinks
        (HeapKnowledge.setsCtx (HeapKnowledge.typeSets G c.context) 1)
        (materialize ⟨result :: entry.names, store, []⟩ (c.context.length + 1)
          (0 :: (passTracked ensures entry startNames).map (·.1 + 1)) false).1)
        (passTracked ensures entry startNames) ensures = true := by
  by_cases hc : (!ensures.isEmpty && !(ExpressionEffects.emptyType G c.type ||
      c.context.any (ExpressionEffects.emptyType G ·))) = true
  · right; right; right
    cases hn : GraphCode.returnEntails (KnowledgeExpand.expandLinks
        (HeapKnowledge.setsCtx (HeapKnowledge.typeSets G c.context) 1)
        (materialize ⟨result :: entry.names, store, []⟩ (c.context.length + 1)
          (0 :: (passTracked ensures entry startNames).map (·.1 + 1)) false).1)
        (passTracked ensures entry startNames) ensures with
    | true => rfl
    | false =>
      unfold returnCheck at h
      simp only [hc, ite_true] at h
      unfold passTracked at hn
      simp only [hn, Bool.not_false, ite_true] at h
      cases h
  · simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, Bool.or_eq_false_iff,
      not_and, ne_eq] at hc
    by_cases he : ensures = []
    · exact .inl he
    · rcases Bool.eq_false_or_eq_true (ExpressionEffects.emptyType G c.type) with h1 | h1
      · exact .inr (.inl h1)
      · rcases Bool.eq_false_or_eq_true (c.context.any (ExpressionEffects.emptyType G ·)) with h2 | h2
        · exact .inr (.inr (.inl h2))
        · exfalso; simp_all

/-- **The return check at a checked node** (`run`, a return's checks): at a
node whose continuation is a return, `returnCheck` at the step's values
refuses nothing. -/
def ReturnChecked {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {pc : PassChecker G images} {P : ControlFlow.Program} {w : Walk ι} {startNames : List Nat}
    {ctx : Nat → List (Ty ι)} {l : Nat} (r : NodeChecked G images codes pc P w startNames ctx l)
    (goal : Goal ι) (ensures : List HeapKnowledge.IndexFact) : Prop :=
  r.node.continuation = .ret → ∃ (start : Nat) (argName : Option Nat) (yields : List (PromiseCalls.Yield ι))
    (debugNode : Nat) (answers : Answered G),
    (returnCheck G images goal ensures r.c l r.entry r.st.store r.st.result start startNames argName yields
      debugNode answers).1 = none

/-- **The return check at a reassigned graph** (`returnCheck_reassign`, the
answers reassigned). -/
theorem ReturnChecked.reassign {G : NormalGraph ι} {η : MixedAssignment ι} {images : InstanceImageCheck G}
    {codes : CodeEntry ι → Bool} {pc : PassChecker G images}
    {pc' : PassChecker (PositiveRules.reassign G η) (images.reassign η)} {P : ControlFlow.Program} {w : Walk ι}
    {startNames : List Nat} {ctx : Nat → List (Ty ι)} {l : Nat} (hpc : PassCheckerReassign G η images pc pc')
    {r : NodeChecked G images codes pc P w startNames ctx l} {goal : Goal ι} {ens : List HeapKnowledge.IndexFact}
    (h : ReturnChecked r goal ens) : ReturnChecked (nodeChecked_reassign hpc r) goal ens := by
  intro hret
  obtain ⟨start, argName, yields, debugNode, answers, hr⟩ := h hret
  refine ⟨start, argName, yields, debugNode, Answered.reassign answers η, ?_⟩
  show (returnCheck (PositiveRules.reassign G η) (images.reassign η) goal ens r.c l r.entry r.st.store
    r.st.result start startNames argName yields debugNode (Answered.reassign answers η)).1 = none
  rw [returnCheck_reassign]
  exact hr

/-- **The return check establishes `ensures` at every node**
(`ReturnsEnsured`): where every visited node is checked (`NodeChecked`), its
entry state holds where the typed node assertion does, its return check
refused nothing at each return (`ReturnChecked`) and the codes are sound,
every run of a node's term to a value at a return meets `ensures` at the
value and the entry values: the state after the step
(`stepChecked_parts`) gives it where `returnEntails` accepts
(`pass_return_ensures`, the tracked slots holding the inputs' start names,
`passTracked_names`); an empty result type admits no value; an empty
context type no environment. -/
theorem returnsEnsured_of {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {pc : PassChecker G images} {P : ControlFlow.Program} {w : Walk ι} {startNames : List Nat} {ρ0 : Env}
    {ctx : Nat → List (Ty ι)} {m : Nat} {goal : Goal ι} {ens : List HeapKnowledge.IndexFact}
    (hacc : ∀ l, w.visited l → ∃ r : NodeChecked G images codes pc P w startNames ctx l,
      (∀ ρ (s : IndexedHeap), passPreT G w startNames ρ0 ctx l ρ m s →
        StateHolds G r.entry (w.implies l) startNames ρ0 ρ m s) ∧ ReturnChecked r goal ens)
    (hcodes : CodesSound G codes) :
    ReturnsEnsured P G w startNames ρ0 ctx ens m := by
  intro l ρ s hp _
  obtain ⟨na, hent, hrc⟩ := hacc l hp.1.1
  have hS := hent ρ s hp
  have he : EnvOk G na.c.context ρ s.n s.W := na.hctx ▸ hp.2
  obtain ⟨-, -, -, cn, ce, hj, hn, hx⟩ :=
    stepChecked_parts na.hstep hS na.wf na.below na.width he hcodes na.sums
  have hex := (stepExits_of hj hn hx).2
  refine ⟨na.node, na.hP, fun k h' t' hst hk => ⟨fun hv => ?_, fun e _ => ?_⟩⟩
  · obtain ⟨s', ha, hh, -, hT, -, hF⟩ := (hex k h' t' hst hk).1 hv
    refine contKeeps_of (fun _ _ _ => trivial) fun hret => ?_
    obtain ⟨start, argName, yields, debugNode, answers, hr⟩ := hrc hret
    have he' := envOk_admissible ha.1 he
    rcases returnCheck_ensures hr with hnil | hempty | hctxe | hc
    · subst hnil; intro F hF'; cases hF'
    · exact (ExpressionEffects.emptyType_sound hempty hT).elim
    · obtain ⟨A, hA, hnil⟩ := List.any_eq_true.mp hctxe
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hA
      exact (ExpressionEffects.emptyType_sound hnil (he'.2 i A hi)).elim
    · rw [← hh]
      exact pass_return_ensures hF he' passTracked_names hc
  · cases na.node.handler <;> trivial

end Returns

end Verification.TolerantFrames
