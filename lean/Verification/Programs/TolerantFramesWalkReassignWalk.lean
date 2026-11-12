import Verification.Programs.TolerantFramesWalkReassignStep
import Verification.Programs.TolerantFramesNodeWalk

/-! # Tolerant frames: the walk at a reassignment from one run

The step theorem from a step accepted with its searches as oracles
(`stepChecked_parts`, `stepChecked_sound`: `checkedStep_parts` and
`checkedStep_sound` with `StepChecked` in place of the step's equation), so
that a node's step at `reassign G η` is stated without the searches run
there. `NodeChecked` is `NodeRan` with the step's equation replaced by
`StepChecked`; `nodeChecked_reassign` carries a node checked at `G` to
`reassign G η`, and `run_guarantee_of_checked` gives `GraphGuarantee` from
one run at `G`, the checker at each admitted assignment
(`PassCheckerReassign`) and `run_traversed`'s statement at the reassigned
graph over `NodeChecked`. -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules

section StepTheorem
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

omit [Instantiates ι] in
/-- **The step theorem, in parts, with the searches as oracles**: the
conclusion of `checkedStep_parts` from `StepChecked`. -/
theorem stepChecked_parts {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {pc : PassChecker G images} {node : Node} {c : PointClaim ι} {entry : SinglePass.State} {ms : List Nat}
    {fresh : Nat} {answers : Answered G} {st : Stepped ι} {ans : Answered G}
    (h : StepChecked G images pc codes c node entry ms fresh answers ans st)
    {I : List (PromiseCalls.Implication ι)} {start : List Nat} {E ρ : Env} {m : Nat} {s : IndexedHeap}
    (hS : StateHolds G entry I start E ρ m s) (w : StoreWF entry.store) (hnb : NamesBelow entry I start fresh)
    (hwidth : entry.names.length ≤ c.context.length)
    (he : EnvOk G c.context ρ s.n s.W) (hcodes : CodesSound G codes)
    (hsum : SummariesSound G images answers.summaries.toList) :
    SummariesSound G images ans.summaries.toList ∧ HeapKnowledge.Holds st.stepK ρ s.h ∧
    ((st.result ∈ entry.names ∧ st.fresh = fresh) ∨ (st.result = fresh ∧ st.fresh = fresh + 1)) ∧
    ∃ cn ce : Footprints.Closed, StepParts G c.type cn ce node.expression st.stepOut
      (StateHolds G ⟨st.result :: entry.names, st.store, entry.fresh⟩ I start E)
      (StateHolds G ⟨entry.names, entry.store.dropHeap (fun _ => false), entry.fresh⟩ I start E) ρ m s := by
  have hS' := hS
  obtain ⟨η, hn, hst, hI, hF, hstart⟩ := hS'
  have hk := stateHolds_stepKnowledge hS he c.context.length ms (wholeOf node.expression)
  rcases h with ⟨x, hc, hr, hstore, hfr, -, hK, hO, rfl⟩ |
      ⟨-, effect, a0, ⟨out, pre, hsel, htree, hres, hfresh, -, -, hpres, hwrit⟩, hss⟩
  · -- A copy of slot `i`: the term is the slot's value.
    obtain ⟨i, hi, hty, hx⟩ := copiedOf_some hc
    have hval : instantiate 0 ρ node.expression = ρ i := by rw [hi]; simp [instantiate]
    have hv : isVal (ρ i) = true := (meaning_value (he.2 i _ hty)).1
    refine ⟨hsum, by rw [hK]; exact holds_empty, .inl ⟨hr ▸ List.mem_of_getElem? hx, hfr⟩,
      Footprints.Closed.empty, Footprints.Closed.empty, ⟨?_, ?_, ?_⟩⟩
    · rw [hval, hO]
      exact SafePostExc.value hv (he.2 i _ hty) ⟨Footprints.Closed.holds_empty.mpr (List.prefix_refl _), holds_empty⟩
    · intro k h' v s' hsteps _ ha _ _
      rw [hval] at hsteps
      have hvv := PromiseCalls.steps_value hv hsteps
      subst hvv
      have hηx : η x = ρ i := (hn i x hx).symm
      obtain ⟨-, g2, -⟩ := set_agree (st := entry) (I := I) (start := start) (r := x) (.inr hηx)
      rw [hr, hstore]
      refine stateHolds_pushed hn hI hF hstart ha.1 (.inr hηx) fun a ha' => ?_
      exact (atomHolds_congr fun y hy => (g2 a ha' y hy).symm).mp
        (named_keep_box (Footprints.Closed.empty_le _) hst s' ha a ha')
    · intro s' ha; exact stateHolds_throw hS w ha.1
  · obtain ⟨hs0, hs1⟩ := hss hsum
    -- The result's name: a slot's name its value holds, or the fresh one.
    have hkv : ∀ k h' v, Steps k s.h (instantiate 0 ρ node.expression) h' v →
        NamesBelow entry I start st.result ∨ η st.result = v := by
      intro k h' v hsteps
      rcases resultOf_cases node.expression entry.names fresh with ⟨i, hi, hx, -⟩ | ⟨hr1, -⟩
      · right
        rw [hres]
        have hval : instantiate 0 ρ node.expression = ρ i := by rw [hi]; simp [instantiate]
        rw [hval] at hsteps
        have hi' : i < c.context.length := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hx).1 hwidth
        obtain ⟨A, hA⟩ : ∃ A, c.context[i]? = some A := ⟨_, List.getElem?_eq_getElem hi'⟩
        have hv : isVal (ρ i) = true := (meaning_value (he.2 i A hA)).1
        rw [PromiseCalls.steps_value hv hsteps]
        exact (hn i _ hx).symm
      · left; rw [hres, hr1]; exact hnb
    have hres' : (st.result ∈ entry.names ∧ st.fresh = fresh) ∨ (st.result = fresh ∧ st.fresh = fresh + 1) := by
      rcases resultOf_cases node.expression entry.names fresh with ⟨i, -, hx, hf⟩ | ⟨hr1, hf⟩
      · exact .inl ⟨hres ▸ List.mem_of_getElem? hx, hfresh.trans hf⟩
      · exact .inr ⟨hres.trans hr1, hfresh.trans hf⟩
    have hok : pc.selectChecks = false → passTreeOk G images (kOf G c entry ms (wholeOf node.expression)) codes
        ans.summaries.toList effect = true := fun hs => passTreeCheck_ok htree hs
    by_cases hp : passPreserving G images (jOf c node) (kOf G c entry ms (wholeOf node.expression)) effect codes
        a0.summaries.toList = true
    · obtain ⟨hstore, hK, hO⟩ := hpres hp
      refine ⟨hs1, by rw [hK]; exact hk.1, hres', Footprints.Closed.empty, Footprints.Closed.top,
        ⟨?_, ?_, ?_⟩⟩
      · rw [hO]; exact preserving_judgment_two hp hok hsel hcodes hs0 hs1 he hk.1 s.adm s.ok
      · intro k h' v s' hsteps _ ha hh hout
        rw [hstore]
        refine stateHolds_pushed hn hI hF hstart ha.1 (hkv k h' v hsteps) ?_
        rw [hO] at hout
        exact preserving_store hn (hkv k h' v hsteps)
          (fun a ha' => named_keep_box (Footprints.Closed.empty_le _) hst s' ha a ha') (hh ▸ hout)
      · intro s' ha; exact stateHolds_throw hS w ha.1
    · have hpf : passPreserving G images (jOf c node) (kOf G c entry ms (wholeOf node.expression)) effect codes
          a0.summaries.toList = false := by simpa using hp
      obtain ⟨out', hwc, hsel', hstore, hK, hO⟩ := hwrit hpf
      have hrun := pass_select_whole htree hwc hsel'
      refine ⟨hs1, by rw [hK]; exact hk.2, hres', Footprints.Closed.top, Footprints.Closed.top,
        ⟨?_, ?_, ?_⟩⟩
      · rw [hO]; exact top_judgment (passRunChecker pc) hrun hcodes hs1 he hk.2 s.adm s.ok
      · intro k h' v s' hsteps _ ha hh hout
        rw [hstore]
        refine stateHolds_pushed hn hI hF hstart ha.1 (hkv k h' v hsteps) ?_
        rw [hO] at hout
        exact writing_store w hn (hkv k h' v hsteps) hst (hh ▸ hout)
      · intro s' ha; exact stateHolds_throw hS w ha.1

omit [Instantiates ι] in
/-- **The step theorem with the searches as oracles**: the conclusion of
`checkedStep_sound` from `StepChecked`. -/
theorem stepChecked_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {pc : PassChecker G images} {node : Node} {c : PointClaim ι} {entry : SinglePass.State} {ms : List Nat}
    {fresh : Nat} {answers : Answered G} {st : Stepped ι} {ans : Answered G}
    (h : StepChecked G images pc codes c node entry ms fresh answers ans st)
    {I : List (PromiseCalls.Implication ι)} {start : List Nat} {E ρ : Env} {m : Nat} {s : IndexedHeap}
    (hS : StateHolds G entry I start E ρ m s) (w : StoreWF entry.store) (hnb : NamesBelow entry I start fresh)
    (hwidth : entry.names.length ≤ c.context.length)
    (he : EnvOk G c.context ρ s.n s.W) (hcodes : CodesSound G codes)
    (hsum : SummariesSound G images answers.summaries.toList) :
    SummariesSound G images ans.summaries.toList ∧ HeapKnowledge.Holds st.stepK ρ s.h ∧
    ((st.result ∈ entry.names ∧ st.fresh = fresh) ∨ (st.result = fresh ∧ st.fresh = fresh + 1)) ∧
    ∃ cn ce : Footprints.Closed, StepExits G c.type cn ce node.expression st.stepOut
      (StateHolds G ⟨st.result :: entry.names, st.store, entry.fresh⟩ I start E)
      (StateHolds G ⟨entry.names, entry.store.dropHeap (fun _ => false), entry.fresh⟩ I start E) ρ m s := by
  obtain ⟨h1, h2, h3, cn, ce, hj, hn, hx⟩ := stepChecked_parts h hS w hnb hwidth he hcodes hsum
  exact ⟨h1, h2, h3, cn, ce, stepExits_of hj hn hx⟩

end StepTheorem

section Nodes
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

/-- **A node's step checked, its searches as oracles**: `NodeRan` with the
step's equation replaced by `StepChecked`. -/
structure NodeChecked (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (pc : PassChecker G images) (P : ControlFlow.Program) (w : Walk ι) (startNames : List Nat)
    (ctx : Nat → List (Ty ι)) (l : Nat) where
  node : Node
  hP : P[l]? = some node
  c : PointClaim ι
  hctx : ctx l = c.context
  entry : SinglePass.State
  ms : List Nat
  fresh : Nat
  answers : Answered G
  st : Stepped ι
  ans : Answered G
  hstep : StepChecked G images pc codes c node entry ms fresh answers ans st
  wf : StoreWF entry.store
  below : NamesBelow entry (w.implies l) startNames fresh
  width : entry.names.length ≤ c.context.length
  sums : SummariesSound G images answers.summaries.toList

/-- A node's run is checked with its searches as oracles, where the direct
call and the search keep the summary table checked. -/
def NodeRan.checked {G : NormalGraph ι} {images : InstanceImageCheck G} {pool : List (Ty ι)} {fuel : Nat}
    {suggestions : List (Sequent ι)} {index : KnownIndex ι} {codes : CodeEntry ι → Bool} {aliases : List (ι × ι)}
    {pc : PassChecker G images} {undefTy : Option (Ty ι)} {P : ControlFlow.Program} {w : Walk ι}
    {startNames : List Nat} {ctx : Nat → List (Ty ι)} {l : Nat}
    (hdir : DirectKeepsSummaries G images undefTy)
    (hsrch : SearchKeepsSummaries G images pool fuel suggestions index codes aliases pc.checker)
    (r : NodeRan G images pool fuel suggestions index codes aliases pc undefTy P w startNames ctx l) :
    NodeChecked G images codes pc P w startNames ctx l :=
  ⟨r.node, r.hP, r.c, r.hctx, r.entry, r.ms, r.fresh, r.answers, r.st, r.ans,
    stepChecked_of_step r.hstep hdir hsrch, r.wf, r.below, r.width, r.sums⟩

omit [Instantiates ι] in
/-- **A checked node at a reassignment**: a node checked at `G` is checked
at `reassign G η` with a checker whose `select` is the same result there,
the answers reassigned, the summary table checked
(`Parametricity.summariesSound_reassign`). -/
def nodeChecked_reassign {G : NormalGraph ι} {η : MixedAssignment ι} {images : InstanceImageCheck G}
    {codes : CodeEntry ι → Bool} {pc : PassChecker G images} {pc' : PassChecker (reassign G η) (images.reassign η)}
    {P : ControlFlow.Program} {w : Walk ι} {startNames : List Nat} {ctx : Nat → List (Ty ι)} {l : Nat}
    (hpc : PassCheckerReassign G η images pc pc') (r : NodeChecked G images codes pc P w startNames ctx l) :
    NodeChecked (reassign G η) (images.reassign η) codes pc' P w startNames ctx l :=
  ⟨r.node, r.hP, r.c, r.hctx, r.entry, r.ms, r.fresh, Answered.reassign r.answers η, r.st,
    Answered.reassign r.ans η, stepChecked_reassign hpc r.hstep r.sums, r.wf, r.below, r.width,
    Parametricity.summariesSound_reassign G η images r.sums⟩

omit [Hashable ι] [Instantiates ι] in
/-- **A qualified body's checker at an admitted instance**: where the
body's check is the lexical body check (`verify_qualified_safe_at`'s
`bodyCheck`), at an assignment `assign η source.binders As` the scheme
admits within its bounds, the lexical body subtyping of the reassigned
graph (`lexicalBodySubtyping`) has the same check, so the checker there
exists (`passCheckerReassign_qualified`). -/
theorem passCheckerReassign_lexical {G : NormalGraph ι} {images : InstanceImageCheck G} (source : SchemeRow ι)
    {N : Fam} {C : ResolutionDescriptors.Capabilities (excOf G) N}
    (domain : G.domain = ResolutionDescriptors.descriptorDomain C)
    (aliases : List (ι × ι)) (aliasesSound : AliasesSound G source aliases)
    (body : BodySubtyping G) (bodyCheck : body.check = lexicalBodyCheck G images source aliases)
    (ord : ∀ {A B p}, checkUsing G images A B p = true → body.check A B p = true)
    (η : MixedAssignment ι) (As : List MixedFamily) (length : As.length = source.binders.length)
    (allowed : G.domain.allowed source As) (bounded : ∀ m, Bounded (mixedMeaning G) η source As m) :
    ∃ pc' : PassChecker (reassign G (assign η source.binders As)) (images.reassign (assign η source.binders As)),
      PassCheckerReassign G (assign η source.binders As) images (.qualified body ord) pc' :=
  ⟨_, passCheckerReassign_qualified G _ images body
    (lexicalBodySubtyping G images source domain aliases aliasesSound η As length allowed bounded)
    bodyCheck.symm ord⟩

/-- **The guarantee from one run at `G`, the searches as oracles**: where
the pass's run at `G` computed every visited node (`NodeRan`), the direct
call and the search keep the summary table checked (`hdir`, `hsrch`), at
every admitted assignment there is a checker whose `select` is the same
result (`hpc`: `passCheckerReassign_ordinary`, or
`passCheckerReassign_lexical` for a qualified body), and the checked nodes
at `reassign G η` give the walk predicates there (`hwalk`,
`run_traversed`'s statement at the reassigned graph over `NodeChecked`),
the run guarantees every field of `GraphGuarantee`. -/
theorem run_guarantee_of_checked {G : NormalGraph ι} {admits : MixedAssignment ι → Prop} {P : Program} {start : Nat}
    {goal : Goal ι} {inputs : List (Ty ι)} {sep : HeapSeparation.Separation} {idx : List HeapKnowledge.IndexAtom}
    {assertions : List (Nat × HeapKnowledge.Knowledge)} {bound : Option (Footprints.Closed × Bool × Bool)}
    {ensures : List HeapKnowledge.IndexFact}
    {regional : Option (Footprints.Closed × List Footprints.ArgumentStoreRegion × Bool)}
    {images : InstanceImageCheck G} {pool : List (Ty ι)} {fuel : Nat} {suggestions : List (Sequent ι)}
    {index : KnownIndex ι} {codes : CodeEntry ι → Bool} {aliases : List (ι × ι)} {pc : PassChecker G images}
    {undefTy : Option (Ty ι)} {w : Walk ι} {ctx : Nat → List (Ty ι)}
    (hran : ∀ l, w.visited l → Nonempty (NodeRan G images pool fuel suggestions index codes aliases pc undefTy P w
      (List.range inputs.length) ctx l))
    (hdir : DirectKeepsSummaries G images undefTy)
    (hsrch : SearchKeepsSummaries G images pool fuel suggestions index codes aliases pc.checker)
    (hpc : ∀ η, admits η → ∃ pc' : PassChecker (reassign G η) (images.reassign η),
      PassCheckerReassign G η images pc pc')
    (hwalk : ∀ η, admits η → ∀ pc' : PassChecker (reassign G η) (images.reassign η),
      (∀ l, w.visited l → Nonempty (NodeChecked (reassign G η) (images.reassign η) codes pc' P w
        (List.range inputs.length) ctx l)) →
      ∃ (given : Nat → Bool)
        (edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping))
        (fresh : Nat → Nat),
        PassWalkSound (reassign G η) P start goal inputs sep idx assertions bound ensures regional w given ctx
          edgesIn fresh) :
    GraphGuarantee G admits P start goal inputs sep idx assertions bound ensures regional :=
  run_guarantee fun η hη => by
    obtain ⟨pc', hp⟩ := hpc η hη
    obtain ⟨given, edgesIn, fresh, h⟩ := hwalk η hη pc' fun l hl =>
      let ⟨r⟩ := hran l hl; ⟨nodeChecked_reassign hp (r.checked hdir hsrch)⟩
    exact ⟨w, given, ctx, edgesIn, fresh, h⟩

end Nodes

end Verification.TolerantFrames
