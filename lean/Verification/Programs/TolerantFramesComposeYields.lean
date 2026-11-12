import Verification.Programs.TolerantFramesComposeRunSound
import Verification.Programs.TolerantFramesNodeRefined

/-! # Tolerant frames: the graph theorem over the nodes' kept yields

`NodeMeaning` states a return's result type and each exit for every value
of the claim's type; the pass checks them only at the values the step
returns, with its kept yields (`NodeYielded`), and checks a merge's joined
implications at the edge's context as the yields refine it. So the graph
theorem takes the nodes' kept yields: at every visited node some yields `ys` with
`NodeYielded` (`NodesYield`), whose exits and handler deliver `edgePreAJ`,
the joined implications included. Proved:

- `stepEdgesSound_of_yields`: every visited node checked (`NodeChecked`:
  its entry the recorded one, its shape check) with `NodeYielded` ∧
  `CodesSound` ⟹ `StepEdgesSoundMarked` at `edgePreAJ`;
- `footprintKept_of_walk`, `returnsEnsured_of_walk`: a checked walk
  (`WalkChecked`) keeps the bound and establishes `ensures` at every
  admitted reassigned graph, the entry states from `NodeChecked.hentry`;
- `exitJoinedY`: an exit's joined implications at a merge from the edge's
  record at the refined context (`joinedAt_of_exit`, `passRefined_env`);
  `exitDeliversAJ_of`: an exit delivering `edgePreA` and those joined
  implications delivers `edgePreAJ`;
- `nodeYielded_of_checks`: what `run` checks of the kept yields and the
  return (`NodeYieldChecks`) gives `NodeYielded`'s judgment and return
  (`yieldsJudged_of_checked`, `goalHolds_of_returnY`), its exits and
  handler given;
- (`run_sound_checked`) `RunTraversedC` ∧ `NodesYield` ∧ `LinearNearFuelEq`
  ∧ `RegionsHeld` ⟹ `RunSound`; (`run_traversedC`) `RecordsSound` ∧
  `RecordsChecked` ⟹ `RunTraversedC`; `run_sound_pass` is their
  composition. -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules LabelStore

section Steps
variable {ι : Type} [DecidableEq ι] [Hashable ι]

/-- **Every checked node delivers, its exits, handler and return reading
its kept yields** (`StepEdgesSoundMarked` at `edgePreAJ`): the entry state from
the recorded entry (`hentry`), the shapes from the shape check
(`nodeShape_of`), the judgment strengthened by the yields
(`NodeYielded.judged`), the return's goal, the exits and the handler from
`NodeYielded`. -/
theorem stepEdgesSound_of_yields {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {pc : PassChecker G images} {P : ControlFlow.Program} {w : Walk ι} {startNames : List Nat} {ρ0 : Env}
    {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge} {given : Nat → Bool}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {Tres : Fam} {m : Nat}
    (hacc : ∀ l, w.visited l → ∃ r : NodeChecked G images codes pc P w startNames ctx l,
      ∃ ys, NodeYielded G w startNames ρ0 ctx stated given edgesIn Tres m l r.node r.c r.entry r.st ys)
    (hcodes : CodesSound G codes) :
    StepEdgesSoundMarked (edgePreAJ G w startNames ρ0 ctx stated given edgesIn) P G w startNames ρ0 ctx (excOf G) Tres
      (fun _ => True) (fun _ => True) m := by
  intro l ρ s hp hm
  obtain ⟨na, ys, hY⟩ := hacc l hp.1.1
  have hS : StateHolds G na.entry (w.implies l) startNames ρ0 ρ m s := na.hentry ▸ hp.1.2
  have he : EnvOk G na.c.context ρ s.n s.W := na.hctx ▸ hp.2
  obtain ⟨-, hkS, -, cn, ce, hparts⟩ := stepChecked_parts na.hstep hS na.wf na.below na.width he hcodes na.sums
  have hjY := hY.judged ρ s _ _ hS he hkS hparts.1
  obtain ⟨hj, ho⟩ := nodeObligations_of_partsY (pre := edgePreAJ G w startNames ρ0 ctx stated given edgesIn)
    (Ξres := excOf G) (Tres := Tres) (Qres := fun _ => True) (Rres := fun _ => True) (x := na.node.handler)
    hparts he hjY
    (fun _ _ _ hv => nodeShape_of na.hshape hv)
    (fun s' v _ hv hF hy he' hout hrun => by
      have hshape := nodeShape_of na.hshape (he'.2 0 _ rfl)
      by_cases hk : na.node.continuation = .ret
      · rw [hk]
        exact ⟨hY.ret hk ρ s' v hv hF he' hy, trivial⟩
      · exact normalTarget_of_exits (Fn := fun ρ' m' s'' => StateHolds G
            ⟨na.st.result :: na.entry.names, na.st.store, na.entry.fresh⟩ (w.implies l) startNames ρ0 ρ' m' s'' ∧
            PromiseCalls.YieldsOk G ys ρ s''.n s''.W (ρ' 0) ∧ HeapKnowledge.Holds na.st.stepOut ρ' s''.h ∧
              ∃ k, k < s.n ∧ Steps k s.h (instantiate 0 ρ na.node.expression) s''.h (ρ' 0))
          (fun t p o q hmem => hY.exits t p o q hmem ρ s hS he hkS hm) (fun h => absurd h hk)
          (fun _ => trivial) s' v hv ⟨hF, hy, hout, hrun⟩ he' hshape)
    (fun s' e _ hFe he' hsc hx => by
      cases hh : na.node.handler with
      | none => exact ⟨hx, trivial⟩
      | some t => exact hY.handler t hh ρ s' e hFe he' hsc hx)
  exact ⟨na.node, na.hP, _, _, cn, ce, _, _, hj, ho⟩

end Steps

section Joined
variable {ι : Type} [DecidableEq ι]

/-- **An exit's joined implications from the edge's record at the refined
context** (`joinedAt_of_exit` with `passRefined_env`): an edge recorded
into `t` as `(SinglePass.refinedContext …, atSlotsOf names carried, m)`, under
`passRefined_env`'s premises at the step's value, the edge's slots naming
`names`' values at `η` and the carried implications holding at `η`. -/
theorem exitJoinedY {G : NormalGraph ι} {w : Walk ι} {given : Nat → Bool} {ctx : Nat → List (Ty ι)}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {c : PointClaim ι} {node : Node} {ysAll : List (PromiseCalls.Yield ι)} {stepOut : HeapKnowledge.Knowledge}
    {t : Target} {pushed : Bool} {observed : Option BranchRefinement.Observation} {promote : Option Bool}
    {names : List Nat} {carried : List (PromiseCalls.Implication ι)} {k : Nat}
    {i : Nat} (hm : (Exit.ofNode node)[i]? = some (Exit.normal t pushed observed promote))
    (hin : (SinglePass.refinedContext G c node.continuation ysAll (SinglePass.outAllOf G c stepOut) (i == 0),
      atSlotsOf names carried, t.mapping) ∈ edgesIn t.label)
    {ρ η : Env} {s : IndexedHeap} {v : Tm}
    (he : EnvOk G (c.type :: c.context) (push v ρ) s.n s.W) (hshape : ShapeOk v node.continuation)
    (ho : ObservedOk observed promote v) (hy : PromiseCalls.YieldsOk G ysAll ρ s.n s.W v)
    (hout : HeapKnowledge.Holds stepOut (push v ρ) s.h)
    (hss : SlotsNamed names (if pushed then push v ρ else ρ) η) (hcar : PromiseCalls.ImpliesOk G carried η s.n s.W) :
    joinedAt G w given ctx edgesIn t.label (PointClaims.mapEnv t.mapping (if pushed then push v ρ else ρ)) k s :=
  joinedAt_of_exit hin (passRefined_env hm he hshape ho hy hout) hss hcar

omit [DecidableEq ι] in
/-- **A normal exit delivers `edgePreAJ`**: `ExitDelivers` at `edgePreA`
and the merge's joined implications at every exit's target environment
(`exitJoinedY`). -/
theorem exitDeliversAJ_of [DecidableEq ι] [Hashable ι] {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat}
    {ρ0 : Env} {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge} {given : Nat → Bool}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {A : Ty ι} {Γ : List (Ty ι)} {Fn : Assertion} {ρ : Env} {m : Nat} {t : Target} {pushed : Bool}
    {observed : Option BranchRefinement.Observation} {promote : Option Bool}
    (hd : ExitDelivers (edgePreA G w startNames ρ0 ctx stated) G A Γ Fn ρ m t pushed observed promote)
    (hJ : ∀ (s' : IndexedHeap) v, isVal v = true → Fn (push v ρ) m s' → EnvOk G (A :: Γ) (push v ρ) s'.n s'.W →
      ObservedOk observed promote v →
      joinedAt G w given ctx edgesIn t.label (PointClaims.mapEnv t.mapping (if pushed then push v ρ else ρ)) m s') :
    ExitDelivers (edgePreAJ G w startNames ρ0 ctx stated given edgesIn) G A Γ Fn ρ m t pushed observed promote :=
  fun s' v hv hF he ho => ⟨hd s' v hv hF he ho, hJ s' v hv hF he ho⟩

end Joined

section Checks
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

/-- **A node's exits and handler deliver with its kept yields** `ys`
(`NodeYielded`'s `exits` and `handler`): each normal exit from the state
after the step, the yields at the pushed value and the step's output; the
handler from the throw state; each at `edgePreAJ`. -/
structure NodeExitsY (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat)
    (ρ0 : Env) (ctx : Nat → List (Ty ι)) (stated : Nat → Option HeapKnowledge.Knowledge) (given : Nat → Bool)
    (edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping))
    (m : Nat) (l : Nat) (node : Node) (c : PointClaim ι) (entry : SinglePass.State) (st : Stepped ι)
    (ys : List (PromiseCalls.Yield ι)) : Prop where
  exits : ∀ t pushed observed promote, Exit.normal t pushed observed promote ∈ Exit.ofNode node → ∀ ρ (s : IndexedHeap),
    StateHolds G entry (w.implies l) startNames ρ0 ρ m s →
    EnvOk G c.context ρ s.n s.W → HeapKnowledge.Holds st.stepK ρ s.h → m ≤ s.h.length →
    ExitDelivers (edgePreAJ G w startNames ρ0 ctx stated given edgesIn) G c.type c.context
      (fun ρ' m' s' => StateHolds G ⟨st.result :: entry.names, st.store, entry.fresh⟩ (w.implies l) startNames ρ0
        ρ' m' s' ∧ PromiseCalls.YieldsOk G ys ρ s'.n s'.W (ρ' 0) ∧ HeapKnowledge.Holds st.stepOut ρ' s'.h ∧
          ∃ k, k < s.n ∧ Steps k s.h (instantiate 0 ρ node.expression) s'.h (ρ' 0))
      ρ m t pushed observed promote
  handler : ∀ t, node.handler = some t → ∀ ρ (s' : IndexedHeap) e,
    StateHolds G ⟨entry.names, entry.store.dropHeap (fun _ => false), entry.fresh⟩ (w.implies l) startNames ρ0
      ρ m s' →
    EnvOk G c.context ρ s'.n s'.W → Scoped 0 e → excOf G s'.n s'.W e →
    edgePreAJ G w startNames ρ0 ctx stated given edgesIn t.label (PointClaims.mapEnv t.mapping (push e ρ)) m s'

/-- **A node's kept yields judged and its return's goal from the checks**:
`NodeYieldChecks` with the subtype answers sound (pass change D5) and the
exits and the handler delivering `edgePreAJ` (`NodeExitsY`) gives
`NodeYielded` (`yieldsJudged_of_checked` with `slotImplOf_entry`,
`goalHolds_of_returnY`). -/
theorem nodeYielded_of_checks {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} {w : Walk ι} {startNames : List Nat} {ρ0 : Env} {ctx : Nat → List (Ty ι)}
    {stated : Nat → Option HeapKnowledge.Knowledge} {given : Nat → Bool}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {goal : Goal ι} {ensures : List HeapKnowledge.IndexFact} {m l : Nat} {node : Node} {c : PointClaim ι}
    {entry : SinglePass.State} {st : Stepped ι} {ys : List (PromiseCalls.Yield ι)}
    (hc : NodeYieldChecks G images codes sums w startNames goal ensures l node c entry st ys)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums) (hsub : SubtypeAnswersSound G images)
    (hx : NodeExitsY G w startNames ρ0 ctx stated given edgesIn m l node c entry st ys) :
    NodeYielded G w startNames ρ0 ctx stated given edgesIn (GoalHolds G goal (goal.argument ρ0)) m l node c entry st
      ys where
  judged := by
    rcases hc.kept with rfl | ⟨xs, deriv, ys0, sums', hsub, hss, rfl⟩
    · exact yieldsJudged_nil
    · exact yieldsJudged_of_checked (fun ρ s hS => slotImplOf_entry hsub hS) hcodes (fun s hs => hsums s (hss s hs))
  ret hk := by
    obtain ⟨start, argName, debugNode, answers, h, harg⟩ := hc.ret hk
    exact goalHolds_of_returnY hsub h harg
  exits := hx.exits
  handler := hx.handler

end Checks

section Run
variable {ι : Type} [Labels ι]

variable (ι) in
/-- **(Named hypothesis) Each checked node delivers with its kept yields**
at every admitted reassigned graph, over a checked walk: some yields `ys`
with `NodeYielded` (the judgment carrying them, the return's goal, each exit
and the handler delivering `edgePreAJ`, the merges' joined implications
included). -/
def NodesYield : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) after admits,
    RunPremises G I c after admits → ∀ r : RunWalkA G I c, WalkChecked c r → ∀ η, admits η →
      ∀ ρ0 m l (hl : r.w.visited l),
      ∃ ys, NodeYielded (reassign G η) r.w (List.range c.inputs.length) ρ0 r.ctx r.stated r.given r.edgesIn
        (GoalHolds (reassign G η) c.goal (c.goal.argument ρ0)) m l (r.node l hl).node (r.node l hl).c
        (r.node l hl).entry (r.node l hl).st ys

variable (ι) in
/-- **The answered subtype requests are
sound**: an answer `subtypeUsing` accepts, from any answers, is an
inclusion of meanings, at every graph (the reassigned ones included). -/
def SubtypeAnswersAll : Prop := ∀ (G : NormalGraph ι) (I : InstanceImageCheck G), SubtypeAnswersSound G I

/-- Subtype acceptance is sound at every graph. -/
theorem subtypeAnswersAll : SubtypeAnswersAll ι := subtypeAnswersSound

variable (ι) in
/-- **(Named hypothesis) Each checked node's exits and handler deliver
with the yields the visit kept** (`NodeExitsY` at `(r.node l hl).ys`), at
every admitted reassigned graph, over a checked walk. -/
def ExitsYield : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) after admits,
    RunPremises G I c after admits → ∀ r : RunWalkA G I c, WalkChecked c r → ∀ η, admits η →
      ∀ ρ0 m l (hl : r.w.visited l),
      NodeExitsY (reassign G η) r.w (List.range c.inputs.length) ρ0 r.ctx r.stated r.given r.edgesIn m l
        (r.node l hl).node (r.node l hl).c (r.node l hl).entry (r.node l hl).st (r.node l hl).ys

/-- **(`nodesYield_of`) Each checked node delivers with its kept yields**
(`NodesYield`): at every admitted reassigned graph, the yields the visit
kept (`(r.node l hl).ys`), checked at `G` (`NodePassChecked.yields`) and
so there (`NodeYieldChecks.reassign`), judged and meeting the return's goal
(`nodeYielded_of_checks`), the codes and the summary table sound there
(`codesSound_reassign`, `summariesSound_reassign`), the exits and handler
by `ExitsYield`. -/
theorem nodesYield_of (hsub : SubtypeAnswersAll ι) (hex : ExitsYield ι) : NodesYield ι := by
  intro G I c after admits hp r hchk η hη ρ0 m l hl
  obtain ⟨dead, hd, hgiven, hmerging⟩ := hchk
  obtain ⟨sums, hsums, hys⟩ := (hd l hl).1.yields
  exact ⟨(r.node l hl).ys, nodeYielded_of_checks (hys.reassign η) (codesSound_reassign hp.2.2.1 η)
    (Parametricity.summariesSound_reassign G η I hsums) (hsub _ _)
    (hex G I c after admits hp r ⟨dead, hd, hgiven, hmerging⟩ η hη ρ0 m l hl)⟩

/-- **The footprint check keeps the bound at a checked walk**
(`FootprintKept` at every admitted reassigned graph), the entry states from
the recorded entries. -/
theorem footprintKept_of_walk {G : NormalGraph ι} {I : InstanceImageCheck G} {c : Target.RunCall G I}
    {after : Answered G} {admits : MixedAssignment ι → Prop} (hp : RunPremises G I c after admits)
    {r : RunWalkA G I c} {dead : List Bool} (hd : ∀ l (hl : r.w.visited l), NodePassChecked c dead (r.node l hl))
    {η : MixedAssignment ι} (hη : admits η) {Φ : Footprints.Closed} {fr ex : Bool}
    (hbd : c.bound = some (Φ, fr, ex)) (ρ0 : Env) (h₀ : Heap) :
    FootprintKept c.P (reassign G η) r.w (List.range c.inputs.length) ρ0 r.ctx Φ h₀ dead fr ex := by
  obtain ⟨pc', hpc⟩ := scope_reassign hp.2.1 hη
  exact footprintKept_of
    (fun l hl => ⟨nodeChecked_reassign hpc (r.node l hl),
      fun _ _ hq => (nodeChecked_reassign hpc (r.node l hl)).hentry ▸ hq.1.2,
      ((hd l hl).bound Φ fr ex hbd).reassign hpc⟩)
    (codesSound_reassign hp.2.2.1 η)

/-- **The return check establishes `ensures` at a checked walk**
(`ReturnsEnsured` at every admitted reassigned graph), the entry states
from the recorded entries. -/
theorem returnsEnsured_of_walk {G : NormalGraph ι} {I : InstanceImageCheck G} {c : Target.RunCall G I}
    {after : Answered G} {admits : MixedAssignment ι → Prop} (hp : RunPremises G I c after admits)
    {r : RunWalkA G I c} {dead : List Bool} (hd : ∀ l (hl : r.w.visited l), NodePassChecked c dead (r.node l hl))
    {η : MixedAssignment ι} (hη : admits η) (hne : c.ensures ≠ []) (ρ0 : Env) (m : Nat) :
    ReturnsEnsured c.P (reassign G η) r.w (List.range c.inputs.length) ρ0 r.ctx c.ensures m := by
  obtain ⟨pc', hpc⟩ := scope_reassign hp.2.1 hη
  exact returnsEnsured_of
    (fun l hl => ⟨nodeChecked_reassign hpc (r.node l hl),
      fun _ _ hq => (nodeChecked_reassign hpc (r.node l hl)).hentry ▸ hq.1.2,
      ((hd l hl).ret hne).reassign hpc⟩)
    (codesSound_reassign hp.2.2.1 η)

/-- **THE GRAPH THEOREM over a checked walk** (`RunSound`): from the
driver's checked walk (`RunTraversedC`), each node's kept yields
(`NodesYield`), `LinearNearFuelEq` and the regional premise
(`RegionsHeld`); the footprint and return fields from the walk's checks
(`footprintKept_of_walk`, `returnsEnsured_of_walk`), the assertions at
their labels from the setup's check (`labelsChecked`). -/
theorem run_sound_checked (hrun : RunTraversedC ι) (hyield : NodesYield ι) (hnear : LinearNearFuelEq)
    (hreg : RegionsHeld ι) : Target.RunSound ι := by
  intro G I c after admits hacc hscope hcodes hsums hfields
  have hp : RunPremises G I c after admits := ⟨hacc, hscope, hcodes, hsums, hfields⟩
  obtain ⟨r, hchk⟩ := hrun G I c after hacc hsums
  obtain ⟨dead, hd, hgiven, hmerging⟩ := hchk
  refine GraphGuarantee.toTarget (run_guarantee fun η hη => ?_)
  obtain ⟨pc', hpc⟩ := scope_reassign hscope hη
  refine ⟨r.w, r.given, r.ctx, r.edgesIn, r.fresh, r.stated,
    { walk := fun ρ0 m => ?_
      entered := r.start.entered η
      stable := fun Φ regions exc hr ρ s he =>
        GraphCode.ArgumentPathTracking.checkEntryFields_sound
          ((checkEntryFields_reassign G η c.inputs regions).trans (hfields Φ regions exc hr)) he s.pos s.ok
      footprint := fun Φ fr ex hbd => ⟨dead, footprintKept_of_walk hp (fun l hl => (hd l hl).1) hη hbd⟩
      returns := fun hne => returnsEnsured_of_walk hp (fun l hl => (hd l hl).1) hη hne
      regions := hreg G I c after admits hp r ⟨dead, hd, hgiven, hmerging⟩ η hη
      labelled := assertionsLabelled_of_checked labelsChecked G I c after admits hp r }⟩
  exact nodesChecked_of_walkJ (r.traversed.reassign η)
    (stepEdgesSound_of_yields
      (fun l hl => ⟨nodeChecked_reassign hpc (r.node l hl),
        hyield G I c after admits hp r ⟨dead, hd, hgiven, hmerging⟩ η hη ρ0 m l hl⟩)
      (codesSound_reassign hcodes η))
    (headsEntered_of_recorded r.heads) hnear

variable (ι) in
/-- **(Named hypothesis) The driver checked every node its record visits**:
for a walk that returned, visiting at least the nodes the start reaches,
whose final summaries are sound, one no-return region `dead` and at every
label the record visits a checked step (`NodeChecked`, its entry the
recorded one) with `NodePassChecked` and `NodeExitTrace`: the footprint,
return and exit computations at the same step's values. -/
def RecordsChecked : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) (σ : SinglePass.WalkState ι G) reach,
    RunCall.walk c = .ok (σ, reach) → reach ≤ σ.walk.visited →
    SummariesSound G I σ.answers.summaries.toList → ∃ dead, ∀ l, (ofPass σ.walk (passHeads c)).visited l →
      ∃ r : NodeChecked G I c.codes c.passChecker c.P (ofPass σ.walk (passHeads c)) (List.range c.inputs.length)
        (passCtx c) l, NodePassChecked c dead r ∧ NodeExitTrace c (passEdgesIn σ.walk) r

/-- **(`run_traversedC`) The driver's checked walk from its record**: the
walk `run_traversedA` builds, its nodes the checked steps `RecordsChecked`
gives. -/
theorem run_traversedC (hrec : RecordsSound ι) (hchk : RecordsChecked ι) : RunTraversedC ι := by
  intro G I c after hacc hsums
  obtain ⟨σ, reach, hw, hle, ha⟩ := walk_of_accepts walkStopsRefuse hacc
  have hr := hrec G I c σ reach hw hle (ha ▸ hsums)
  obtain ⟨dead, hn⟩ := hchk G I c σ reach hw hle (ha ▸ hsums)
  exact ⟨⟨ofPass σ.walk (passHeads c), passHeads c, passCtx c, passEdgesIn σ.walk, passFresh σ.walk,
    passStated c, fun l hl => Classical.choose (hn l hl), hr.traversed, ofPass_heads σ.walk (passHeads c),
    hr.start, fun _ => rfl⟩, dead, (fun l hl => Classical.choose_spec (hn l hl)), rfl, hr.merging⟩

/-- **THE GRAPH THEOREM of the single pass** (`run_sound_checked` with the
driver's checked walk from its record, `run_traversedC`). -/
theorem run_sound_pass (hrec : RecordsSound ι) (hchk : RecordsChecked ι) (hyield : NodesYield ι)
    (hnear : LinearNearFuelEq) (hreg : RegionsHeld ι) : Target.RunSound ι :=
  run_sound_checked (run_traversedC hrec hchk) hyield hnear hreg

end Run

end Verification.TolerantFrames
