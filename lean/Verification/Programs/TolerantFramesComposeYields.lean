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
  `CodesSound` ⟹ `StepEdgesSoundAt` at `edgePreAJ`;
- `footprintsKept_of_bounds`, `returnsKept_of_returns`: `BoundsChecked` ⟹
  `FootprintsKept`, `ReturnsChecked` ⟹ `ReturnsKept`, the entry states from
  `NodeChecked.hentry`;
- `exitJoinedY`: an exit's joined implications at a merge from the edge's
  record at the refined context (`joinedAt_of_exit`, `passRefined_env`);
- (`run_sound_yields`) `RunTraversedA` ∧ `NodesYield` ∧ `LinearNearFuelEq`
  ∧ `BoundsChecked` ∧ `ReturnsChecked` ∧ `RegionsHeld` ∧ `LabelsChecked` ⟹
  `RunSound`; `run_sound_pass` is it with `run_traversedA`. -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules LabelStore

section Steps
variable {ι : Type} [DecidableEq ι] [Hashable ι]

/-- **Every checked node delivers, its exits, handler and return reading
its kept yields** (`StepEdgesSoundAt` at `edgePreAJ`): the entry state from
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
    StepEdgesSoundAt (edgePreAJ G w startNames ρ0 ctx stated given edgesIn) P G w startNames ρ0 ctx (excOf G) Tres
      (fun _ => True) (fun _ => True) m := by
  intro l ρ s hp
  obtain ⟨na, ys, hY⟩ := hacc l hp.1.1
  have hS : StateHolds G na.entry (w.implies l) startNames ρ0 ρ m s := na.hentry ▸ hp.1.2
  have he : EnvOk G na.c.context ρ s.n s.W := na.hctx ▸ hp.2
  obtain ⟨-, hkS, -, cn, ce, hparts⟩ := stepChecked_parts na.hstep hS na.wf na.below na.width he hcodes na.sums
  have hjY := hY.judged ρ s _ _ hS he hkS hparts.1
  obtain ⟨hj, ho⟩ := nodeObligations_of_partsY (pre := edgePreAJ G w startNames ρ0 ctx stated given edgesIn)
    (Ξres := excOf G) (Tres := Tres) (Qres := fun _ => True) (Rres := fun _ => True) (x := na.node.handler)
    hparts he hjY
    (fun _ _ _ hv => nodeShape_of na.hshape hv)
    (fun s' v _ hv hF hy he' hout => by
      have hshape := nodeShape_of na.hshape (he'.2 0 _ rfl)
      by_cases hk : na.node.continuation = .ret
      · rw [hk]
        exact ⟨hY.ret hk ρ s' v hv hF he' hy, trivial⟩
      · exact normalTarget_of_exits (Fn := fun ρ' m' s'' => StateHolds G
            ⟨na.st.result :: na.entry.names, na.st.store, na.entry.fresh⟩ (w.implies l) startNames ρ0 ρ' m' s'' ∧
            PromiseCalls.YieldsOk G ys ρ s''.n s''.W (ρ' 0) ∧ HeapKnowledge.Holds na.st.stepOut ρ' s''.h)
          (fun t p o q hmem => hY.exits t p o q hmem ρ) (fun h => absurd h hk)
          (fun _ => trivial) s' v hv ⟨hF, hy, hout⟩ he' hshape)
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
into `t` as `(passRefined …, atSlotsOf names carried, m)`, under
`passRefined_env`'s premises at the step's value, the edge's slots naming
`names`' values at `η` and the carried implications holding at `η`. -/
theorem exitJoinedY {G : NormalGraph ι} {w : Walk ι} {given : Nat → Bool} {ctx : Nat → List (Ty ι)}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {c : PointClaim ι} {node : Node} {ysAll : List (PromiseCalls.Yield ι)} {stepOut : HeapKnowledge.Knowledge}
    {t : Target} {pushed : Bool} {observed : Option BranchRefinement.Observation} {promote : Option Bool}
    {names : List Nat} {carried : List (PromiseCalls.Implication ι)} {k : Nat}
    (hm : Exit.normal t pushed observed promote ∈ Exit.ofNode node) (harms : ArmsDistinct node.continuation)
    (hin : (passRefined G c node.continuation ysAll (passOutAll G c stepOut) (passFirst node.continuation t),
      atSlotsOf names carried, t.mapping) ∈ edgesIn t.label)
    {ρ η : Env} {s : IndexedHeap} {v : Tm}
    (he : EnvOk G (c.type :: c.context) (push v ρ) s.n s.W) (hshape : ShapeOk v node.continuation)
    (ho : ObservedOk observed promote v) (hy : PromiseCalls.YieldsOk G ysAll ρ s.n s.W v)
    (hout : HeapKnowledge.Holds stepOut (push v ρ) s.h)
    (hss : SlotsNamed names (if pushed then push v ρ else ρ) η) (hcar : PromiseCalls.ImpliesOk G carried η s.n s.W) :
    joinedAt G w given ctx edgesIn t.label (PointClaims.mapEnv t.mapping (if pushed then push v ρ else ρ)) k s :=
  joinedAt_of_exit hin (passRefined_env hm harms he hshape ho hy hout) hss hcar

end Joined

section Run
variable {ι : Type} [Labels ι]

variable (ι) in
/-- **(Named hypothesis) Each checked node delivers with its kept yields**
at every admitted reassigned graph: some yields `ys` with `NodeYielded`
(the judgment carrying them, the return's goal, each exit and the handler
delivering `edgePreAJ`, the merges' joined implications included). -/
def NodesYield : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) after admits,
    RunPremises G I c after admits → ∀ r : RunWalkA G I c, ∀ η, admits η → ∀ ρ0 m l (hl : r.w.visited l),
      ∃ ys, NodeYielded (reassign G η) r.w (List.range c.inputs.length) ρ0 r.ctx r.stated r.given r.edgesIn
        (GoalHolds (reassign G η) c.goal (c.goal.argument ρ0)) m l (r.node l hl).node (r.node l hl).c
        (r.node l hl).entry (r.node l hl).st ys

/-- **The footprint check keeps the bound** (`FootprintsKept`) from
`BoundsChecked`, the entry states from the recorded entries. -/
theorem footprintsKept_of_bounds (hb : BoundsChecked ι) : FootprintsKept ι := by
  intro G I c after admits hp r η hη Φ fr ex hbd
  obtain ⟨dead, hd⟩ := hb G I c after admits hp r Φ fr ex hbd
  obtain ⟨pc', hpc⟩ := scope_reassign hp.2.1 hη
  exact ⟨dead, fun ρ0 h₀ => footprintKept_of
    (fun l hl => ⟨nodeChecked_reassign hpc (r.node l hl),
      fun _ _ hq => (nodeChecked_reassign hpc (r.node l hl)).hentry ▸ hq.1.2, (hd l hl).reassign hpc⟩)
    (codesSound_reassign hp.2.2.1 η)⟩

/-- **The return check establishes `ensures`** (`ReturnsKept`) from
`ReturnsChecked`, the entry states from the recorded entries. -/
theorem returnsKept_of_returns (hrc : ReturnsChecked ι) : ReturnsKept ι := by
  intro G I c after admits hp r η hη hne ρ0 m
  obtain ⟨pc', hpc⟩ := scope_reassign hp.2.1 hη
  exact returnsEnsured_of
    (fun l hl => ⟨nodeChecked_reassign hpc (r.node l hl),
      fun _ _ hq => (nodeChecked_reassign hpc (r.node l hl)).hentry ▸ hq.1.2,
      (hrc G I c after admits hp r hne l hl).reassign hpc⟩)
    (codesSound_reassign hp.2.2.1 η)

/-- **THE GRAPH THEOREM over the nodes' kept yields** (`RunSound`): from
the driver's walk (`RunTraversedA`), each node's kept yields (`NodesYield`),
`LinearNearFuelEq`, the driver's footprint and return checks
(`BoundsChecked`, `ReturnsChecked`), the regional premise (`RegionsHeld`)
and the setup's label check (`LabelsChecked`). -/
theorem run_sound_yields (hrun : RunTraversedA ι) (hyield : NodesYield ι) (hnear : LinearNearFuelEq)
    (hb : BoundsChecked ι) (hrc : ReturnsChecked ι) (hreg : RegionsHeld ι) (hlab : LabelsChecked ι) :
    Target.RunSound ι := by
  intro G I c after admits hacc hscope hcodes hsums hfields
  have hp : RunPremises G I c after admits := ⟨hacc, hscope, hcodes, hsums, hfields⟩
  obtain ⟨r⟩ := hrun G I c after hacc hsums
  refine GraphGuarantee.toTarget (run_guarantee fun η hη => ?_)
  obtain ⟨pc', hpc⟩ := scope_reassign hscope hη
  refine ⟨r.w, r.given, r.ctx, r.edgesIn, r.fresh, r.stated,
    { walk := fun ρ0 m => ?_
      entered := r.start.entered η
      stable := fun Φ regions exc hr ρ s he =>
        GraphCode.ArgumentPathTracking.checkEntryFields_sound
          ((checkEntryFields_reassign G η c.inputs regions).trans (hfields Φ regions exc hr)) he s.pos s.ok
      footprint := footprintsKept_of_bounds hb G I c after admits hp r η hη
      returns := returnsKept_of_returns hrc G I c after admits hp r η hη
      regions := hreg G I c after admits hp r η hη
      labelled := assertionsLabelled_of_checked hlab G I c after admits hp r }⟩
  exact nodesChecked_of_walkJ (r.traversed.reassign η)
    (stepEdgesSound_of_yields
      (fun l hl => ⟨nodeChecked_reassign hpc (r.node l hl), hyield G I c after admits hp r η hη ρ0 m l hl⟩)
      (codesSound_reassign hcodes η))
    (headsEntered_of_recorded r.heads) hnear

/-- **THE GRAPH THEOREM of the single pass over the nodes' kept yields**
(`run_sound_yields` with the driver's walk from its record,
`run_traversedA`). -/
theorem run_sound_pass (hstop : WalkStopsRefuse ι) (hrec : RecordsSound ι) (hyield : NodesYield ι)
    (hnear : LinearNearFuelEq) (hb : BoundsChecked ι) (hrc : ReturnsChecked ι) (hreg : RegionsHeld ι)
    (hlab : LabelsChecked ι) : Target.RunSound ι :=
  run_sound_yields (run_traversedA hstop hrec) hyield hnear hb hrc hreg hlab

end Run

end Verification.TolerantFrames
