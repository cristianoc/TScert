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
  composition;
- at framed returns: `framedKept_holds` (a framed node's return keeps the
  facts of its input whose support lies in a kept support),
  `stepEdgesSound_of_yieldsR` (the framed node's delivery, its exits
  reading those facts, `NodeYieldedR`), `run_sound_checkedR`,
  `run_sound_passR` (`RunSoundFramed` over the pass's framed mode
  `RunCall.AcceptsFramed`), `acceptsFramed_of_accepts` (the walk the pass
  records meets the framed mode at every framed set). -/
namespace Verification.TolerantFrames
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules LabelStore

section Framed

/-- **The returns of framed nodes keeping supports** (the draft, "The graph
at framed returns", $`\mathrm{Ret}_l`$ with no invariant kept): an
evaluation of the framed node `l` from the heap `h` to the heap `h'`, at its
environment `ρ`, changes the regions of each support of `S l` within their
changes (`Supported`). -/
def framedRet (S : Nat → List Confinement.FrameSpec) : Nat → Env → Heap → Heap → Prop :=
  fun l ρ h h' => ∀ T ∈ S l, T.Supported ρ h h'

/-- **A framed node's return keeps the facts its supports support** (the
note's Definition "Support"): where each support of `Ss` holds of the
transition from `h` to `h'` at `ρ`, each index atom of the entry's
knowledge whose produced support lies in one of them holds after it, past
the result (`IndexFact.support?_supports`, `supported_sub`). -/
theorem framedKept_holds {Ss : List Confinement.FrameSpec} {k : HeapKnowledge.Knowledge} {ρ : Env} {h h' : Heap}
    {v : Tm} (hk : HeapKnowledge.Holds k ε ρ h) (hS : ∀ S ∈ Ss, S.Supported ρ h h') :
    ∀ a ∈ framedKept Ss k, AtomHolds ε a (push v ρ) h' := by
  have hcov : ∀ {T : Footprints.Footprint}, SinglePass.footprintSupportedIn Ss T = true →
      Footprints.Supported T ρ h h' := by
    intro T hT
    obtain ⟨S, hSm, hall⟩ := List.any_eq_true.mp hT
    exact Confinement.FrameSpec.covers_supported (hS S hSm) hall
  intro a ha
  simp only [SinglePass.framedKept, List.mem_append, List.mem_map] at ha
  rcases ha with ((⟨f, hf, rfl⟩ | ⟨g, hg, rfl⟩) | ⟨e, he, rfl⟩) | ⟨idx, hidx, rfl⟩
  · have hcells : HeapFacts.Holds (k.cells.filter fun f =>
        SinglePass.footprintSupportedIn Ss (Footprints.FactKind.cell f).support) ρ h' := by
      intro f₀ hf₀
      obtain ⟨hf₀, hsup⟩ := List.mem_filter.mp hf₀
      have := Footprints.FactKind.support_sound (F := .cell f₀)
        (fun x hx => by rw [List.mem_singleton.mp hx]; exact hk.1 f₀ hf₀) (hcov hsup)
      exact this f₀ (List.mem_singleton.mpr rfl)
    intro x hx
    rw [List.mem_singleton.mp hx]
    exact HeapFacts.shift_holds hcells f hf
  · have hlinks : HeapLinks.Holds (k.links.filter fun g =>
        SinglePass.footprintSupportedIn Ss (Footprints.FactKind.link g).support) ρ h' := by
      intro g₀ hg₀
      obtain ⟨hg₀, hsup⟩ := List.mem_filter.mp hg₀
      have := Footprints.FactKind.support_sound (F := .link g₀)
        (fun x hx => by rw [List.mem_singleton.mp hx]; exact hk.2.2.1 g₀ hg₀) (hcov hsup)
      exact this g₀ (List.mem_singleton.mpr rfl)
    intro x hx
    rw [List.mem_singleton.mp hx]
    exact HeapLinks.pull_holds (pre := fun i => [i + 1]) hlinks
      (fun i j hj => by rw [List.mem_singleton.mp hj]; rfl) g hg
  · have helems : HeapKnowledge.ElemsHolds (k.elems.filter fun a =>
        SinglePass.footprintSupportedIn Ss (Footprints.FactKind.elems a.slot a.pred).support) ρ h' := by
      intro e₀ he₀ hcd
      obtain ⟨he₀, hsup⟩ := List.mem_filter.mp he₀
      exact Footprints.FactKind.support_sound (F := .elems e₀.slot e₀.pred)
        (hk.2.2.2.2.1 e₀ he₀ hcd) (hcov hsup)
    intro x hx
    rw [List.mem_singleton.mp hx]
    exact HeapKnowledge.shiftElems_holds helems e he
  · have hind : HeapKnowledge.IndexHolds ε (k.indices.filter fun a =>
        SinglePass.supportedIn Ss a.fact) ρ h' := by
      intro a₀ ha₀ hcd
      obtain ⟨ha₀, hin⟩ := List.mem_filter.mp ha₀
      have hF := hk.2.2.2.2.2 a₀ ha₀ hcd
      unfold SinglePass.supportedIn at hin
      split at hin
      · rename_i T hT
        exact Footprints.Supports.apply (Footprints.IndexFact.support?_supports {} a₀.fact hT)
          (fun _ _ _ _ _ _ _ hs => by cases hs) hF (hcov hin)
      · cases hin
    intro x hx
    rw [List.mem_singleton.mp hx]
    exact HeapKnowledge.shiftIndices_holds hind idx hidx

/-- **What a framed node's exits read beside the step's output**: at a
framed node `l`, the facts of the step's input `st.stepK` its supports
keep (`framedKept`); nothing at another node. -/
def framedK (F : Nat → Bool) (S : Nat → List Confinement.FrameSpec) (l : Nat) (stepK : HeapKnowledge.Knowledge) :
    Env → Heap → Prop :=
  fun ρ' h' => F l = true → ∀ a ∈ framedKept (S l) stepK, AtomHolds ε a ρ' h'

/-- The framed nodes of the list `fr` (`SinglePass.framedAt`). -/
def framedFOf (fr : List (Nat × List Confinement.FrameSpec)) : Nat → Bool := fun l => (SinglePass.framedAt fr l).isSome

/-- The supports the framed nodes of the list `fr` keep. -/
def framedSOf (fr : List (Nat × List Confinement.FrameSpec)) : Nat → List Confinement.FrameSpec :=
  fun l => (SinglePass.framedAt fr l).getD []

/-- **What a framed node's exits read holds the facts its store keeps**:
where `framedK` holds at the node `l` of the list `fr`, the atoms
`SinglePass.keptStep` adds to the store after the step hold. -/
theorem keptHolds_of_framedK {fr : List (Nat × List Confinement.FrameSpec)} {l : Nat}
    {stepK : HeapKnowledge.Knowledge} {ρ : Env} {h : Heap}
    (hK : framedK (ε := ε) (framedFOf fr) (framedSOf fr) l stepK ρ h) :
    ∀ a ∈ (((SinglePass.framedAt fr l).map (fun Ss => SinglePass.framedKept Ss stepK)).getD []),
      AtomHolds ε a ρ h := by
  unfold framedK framedFOf framedSOf at hK
  cases hf : SinglePass.framedAt fr l with
  | none => intro a ha; simp at ha
  | some Ss =>
    simp only [hf, Option.isSome_some, Option.getD_some, forall_const] at hK
    simpa only [Option.map_some, Option.getD_some] using hK

end Framed

section Steps
variable {ι : Type} [DecidableEq ι] [Hashable ι]

/-- **What a node's step means with its kept yields, its exits reading `K`
beside the step's output**: `NodeYielded` with each normal exit delivering
from the state after the step where `K` also holds there (at a framed node,
the facts its return keeps, `framedK`). -/
structure NodeYieldedR (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat)
    (ε : HeapKnowledge.EntryState) (ctx : Nat → List (Ty ι)) (stated : Nat → Option HeapKnowledge.Knowledge)
    («given» : Nat → Bool)
    (edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping))
    (Tres : Fam) (m : Nat) (l : Nat) (node : Node) (c : PointClaim ι) (entry : SinglePass.State) (st : Stepped ι)
    (ys : List (PromiseCalls.Yield ι)) (K : Env → Heap → Prop) : Prop where
  judged : YieldsJudged G c.type c.context node.expression entry (w.implies l) startNames ε m st.stepK ys
  ret : node.continuation = .ret → ∀ ρ (s' : IndexedHeap) v, isVal v = true →
    StateHolds G ⟨st.result :: entry.names, st.store, entry.fresh⟩ (w.implies l) startNames ε (push v ρ) m s' →
    EnvOk G (c.type :: c.context) (push v ρ) s'.n s'.W → PromiseCalls.YieldsOk G ys ρ s'.n s'.W v →
    Tres s'.n s'.W v
  exits : ∀ t pushed observed promote, Exit.normal t pushed observed promote ∈ Exit.ofNode node → ∀ ρ (s : IndexedHeap),
    StateHolds G entry (w.implies l) startNames ε ρ m s →
    EnvOk G c.context ρ s.n s.W → HeapKnowledge.Holds st.stepK ε ρ s.h → m ≤ s.h.length →
    RefsOk s.W (instantiate 0 ρ node.expression) →
    ExitDelivers (edgePreAJ G w startNames ε ctx stated «given» edgesIn) G c.type c.context
      (fun ρ' m' s' => (StateHolds G ⟨st.result :: entry.names, st.store, entry.fresh⟩ (w.implies l) startNames ε
        ρ' m' s' ∧ PromiseCalls.YieldsOk G ys ρ s'.n s'.W (ρ' 0) ∧ HeapKnowledge.Holds st.stepOut ε ρ' s'.h ∧
          ∃ k, k < s.n ∧ Steps k s.h (instantiate 0 ρ node.expression) s'.h (ρ' 0)) ∧ K ρ' s'.h)
      ρ m t pushed observed promote
  handler : ∀ t, node.handler = some t → ∀ ρ (s' : IndexedHeap) e,
    StateHolds G ⟨entry.names, entry.store.dropHeap (fun _ => false), entry.fresh⟩ (w.implies l) startNames ε
      ρ m s' →
    EnvOk G c.context ρ s'.n s'.W → Scoped 0 e → excOf G s'.n s'.W e →
    edgePreAJ G w startNames ε ctx stated «given» edgesIn t.label (PointClaims.mapEnv t.mapping (push e ρ)) m s'

omit [Hashable ι] in
/-- A node meaning what it states with its yields means it with its exits
reading `K` beside the step's output. -/
theorem NodeYielded.toR {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat} {ctx : Nat → List (Ty ι)}
    {stated : Nat → Option HeapKnowledge.Knowledge} {given : Nat → Bool}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {Tres : Fam} {m l : Nat} {node : Node} {c : PointClaim ι} {entry : SinglePass.State} {st : Stepped ι}
    {ys : List (PromiseCalls.Yield ι)}
    (hY : NodeYielded G w startNames ε ctx stated given edgesIn Tres m l node c entry st ys) (K : Env → Heap → Prop) :
    NodeYieldedR G w startNames ε ctx stated given edgesIn Tres m l node c entry st ys K :=
  ⟨hY.judged, hY.ret, fun t p o q hmem ρ s hS he hk hm hr s' v hv hF he' ho =>
    hY.exits t p o q hmem ρ s hS he hk hm hr s' v hv hF.1 he' ho, hY.handler⟩

omit [Hashable ι] in
/-- A node meaning what it states with its exits reading `K` means it
where `K` always holds. -/
theorem NodeYieldedR.toPlain {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat} {ctx : Nat → List (Ty ι)}
    {stated : Nat → Option HeapKnowledge.Knowledge} {given : Nat → Bool}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {Tres : Fam} {m l : Nat} {node : Node} {c : PointClaim ι} {entry : SinglePass.State} {st : Stepped ι}
    {ys : List (PromiseCalls.Yield ι)} {K : Env → Heap → Prop}
    (hY : NodeYieldedR G w startNames ε ctx stated given edgesIn Tres m l node c entry st ys K)
    (hK : ∀ ρ h, K ρ h) : NodeYielded G w startNames ε ctx stated given edgesIn Tres m l node c entry st ys :=
  ⟨hY.judged, hY.ret, fun t p o q hmem ρ s hS he hk hm hr s' v hv hF he' ho =>
    hY.exits t p o q hmem ρ s hS he hk hm hr s' v hv ⟨hF, hK _ _⟩ he' ho, hY.handler⟩

omit [DecidableEq ι] [Hashable ι] in
/-- Nodes delivering their targets at framed returns with no framed node
deliver them. -/
theorem StepEdgesSoundMarkedR.toPlain {pre : Nat → Assertion} {P : ControlFlow.Program} {G : NormalGraph ι}
    {w : Walk ι} {startNames : List Nat} {ctx : Nat → List (Ty ι)} {Ret RetE : Nat → Env → Heap → Heap → Prop}
    {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat}
    (h : StepEdgesSoundMarkedR pre P G w startNames ε ctx (fun _ => false) Ret RetE Ξres Tres Qres Rres m) :
    StepEdgesSoundMarked pre P G w startNames ε ctx Ξres Tres Qres Rres m := by
  intro l ρ s hp hm
  obtain ⟨node, hP, hck⟩ := h l ρ s hp hm
  refine ⟨node, hP, fun hr hρ => ?_⟩
  obtain ⟨Ξ, T, cn, ce, Qn, Qe, hs, ho⟩ := hck hr hρ
  exact ⟨Ξ, T, cn, ce, Qn, Qe, hs, ho.toPlain (fun _ => trivial) (fun _ => trivial)⟩

/-- **Every checked node delivers at framed returns, a framed node's exits
reading the facts its return keeps** (the framed node's delivery,
`StepEdgesSoundMarkedR` at `edgePreAJ`, the returns `framedRet S`): as
`stepEdgesSound_of_yields`, each node's obligations from its step's parts
under the return premises (`nodeObligationsR_of_partsY`); at a framed node
`l` entered at the heap `s.h`, a normal exit whose heap meets
`framedRet S l ρ s.h` holds the facts of the step's input its supports
support (`framedKept_holds`, in place of `callerFrame_post`), which its
exits read (`NodeYieldedR` at `framedK`). A throw's return premise `RetE`
is any; the handler reads none. -/
theorem stepEdgesSound_of_yieldsR {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {pc : PassChecker G images} {P : ControlFlow.Program} {w : Walk ι} {startNames : List Nat}
    {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge} {given : Nat → Bool}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {Tres : Fam} {m : Nat} {F : Nat → Bool} {S : Nat → List Confinement.FrameSpec}
    {RetE : Nat → Env → Heap → Heap → Prop}
    (hacc : ∀ l, w.visited l → ∃ r : NodeChecked G images codes pc P w startNames ctx l,
      ∃ ys, NodeYieldedR G w startNames ε ctx stated given edgesIn Tres m l r.node r.c r.entry r.st ys
        (framedK (ε := ε) F S l r.st.stepK))
    (hcodes : CodesSound G codes) :
    StepEdgesSoundMarkedR (edgePreAJ G w startNames ε ctx stated given edgesIn) P G w startNames ε ctx F
      (framedRet S) RetE (excOf G) Tres (fun _ => True) (fun _ => True) m := by
  intro l ρ s hp hm
  obtain ⟨na, ys, hY⟩ := hacc l hp.1.1
  have hS : StateHolds G na.entry (w.implies l) startNames ε ρ m s := na.hentry ▸ hp.1.2
  have he : EnvOk G na.c.context ρ s.n s.W := na.hctx ▸ hp.2
  refine ⟨na.node, na.hP, fun hr hρ => ?_⟩
  obtain ⟨-, hkS, -, cn, ce, hparts⟩ := stepChecked_parts na.hstep hS na.wf na.below na.width he hcodes na.sums
  have hjY := hY.judged ρ s _ _ hS he hkS (hparts.1 hr hρ)
  obtain ⟨hj, ho⟩ := nodeObligationsR_of_partsY (pre := edgePreAJ G w startNames ε ctx stated given edgesIn)
    (Ξres := excOf G) (Tres := Tres) (Qres := fun _ => True) (Rres := fun _ => True) (x := na.node.handler)
    (Rn := RetP (framedRet S) (enterPend F l s.h) ρ) (Re := RetP RetE (enterPend F l s.h) ρ)
    hparts he hjY
    (fun _ _ _ hv => nodeShape_of na.hshape hv)
    (fun s' v _ hv hF hy he' hout hrun hR => by
      have hshape := nodeShape_of na.hshape (he'.2 0 _ rfl)
      have hK : framedK (ε := ε) F S l na.st.stepK (push v ρ) s'.h := fun hFl => by
        have hR' : framedRet S l ρ s.h s'.h := by
          simpa only [RetP, enterPend, hFl, Bool.cond_true] using hR
        exact framedKept_holds hkS hR'
      by_cases hk : na.node.continuation = .ret
      · rw [hk]
        exact ⟨hY.ret hk ρ s' v hv hF he' hy, trivial⟩
      · exact normalTarget_of_exits (Fn := fun ρ' m' s'' => (StateHolds G
            ⟨na.st.result :: na.entry.names, na.st.store, na.entry.fresh⟩ (w.implies l) startNames ε ρ' m' s'' ∧
            PromiseCalls.YieldsOk G ys ρ s''.n s''.W (ρ' 0) ∧ HeapKnowledge.Holds na.st.stepOut ε ρ' s''.h ∧
              ∃ k, k < s.n ∧ Steps k s.h (instantiate 0 ρ na.node.expression) s''.h (ρ' 0)) ∧
            framedK (ε := ε) F S l na.st.stepK ρ' s''.h)
          (fun t p o q hmem => hY.exits t p o q hmem ρ s hS he hkS hm hr) (fun h => absurd h hk)
          (fun _ => trivial) s' v hv ⟨⟨hF, hy, hout, hrun⟩, hK⟩ he' hshape)
    (fun s' e _ hFe he' hsc hx _ => by
      cases hh : na.node.handler with
      | none => exact ⟨hx, trivial⟩
      | some t => exact hY.handler t hh ρ s' e hFe he' hsc hx)
  exact ⟨_, _, cn, ce, _, _, hj, ho⟩

/-- **Every checked node delivers, its exits, handler and return reading
its kept yields** (`StepEdgesSoundMarked` at `edgePreAJ`;
`stepEdgesSound_of_yieldsR` with no framed node). -/
theorem stepEdgesSound_of_yields {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {pc : PassChecker G images} {P : ControlFlow.Program} {w : Walk ι} {startNames : List Nat} 
    {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge} {given : Nat → Bool}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {Tres : Fam} {m : Nat}
    (hacc : ∀ l, w.visited l → ∃ r : NodeChecked G images codes pc P w startNames ctx l,
      ∃ ys, NodeYielded G w startNames ε ctx stated given edgesIn Tres m l r.node r.c r.entry r.st ys)
    (hcodes : CodesSound G codes) :
    StepEdgesSoundMarked (edgePreAJ G w startNames ε ctx stated given edgesIn) P G w startNames ε ctx (excOf G) Tres
      (fun _ => True) (fun _ => True) m :=
  (stepEdgesSound_of_yieldsR (F := fun _ => false) (S := fun _ => []) (RetE := fun _ _ _ _ => True)
    (fun l hl => by
      obtain ⟨r, ys, hY⟩ := hacc l hl
      exact ⟨r, ys, hY.toR _⟩) hcodes).toPlain

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
    (hout : HeapKnowledge.Holds stepOut ε (push v ρ) s.h)
    (hss : SlotsNamed names (if pushed then push v ρ else ρ) η) (hcar : PromiseCalls.ImpliesOk G carried η s.n s.W) :
    joinedAt G w given ctx edgesIn t.label (PointClaims.mapEnv t.mapping (if pushed then push v ρ else ρ)) k s :=
  joinedAt_of_exit hin (passRefined_env hm he hshape ho hy hout) hss hcar

omit [DecidableEq ι] in
/-- **A normal exit delivers `edgePreAJ`**: `ExitDelivers` at `edgePreA`
and the merge's joined implications at every exit's target environment
(`exitJoinedY`). -/
theorem exitDeliversAJ_of [DecidableEq ι] [Hashable ι] {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat}
    {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge} {given : Nat → Bool}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {A : Ty ι} {Γ : List (Ty ι)} {Fn : Assertion} {ρ : Env} {m : Nat} {t : Target} {pushed : Bool}
    {observed : Option BranchRefinement.Observation} {promote : Option Bool}
    (hd : ExitDelivers (edgePreA G w startNames ε ctx stated) G A Γ Fn ρ m t pushed observed promote)
    (hJ : ∀ (s' : IndexedHeap) v, isVal v = true → Fn (push v ρ) m s' → EnvOk G (A :: Γ) (push v ρ) s'.n s'.W →
      ObservedOk observed promote v →
      joinedAt G w given ctx edgesIn t.label (PointClaims.mapEnv t.mapping (if pushed then push v ρ else ρ)) m s') :
    ExitDelivers (edgePreAJ G w startNames ε ctx stated given edgesIn) G A Γ Fn ρ m t pushed observed promote :=
  fun s' v hv hF he ho => ⟨hd s' v hv hF he ho, hJ s' v hv hF he ho⟩

end Joined

section Checks
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

/-- **A node's exits and handler deliver with its kept yields** `ys`
(`NodeYielded`'s `exits` and `handler`): each normal exit from the state
after the step, the yields at the pushed value and the step's output; the
handler from the throw state; each at `edgePreAJ`. -/
structure NodeExitsY (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat)
    (ε : HeapKnowledge.EntryState) (ctx : Nat → List (Ty ι)) (stated : Nat → Option HeapKnowledge.Knowledge) («given» : Nat → Bool)
    (edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping))
    (m : Nat) (l : Nat) (node : Node) (c : PointClaim ι) (entry : SinglePass.State) (st : Stepped ι)
    (ys : List (PromiseCalls.Yield ι)) : Prop where
  exits : ∀ t pushed observed promote, Exit.normal t pushed observed promote ∈ Exit.ofNode node → ∀ ρ (s : IndexedHeap),
    StateHolds G entry (w.implies l) startNames ε ρ m s →
    EnvOk G c.context ρ s.n s.W → HeapKnowledge.Holds st.stepK ε ρ s.h → m ≤ s.h.length →
    RefsOk s.W (instantiate 0 ρ node.expression) →
    ExitDelivers (edgePreAJ G w startNames ε ctx stated «given» edgesIn) G c.type c.context
      (fun ρ' m' s' => StateHolds G ⟨st.result :: entry.names, st.store, entry.fresh⟩ (w.implies l) startNames ε
        ρ' m' s' ∧ PromiseCalls.YieldsOk G ys ρ s'.n s'.W (ρ' 0) ∧ HeapKnowledge.Holds st.stepOut ε ρ' s'.h ∧
          ∃ k, k < s.n ∧ Steps k s.h (instantiate 0 ρ node.expression) s'.h (ρ' 0))
      ρ m t pushed observed promote
  handler : ∀ t, node.handler = some t → ∀ ρ (s' : IndexedHeap) e,
    StateHolds G ⟨entry.names, entry.store.dropHeap (fun _ => false), entry.fresh⟩ (w.implies l) startNames ε
      ρ m s' →
    EnvOk G c.context ρ s'.n s'.W → Scoped 0 e → excOf G s'.n s'.W e →
    edgePreAJ G w startNames ε ctx stated «given» edgesIn t.label (PointClaims.mapEnv t.mapping (push e ρ)) m s'

/-- **A node's kept yields judged and its return's goal from the checks**:
`NodeYieldChecks` with the subtype answers sound (pass change D5) and the
exits and the handler delivering `edgePreAJ` (`NodeExitsY`) gives
`NodeYielded` (`yieldsJudged_of_checked` with `slotImplOf_entry`,
`goalHolds_of_returnY`). -/
theorem nodeYielded_of_checks {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} {w : Walk ι} {startNames : List Nat} {ctx : Nat → List (Ty ι)}
    {stated : Nat → Option HeapKnowledge.Knowledge} {given : Nat → Bool}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {goal : Goal ι} {ensures : List HeapKnowledge.IndexFact} {m l : Nat} {node : Node} {c : PointClaim ι}
    {entry : SinglePass.State} {st : Stepped ι} {ys : List (PromiseCalls.Yield ι)}
    (hc : NodeYieldChecks G images codes sums w startNames goal ensures l node c entry st ys)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums) (hsub : SubtypeAnswersSound G images)
    (hx : NodeExitsY G w startNames ε ctx stated given edgesIn m l node c entry st ys) :
    NodeYielded G w startNames ε ctx stated given edgesIn (GoalHolds G goal (goal.argument ε.env)) m l node c entry st
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

/-- **A node's kept yields judged, its return's goal, its exits reading the
facts a framed return keeps** (`NodeYieldedR` at `framedK` of the framed
nodes `fr`): `nodeYielded_of_checks`, the exits delivering from the step
with the kept facts in its store (`NodeExitsY` at `SinglePass.keptStep`),
which holds where the state after the step and `framedK` do
(`stateHolds_keep`, `keptHolds_of_framedK`). -/
theorem nodeYieldedR_of_checks {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} {w : Walk ι} {startNames : List Nat} {ctx : Nat → List (Ty ι)}
    {stated : Nat → Option HeapKnowledge.Knowledge} {given : Nat → Bool}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {goal : Goal ι} {ensures : List HeapKnowledge.IndexFact} {m l : Nat} {node : Node} {c : PointClaim ι}
    {entry : SinglePass.State} {st : Stepped ι} {ys : List (PromiseCalls.Yield ι)}
    {fr : List (Nat × List Confinement.FrameSpec)}
    (hc : NodeYieldChecks G images codes sums w startNames goal ensures l node c entry st ys)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums) (hsub : SubtypeAnswersSound G images)
    (hx : NodeExitsY G w startNames ε ctx stated given edgesIn m l node c entry
      (SinglePass.keptStep (SinglePass.framedAt fr l) entry st) ys) :
    NodeYieldedR G w startNames ε ctx stated given edgesIn (GoalHolds G goal (goal.argument ε.env)) m l node c entry
      st ys (framedK (ε := ε) (framedFOf fr) (framedSOf fr) l st.stepK) where
  judged := by
    rcases hc.kept with rfl | ⟨xs, deriv, ys0, sums', hsub, hss, rfl⟩
    · exact yieldsJudged_nil
    · exact yieldsJudged_of_checked (fun ρ s hS => slotImplOf_entry hsub hS) hcodes (fun s hs => hsums s (hss s hs))
  ret hk := by
    obtain ⟨start, argName, debugNode, answers, h, harg⟩ := hc.ret hk
    exact goalHolds_of_returnY hsub h harg
  exits t p o q hmem ρ s hS he hk hm hr := fun s' v hv hF he' ho =>
    hx.exits t p o q hmem ρ s hS he hk hm hr s' v hv
      ⟨stateHolds_keep hF.1.1 (keptHolds_of_framedK hF.2), hF.1.2.1, hF.1.2.2.1, hF.1.2.2.2⟩ he' ho
  handler := hx.handler

end Checks

section Run
variable {ι : Type} [Labels ι]

variable (ι) in
/-- **(Named hypothesis) Each checked node delivers with its kept yields**
at every admitted reassigned graph, over a checked walk: some yields `ys`
with `NodeYieldedR` (the judgment carrying them, the return's goal, each exit
and the handler delivering `edgePreAJ`, the merges' joined implications
included), a framed node's exits reading the facts its return keeps
(`framedK` at the call's framed nodes). -/
def NodesYield : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) after admits,
    RunPremises G I c after admits → ∀ r : RunWalkA G I c, WalkChecked c r → ∀ η, admits η →
      ∀ ε m l (hl : r.w.visited l),
      ∃ ys, NodeYieldedR (reassign G η) r.w (List.range c.inputs.length) ε r.ctx r.stated r.given r.edgesIn
        (GoalHolds (reassign G η) c.goal (c.goal.argument ε.env)) m l (r.node l hl).node (r.node l hl).c
        (r.node l hl).entry (r.node l hl).st ys
        (framedK (ε := ε) (framedFOf c.framed) (framedSOf c.framed) l (r.node l hl).st.stepK)

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
every admitted reassigned graph, over a checked walk, from the step the
exits read (`SinglePass.keptStep` at the call's framed nodes). -/
def ExitsYield : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) after admits,
    RunPremises G I c after admits → ∀ r : RunWalkA G I c, WalkChecked c r → ∀ η, admits η →
      ∀ ε m l (hl : r.w.visited l),
      NodeExitsY (reassign G η) r.w (List.range c.inputs.length) ε r.ctx r.stated r.given r.edgesIn m l
        (r.node l hl).node (r.node l hl).c (r.node l hl).entry
        (SinglePass.keptStep (SinglePass.framedAt c.framed l) (r.node l hl).entry (r.node l hl).st) (r.node l hl).ys

/-- **(`nodesYield_of`) Each checked node delivers with its kept yields**
(`NodesYield`): at every admitted reassigned graph, the yields the visit
kept (`(r.node l hl).ys`), checked at `G` (`NodePassChecked.yields`) and
so there (`NodeYieldChecks.reassign`), judged and meeting the return's goal
(`nodeYieldedR_of_checks`), the codes and the summary table sound there
(`codesSound_reassign`, `summariesSound_reassign`), the exits and handler
by `ExitsYield`. -/
theorem nodesYield_of (hsub : SubtypeAnswersAll ι) (hex : ExitsYield ι) : NodesYield ι := by
  intro G I c after admits hp r hchk η hη ε m l hl
  obtain ⟨dead, hd, hgiven, hmerging, hrecord⟩ := hchk
  obtain ⟨sums, hsums, hys⟩ := (hd l hl).1.yields
  exact ⟨(r.node l hl).ys, nodeYieldedR_of_checks (hys.reassign η) (codesSound_reassign hp.2.2.1 η)
    (Parametricity.summariesSound_reassign G η I hsums) (hsub _ _)
    (hex G I c after admits hp r ⟨dead, hd, hgiven, hmerging, hrecord⟩ η hη ε m l hl)⟩

/-- **The footprint check keeps the bound at a checked walk**
(`FootprintKept` at every admitted reassigned graph), the entry states from
the recorded entries. -/
theorem footprintKept_of_walk {G : NormalGraph ι} {I : InstanceImageCheck G} {c : Target.RunCall G I}
    {after : Answered G} {admits : MixedAssignment ι → Prop} (hp : RunPremises G I c after admits)
    {r : RunWalkA G I c} {dead : List Bool} (hd : ∀ l (hl : r.w.visited l), NodePassChecked c dead (r.node l hl))
    {η : MixedAssignment ι} (hη : admits η) {Φ Ψ : Footprints.Closed} {fr : Bool}
    (hbd : c.bound = some (⟨Φ, Ψ⟩, fr)) (ε : HeapKnowledge.EntryState) (h₀ : Heap) :
    FootprintKept c.P (reassign G η) r.w (List.range c.inputs.length) ε r.ctx Φ Ψ h₀ dead fr := by
  obtain ⟨pc', hpc⟩ := scope_reassign hp.2.1 hη
  exact footprintKept_of
    (fun l hl => ⟨nodeChecked_reassign hpc (r.node l hl),
      fun _ _ hq => (nodeChecked_reassign hpc (r.node l hl)).hentry ▸ hq.1.2,
      ((hd l hl).bound Φ Ψ fr hbd).reassign hpc⟩)
    (codesSound_reassign hp.2.2.1 η)

/-- **The return check establishes `ensures` at a checked walk**
(`ReturnsEnsured` at every admitted reassigned graph), the entry states
from the recorded entries. -/
theorem returnsEnsured_of_walk {G : NormalGraph ι} {I : InstanceImageCheck G} {c : Target.RunCall G I}
    {after : Answered G} {admits : MixedAssignment ι → Prop} (hp : RunPremises G I c after admits)
    {r : RunWalkA G I c} {dead : List Bool} (hd : ∀ l (hl : r.w.visited l), NodePassChecked c dead (r.node l hl))
    {η : MixedAssignment ι} (hη : admits η) (hne : c.ensures ≠ []) (ε : HeapKnowledge.EntryState) (m : Nat) :
    ReturnsEnsured c.P (reassign G η) r.w (List.range c.inputs.length) ε r.ctx c.ensures m := by
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
theorem run_sound_checked_unframed (hrun : RunTraversedC ι) (hyield : NodesYield ι) (hnear : LinearNearFuelEq)
    (hreg : RegionsHeld ι) {G : NormalGraph ι} {I : InstanceImageCheck G} {c : Target.RunCall G I}
    {after : Answered G} {admits : MixedAssignment ι → Prop}
    (hacc : c.AcceptsWalk after) (hnf : c.framed = [])
    (hscope : Target.CheckerScope G I c.passChecker admits)
    (hcodes : CodesSound G c.codes) (hsums : SummariesSound G I after.summaries.toList)
    (hfields : ∀ Φ regions exc, Target.regionOf c.regional = some (Φ, regions, exc) →
      GraphCode.ArgumentPathTracking.checkEntryFields G c.inputs regions = true) :
    Target.GraphGuarantee G admits c.P c.start c.goal c.inputs c.entrySeparation c.entryIndices c.assertions
      c.bound c.ensures (Target.regionOf c.regional) := by
  have hp : RunPremises G I c after admits := ⟨hacc, hscope, hcodes, hsums, hfields⟩
  obtain ⟨r, hchk⟩ := hrun G I c after hacc hsums
  obtain ⟨dead, hd, hgiven, hmerging, hrecord⟩ := hchk
  refine GraphGuarantee.toTarget (accepts_source hacc) (run_guarantee fun η hη => ?_)
  obtain ⟨pc', hpc⟩ := scope_reassign hscope hη
  refine ⟨r.w, r.given, r.ctx, r.edgesIn, r.fresh, r.stated,
    { walk := fun ε m => ?_
      entered := r.start.entered η
      stable := fun Φ regions exc hr ρ s he =>
        GraphCode.ArgumentPathTracking.checkEntryFields_sound
          ((checkEntryFields_reassign G η c.inputs regions).trans (hfields Φ regions exc hr)) he s.pos s.ok
      footprint := fun Φ Ψ fr hbd => ⟨dead, footprintKept_of_walk hp (fun l hl => (hd l hl).1) hη hbd⟩
      returns := fun hne => returnsEnsured_of_walk hp (fun l hl => (hd l hl).1) hη hne
      regions := hreg G I c after admits hp r ⟨dead, hd, hgiven, hmerging, hrecord⟩ η hη
      labelled := assertionsLabelled_of_checked labelsChecked G I c after admits hp r }⟩
  exact nodesChecked_of_walkJ (r.traversed.reassign η)
    (stepEdgesSound_of_yields
      (fun l hl => ⟨nodeChecked_reassign hpc (r.node l hl), by
        obtain ⟨ys, hY⟩ := hyield G I c after admits hp r ⟨dead, hd, hgiven, hmerging, hrecord⟩ η hη ε m l hl
        exact ⟨ys, hY.toPlain fun _ _ hF => by simp [framedFOf, SinglePass.framedAt, hnf] at hF⟩⟩)
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
        (passCtx c) l, NodePassChecked c dead r ∧ NodeExitTrace c (passEdgesIn σ.walk) r ∧
          (σ.walk.labels[l]?).bind (·.stepped) = some r.st

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
    hr.start, (fun _ => rfl), rfl, rfl⟩, dead, (fun l hl => ⟨(Classical.choose_spec (hn l hl)).1, (Classical.choose_spec (hn l hl)).2.1⟩),
    rfl, hr.merging, σ, reach, hw, rfl, fun l hl => (Classical.choose_spec (hn l hl)).2.2⟩



/-- **The pass's framed mode at a call** (the draft's
`RunCall.AcceptsFramed`, "The graph at framed returns"): the call's walk
accepted, and at every admitted reassigned graph, over every checked walk
of it, each visited node delivering with its kept yields where its exits
read, at a node `l` with `F l`, the facts of the step's input the supports
`S l` keep (`NodeYieldedR` at `framedK`). -/
def _root_.Verification.TolerantFrames.Target.RunCall.AcceptsFramed {G : NormalGraph ι} {I : InstanceImageCheck G}
    (c : Target.RunCall G I) (after : Answered G) (admits : MixedAssignment ι → Prop) (F : Nat → Bool)
    (S : Nat → List Confinement.FrameSpec) : Prop :=
  c.AcceptsWalk after ∧ (RunPremises G I c after admits → ∀ r : RunWalkA G I c, WalkChecked c r → ∀ η, admits η →
    ∀ ε m l (hl : r.w.visited l),
      ∃ ys, NodeYieldedR (reassign G η) r.w (List.range c.inputs.length) ε r.ctx r.stated r.given r.edgesIn
        (GoalHolds (reassign G η) c.goal (c.goal.argument ε.env)) m l (r.node l hl).node (r.node l hl).c
        (r.node l hl).entry (r.node l hl).st ys (framedK (ε := ε) F S l (r.node l hl).st.stepK))

/-- **A call whose walk accepted is accepted in the framed mode at its
framed nodes** (`framedFOf c.framed`, keeping `framedSOf c.framed`), where
its nodes deliver with their kept yields (`NodesYield`): the walk's framed
nodes' exits read the facts their returns keep. -/
theorem acceptsFramed_of_walk (hyield : NodesYield ι) {G : NormalGraph ι} {I : InstanceImageCheck G}
    {c : Target.RunCall G I} {after : Answered G} {admits : MixedAssignment ι → Prop} (hacc : c.AcceptsWalk after) :
    c.AcceptsFramed after admits (framedFOf c.framed) (framedSOf c.framed) :=
  ⟨hacc, fun hp r hchk η hη ε m l hl => hyield G I c after admits hp r hchk η hη ε m l hl⟩

variable (ι) in
/-- **The graph theorem at framed returns** (the draft's `RunSoundFramed`):
a call accepted in the framed mode at the framed nodes `F` keeping the
supports `S`, whose checker covers `admits`, run with sound codes, the read
summaries it leaves sound and each region's entry field condition,
mentions no location in its program and guarantees what its options ask at
framed returns (`GraphGuaranteeR` at `F`, the returns `framedRet S` and any
throw's return premise). -/
def RunSoundFramed : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) (after : Answered G)
    (admits : MixedAssignment ι → Prop) (F : Nat → Bool) (S : Nat → List Confinement.FrameSpec)
    (RetE : Nat → Env → Heap → Heap → Prop),
    c.AcceptsFramed after admits F S → Target.CheckerScope G I c.passChecker admits →
    CodesSound G c.codes → SummariesSound G I after.summaries.toList →
    (∀ Φ regions exc, Target.regionOf c.regional = some (Φ, regions, exc) →
      GraphCode.ArgumentPathTracking.checkEntryFields G c.inputs regions = true) →
    c.P.all (fun node => ObjectCoherence.sourceTerm node.expression) = true ∧
      GraphGuaranteeR G admits c.P c.start c.goal c.inputs c.entrySeparation c.entryIndices c.assertions c.bound
        c.ensures (Target.regionOf c.regional) F (framedRet S) RetE

/-- **THE GRAPH THEOREM at framed returns over a checked walk**
(`run_sound_checked` at framed returns): from the driver's checked walk
(`RunTraversedC`), `LinearNearFuelEq` and the regional premise
(`RegionsHeld`), a call accepted in the framed mode guarantees at framed
returns: the walk checked at framed returns from the framed node's
delivery (`stepEdgesSound_of_yieldsR` over the mode's `NodeYieldedR`), the
footprint, return and regional hypotheses from the walk's checks at every
framed set (`NodesKeep.toRF`), by `run_guaranteeR`. -/
theorem run_sound_checkedR (hrun : RunTraversedC ι) (hnear : LinearNearFuelEq) (hreg : RegionsHeld ι) :
    RunSoundFramed ι := by
  intro G I c after admits F S RetE hframed hscope hcodes hsums hfields
  obtain ⟨hacc, hdeliv⟩ := hframed
  have hp : RunPremises G I c after admits := ⟨hacc, hscope, hcodes, hsums, hfields⟩
  obtain ⟨r, hchk⟩ := hrun G I c after hacc hsums
  obtain ⟨dead, hd, hgiven, hmerging, hrecord⟩ := hchk
  refine ⟨accepts_source hacc, run_guaranteeR fun η hη => ?_⟩
  obtain ⟨pc', hpc⟩ := scope_reassign hscope hη
  refine ⟨r.w, r.ctx, r.stated,
    { walk := fun ε m => ?_
      entered := r.start.entered η
      stable := fun Φ regions exc hr ρ s he =>
        GraphCode.ArgumentPathTracking.checkEntryFields_sound
          ((checkEntryFields_reassign G η c.inputs regions).trans (hfields Φ regions exc hr)) he s.pos s.ok
      footprint := fun Φ Ψ fr hbd => ⟨dead, fun ε h₀ =>
        (footprintKept_of_walk hp (fun l hl => (hd l hl).1) hη hbd ε h₀).toRF F (framedRet S) RetE⟩
      returns := fun hne ε m =>
        (returnsEnsured_of_walk hp (fun l hl => (hd l hl).1) hη hne ε m).toRF F (framedRet S) RetE
      regions := fun Φ regions exc hr => by
        obtain ⟨X, hX⟩ := hreg G I c after admits hp r ⟨dead, hd, hgiven, hmerging, hrecord⟩ η hη Φ regions exc hr
        exact ⟨X, fun ε h₀ hcat => ⟨(hX ε h₀ hcat).1, (hX ε h₀ hcat).2.toRF F (framedRet S) RetE⟩⟩
      labelled := assertionsLabelled_of_checked labelsChecked G I c after admits hp r }⟩
  exact nodesChecked_of_walkJR (r.traversed.reassign η)
    (stepEdgesSound_of_yieldsR
      (fun l hl => ⟨nodeChecked_reassign hpc (r.node l hl),
        hdeliv hp r ⟨dead, hd, hgiven, hmerging, hrecord⟩ η hη ε m l hl⟩)
      (codesSound_reassign hcodes η))
    (headsEntered_of_recorded r.heads) hnear

/-- **THE GRAPH THEOREM of the single pass at framed returns**
(`run_sound_checkedR` with the driver's checked walk from its record,
`run_traversedC`). -/
theorem run_sound_passR (hrec : RecordsSound ι) (hchk : RecordsChecked ι) (hnear : LinearNearFuelEq)
    (hreg : RegionsHeld ι) : RunSoundFramed ι :=
  run_sound_checkedR (run_traversedC hrec hchk) hnear hreg

end Run

end Verification.TolerantFrames
