import Verification.Programs.TolerantFramesWalkReassignWalk
import Verification.Programs.TolerantFramesMergeChecked

/-! # Tolerant frames: each exit into a merge delivers the merge's joined implications

A merge keeps a joined implication (`joinedChecked`) where every edge
recorded into it as `(Γe, atSlots, m)` passes `impliesCheck` at its source
context `Γe`. The implication is justified by the source environment's
types, which the edge state's meaning (`StateHolds`) does not read; so it
holds where an exit delivers it, at the exit's source environment `ρs`
typed by `Γe` (`meetImplications_ok_of_check`). `JoinedAt t ρ s` is the
merge's joined implications at `t`'s environment `ρ`, at a merge (no given
facts, at least two incoming states) and nothing elsewhere.

Proved:

- `joinedAt_of_exit`: an edge recorded as `(Γe, atSlotsOf names carried,
  m)` into `t`, its source environment `ρs` typed by `Γe`, its slots naming
  `names`' values at `η`, its carried implications holding at `η` ⟹
  `JoinedAt t (mapEnv m ρs)`;
- `stepEdgesSoundJ_of_checked`: `NodeChecked` with its `NodeMeaning` and
  its exits' and handler's joined implications (`NodeJoined`) at every
  visited label ∧ `CodesSound` ⟹ `StepEdgesSoundJ`, the node obligations
  with every target's `edgePreA` and `JoinedAt`; `StepEdgesSoundJ.toA`
  forgets `JoinedAt`. -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules

section Joined
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

omit [DecidableEq ι] [Hashable ι] [Instantiates ι] in
/-- **The merge's joined implications at a target**: where `t` is a merge
(no given facts, at least two incoming states), the implications it keeps
(`joinedChecked` over its recorded edges `edgesIn t`) hold at `ρ`. -/
def JoinedAt [DecidableEq ι] (G : NormalGraph ι) (w : Walk ι) (given : Nat → Bool) (ctx : Nat → List (Ty ι))
    (edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping))
    (t : Nat) (ρ : Env) (s : IndexedHeap) : Prop :=
  given t = false → 2 ≤ (w.incoming t).length →
    PromiseCalls.ImpliesOk G (joinedChecked G (ctx t) (edgesIn t)) ρ s.n s.W

omit [Hashable ι] [Instantiates ι] in
/-- **An exit establishes the merge's joined implications**: an edge
recorded into `t` as `(Γe, atSlotsOf names carried, m)`, a source
environment `ρs` typed by `Γe` whose slots hold `names`' values at `η`, the
carried implications holding at `η` (`atSlots_ok`,
`meetImplications_ok_of_check`). -/
theorem joinedAt_of_exit {G : NormalGraph ι} {w : Walk ι} {given : Nat → Bool} {ctx : Nat → List (Ty ι)}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)} {t : Nat}
    {Γe : List (Ty ι)} {names : List Nat} {carried : List (PromiseCalls.Implication ι)} {m : PointClaims.Mapping}
    {ρs η : Env} {s : IndexedHeap} (hin : (Γe, atSlotsOf names carried, m) ∈ edgesIn t)
    (he : EnvOk G Γe ρs s.n s.W) (hss : SlotsNamed names ρs η) (hcar : PromiseCalls.ImpliesOk G carried η s.n s.W) :
    JoinedAt G w given ctx edgesIn t (PointClaims.mapEnv m ρs) s :=
  fun _ _ => meetImplications_ok_of_check hin he (atSlots_ok hss hcar)

/-- **What an exit delivers, with a merge's joined implications**: the
target's typed and written assertion (`edgePreA`) and `JoinedAt`. -/
def edgePreAJ (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ρ0 : Env) (ctx : Nat → List (Ty ι))
    (stated : Nat → Option HeapKnowledge.Knowledge) (given : Nat → Bool)
    (edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)) :
    Nat → Assertion :=
  fun t ρ m s => edgePreA G w startNames ρ0 ctx stated t ρ m s ∧ JoinedAt G w given ctx edgesIn t ρ s

/-- **The node obligations with the merges' joined implications**:
`StepEdgesSoundA` with every target's `edgePreAJ`. -/
def StepEdgesSoundJ (P : ControlFlow.Program) (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ρ0 : Env)
    (ctx : Nat → List (Ty ι)) (stated : Nat → Option HeapKnowledge.Knowledge) (given : Nat → Bool)
    (edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping))
    (Ξres Tres : Fam) (Qres Rres : Heap → Prop) (m : Nat) : Prop :=
  ∀ l ρ (s : IndexedHeap), passPreT G w startNames ρ0 ctx l ρ m s → ∃ node, P[l]? = some node ∧
    ∃ (Ξ T : Fam) (cn ce : Footprints.Closed) (Qn : Post) (Qe : Heap → Prop),
      SafePostExc Ξ T (fun h' v => cn.Holds s.h h' ∧ Qn h' v) (fun h' => ce.Holds s.h h' ∧ Qe h')
        s.n s.W s.h (instantiate 0 ρ node.expression) ∧
      NodeObligations (edgePreAJ G w startNames ρ0 ctx stated given edgesIn) Ξres Tres Qres Rres Ξ T cn ce Qn Qe
        ρ m s node.continuation node.handler

/-- **A node's exits and handler deliver the merges' joined implications**:
at each normal exit, from the state after the step at the pushed
environment, the joined implications at the target's environment; at the
handler, from the throw state, at the handler's. -/
structure NodeJoined (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ρ0 : Env) (ctx : Nat → List (Ty ι))
    (given : Nat → Bool)
    (edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping))
    (m : Nat) (l : Nat) (node : Node) (c : PointClaim ι) (entry : SinglePass.State) (st : Stepped ι) : Prop where
  exits : ∀ t pushed observed promote, Exit.normal t pushed observed promote ∈ Exit.ofNode node → ∀ ρ
    (s' : IndexedHeap) v, isVal v = true →
    StateHolds G ⟨st.result :: entry.names, st.store, entry.fresh⟩ (w.implies l) startNames ρ0 (push v ρ) m s' →
    EnvOk G (c.type :: c.context) (push v ρ) s'.n s'.W → ObservedOk observed promote v →
    JoinedAt G w given ctx edgesIn t.label (PointClaims.mapEnv t.mapping (if pushed then push v ρ else ρ)) s'
  handler : ∀ t, node.handler = some t → ∀ ρ (s' : IndexedHeap) e,
    StateHolds G ⟨entry.names, entry.store.dropHeap (fun _ => false), entry.fresh⟩ (w.implies l) startNames ρ0
      ρ m s' →
    EnvOk G c.context ρ s'.n s'.W → Scoped 0 e → excOf G s'.n s'.W e →
    JoinedAt G w given ctx edgesIn t.label (PointClaims.mapEnv t.mapping (push e ρ)) s'

omit [Instantiates ι] in
/-- **Every checked node delivers with the merges' joined implications**
(`StepEdgesSoundJ`): `stepEdgesSound_of_checked` with each exit's and the
handler's `JoinedAt` (`NodeJoined`) beside the target's `edgePreA`. -/
theorem stepEdgesSoundJ_of_checked {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {pc : PassChecker G images} {P : ControlFlow.Program} {w : Walk ι} {startNames : List Nat} {ρ0 : Env}
    {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge} {given : Nat → Bool}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {Tres : Fam} {m : Nat}
    (hacc : ∀ l, w.visited l → ∃ r : NodeChecked G images codes pc P w startNames ctx l,
      NodeMeaning G w startNames ρ0 ctx stated Tres m l r.node r.c r.entry r.st ∧
      NodeJoined G w startNames ρ0 ctx given edgesIn m l r.node r.c r.entry r.st)
    (hcodes : CodesSound G codes) :
    StepEdgesSoundJ P G w startNames ρ0 ctx stated given edgesIn (excOf G) Tres (fun _ => True) (fun _ => True) m := by
  intro l ρ s hp
  obtain ⟨na, hm, hJ⟩ := hacc l hp.1.1
  have hS := hm.entered ρ s hp
  have he : EnvOk G na.c.context ρ s.n s.W := na.hctx ▸ hp.2
  obtain ⟨-, -, -, cn, ce, hparts⟩ := stepChecked_parts na.hstep hS na.wf na.below na.width he hcodes na.sums
  obtain ⟨hj, ho⟩ := nodeObligations_of_parts (pre := edgePreAJ G w startNames ρ0 ctx stated given edgesIn)
    (Ξres := excOf G) (Tres := Tres) (Qres := fun _ => True) (Rres := fun _ => True) (x := na.node.handler)
    hparts he
    (fun j U v hv => hm.shape (j + 1) U v hv)
    (fun s' v _ hv hF he' _ => normalTarget_of_exits
      (fun t p o q hmem s'' v' hv' hF' he'' ho' =>
        ⟨hm.exits t p o q hmem ρ s'' v' hv' hF' he'' ho', hJ.exits t p o q hmem ρ s'' v' hv' hF' he'' ho'⟩)
      hm.ret (fun _ => trivial) s' v hv hF he' (hm.shape _ _ v (he'.2 0 _ rfl)))
    (fun s' e _ hFe he' hsc hx => by
      cases hh : na.node.handler with
      | none => exact ⟨hx, trivial⟩
      | some t =>
        exact ⟨hm.handler t hh ρ s' e hFe he' hsc hx, hJ.handler t hh ρ s' e hFe he' hsc hx⟩)
  exact ⟨na.node, na.hP, _, _, cn, ce, _, _, hj, ho⟩

omit [Hashable ι] [Instantiates ι] in
/-- **The joined obligations give the typed and written ones**
(`StepEdgesSoundA`), by `nodeObligations_mono`. -/
theorem StepEdgesSoundJ.toA {P : ControlFlow.Program} {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat}
    {ρ0 : Env} {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge} {given : Nat → Bool}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat}
    (h : StepEdgesSoundJ P G w startNames ρ0 ctx stated given edgesIn Ξres Tres Qres Rres m) :
    StepEdgesSoundA P G w startNames ρ0 ctx stated Ξres Tres Qres Rres m := by
  intro l ρ s hp
  obtain ⟨node, hP, Ξ, T, cn, ce, Qn, Qe, hj, ho⟩ := h l ρ s hp
  exact ⟨node, hP, Ξ, T, cn, ce, Qn, Qe, hj, nodeObligations_mono (fun _ _ _ hq => hq.1) ho⟩

end Joined

end Verification.TolerantFrames
