import Verification.Source.Claims.FramedInitial
import Verification.Source.Claims.PassUnitMember

/-! # The framed returns, from the checks the pass makes

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "The returns, at reached
executions"). `ret_reachedW_spec` gives the returns at the executions a
framed plan's claim is about from premises of three kinds; here each
premise that is a check is read from the check the pass makes:

- **the component's checks at the frame's flow** (`frameFlowB`, run by
  `componentBindingRefusal` at the flow with the frame's sites and decided
  tags, `frameFlowOf`): the flow's facts, its tokens, its lowered codes,
  the closure of its capture sites and `O`, and layout provenance and the
  residual invariant of the initialization and the realm
  (`frameFlow_checks`, by `frame_transport`);
- **the request's checks** (`FramedSpec.requestB`): its tag, its source
  terms, its client obligation keeping every part, and at each framed node
  the call's operands read from slots, the node's set closed
  (`nodeSetOf`), each support passing the frame's check at the node's
  protocol (`nodeProtocolOf`) at every context and every node sharing the
  call's continuation and handler (`framedNodesAt_sound`);
- **the protocol orders** by definition of the node's protocol: the
  component's protocol and the node's depth charges are within it, and
  the client obligation is within the component's protocol where it keeps
  every part (`thetaKeepB_sound`);
- **the separation the frame's check reads** is the separation of classes,
  sound at every state (`classQuery_sound`).

The callee's effect bounding the heap along each framed call is the
callback row of the client obligation (`FramedSpec.CallbacksWithin`, a
trust). The invariants of the frame's executions are read along the
program (`ret_reachedW_public`), from the checks of its starts
(`FramedSpec.starts_checks`) and the two premises on the initial
configurations, which the component's checks give
(`FramedSpec.initialFits`, `FramedSpec.initialEntry`).
`framedReturns_reached` assembles them. -/

namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow LabelStore
open Verification.TolerantFrames.ReadOnly Verification.TolerantFrames.ReadOnly.ClientFrame

section
variable {P : Package} [DecidableEq P.Site] [Hashable P.Site]

/-- A framed node's operand sets, at its expression. -/
def operandSetsOf (F : FFlow P) (m : Code) (l : Nat) : Sites P :=
  match m.1[l]? with
  | some e => operandSets F m l e
  | none => []

/-- A framed node's set, at its expression. -/
def nodeSetOf (F : FFlow P) (lay : List (Nat × Bool × Nat × Nat)) (m : Code) (l : Nat) : Sites P :=
  match m.1[l]? with
  | some e => nodeSet F lay m l e
  | none => []

/-- A framed node's protocol, at its set. -/
def nodeProtocolOf (F : FFlow P) (lay : List (Nat × Bool × Nat × Nat))
    (theta : List (Option Verification.Kind × Footprints.Change)) (m : Code) (l : Nat) : Protocol P :=
  nodeProtocol F lay (protocolOfKinds theta) (nodeSetOf F lay m l)

/-- **A framed node passes its checks** (proved): a node the plan frames
has an expression and a stated effect of its callee, at which
`framedNodeOkB` passes for the supports it keeps. -/
theorem framedNode_ok {F : FFlow P} {lay : List (Nat × Bool × Nat × Nat)}
    {theta : List (Option Verification.Kind × Footprints.Change)} {framed : List (Nat × List Footprints.Footprint)}
    {m : Code} {eff : Nat → Option Footprints.Footprint} (h : framedNodesAt F lay theta framed m eff = true)
    {l : Nat} (hl : Verification.TolerantFrames.framedFOf framed l = true) :
    ∃ e Φ, m.1[l]? = some e ∧ eff l = some Φ ∧
      framedNodeOkB F lay (protocolOfKinds theta) m l e Φ (Verification.TolerantFrames.framedSOf framed l) = true := by
  simp only [Verification.TolerantFrames.framedFOf, SinglePass.framedAt, Option.isSome_map] at hl
  cases hf : framed.find? (·.1 == l) with
  | none => rw [hf] at hl; cases hl
  | some p =>
    have hp := List.mem_of_find?_eq_some hf
    have hk : p.1 = l := by simpa using List.find?_some hf
    have hS : Verification.TolerantFrames.framedSOf framed l = p.2 := by
      simp [Verification.TolerantFrames.framedSOf, SinglePass.framedAt, hf]
    simp only [framedNodesAt, List.all_eq_true] at h
    have h' := h p hp
    obtain ⟨l₀, Ss⟩ := p
    simp only at hk hS h'
    subst hk
    rw [hS]
    revert h'
    cases m.1[l₀]? <;> cases eff l₀ <;> simp

/-- **What the checks of a plan's framed nodes give** (proved): at each
framed node `l` of the code `m`, the call's operands read from slots, its
callee's stated effect, the node's set closed and holding its operand
sets, the sets of its operand slots at every context and every node
sharing its continuation and handler within the node's set, and each
support it keeps passing the frame's check there at the node's protocol. -/
theorem framedNodesAt_sound {F : FFlow P} {lay : List (Nat × Bool × Nat × Nat)}
    {theta : List (Option Verification.Kind × Footprints.Change)} {framed : List (Nat × List Footprints.Footprint)}
    {m : Code} {eff : Nat → Option Footprints.Footprint} (h : framedNodesAt F lay theta framed m eff = true) :
    (∀ l e, Verification.TolerantFrames.framedFOf framed l = true → m.1[l]? = some e → atomCallB e = true) ∧
    (∀ l, Verification.TolerantFrames.framedFOf framed l = true → eff l = some ((eff l).getD [])) ∧
    (∀ l, Verification.TolerantFrames.framedFOf framed l = true →
      capClosedB F (tokenCaps F lay) (operandSetsOf F m l) (nodeSetOf F lay m l) = true) ∧
    (∀ l e k x, Verification.TolerantFrames.framedFOf framed l = true → m.1[l]? = some e → m.2[l]? = some (k, x) →
      ∀ c π l', F.flow.code m c = some π → NodeOf m l' k x → ∀ j ∈ atomSlots e, Sub (π.env l' j) (nodeSetOf F lay m l)) ∧
    (∀ l e k x, Verification.TolerantFrames.framedFOf framed l = true → m.1[l]? = some e → m.2[l]? = some (k, x) →
      ∀ c π l', F.flow.code m c = some π → NodeOf m l' k x →
      ∀ T ∈ Verification.TolerantFrames.framedSOf framed l,
        frameCheckAt classQuery (nodeProtocolOf F lay theta m l) ((eff l).getD []) T F.flow.H (π.env l') noKeys
          (fun _ => false) = true) := by
  -- (a framed node's sharing nodes, contexts and checks)
  have hshare : ∀ {l l' k x}, m.2[l]? = some (k, x) → NodeOf m l' k x → l' ∈ sharingNodes m l := by
    intro l l' k x hk hn
    simp only [sharingNodes, List.mem_filter, List.mem_range, beq_iff_eq]
    refine ⟨?_, by rw [hn.1, hk]⟩
    have := hn.1
    exact (List.getElem?_eq_some_iff.mp this).1
  refine ⟨fun l e hl he => ?_, fun l hl => ?_, fun l hl => ?_, fun l e k x hl he hk c π l' hc hn j hj => ?_,
    fun l e k x hl he hk c π l' hc hn T hT => ?_⟩
  · obtain ⟨e', Φ, he', -, hok⟩ := framedNode_ok h hl
    rw [he] at he'; cases he'
    simp only [framedNodeOkB, Bool.and_eq_true] at hok
    exact hok.1.1
  · obtain ⟨e', Φ, -, hΦ, -⟩ := framedNode_ok h hl
    rw [hΦ]; rfl
  · obtain ⟨e', Φ, he', -, hok⟩ := framedNode_ok h hl
    simp only [framedNodeOkB, Bool.and_eq_true] at hok
    simp only [operandSetsOf, nodeSetOf, he']
    exact hok.1.2
  · obtain ⟨e', Φ, he', -, hok⟩ := framedNode_ok h hl
    rw [he] at he'; cases he'
    simp only [framedNodeOkB, Bool.and_eq_true] at hok
    have hsub := (capClosedB_sound hok.1.2).1
    simp only [nodeSetOf, he]
    obtain ⟨fc, hfc, rfl⟩ := FFlow.code_at hc
    refine Sub.trans ?_ hsub
    intro s hs
    simp only [operandSets, List.mem_flatMap]
    exact ⟨(c, fc), FFlow.at_ctxs hfc, l', hshare hk hn, j, hj, hs⟩
  · obtain ⟨e', Φ, he', hΦ, hok⟩ := framedNode_ok h hl
    rw [he] at he'; cases he'
    simp only [framedNodeOkB, Bool.and_eq_true, List.all_eq_true] at hok
    obtain ⟨fc, hfc, rfl⟩ := FFlow.code_at hc
    have := hok.2 T hT (c, fc) (FFlow.at_ctxs hfc) l' (hshare hk hn)
    simp only [nodeProtocolOf, nodeSetOf, he, hΦ, Option.getD_some]
    exact this
end

/-- The order of a framed node's protocol (proved, by its definition): the
component's protocol and the depth charges at the node's set are within
it. -/
theorem nodeProtocolOf_ge {P : Package} [DecidableEq P.Site] [Hashable P.Site] (F : FFlow P)
    (lay : List (Nat × Bool × Nat × Nat)) (theta : List (Option Verification.Kind × Footprints.Change)) (m : Code)
    (l : Nat) (p : Part P) :
    (componentProtocol F lay p).le (nodeProtocolOf F lay theta m l p) = true ∧
      (probeProtocol (flowKinds F) (nodeSetOf F lay m l) p).le (nodeProtocolOf F lay theta m l p) = true :=
  ⟨Footprints.Change.le_trans (Footprints.Change.le_max_right _ _) (Footprints.Change.le_max_left _ _),
    Footprints.Change.le_max_right _ _⟩

namespace FramedSpec
variable {ι : Type} (spec : FramedSpec ι)

/-- **The checks of a plan's framed nodes at the frame's flow** (proved,
by `frame_transport` from the check at the flow with the frame's sites and
decided tags). -/
theorem framedNodes_frame {m : Code} {eff : Nat → Option Footprints.Footprint}
    (h : framedNodesAt spec.fflowC spec.lay spec.theta spec.framed m eff = true) :
    framedNodesAt spec.fflow spec.lay spec.theta spec.framed m eff = true :=
  frame_transport spec.C spec.checked (fun _ Fl => framedNodesAt Fl spec.lay spec.theta spec.framed m eff = true) h
/-- **The realization check at the frame's flow** (proved, by
`frame_transport`). -/
theorem realized_frame {σ : Type} [Labels ι] [StoreView σ ι] {r : SourceRequest σ ι}
    (h : realizedFlowB spec.fflowC r = true) : realizedFlowB spec.fflow r = true :=
  frame_transport spec.C spec.checked (fun _ Fl => realizedFlowB Fl r = true) h

/-- **The checks of the program's starts** (proved): the premises of the
returns at reached executions from a program's initial configurations
(`ret_reachedW_public`, track C1) that the pass checks: the frame's flow's
marks, the request's start a label of its program, the realized code's
proposals the request's at body labels at the frame's flow, and the
initialization's node expressions free of runs. -/
theorem starts_checks {σ : Type} [Labels ι] [StoreView σ ι] {r : SourceRequest σ ι}
    {eff : Nat → Option Footprints.Footprint} (hcomp₀ : spec.componentRefusal.val = none)
    (hreq : spec.requestB r eff = true) :
    spec.fflow.marksB = true ∧ r.start < r.program.length ∧ realizedFlowB spec.fflow r = true ∧
      ∀ e ∈ spec.initE, free false e = true := by
  simp only [FramedSpec.requestB, Bool.and_eq_true, decide_eq_true_eq] at hreq
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hst⟩, hreal⟩, -⟩ := hreq
  obtain ⟨-, hmk, -, -, -, -, -, -, -, hEf, -, -, -⟩ := frameFlowB_sound (spec.frameFlow_checks hcomp₀)
  exact ⟨hmk, hst, spec.realized_frame hreal, hEf⟩
end FramedSpec

namespace PassUnit
open HeapObservations

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- **The framed returns at the executions the claim is about, from the
checks** (proved, `ret_reachedW_public`): where the component's binding
checks refuse nothing and the request's checks pass (`requestB`, each
framed node's callee's stated effect read by `eff`), and calls meet the
callback row of the client obligation at `eff` (`CallbacksWithin`), the
returns of the plan's framed nodes keeping their supports hold at the
executions the frame's claim is about, read at their worlds; the initial
configurations fit the flow and are entries by the component's checks
(`FramedSpec.initialFits`, `FramedSpec.initialEntry`). -/
theorem framedReturns_reached {spec : FramedSpec ι} {r : SourceRequest σ ι}
    {eff : Nat → Option Footprints.Footprint} (hcomp₀ : spec.componentRefusal.val = none)
    (hreq : spec.requestB r eff = true) (hcb : spec.CallbacksWithin r eff) :
    FramedReturnsReachedW r (spec.frame r) (Verification.TolerantFrames.framedFOf spec.framed)
      (Verification.TolerantFrames.framedRet (Verification.TolerantFrames.framedSOf spec.framed))
      (fun _ _ _ _ => True) := by
  obtain ⟨hmk, hst, hreal, hEf⟩ := spec.starts_checks hcomp₀ hreq
  simp only [FramedSpec.requestB, Bool.and_eq_true] at hreq
  obtain ⟨⟨⟨⟨⟨hc, hsrc⟩, hθ⟩, -⟩, -⟩, hn⟩ := hreq
  obtain ⟨hFa, -, htok, hlow, hTm, hEl, hEw, hRl, hRw, -, -, hLi, -⟩ := frameFlowB_sound (spec.frameFlow_checks hcomp₀)
  obtain ⟨hatom, heff, hT, hslots, hcheck⟩ := framedNodesAt_sound (spec.framedNodes_frame hn)
  exact ret_reachedW_public spec r (F := Verification.TolerantFrames.framedFOf spec.framed)
    (S := Verification.TolerantFrames.framedSOf spec.framed) hsrc hcomp₀ hEl hEw hLi hRl hRw hFa hmk hst hreal hEf
    (spec.initialFits r hcomp₀) (spec.initialEntry r hcomp₀) htok hlow (compB_sound hc) hatom (S₀ := operandSetsOf spec.fflow (requestCode r))
    (T := nodeSetOf spec.fflow spec.lay (requestCode r))
    (Ψc := nodeProtocolOf spec.fflow spec.lay spec.theta (requestCode r)) hT
    (fun l _ p => (nodeProtocolOf_ge spec.fflow spec.lay spec.theta (requestCode r) l p).2) hslots
    (Φ := fun l => (eff l).getD []) hcheck hTm
    (fun p => thetaKeepB_sound hθ _ p)
    (fun l p => (nodeProtocolOf_ge spec.fflow spec.lay spec.theta (requestCode r) l p).1)
    (fun l b₀ a m e L d k x v hl hb he hk hL hbt hex hat hv =>
      hcb l _ b₀ a m e L d k x v (heff l hl) hb he hk hL.1 hL.2 hbt hex hat hv)
end
end PassUnit

end Verification.SourceClaimJson
