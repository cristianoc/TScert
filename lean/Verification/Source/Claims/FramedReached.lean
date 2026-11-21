import Verification.Source.Claims.FramedStarts
import Verification.Source.Claims.PassUnitMember
import Verification.Source.Claims.FramedReading

/-! # The framed returns, from the checks the pass makes

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "The returns, at reached
executions"). `ret_reachedW_spec` gives the returns at the executions a
framed plan's claim is about from premises of three kinds; here each
premise that is a check is read from the check the pass makes:

- **the component's checks at the frame's flow** (`frameFlowB`, run by
  `componentBindingRefusal` at the flow with the frame's sites and decided
  tags, `frameFlowOf`): the flow's facts, its tokens, its lowered codes,
  the closure of its capture sites and `O` (`frameFlow_checks`, by
  `frame_transport`);
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
configurations, which hold by the definition of `FramedSpec.Initial`
(`FramedSpec.initialFits`, `FramedSpec.initialEntry`).
`framedReturns_reached` assembles them. -/

namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceElaboration ControlFlow LabelStore
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

/-- A node the plan frames is a framed node's (proved). -/
theorem framedFOf_mem {framed : List (Nat × List Footprints.Footprint)} {l : Nat}
    (hl : Verification.TolerantFrames.framedFOf framed l = true) : l ∈ framed.map (·.1) := by
  simp only [Verification.TolerantFrames.framedFOf, SinglePass.framedAt, Option.isSome_map] at hl
  cases hf : framed.find? (·.1 == l) with
  | none => rw [hf] at hl; cases hl
  | some p =>
    have hk : p.1 = l := by simpa using List.find?_some hf
    exact List.mem_map.mpr ⟨p, List.mem_of_find?_eq_some hf, hk⟩

/-- **A framed node passes its checks** (proved): a node the plan frames
has an expression and a stated effect of its callee, at which
`framedNodeOkB` passes for the supports it keeps. -/
theorem framedNode_ok {F : FFlow P} {lay : List (Nat × Bool × Nat × Nat)}
    {theta : List (Option Verification.Kind × Footprints.Change)} {framed : List (Nat × List Footprints.Footprint)}
    {m : Code} {eff : Nat → Option (Option Footprints.Footprint)} {prot : Nat → Footprints.Region → Bool}
    (h : framedNodesAt F lay theta framed m eff prot = true)
    {l : Nat} (hl : Verification.TolerantFrames.framedFOf framed l = true) :
    ∃ e Φ, m.1[l]? = some e ∧ eff l = some Φ ∧
      framedNodeOkB F lay (protocolOfKinds theta) m l e Φ (prot l) (Verification.TolerantFrames.framedSOf framed l) = true := by
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
support it keeps passing there, at the node's protocol, the frame's check
at the bound of its call or, where none is read, the check of the
charges' premise. -/
theorem framedNodesAt_sound {F : FFlow P} {lay : List (Nat × Bool × Nat × Nat)}
    {theta : List (Option Verification.Kind × Footprints.Change)} {framed : List (Nat × List Footprints.Footprint)}
    {m : Code} {eff : Nat → Option (Option Footprints.Footprint)} {prot : Nat → Footprints.Region → Bool}
    (h : framedNodesAt F lay theta framed m eff prot = true) :
    (∀ l e, Verification.TolerantFrames.framedFOf framed l = true → m.1[l]? = some e → atomCallB e = true) ∧
    (∀ l, Verification.TolerantFrames.framedFOf framed l = true → eff l = some ((eff l).getD none)) ∧
    (∀ l, Verification.TolerantFrames.framedFOf framed l = true →
      capClosedB F (tokenCaps F lay) (operandSetsOf F m l) (nodeSetOf F lay m l) = true) ∧
    (∀ l e k x, Verification.TolerantFrames.framedFOf framed l = true → m.1[l]? = some e → m.2[l]? = some (k, x) →
      ∀ c π l', F.flow.code m c = some π → NodeOf m l' k x → ∀ j ∈ atomSlots e, Sub (π.env l' j) (nodeSetOf F lay m l)) ∧
    (∀ l e k x, Verification.TolerantFrames.framedFOf framed l = true → m.1[l]? = some e → m.2[l]? = some (k, x) →
      ∀ c π l', F.flow.code m c = some π → NodeOf m l' k x →
      ∀ T ∈ Verification.TolerantFrames.framedSOf framed l, match (eff l).getD none with
        | some Φ => frameCheckAt classQuery (nodeProtocolOf F lay theta m l) Φ T F.flow.H (π.env l') (prot l) = true
        | none => frameCheckOwnAt (nodeProtocolOf F lay theta m l) T F.flow.H (π.env l') = true) := by
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
    simp only [framedNodeOkB, supportKeptB, Bool.and_eq_true, List.all_eq_true] at hok
    obtain ⟨fc, hfc, rfl⟩ := FFlow.code_at hc
    have := hok.2 T hT (c, fc) (FFlow.at_ctxs hfc) l' (hshare hk hn)
    simp only [nodeProtocolOf, nodeSetOf, he, hΦ, Option.getD_some]
    cases Φ <;> exact this
end

/-- The order of a framed node's protocol (proved, by its definition): the
component's protocol and the depth charges at the node's set are within
it. -/
theorem nodeProtocolOf_ge {P : Package} [DecidableEq P.Site] [Hashable P.Site] (F : FFlow P)
    (lay : List (Nat × Bool × Nat × Nat)) (theta : List (Option Verification.Kind × Footprints.Change)) (m : Code)
    (l : Nat) (p : Part P) :
    (componentProtocol F lay p).le (nodeProtocolOf F lay theta m l p) = true ∧
      (probeProtocol (flowKinds F) (nodeSetOf F lay m l) p).le (nodeProtocolOf F lay theta m l p) = true :=
  ⟨Footprints.Change.le_trans (Footprints.Change.le_trans (Footprints.Change.le_max_right _ _)
      (Footprints.Change.le_max_left _ _)) (Footprints.Change.le_max_left _ _),
    Footprints.Change.le_trans (Footprints.Change.le_max_right _ _) (Footprints.Change.le_max_left _ _)⟩

/-- A join that keeps keeps its left side (proved). -/
theorem _root_.Verification.Footprints.Change.max_keep_left {a b : Footprints.Change} (h : a.max b = .keep) :
    a = .keep := by
  revert h; cases a <;> cases b <;> decide

/-- **A step kept at a larger protocol is kept** (proved). -/
theorem stepKeptB_mono {P : Package} {Ψ Ψ' : Protocol P} (h : ∀ p, Ψ' p = .keep → Ψ p = .keep) {q : Footprints.Region}
    (hq : stepKeptB Ψ' q = true) : stepKeptB Ψ q = true := by
  unfold stepKeptB at hq ⊢
  split at hq
  · simp only [List.all_eq_true, beq_iff_eq] at hq ⊢
    exact fun p hp => h p (hq p hp)
  · cases hq

/-- **A region read as protected at a larger protocol is read so** (proved,
`stepKeptB_mono`). -/
theorem protRegionB_mono {P : Package} [DecidableEq P.Site] [Hashable P.Site] {Ψ Ψ' : Protocol P}
    (h : ∀ p, Ψ' p = .keep → Ψ p = .keep) {cp : CopyTable} {arity : Nat} {roPos : Nat → Bool} {m : Code} {l : Nat}
    {r : Footprints.Region} (hr : protRegionB Ψ' cp arity roPos m l r = true) :
    protRegionB Ψ cp arity roPos m l r = true := by
  unfold protRegionB at hr ⊢
  split at hr
  · cases hr
  · simp only [stepsKeptB, Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at hr ⊢
    obtain ⟨hs, hall⟩ := hr
    refine ⟨fun q hq => stepKeptB_mono h (hs q hq), fun l' hl' => ?_⟩
    obtain ⟨e, he, hc⟩ := hall l' hl'
    obtain ⟨hc1, hc2⟩ := hc
    exact ⟨e, he, hc1, fun q hq => stepKeptB_mono h (hc2 q hq)⟩

namespace FramedSpec
variable {ι : Type} (spec : FramedSpec ι)

/-- **The component's checks at the frame's flow** (proved, by
`frame_transport` from the check `componentBindingRefusal` runs at the
flow with the frame's sites and decided tags). -/
theorem frameFlow_checks (h : spec.componentRefusal.val = none) : frameFlowB spec.fflow spec.lay = true :=
  frame_transport spec.C spec.checked (fun _ Fl => frameFlowB Fl spec.lay = true)
    (componentBindingRefusal_none (spec.componentRefusal_none h)).2.2.2.2.2.2

/-- **The checks of a plan's framed nodes at the frame's flow** (proved,
by `frame_transport` from the check at the flow with the frame's sites and
decided tags). -/
theorem framedNodes_frame {m : Code}
    {eff : ∀ {P : Package} [DecidableEq P.Site] [Hashable P.Site], FFlow P → Nat → Option (Option Footprints.Footprint)}
    {prot : ∀ {P : Package} [DecidableEq P.Site] [Hashable P.Site], FFlow P → Nat → Footprints.Region → Bool}
    (h : framedNodesAt spec.fflowC spec.lay spec.theta spec.framed m (eff spec.fflowC) (prot spec.fflowC) = true) :
    framedNodesAt spec.fflow spec.lay spec.theta spec.framed m (eff spec.fflow) (prot spec.fflow) = true :=
  frame_transport spec.C spec.checked
    (fun _ Fl => framedNodesAt Fl spec.lay spec.theta spec.framed m (eff Fl) (prot Fl) = true) h
/-- **The realization check at the frame's flow** (proved, by
`frame_transport`). -/
theorem realized_frame {σ : Type} [Labels ι] [StoreView σ ι] {r : SourceRequest σ ι}
    (h : realizedFlowB spec.fflowC r = true) : realizedFlowB spec.fflow r = true :=
  frame_transport spec.C spec.checked (fun _ Fl => realizedFlowB Fl r = true) h

/-- **The returns check at the frame's flow** (proved, by
`frame_transport`). -/
theorem rets_frame {m : Code} (h : retsInB spec.fflowC m = true) : retsInB spec.fflow m = true :=
  frame_transport spec.C spec.checked (fun _ Fl => retsInB Fl m = true) h

/-- **The checks of the program's starts** (proved): the premises of the
returns at reached executions from a program's initial configurations
(`ret_reachedW_public`, track C1) that the pass checks: the frame's flow's
marks, the request's start a label of its program, the realized code's
proposals the request's at body labels at the frame's flow. -/
theorem starts_checks {σ : Type} [Labels ι] [StoreView σ ι] {r : SourceRequest σ ι}
    {eff : Nat → Option Footprints.Footprint} (hcomp₀ : spec.componentRefusal.val = none)
    (hreq : spec.requestB r eff = true) :
    spec.fflow.marksB = true ∧ r.start < r.program.length ∧ realizedFlowB spec.fflow r = true := by
  simp only [FramedSpec.requestB, Bool.and_eq_true, decide_eq_true_eq] at hreq
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hst⟩, hreal⟩, -⟩, -⟩ := hreq
  obtain ⟨-, hmk, -, -, -⟩ := frameFlowB_sound (spec.frameFlow_checks hcomp₀)
  exact ⟨hmk, hst, spec.realized_frame hreal⟩
end FramedSpec

namespace PassUnit
open HeapObservations

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- **An execution's world transition is admissible** (proved, each step's
admissible, composed). -/
theorem ex_admissible {τ : Type} {fr : ClientFrame τ} {q : Conf × Ghost (fr.F.at fr.C) → Prop} :
    ∀ {n : Nat} {a e : Conf × Ghost (fr.F.at fr.C)}, Ex fr.KStep q n a e → TolerantFrames.Admissible a.1.s e.1.s
  | _, _, _, .refl _ => TolerantFrames.Admissible.refl _
  | _, _, _, .next _ hab he => TolerantFrames.WorldReach.trans hab.1.adm (ex_admissible he)

/-- **The framed returns at the executions the claim is about, from the
checks** (proved, `ret_reachedW_public`): where the component's binding
checks refuse nothing and the request's checks pass (`requestB`, each
framed node's callee's stated effect read by `eff`), and calls meet the
callback row of the client obligation at `eff` (`CallbacksWithin`), the
returns of the plan's framed nodes keeping their supports hold at the
executions the frame's claim is about, read at their worlds; the initial
configurations fit the flow and are entries by definition
(`FramedSpec.initialFits`, `FramedSpec.initialEntry`). -/
theorem framedReturns_reached {spec : FramedSpec ι} {name : String} {r : SourceRequest σ ι}
    {eff : Nat → Option Footprints.Footprint} (hcomp₀ : spec.componentRefusal.val = none)
    (hbind : spec.bindingB name r = true) (hreq : spec.requestB r eff = true) (hcb : spec.CallbacksWithin r eff) :
    FramedReturnsReachedW r (spec.frame r) (Verification.TolerantFrames.framedFOf spec.framed)
      (Verification.TolerantFrames.framedRet (Verification.TolerantFrames.framedSOf spec.framed))
      (fun _ _ _ _ => True) := by
  obtain ⟨hmk, hst, hreal⟩ := spec.starts_checks hcomp₀ hreq
  simp only [FramedSpec.requestB, Bool.and_eq_true] at hreq
  obtain ⟨⟨⟨⟨⟨⟨hc, hsrc⟩, hθ⟩, -⟩, -⟩, hn⟩, hri⟩ := hreq
  obtain ⟨hFa, -, htok, hlow, hTm⟩ := frameFlowB_sound (spec.frameFlow_checks hcomp₀)
  obtain ⟨hatom, heff, hT, hslots, hcheck⟩ := framedNodesAt_sound
    (spec.framedNodes_frame (eff := fun F => spec.boundAt F r eff) (prot := fun F => spec.protAt F r) hn)
  -- The witnesses of the regions read as protected.
  obtain ⟨-, -, -, -, -, -, hro, har, -⟩ := FramedSpec.bindingB_iff.mp hbind
  have hnone := componentBindingRefusal_none (spec.componentRefusal_none hcomp₀)
  have hr : noRestB spec.lay = true := hnone.2.2.2.2.2.1
  have hcomp : (spec.F.at spec.C).ofC r.comp = true := compB_sound hc
  have hm := FFlow.marksB_sound hmk
  have hinitF := spec.initialFits r
  have hinitE := spec.initialEntry r
  have hinit : ∀ x, spec.Initial r x → spec.ProgOk r (x, bareStart (spec.core r).F (spec.core r).C x.t) :=
    fun _ hx => spec.progOk_initial r hx
  have hrets : spec.RetsIn r := fun hi c π hc =>
    FramedSpec.retsInB_sound (spec.rets_frame (by simpa [hi] using hri)) c π hc
  have hE := spec.entryFits r hr hFa hst hreal hcomp hinit hrets
  have hcs := spec.chkSound r hFa hm hE
  have hsi := spec.startInv r hFa hm hinitF hinitE hcomp
  have hwk := spec.wok_start r (fun _ hx => hx.2.2.1.2.2.2)
  have hw : (spec.frame r).ProtWitness (r.program.map (·.expression))
      (r.program.map fun n => (n.continuation, n.handler)) r.comp (Verification.TolerantFrames.framedFOf spec.framed)
      (Verification.TolerantFrames.framedSOf spec.framed) (fun l => spec.protAt spec.fflow r l) := by
    cases hi : spec.inner with
    | true =>
      have h0 : (fun l => spec.protAt spec.fflow r l) = fun _ _ => false := by
        funext l q; simp [FramedSpec.protAt, hi]
      rw [h0]; exact ClientFrame.ProtWitness.none
    | false =>
    intro l b₀ e L d k x _ hb _ hk _ hbt T _ e' _ hp w _ hmem hL
    exact spec.prot_witness r hr hFa hst hreal hcomp har hro hi hm hinitF hinitE hinit hrets hcs hsi hE hwk
      (fun p => thetaKeepB_keep hθ p) (copiesOf_sound _ _ _ _ _) hb hk hbt e'.1
      (protRegionB_mono (fun p hp => Footprints.Change.max_keep_left hp)
        ((Bool.and_eq_true _ _).mp hp).2) w hmem hL
  exact ret_reachedW_public spec r (F := Verification.TolerantFrames.framedFOf spec.framed)
    (S := Verification.TolerantFrames.framedSOf spec.framed) hsrc hcomp₀ hFa hmk hst hreal
    hinitF hinitE htok hlow hcomp hrets hatom (S₀ := operandSetsOf spec.fflow (requestCode r))
    (T := nodeSetOf spec.fflow spec.lay (requestCode r))
    (Ψc := nodeProtocolOf spec.fflow spec.lay spec.theta (requestCode r)) hT
    (fun l _ p => (nodeProtocolOf_ge spec.fflow spec.lay spec.theta (requestCode r) l p).2) hslots
    (Φ := fun l => ((spec.boundAt spec.fflow r eff l).getD none).getD [])
    (own := fun l => ((spec.boundAt spec.fflow r eff l).getD none).isNone)
    (fun l e k x hl ho he hk c π l' hc hn T hT => by
      have h := hcheck l e k x hl he hk c π l' hc hn T hT
      generalize (spec.boundAt spec.fflow r eff l).getD none = b at h ho ⊢
      cases b with
      | none => simp at ho
      | some Φ => exact h)
    hw hTm
    (fun p => thetaKeepB_sound hθ _ p)
    (fun l p => (nodeProtocolOf_ge spec.fflow spec.lay spec.theta (requestCode r) l p).1)
    (fun l b₀ a m e L d k x v hl ho hb he hk hL hbt hex hat hv => by
      have hb' := heff l hl
      by_cases hcl : spec.clientCallee r l = true
      · -- (an argument's own value at an entry: the callback row)
        simp only [FramedSpec.boundAt, callBound, hcl, ite_true] at hb' ho ⊢
        cases hE : eff l with
        | none => rw [hE] at hb'; cases hb'
        | some Φ =>
          simp only [Option.map_some, Option.getD_some]
          exact hcb l Φ b₀ a m e L d k x v (framedFOf_mem hl) hcl hE hb he hk hL.1 hL.2 hbt hex hat hv
      · -- (any other call with an outside run: the top effect)
        simp only [FramedSpec.boundAt, callBound, hcl, Bool.false_eq_true, ite_false] at ho ⊢
        cases hno : noOutB spec.fflow
        · simp only [Bool.false_eq_true, ite_false, Option.getD_some]
          exact TolerantFrames.action_top (ex_admissible hex)
        · simp [hno] at ho)
    ⟨fun l hl ho => by
      have hb' := heff l hl
      by_cases hcl : spec.clientCallee r l = true
      · simp only [FramedSpec.boundAt, callBound, hcl, ite_true] at hb' ho
        cases hE : eff l with
        | none => rw [hE] at hb'; cases hb'
        | some Φ => simp [hE] at ho
      · simp only [FramedSpec.boundAt, callBound, hcl, Bool.false_eq_true, ite_false] at ho
        cases hno : noOutB spec.fflow
        · simp [hno] at ho
        · exact noOutB_sound hno,
     fun l e k x hl ho he hk c π l' hc hn T hT => by
      have h := hcheck l e k x hl he hk c π l' hc hn T hT
      simp only at ho
      generalize (spec.boundAt spec.fflow r eff l).getD none = b at h ho
      cases b with
      | none => exact h
      | some Φ => simp at ho⟩
end
end PassUnit

end Verification.SourceClaimJson
