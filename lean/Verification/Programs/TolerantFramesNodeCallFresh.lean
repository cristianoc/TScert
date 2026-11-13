import Verification.Programs.TolerantFramesNodeBound
import Verification.Programs.TolerantFramesWalkReassignWalk

/-! # Tolerant frames: the footprint check kept along a run

`FootprintKept` (`TolerantFramesGuarantee`) asks, at every node entry where
the pass's typed assertion holds and the node is in the no-return region
`dead` or the heap is within `Φ` from the invocation's entry `h₀`, that every
run of the node's term with budget left reaches an exit meeting the same
property at its target, a return within `Φ` (its value fresh where the bound
states a fresh result) and an escaping throw within `Φ` where the bound
covers throws.

`BoundChecked` is the check `run` makes at a node under a bound (the
footprint bound at this node), over a checked node (`NodeChecked`): inside
`dead`, `deadNode` and no throw bound; outside it, `footprintCheck` at the
values `run` computes there, its `outFresh` restated as `passOutFreshChecked`
(a copy of a slot holding a fresh name, or a call stating a fresh result
whose derivation `derivChecked` accepts). `callFresh_of_checked` proves the
call disjunct gives every run of the node's term to a value within the
state's budget a store allocated at or past the mark, the mark at most the
heap's length; outside `dead` the heap is within `Φ` from `h₀`, so at least
as long as `h₀`. `footprintKept_of` composes these with the step theorem
(`stepChecked_parts`) into `FootprintKept`; `BoundChecked.reassign` carries
the check to every reassigned graph. -/
namespace Verification.TolerantFrames
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules

section CallFresh
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

omit [Hashable ι] [Instantiates ι] in
/-- `run`'s `outFresh` at a node (the pass's code): a copy of a slot holding
a fresh name, or a call at a selected signature stating a fresh result,
its operands selected, whose derivation `derivChecked` accepts at the
step's knowledge `stepK`. -/
def passOutFreshChecked (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) (c : PointClaim ι) (node : Node) (entry : SinglePass.State)
    (stepK : HeapKnowledge.Knowledge) (deriv : ProgramCertificates.Evidence ι) : Bool :=
  (match node.expression with
    | .var i => (entry.names[i]?).any entry.fresh.contains
    | _ => false) ||
    ((match ExpressionEffects.selectedEffect deriv with | some eff => eff.fresh | none => false) &&
      ExpressionEffects.selectedOperands deriv &&
      SinglePass.derivChecked G images codes sums c node stepK deriv)

omit [Hashable ι] [Instantiates ι] in
/-- **`outFresh`'s two cases**: a copy of a fresh slot, or a call stating a
fresh result (`passCallFresh`) whose derivation passes `passDerivChecked`
at the node's sequent. -/
theorem passOutFreshChecked_cases {G : NormalGraph ι} {images : InstanceImageCheck G}
    {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} {c : PointClaim ι} {node : Node}
    {entry : SinglePass.State} {stepK : HeapKnowledge.Knowledge} {deriv : ProgramCertificates.Evidence ι}
    (h : passOutFreshChecked G images codes sums c node entry stepK deriv = true) :
    (match node.expression with
      | .var i => (entry.names[i]?).any entry.fresh.contains
      | _ => false) = true ∨
    (passCallFresh node deriv = true ∧
      passDerivChecked G images codes sums stepK ⟨c.context, node.expression, c.type⟩ deriv = true) := by
  simp only [passOutFreshChecked, Bool.or_eq_true, Bool.and_eq_true] at h
  refine h.imp id fun ⟨⟨hf, ho⟩, hd⟩ => ?_
  have hd' := hd
  simp only [SinglePass.derivChecked, Bool.and_eq_true] at hd'
  refine ⟨?_, hd⟩
  simp only [passCallFresh, Bool.and_eq_true]
  exact ⟨⟨hf, ho⟩, hd'.1.1⟩

omit [Hashable ι] [Instantiates ι] in
/-- **The checked call disjunct gives a fresh result** (what D4 makes
provable): where the selected effect states a fresh result
(`passCallFresh`) and `passDerivChecked` accepts the derivation at the
node's term and context (its tree, or `requiresTree` at the step's
knowledge, which holds), every run of the node's term to a value within
the budget returns a store allocated at or past the heap's length, hence
at or past any mark below it. -/
theorem callFresh_of_checked {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} {kS : HeapKnowledge.Knowledge} {c : PointClaim ι} {node : Node}
    {d : ProgramCertificates.Evidence ι}
    (hcf : passCallFresh node d = true)
    (hdc : passDerivChecked G images codes sums kS ⟨c.context, node.expression, c.type⟩ d = true)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ : Env} {s : IndexedHeap} {m : Nat} (hm : m ≤ s.h.length)
    (he : EnvOk G c.context ρ s.n s.W) (hkS : HeapKnowledge.Holds kS ε ρ s.h) :
    ∀ k h' v, k < s.n → Steps k s.h (instantiate 0 ρ node.expression) h' v → isVal v = true → FreshAt m v := by
  simp only [passCallFresh, Bool.and_eq_true, beq_iff_eq] at hcf
  obtain ⟨⟨hfr, hops⟩, hterm⟩ := hcf
  simp only [passDerivChecked, Bool.and_eq_true, beq_iff_eq] at hdc
  obtain ⟨⟨-, hctx⟩, htree⟩ := hdc
  cases heff : ExpressionEffects.selectedEffect d with
  | none => rw [heff] at hfr; cases hfr
  | some eff =>
    rw [heff] at hfr
    simp only at hfr
    have hs : SafePost (excOf G) (meaning G (claim d).type)
        (eff.post (ExpressionEffects.receiverOf (instantiate 0 ρ (claim d).term))
          (ExpressionEffects.actualsOf (instantiate 0 ρ (claim d).term)) s.h) s.n s.W s.h
        (instantiate 0 ρ (claim d).term) := by
      rcases Bool.or_eq_true_iff.mp htree with htree | hreq
      · exact ExpressionEffects.selected_sound d htree hops heff hcodes hsums (hctx ▸ he) s.adm s.ok
      · obtain ⟨eff', heff', hs⟩ := PromiseCalls.requiresTree_sound hcodes hsums d hreq
        rw [heff] at heff'
        cases heff'
        exact hs (hctx ▸ he) hkS s.adm s.ok
    rw [hterm] at hs
    intro k h' v hk hst hv
    have hpost := GraphCode.returnsPost_of_safePost hs k h' v hk hst hv
    exact FreshAt.lower hm (hpost.2.1 hfr)

/-- **The footprint bound's check at a checked node** (`run`, "The footprint
bound at this node", under `bound = some (Φ, ret, exc)` and the region
`dead`): inside the region, `deadNode` with no throw bound; outside it,
`footprintCheck` at the step's values, `outFresh` as `run` computes it
(`passOutFreshChecked`). -/
def BoundChecked {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {pc : SinglePass.PassChecker G images} {P : ControlFlow.Program} {w : Walk ι} {startNames : List Nat}
    {ctx : Nat → List (Ty ι)} {l : Nat} (r : NodeChecked G images codes pc P w startNames ctx l)
    (Φ : Footprints.Closed) (dead : List Bool) (ret exc : Bool) : Prop :=
  (GraphCode.deadAt dead l = true →
    GraphCode.deadNode G dead r.node (passDeadEvidence r.c r.node) = true ∧ exc = false) ∧
  (GraphCode.deadAt dead l = false →
    SinglePass.footprintCheck G images codes r.ans.summaries.toList Φ (passRecvFresh r.node r.entry) r.c r.node
      r.st.stepK (passDerivOf r.c r.node r.st) (passLiveHandler dead r.node) exc ret
      (passOutFreshChecked G images codes r.ans.summaries.toList r.c r.node r.entry r.st.stepK
        (passDerivOf r.c r.node r.st)) = true)

omit [Hashable ι] [Instantiates ι] in
/-- `outFresh` at a reassigned graph: the derivation's check is the same
(`checkTree_reassign`, `requiresTree_reassign`). -/
theorem passOutFreshChecked_reassign (G : NormalGraph ι) (η : MixedAssignment ι) (images : InstanceImageCheck G)
    (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) (c : PointClaim ι) (node : Node)
    (entry : SinglePass.State) (stepK : HeapKnowledge.Knowledge) (deriv : ProgramCertificates.Evidence ι) :
    passOutFreshChecked (reassign G η) (images.reassign η) codes sums c node entry stepK deriv =
      passOutFreshChecked G images codes sums c node entry stepK deriv := by
  simp only [passOutFreshChecked, SinglePass.derivChecked, Parametricity.checkTree_reassign,
    Parametricity.requiresTree_reassign]

omit [Instantiates ι] in
/-- **The bound's check at a reassigned graph**: a node whose bound `run`
checks at `G` is checked at `reassign G η`, the node carried by
`nodeChecked_reassign`. -/
theorem BoundChecked.reassign {G : NormalGraph ι} {η : MixedAssignment ι} {images : InstanceImageCheck G}
    {codes : CodeEntry ι → Bool} {pc : SinglePass.PassChecker G images}
    {pc' : SinglePass.PassChecker (reassign G η) (images.reassign η)} {P : ControlFlow.Program} {w : Walk ι}
    {startNames : List Nat} {ctx : Nat → List (Ty ι)} {l : Nat} (hpc : PassCheckerReassign G η images pc pc')
    {r : NodeChecked G images codes pc P w startNames ctx l} {Φ : Footprints.Closed} {dead : List Bool}
    {ret exc : Bool} (hb : BoundChecked r Φ dead ret exc) :
    BoundChecked (nodeChecked_reassign hpc r) Φ dead ret exc := by
  refine ⟨fun hd => hb.1 hd, fun hd => ?_⟩
  have h2 := hb.2 hd
  show SinglePass.footprintCheck (PositiveRules.reassign G η) (images.reassign η) codes r.ans.summaries.toList Φ _ r.c r.node
    r.st.stepK _ _ exc ret (passOutFreshChecked (PositiveRules.reassign G η) (images.reassign η) codes r.ans.summaries.toList
      r.c r.node r.entry r.st.stepK (passDerivOf r.c r.node r.st)) = true
  rw [passOutFreshChecked_reassign, footprintCheck_reassign]
  exact h2

omit [Instantiates ι] in
/-- **The footprint check keeps the bound at every node** (`FootprintKept`):
where every visited node is checked (`NodeChecked`), its entry state holds
where the typed node assertion does at the mark `|h₀|`, `run` checked its
bound there (`BoundChecked`, with `ret` the bound's fresh result and `exc`
its throw bound) and the codes are sound, every node keeps `BoundX`: a run
of a node outside `dead` from a heap within `Φ` stays within it on each
exit (`footprint_exits`, its fresh receivers from the state,
`freshOk_recv`), a return's value fresh where `ret` (`passOutFreshChecked`:
a copy of a fresh slot, `copyFresh`, or a checked fresh call,
`callFresh_of_checked`, the heap at least as long as `h₀`); a run of a node
of `dead` reaches a target of `dead` or no normal exit (`deadNode`: an
empty result type, or a continuation into `dead`), and a throw a handler of
`dead`, or escapes with no throw bound. -/
theorem footprintKept_of {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {pc : SinglePass.PassChecker G images} {P : ControlFlow.Program} {w : Walk ι} {startNames : List Nat}
    {ctx : Nat → List (Ty ι)} {Φ : Footprints.Closed} {h₀ : Heap} {dead : List Bool} {ret exc : Bool}
    (hacc : ∀ l, w.visited l → ∃ r : NodeChecked G images codes pc P w startNames ctx l,
      (∀ ρ (s : IndexedHeap), passPreT G w startNames ε ctx l ρ h₀.length s →
        StateHolds G r.entry (w.implies l) startNames ε ρ h₀.length s) ∧ BoundChecked r Φ dead ret exc)
    (hcodes : CodesSound G codes) :
    FootprintKept P G w startNames ε ctx Φ h₀ dead ret exc := by
  intro l ρ s hp hX
  obtain ⟨na, hent, hb⟩ := hacc l hp.1.1
  have hS := hent ρ s hp
  have he : EnvOk G na.c.context ρ s.n s.W := na.hctx ▸ hp.2
  obtain ⟨hsums', hkS, -, cn, ce, hj, hn, hx⟩ :=
    stepChecked_parts na.hstep hS na.wf na.below na.width he hcodes na.sums
  have hex := (stepExits_of hj hn hx).2
  refine ⟨na.node, na.hP, fun k h' t' hst hk => ?_⟩
  cases hd : GraphCode.deadAt dead l with
  | true =>
    obtain ⟨hdn, hexc⟩ := hb.1 hd
    simp only [GraphCode.deadNode, passDeadEvidence_result, Bool.and_eq_true, Bool.or_eq_true] at hdn
    refine ⟨fun hv => ?_, fun e hr => ?_⟩
    · obtain ⟨s', -, -, -, hT, -⟩ := (hex k h' t' hst hk).1 hv
      rcases hdn.1 with hempty | hcont
      · exact (ExpressionEffects.emptyType_sound hempty hT).elim
      · simp only [GraphCode.deadContinuation, Bool.and_eq_true, List.all_eq_true] at hcont
        exact contKeeps_of (fun t ht _ => .inl (hcont.2 t ht))
          (fun hk' => by rw [hk'] at hcont; simp at hcont)
    · cases hh : na.node.handler with
      | none => intro hexc'; rw [hexc] at hexc'; cases hexc'
      | some t =>
        have := hdn.2
        simp only [GraphCode.deadHandler, hh] at this
        exact .inl this
  | false =>
    have hΦ : Φ.Holds h₀ s.h := hX.resolve_left (by simp [hd])
    have hm : h₀.length ≤ s.h.length := hΦ.1
    have hfc := hb.2 hd
    have hsafe : Safe (excOf G) (meaning G na.c.type) s.n s.W s.h (instantiate 0 ρ na.node.expression) :=
      HeapObservations.erase hj.post
    obtain ⟨hN, hT⟩ := footprint_exits hfc hcodes hsums' (freshOk_recv hS) he hkS hsafe hΦ hst hk
    obtain ⟨-, -, hret, -⟩ := footprintCheck_sound hfc
    refine ⟨fun hv => contKeeps_of (fun _ _ _ => .inr (hN hv)) fun hk' => ⟨hN hv, fun hr => ?_⟩,
      fun e hr => ?_⟩
    · rcases passOutFreshChecked_cases (hret hk' hr) with hc | ⟨hcf, hdc⟩
      · exact copyFresh hS he na.width hc hst
      · exact callFresh_of_checked hcf hdc hcodes hsums' hm he hkS k h' t' hk hst hv
    · cases hh : na.node.handler with
      | none =>
        intro hexc
        exact hT (by simp [hexc]) e hr
      | some t =>
        simp only [HandlerKeeps, BoundX]
        cases hdt : GraphCode.deadAt dead t.label with
        | true => exact .inl rfl
        | false => exact .inr (hT (by simp [passLiveHandler, hh, hdt]) e hr)

end CallFresh

end Verification.TolerantFrames
