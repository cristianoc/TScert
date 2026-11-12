import Verification.Programs.TolerantFramesExitDelivers

/-! # Exit checks and their final-world delivery

The initial and per-exit yield lists equal the node's kept yields.
`AfterStep` carries their `YieldsOk` at the final state; the exit checks
supply mapping bounds and normal and handler delivery.
-/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules

section Node
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

/-- **What the visit checks on a node's exits** at its claim `c`, entry,
step `st` and kept yields `ys`, with the node's `here` answer, the step's
`outFresh`, the yields the exits' contexts read `ysA`, the thrown value's
name `thrown` and type `TT`. -/
structure NodeExitsChecked (G : NormalGraph ι) (images : InstanceImageCheck G) (w : Walk ι)
    (startNames : List Nat) (ctx : Nat → List (Ty ι)) (stated : Nat → Option HeapKnowledge.Knowledge)
    (given : Nat → Bool)
    (edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping))
    (l : Nat) (node : Node) (c : PointClaim ι) (entry : SinglePass.State) (st : Stepped ι)
    (ys : List (PromiseCalls.Yield ι)) (here outFresh : Bool) (ysA : List (PromiseCalls.Yield ι)) (thrown : Nat)
    (TT : Ty ι) : Prop where
  hereEmpty : here = true → HereEmpty G c.context
  yieldsRead : ysA = ys
  widths : ∀ (i : Nat) t pushed observed promote, (Exit.ofNode node)[i]? = some (Exit.normal t pushed observed promote) →
    ∀ slots, t.mapping = some slots → ∀ j ∈ slots, j < (normalNames entry st pushed).length
  handlerWidth : ∀ t, node.handler = some t → ∀ slots, t.mapping = some slots → ∀ j ∈ slots,
    j < (thrown :: entry.names).length
  normal : ∀ (i : Nat) t pushed observed promote, (Exit.ofNode node)[i]? = some (Exit.normal t pushed observed promote) →
    ∃ ysE : List (PromiseCalls.Yield ι), ysE = ys ∧
      (given t.label = false →
        NonHeadExitChecked G images w ctx stated edgesIn l node c entry st ys ysA ysE here outFresh i t pushed observed
          promote) ∧
      (given t.label = true → ∃ (req written : HeapKnowledge.Knowledge) (cf : List HeapKnowledge.IndexAtom)
        (gimp : List (PromiseCalls.Implication ι)) (argName : Option Nat) (argSlots : List Nat)
        (inputSlots : List (Nat × Nat)) (hwidth hfresh : Nat),
        HeadExitChecked G images w startNames ctx stated l node c entry st ys ysE here i t pushed observed promote req
          written cf gimp argName argSlots inputSlots hwidth hfresh ∧
        (∀ y ∈ startNames, y < hfresh) ∧ (∀ a, argName = some a → ∃ q : Nat, startNames[q]? = some a))
  handler : ∀ t, node.handler = some t →
    HandlerExitChecked G images w startNames ctx stated given edgesIn l c entry st here outFresh TT thrown t
  thrownBelow : node.handler.isSome = true → NamesBelow entry (w.implies l) startNames thrown

/-- Exit checks reassign with the same kept yield lists. -/
theorem NodeExitsChecked.reassign {G : NormalGraph ι} {images : InstanceImageCheck G} {w : Walk ι}
    {startNames : List Nat} {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge}
    {given : Nat → Bool}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {l : Nat} {node : Node} {c : PointClaim ι} {entry : SinglePass.State} {st : Stepped ι}
    {ys : List (PromiseCalls.Yield ι)} {here outFresh : Bool} {ysA : List (PromiseCalls.Yield ι)} {thrown : Nat}
    {TT : Ty ι}
    (hc : NodeExitsChecked G images w startNames ctx stated given edgesIn l node c entry st ys here outFresh ysA thrown TT)
    (η : MixedAssignment ι) :
    NodeExitsChecked (reassign G η) (images.reassign η) w startNames ctx stated given edgesIn l node c entry st ys
      here outFresh ysA thrown TT where
  hereEmpty h := (hc.hereEmpty h).reassign η
  yieldsRead := hc.yieldsRead
  widths := hc.widths
  handlerWidth := hc.handlerWidth
  normal i t pushed observed promote hm := by
    obtain ⟨ysE, hE, hnh, hh⟩ := hc.normal i t pushed observed promote hm
    refine ⟨ysE, hE, fun hn => (hnh hn).reassign η, fun hg => ?_⟩
    obtain ⟨req, written, cf, gimp, argName, argSlots, inputSlots, hwidth, hfresh, hc, hlt, ha⟩ := hh hg
    exact ⟨req, written, cf, gimp, argName, argSlots, inputSlots, hwidth, hfresh, hc.reassign η, hlt, ha⟩
  handler t ht := (hc.handler t ht).reassign η
  thrownBelow := hc.thrownBelow

/-- **A node's exits and handler deliver** (`NodeExitsY` with the step's
result's freshness in the state after the step, `AfterStep`). -/
structure NodeExitsYF (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat)
    (ρ0 : Env) (ctx : Nat → List (Ty ι)) (stated : Nat → Option HeapKnowledge.Knowledge) (given : Nat → Bool)
    (edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping))
    (m : Nat) (l : Nat) (node : Node) (c : PointClaim ι) (entry : SinglePass.State) (st : Stepped ι)
    (ys : List (PromiseCalls.Yield ι)) (outFresh : Bool) : Prop where
  exits : ∀ t pushed observed promote, Exit.normal t pushed observed promote ∈ Exit.ofNode node → ∀ ρ,
    ExitDelivers (edgePreAJ G w startNames ρ0 ctx stated given edgesIn) G c.type c.context
      (AfterStep G w startNames ρ0 l entry st ys outFresh ρ) ρ m t pushed observed promote
  handler : ∀ t, node.handler = some t → ∀ ρ (s' : IndexedHeap) e,
    StateHolds G ⟨entry.names, entry.store.dropHeap (fun _ => false), entry.fresh⟩ (w.implies l) startNames ρ0
      ρ m s' →
    EnvOk G c.context ρ s'.n s'.W → Scoped 0 e → excOf G s'.n s'.W e →
    edgePreAJ G w startNames ρ0 ctx stated given edgesIn t.label (PointClaims.mapEnv t.mapping (push e ρ)) m s'

/-- Exit checks, sound subtype answers and the kept exit yields deliver
at the graph of the checks. Mapping bounds supply `MapNamesSound`. -/
theorem nodeExitsYF_of_checks {G : NormalGraph ι} {images : InstanceImageCheck G} {w : Walk ι}
    {startNames : List Nat} {ρ0 : Env} {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge}
    {given : Nat → Bool}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {l : Nat} {node : Node} {c : PointClaim ι} {entry : SinglePass.State} {st : Stepped ι}
    {ys : List (PromiseCalls.Yield ι)} {here outFresh : Bool} {ysA : List (PromiseCalls.Yield ι)} {thrown : Nat}
    {TT : Ty ι}
    (hc : NodeExitsChecked G images w startNames ctx stated given edgesIn l node c entry st ys here outFresh ysA thrown
      TT)
    (hshape : SinglePass.passShapeCheck' G c.type node.continuation = true) (wf : StoreWF entry.store)
    (hnd : startNames.Nodup)
    (hsub : SubtypeAnswersSound G images) (m : Nat) :
    NodeExitsYF G w startNames ρ0 ctx stated given edgesIn m l node c entry st ys outFresh where
  exits t pushed observed promote hmem ρ := by
    obtain ⟨i, hm⟩ := List.mem_iff_getElem?.mp hmem
    obtain ⟨ysE, hE, hnh, hhd⟩ := hc.normal i t pushed observed promote hm
    cases hg : given t.label with
    | false =>
      exact nonHeadExit_delivers hm (hnh hg) hshape hsub
        (mapNamesSound_of_lt fun slots hs => hc.widths i t pushed observed promote hm slots hs)
        hc.hereEmpty (fun _ _ _ _ h => hc.yieldsRead ▸ h.2.1) (fun _ _ _ _ h => hE ▸ h.2.1) ρ m
    | true =>
      obtain ⟨req, written, cf, gimp, argName, argSlots, inputSlots, hwidth, hfresh, hh, hlt, hargs⟩ := hhd hg
      exact headExit_delivers hm hh hg hshape hsub hc.hereEmpty (fun _ _ _ _ h => hE ▸ h.2.1) hnd hlt hargs ρ m
  handler t ht ρ s' e hS he hsc hx :=
    handlerExit_delivers (hc.handler t ht) hsub (mapNamesSound_of_lt (hc.handlerWidth t ht))
      hc.hereEmpty wf (hc.thrownBelow (by rw [ht]; rfl)) hnd ρ m s' e hS he hsc hx

end Node

end Verification.TolerantFrames
