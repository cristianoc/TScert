import Verification.Programs.TolerantFramesExitDelivers

/-! # Tolerant frames: a node's exits deliver from what the visit checked on them

What `visitExits` checks at a node's values (`NodeExitsChecked`): the
node's `here` answer stating its context empty, the yields the exits read
(`ysA`) the kept ones or none, each mapping's slots below its source's
width (`ExitsWidth`), and each exit's checks: a normal exit's into a node
other than a loop head (`NonHeadExitChecked`) or into a loop head
(`HeadExitChecked`, with the start names below the head's counter), the
yields its implications read (`ysE`) the kept ones or none; the handler's
(`HandlerExitChecked`), the thrown name above the entry's names. All of it
is stated by the pass's functions and what their searches found, the same
at every reassigned graph.

Proved (`nodeExitsYF_of_checks`): at every reassigned graph, those checks
with the subtype answers sound there give every exit and the handler
delivering `edgePreAJ` (`NodeExitsYF`), each normal exit from the state
after the step with its kept yields, its output and, where the step
states its result fresh and its name is not fresh yet, the result's
freshness (`AfterStep`). `NodeExitsY` is `NodeExitsYF` without that last
conjunct of the state after the step: the edge lemmas need it wherever an
exit pushes a fresh result (`normal_edge_delivers`'s `hfo`), and it is a
property of the step's run (`callFresh_of_checked`, at `outFreshOf_eq`). -/
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
  yieldsRead : ysA = [] ∨ ysA = ys
  widths : ∀ (i : Nat) t pushed observed promote, (Exit.ofNode node)[i]? = some (Exit.normal t pushed observed promote) →
    ∀ slots, t.mapping = some slots → ∀ j ∈ slots, j < (normalNames entry st pushed).length
  handlerWidth : ∀ t, node.handler = some t → ∀ slots, t.mapping = some slots → ∀ j ∈ slots,
    j < (thrown :: entry.names).length
  normal : ∀ (i : Nat) t pushed observed promote, (Exit.ofNode node)[i]? = some (Exit.normal t pushed observed promote) →
    ∃ ysE : List (PromiseCalls.Yield ι), (ysE = [] ∨ ysE = ys) ∧
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

/-- **(`nodeExitsYF_of_checks`) A node's exits deliver from the visit's
checks at every reassigned graph**: `NodeExitsChecked` at `G`, the node's
shape check, the entry's store well-formed, the start names distinct and
the subtype answers sound at `reassign G η` give `NodeExitsYF` there
(`nonHeadExit_delivers`, `headExit_delivers`, `handlerExit_delivers` at the
checks reassigned; each mapping's names sound by `mapNamesSound_of_lt`). -/
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
    (hnd : startNames.Nodup) (η : MixedAssignment ι)
    (hsub : SubtypeAnswersSound (PositiveRules.reassign G η) (images.reassign η)) (m : Nat) :
    NodeExitsYF (PositiveRules.reassign G η) w startNames ρ0 ctx stated given edgesIn m l node c entry st ys outFresh where
  exits t pushed observed promote hmem ρ := by
    obtain ⟨i, hm⟩ := List.mem_iff_getElem?.mp hmem
    have hshape' : SinglePass.passShapeCheck' (PositiveRules.reassign G η) c.type node.continuation = true := by
      rw [passShapeCheck'_reassign]; exact hshape
    have hhere : here = true → HereEmpty (PositiveRules.reassign G η) c.context := fun h => (hc.hereEmpty h).reassign η
    obtain ⟨ysE, hE, hnh, hhd⟩ := hc.normal i t pushed observed promote hm
    cases hg : given t.label with
    | false =>
      exact nonHeadExit_delivers hm ((hnh hg).reassign η) hshape' hsub
        (mapNamesSound_of_lt fun slots hs => hc.widths i t pushed observed promote hm slots hs) hhere hc.yieldsRead hE
        ρ m
    | true =>
      obtain ⟨req, written, cf, gimp, argName, argSlots, inputSlots, hwidth, hfresh, hh, hlt, hargs⟩ := hhd hg
      exact headExit_delivers hm (hh.reassign η) hg hshape' hsub hhere hE hnd hlt hargs ρ m
  handler t ht ρ s' e hS he hsc hx :=
    handlerExit_delivers ((hc.handler t ht).reassign η) hsub (mapNamesSound_of_lt (hc.handlerWidth t ht))
      (fun h => (hc.hereEmpty h).reassign η) wf (hc.thrownBelow (by rw [ht]; rfl)) hnd ρ m s' e hS he hsc hx

end Node

end Verification.TolerantFrames
