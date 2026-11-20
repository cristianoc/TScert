import Verification.Source.Claims.FramedBinding
import Verification.Source.Claims.FramedFrameFlow
import Verification.Paper.TolerantFrames.ReadOnlyTransfer
import Verification.Paper.TolerantFrames.ReadOnlyCallFrame
import Verification.Paper.TolerantFrames.ReadOnlyBridge
import Verification.Paper.TolerantFrames.ReadOnlyFitsReach

/-! # The checks of a framed plan's call nodes, at the frame's flow

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "What the pass checks" and "The
returns, at reached executions"). The returns at a framed call node `l`
of the request's code (`ret_reachedW_spec`) read, of the flow the frame
reads, at every context of the request's code and every node `l'` sharing
`l`'s continuation and handler (`NodeOf`, `sharingNodes`):

- **the call's operands** read from slots or constants (`atomCallB`);
- **the node's set** $`T_l`$ (`nodeSet`): the closure, under contents and
  captures, of the sets of `l`'s operand slots at each such `l'` and
  context (`operandSets`), checked closed and holding them (`capClosedB`);
- **the node's protocol** $`\Psi_c(l)`$ (`nodeProtocol`): the client
  obligation $`\Theta_C`$ joined with the component's protocol
  (`componentProtocol`) and the depth charges at $`T_l`$
  (`probeProtocol`), so that the component's protocol and the charges are
  within it by definition;
- **each support the node keeps** passing the frame's check at that
  protocol and the callee's stated effect (`frameCheckAt`, the separation
  of classes, no keys, no protection) at each such `l'` and context.

`framedNodesB` decides them at every framed node of a plan, at the flow at
the frame's sites with its tags decided (`FramedSpec.fflowC`), which
`frame_transport` reads at the frame's. A plan's client obligation keeps
every part (`thetaKeepB`), as the returns read $`\Theta_C`$ below the
component's protocol at every part; and its request's node expressions are
source terms (`sourceTermsB`).

**The callback row** (`FramedSpec.CallbacksWithin`, the owner's decision
of 2026-11-19, a part of $`\Theta_C`$): a call at a framed node of the
request's code, whose callee may be a value of outside code and whose
callee's type states an effect, from a reached state to its return,
changes the heap within that effect. -/

namespace Verification.TolerantFrames.ReadOnly.ClientFrame
open Verification

/-- **An operand read from the slots**: a slot or a primitive constant,
which the node's entry instantiates to a value. -/
def atomB : Tm → Bool
  | .var _ | .nul | .undef | .tru | .fls | .num _ | .str _ => true
  | _ => false

/-- **A call of operands read from the slots** (decided at each framed
node): an invocation whose callee, receiver and arguments are slots or
constants. -/
def atomCallB : Tm → Bool
  | .invoke f r args => atomB f && atomB r && args.all atomB
  | _ => false

/-- **The slots a call's operands read**: the slot of each operand of an
invocation that is a slot. -/
def atomSlots : Tm → List Nat
  | .invoke f r args => (f :: r :: args).filterMap fun
    | .var j => some j
    | _ => none
  | _ => []
end Verification.TolerantFrames.ReadOnly.ClientFrame

namespace Verification.Footprints
/-- The order of changes is transitive (proved). -/
theorem Change.le_trans {a b c : Change} (h₁ : a.le b = true) (h₂ : b.le c = true) : a.le c = true := by
  simp only [Change.le, decide_eq_true_eq] at *; omega

/-- `keep` is at most every change (proved). -/
theorem Change.keep_le (a : Change) : Change.keep.le a = true := by
  cases a <;> decide
end Verification.Footprints

namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceElaboration ControlFlow LabelStore
open Verification.TolerantFrames.ReadOnly Verification.TolerantFrames.ReadOnly.ClientFrame

section
variable {P : Package} [DecidableEq P.Site] [Hashable P.Site]

/-- **The nodes sharing a node's continuation and handler** in a code. -/
def sharingNodes (m : Code) (l : Nat) : List Nat := (List.range m.2.length).filter fun l' => m.2[l']? == m.2[l]?

/-- **The sets of a call's operand slots**: at every context of the code
and every node sharing the call's continuation and handler, the set of
each slot an operand of `e` reads. -/
def operandSets (F : FFlow P) (m : Code) (l : Nat) (e : Tm) : Sites P :=
  (F.ctxs m).flatMap fun (_, c) => (sharingNodes m l).flatMap fun l' => (atomSlots e).flatMap fun j => (c.node l').envAt j

/-- **A framed node's set** $`T_l`$: the closure of its operand sets
under contents and captures. -/
def nodeSet (F : FFlow P) (lay : List (Nat × Bool × Nat × Nat)) (m : Code) (l : Nat) (e : Tm) : Sites P :=
  capClose F (tokenCaps F lay) (operandSets F m l e)

/-- **A framed node's protocol** $`\Psi_c(l)`$: the client obligation, the
component's protocol and the depth charges at the node's set, joined. -/
def nodeProtocol (F : FFlow P) (lay : List (Nat × Bool × Nat × Nat)) (Θ : Protocol P) (T : Sites P) : Protocol P :=
  let Ψ₀ := componentProtocol F lay
  let W := probeProtocol (flowKinds F) T
  fun p => ((Θ p).max (Ψ₀ p)).max (W p)

/-- **A support a framed node keeps**: at the node's protocol, the
support passes the frame's check and the callee's stated effect `Φ` at
every context of code `m` and every node sharing `l`'s continuation and
handler. -/
def supportKeptB (F : FFlow P) (lay : List (Nat × Bool × Nat × Nat)) (Θ : Protocol P) (m : Code) (l : Nat) (e : Tm)
    (Φ : Footprints.Footprint) (S : Footprints.Footprint) : Bool :=
  let Ψ := nodeProtocol F lay Θ (nodeSet F lay m l e)
  (F.ctxs m).all fun (_, c) => (sharingNodes m l).all fun l' =>
    frameCheckAt classQuery Ψ Φ S F.flow.H (c.node l').envAt (fun _ => false)

/-- **The supports a framed node keeps, of those offered** (`supportKeptB`):
the producer's proposal of a framed plan's supports. -/
def framedNodeKeeps (F : FFlow P) (lay : List (Nat × Bool × Nat × Nat)) (Θ : Protocol P) (m : Code) (l : Nat)
    (e : Tm) (Φ : Footprints.Footprint) (Ss : List Footprints.Footprint) : List Footprints.Footprint :=
  Ss.filter (supportKeptB F lay Θ m l e Φ)

/-- **The checks of one framed node** `l` of code `m`, whose expression is
`e`, its callee's stated effect `Φ`, keeping the supports `Ss`: the call's
operands read from slots, the node's set closed and holding its operand
sets, and each support passing the frame's check at the node's protocol at
every context and every node sharing `l`'s continuation and handler
(`supportKeptB`). -/
def framedNodeOkB (F : FFlow P) (lay : List (Nat × Bool × Nat × Nat)) (Θ : Protocol P) (m : Code) (l : Nat) (e : Tm)
    (Φ : Footprints.Footprint) (Ss : List Footprints.Footprint) : Bool :=
  atomCallB e && capClosedB F (tokenCaps F lay) (operandSets F m l e) (nodeSet F lay m l e) &&
    Ss.all (supportKeptB F lay Θ m l e Φ)

/-- **The checks of a plan's framed nodes** (`framedNodeOkB` at each): at
the client obligation by kind `theta`, each node's expression and its
callee's stated effect (`eff`) present. -/
def framedNodesAt (F : FFlow P) (lay : List (Nat × Bool × Nat × Nat))
    (theta : List (Option Verification.Kind × Footprints.Change)) (framed : List (Nat × List Footprints.Footprint))
    (m : Code) (eff : Nat → Option Footprints.Footprint) : Bool :=
  let Θ : Protocol P := protocolOfKinds theta
  framed.all fun (l, Ss) => match m.1[l]?, eff l with
    | some e, some Φ => framedNodeOkB F lay Θ m l e Φ Ss
    | _, _ => false

/-- **Why a plan's framed nodes fail their checks** (a refusal's text, at
the first node `framedNodeOkB` refuses): no stated effect of its callee,
operands other than slots, its set not closed, or how many of the
supports it keeps fail the frame's check. -/
def framedNodesWhy (F : FFlow P) (lay : List (Nat × Bool × Nat × Nat))
    (theta : List (Option Verification.Kind × Footprints.Change)) (framed : List (Nat × List Footprints.Footprint))
    (m : Code) (eff : Nat → Option Footprints.Footprint) : String :=
  let Θ : Protocol P := protocolOfKinds theta
  (framed.findSome? fun (l, Ss) => match m.1[l]?, eff l with
    | none, _ => some s!" (its framed call node {l} is no node of its code)"
    | _, none => some s!" (its framed call node {l} has no stated effect of its callee)"
    | some e, some Φ =>
      if !atomCallB e then some s!" (its framed call node {l} calls operands other than slots)"
      else if !capClosedB F (tokenCaps F lay) (operandSets F m l e) (nodeSet F lay m l e) then
        some s!" (its framed call node {l}'s set is not closed)"
      else
        let n := (Ss.filter fun S => !supportKeptB F lay Θ m l e Φ S).length
        if n == 0 then none else some s!" (at its framed call node {l}, {n} of the supports it keeps fail the frame's check)").getD ""
end

/-- **The client obligation keeps every part**, decided: every change the
wire states by kind is `keep`. -/
def thetaKeepB (theta : List (Option Verification.Kind × Footprints.Change)) : Bool :=
  theta.all fun e => e.2 == .keep

/-- **A client obligation keeping every part is below every protocol**
(proved). -/
theorem thetaKeepB_sound {P : Package} {theta : List (Option Verification.Kind × Footprints.Change)}
    (h : thetaKeepB theta = true) (Ψ : Protocol P) (p : Part P) : ((protocolOfKinds theta : Protocol P) p).le (Ψ p) = true := by
  have hk : (protocolOfKinds theta : Protocol P) p = .keep := by
    simp only [protocolOfKinds]
    cases hf : theta.find? (fun e => decide (e.1 = p.kind)) with
    | none => rfl
    | some e =>
      have hm := List.mem_of_find?_eq_some hf
      simp only [thetaKeepB, List.all_eq_true, beq_iff_eq] at h
      simp [h e hm]
  rw [hk]; exact Footprints.Change.keep_le _

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- **The request's node expressions are source terms**, decided. -/
def sourceTermsB (r : SourceRequest σ ι) : Bool := r.program.all fun node => ObjectCoherence.sourceTerm node.expression

namespace FramedSpec
variable (spec : FramedSpec ι)

/-- **The flow the frame reads, its tags decided** (`frameFlowOf`): the
checked flow's sites renamed into the family of one component, at the
package whose tags of `C`'s code are those equal to `C`. -/
def fflowC : FFlow (framePkg spec.C spec.mark) := frameFlowOf spec.C spec.checked

/-- **The checks of a framed plan at its request** (the draft, "What the
pass checks"): its request's tag `C` (`compB`), its request's node
expressions source terms (`sourceTermsB`), its client obligation keeping
every part (`thetaKeepB`), its start a label of its program, its realized
code's proposals the request's at body labels (`realizedFlowB`) and the checks of its framed nodes at the
request's code (`framedNodesAt`), at the flow the frame reads with its
tags decided (`fflowC`), each node's callee's stated effect read by
`eff`. -/
def requestB (r : SourceRequest σ ι) (eff : Nat → Option Footprints.Footprint) : Bool :=
  compB spec.C r && sourceTermsB r && thetaKeepB spec.theta && decide (r.start < r.program.length) &&
    realizedFlowB spec.fflowC r && framedNodesAt spec.fflowC spec.lay spec.theta spec.framed (requestCode r) eff

/-- **The callback row of the client obligation** (the owner's decision of
2026-11-19, the draft "The callback's type"): a function value outside code
passes to `C` at a function type meets that type, so a call at a framed
node `l` of the request's code (a call whose callee may be a value of
outside code, `framedCallNodes`) whose callee's type states the effect
`Φ` (`eff`), from a reached state entering it to the state its evaluation
returns to, its calls of `C` included, changes the heap within `Φ` at the
node's slots. -/
def CallbacksWithin (r : SourceRequest σ ι) (eff : Nat → Option Footprints.Footprint) : Prop :=
  ∀ l Φ (b₀ a : Conf × Ghost ((spec.frame r).F.at (spec.frame r).C)) m e L d k x v,
    l ∈ spec.framed.map (·.1) → eff l = some Φ → (spec.frame r).Reached b₀ → (requestCode r).1[l]? = some e →
    (requestCode r).2[l]? = some (k, x) → (∀ v ∈ L, isVal v = true) → isVal d = true →
    b₀.1.t = .frame (requestCode r).1 (requestCode r).2 (instantiate 0 (envOf L d) e) L d k x r.comp →
    Ex (spec.frame r).KStep (fun s => Inside (spec.frame r).F (spec.frame r).C (requestCode r).1 (requestCode r).2
      L d k x r.comp s.1.t) m b₀ a →
    a.1.t = .frame (requestCode r).1 (requestCode r).2 v L d k x r.comp → isVal v = true →
    TolerantFrames.Action Φ (envOf L d) b₀.1.s a.1.s
end FramedSpec
end

end Verification.SourceClaimJson
