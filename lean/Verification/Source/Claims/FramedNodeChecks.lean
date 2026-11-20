import Verification.Source.Claims.FramedBinding
import Verification.Source.Claims.FramedFrameFlow
import Verification.Paper.TolerantFrames.ReadOnlyTransfer
import Verification.Paper.TolerantFrames.ReadOnlyCallFrame
import Verification.Paper.TolerantFrames.ReadOnlyBridge
import Verification.Paper.TolerantFrames.ReadOnlyFitsReach
import Verification.Source.Claims.FramedCopyDefs

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

**The bound of a framed node's call** (`FramedSpec.boundAt`): at a call
of an argument's own value at an entry, its type's stated effect, by **the
callback row** (`FramedSpec.CallbacksWithin`, the owner's decision of
2026-11-19, a part of $`\Theta_C`$: such a call, from a reached state to
its return, changes the heap within that effect); at any other call, where
no node of the flow may call outside code (`noOutB`), the charges of its
segment at every location (`frameCheckOwnAt`), and otherwise the top
effect. -/

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

/-- **A call's callee is an argument's own value**, decided at a table of
copies: at every node sharing the call's continuation and handler, the
callee's slot copies an entry slot in `[lo, hi)` along no read. -/
def calleeArgB (cp : CopyTable) (lo hi : Nat) (m : Code) (l : Nat) : Bool :=
  match m.1[l]? with
  | some (.invoke (.var f) _ _) => (sharingNodes m l).all fun l' =>
      (cp.at l').any fun (i, j, π) => i == f && π.isEmpty && decide (lo ≤ j) && decide (j < hi)
  | _ => false

/-- **The reach of the calls of natives the realm does not model**: at each
code of the flow with a closure's layout `(ar, _, _, s)`, run from its
entry `s` (the receiver then the `ar` parameters in its slots), each call
whose callee may be outside code (`outsideCalleeAt`) and is no
argument's own value (`calleeArgB`) is a call of a value read from
storage, such as a method of a standard object (`a.pop()`), whose steps
are `C`'s; the reach of its callee, receiver and actuals (`callReach`). -/
def nativeSites (F : FFlow P) (lay : List (Nat × Bool × Nat × Nat)) : Sites P :=
  F.codes.flatMap fun (m, _) => match layAt F lay m with
    | some (ar, _, _, s) =>
      let cp := copiesOf m.1 m.2 s (ar + 1) copyBound
      (F.ctxs m).flatMap fun (_, c) => (List.range m.1.length).flatMap fun l =>
        if outsideCalleeAt c m l && !calleeArgB cp 1 (ar + 1) m l then
          let sets := callsAtNode F c m l
          let width := (sets.map (·.2.2.length)).foldl max 0
          callReach F lay (sets.flatMap (·.1)) (sets.flatMap (·.2.1))
            ((List.range width).map fun i => sets.flatMap fun x => x.2.2.getD i [])
        else []
    | none => []

/-- **The charges of the natives the realm does not model**: `any` at
every part of a site such a call may reach. -/
def nativeProtocol (N : Sites P) : Protocol P := fun p => if N.contains p.site then .any else .keep

/-- **No node of the flow may call outside code**, decided: at every code
and every context, each node's `out` is false. -/
def noOutB (F : FFlow P) : Bool :=
  F.codes.all fun (m, cs) => cs.all fun (_, fc) => (List.range m.1.length).all fun l => !(fc.node l).out

omit [Hashable P.Site] in
/-- **No node of the flow may call outside code** (proved): where `noOutB`
passes, every node of every code at every context has `out` false. -/
theorem noOutB_sound {F : FFlow P} (h : noOutB F = true) :
    ∀ E K c π, F.flow.code (E, K) c = some π → ∀ l k x, NodeOf (E, K) l k x → π.out l = false := by
  intro E K c π hc l k x hn
  obtain ⟨fc, hfc, rfl⟩ := FFlow.code_at hc
  obtain ⟨cs, hm, hcs⟩ := FFlow.at_mem hfc
  obtain ⟨-, e, he⟩ := hn
  have hl : l < E.length := (List.getElem?_eq_some_iff.mp he).1
  simp only [noOutB, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h
  exact h _ hm _ hcs l hl

/-- **The effect bounding a framed call**, from whether its callee is a
argument's own value at an entry (`client`), whether no node of the flow may
call outside code (`noOut`) and the callee's stated effect (`eff`): the
stated effect at an argument's own value at an entry; none, the segment's
charges bounding it, where no node may call outside code; the top effect
otherwise. -/
def callBound (client noOut : Bool) (eff : Option Footprints.Footprint) : Option (Option Footprints.Footprint) :=
  if client then eff.map some else if noOut then some none else some (some Footprints.Closed.top.fp)

/-- **A framed node's protocol** $`\Psi_c(l)`$: the client obligation, the
component's protocol, the depth charges at the node's set and the charges
of the natives the realm does not model (`nativeSites`), joined. -/
def nodeProtocol (F : FFlow P) (lay : List (Nat × Bool × Nat × Nat)) (Θ : Protocol P) (T : Sites P) : Protocol P :=
  let Ψ₀ := componentProtocol F lay
  let W := probeProtocol (flowKinds F) T
  let N := nativeProtocol (nativeSites F lay)
  fun p => (((Θ p).max (Ψ₀ p)).max (W p)).max (N p)

/-- **A region read as protected at a framed node** (the Read-only frames
note, §4.1, decided): a region read from a slot whose read locations'
steps `Ψ` keeps (`regionSteps`, `stepsKeptB`), where at every node sharing
the node's continuation and handler the slot holds a copy of an argument
at a read-only position below the arity (`roPos`), read along a path whose
steps `Ψ` keeps (`pathSteps`). -/
def protRegionB (Ψ : Protocol P) (cp : CopyTable) (arity : Nat) (roPos : Nat → Bool) (m : Code) (l : Nat)
    (r : Footprints.Region) : Bool :=
  match regionSlot r with
  | none => false
  | some x => stepsKeptB Ψ (regionSteps r) && (sharingNodes m l).all fun l' =>
      (cp.at l').any fun (i, j, π) => i == x && decide (j < arity) && roPos j && stepsKeptB Ψ (pathSteps π)

/-- **A support a framed node keeps**: at the node's protocol, at every
context of code `m` and every node sharing `l`'s continuation and handler,
the support passes the frame's check and the effect bounding the call
(`some Φ`), the regions `prot` reads as protected read so, or, at a node
whose segment runs no outside code (`none`), the check of the charges'
premise at every part (`frameCheckOwnAt`). -/
def supportKeptB (F : FFlow P) (lay : List (Nat × Bool × Nat × Nat)) (Θ : Protocol P) (m : Code) (l : Nat) (e : Tm)
    (Φ : Option Footprints.Footprint) (prot : Footprints.Region → Bool) (S : Footprints.Footprint) : Bool :=
  let Ψ := nodeProtocol F lay Θ (nodeSet F lay m l e)
  (F.ctxs m).all fun (_, c) => (sharingNodes m l).all fun l' => match Φ with
    | some Φ => frameCheckAt classQuery Ψ Φ S F.flow.H (c.node l').envAt prot
    | none => frameCheckOwnAt Ψ S F.flow.H (c.node l').envAt

/-- **Why a framed node drops a support** (a diagnostic, the frame's check
of `supportKeptB` read back): at the first context and node sharing `l`'s
continuation and handler where the check fails, a region with no sites,
or the first part at which the node's protocol or the callee's stated
effect exceeds the region's change (`frameCheckFailure`); `none` where the
support is kept. -/
def supportFailure (F : FFlow P) (lay : List (Nat × Bool × Nat × Nat)) (Θ : Protocol P) (m : Code) (l : Nat) (e : Tm)
    (Φ : Option Footprints.Footprint) (prot : Footprints.Region → Bool) (S : Footprints.Footprint) :
    Option (Footprints.Region × Option ((Footprints.Region × Footprints.Change) × Part P × Bool × Bool × Footprints.Change)) :=
  let Ψ := nodeProtocol F lay Θ (nodeSet F lay m l e)
  (F.ctxs m).findSome? fun (_, c) => (sharingNodes m l).findSome? fun l' =>
    let τ := (c.node l').envAt
    match S.find? fun e => (regionSites F.flow.H τ e.1).isNone with
    | some e => some (e.1, none)
    | none => match Φ with
      | some Φ => (frameCheckFailure classQuery Ψ Φ S (callParts F.flow.H τ) prot).map
          fun (e, p, i, o) => (e.1, some (e, p, i, o, Ψ p))
      | none => S.findSome? fun e => ((callParts F.flow.H τ e.1).find? fun p => !(Ψ p).le e.2).map
          fun p => (e.1, some (e, p, true, false, Ψ p))

/-- **The supports a framed node keeps, of those offered** (`supportKeptB`):
the producer's proposal of a framed plan's supports. -/
def framedNodeKeeps (F : FFlow P) (lay : List (Nat × Bool × Nat × Nat)) (Θ : Protocol P) (m : Code) (l : Nat)
    (e : Tm) (Φ : Option Footprints.Footprint) (prot : Footprints.Region → Bool) (Ss : List Footprints.Footprint) :
    List Footprints.Footprint :=
  Ss.filter (supportKeptB F lay Θ m l e Φ prot)

/-- **The checks of one framed node** `l` of code `m`, whose expression is
`e`, the effect bounding its call `Φ` (`none` where its segment runs no
outside code), keeping the supports `Ss`: the call's
operands read from slots, the node's set closed and holding its operand
sets, and each support passing the frame's check at the node's protocol at
every context and every node sharing `l`'s continuation and handler
(`supportKeptB`). -/
def framedNodeOkB (F : FFlow P) (lay : List (Nat × Bool × Nat × Nat)) (Θ : Protocol P) (m : Code) (l : Nat) (e : Tm)
    (Φ : Option Footprints.Footprint) (prot : Footprints.Region → Bool) (Ss : List Footprints.Footprint) : Bool :=
  atomCallB e && capClosedB F (tokenCaps F lay) (operandSets F m l e) (nodeSet F lay m l e) &&
    Ss.all (supportKeptB F lay Θ m l e Φ prot)

/-- **The checks of a plan's framed nodes** (`framedNodeOkB` at each): at
the client obligation by kind `theta`, each node's expression and the
bound of its call (`eff`, `FramedSpec.boundAt`) present. -/
def framedNodesAt (F : FFlow P) (lay : List (Nat × Bool × Nat × Nat))
    (theta : List (Option Verification.Kind × Footprints.Change)) (framed : List (Nat × List Footprints.Footprint))
    (m : Code) (eff : Nat → Option (Option Footprints.Footprint)) (prot : Nat → Footprints.Region → Bool) : Bool :=
  let Θ : Protocol P := protocolOfKinds theta
  framed.all fun (l, Ss) => match m.1[l]?, eff l with
    | some e, some Φ => framedNodeOkB F lay Θ m l e Φ (prot l) Ss
    | _, _ => false

/-- **Why a plan's framed nodes fail their checks** (a refusal's text, at
the first node `framedNodeOkB` refuses): no stated effect of its callee,
operands other than slots, its set not closed, or how many of the
supports it keeps fail the frame's check. -/
def framedNodesWhy (F : FFlow P) (lay : List (Nat × Bool × Nat × Nat))
    (theta : List (Option Verification.Kind × Footprints.Change)) (framed : List (Nat × List Footprints.Footprint))
    (m : Code) (eff : Nat → Option (Option Footprints.Footprint)) (prot : Nat → Footprints.Region → Bool) : String :=
  let Θ : Protocol P := protocolOfKinds theta
  (framed.findSome? fun (l, Ss) => match m.1[l]?, eff l with
    | none, _ => some s!" (its framed call node {l} is no node of its code)"
    | _, none => some s!" (its framed call node {l} has no stated effect of its callee)"
    | some e, some Φ =>
      if !atomCallB e then some s!" (its framed call node {l} calls operands other than slots)"
      else if !capClosedB F (tokenCaps F lay) (operandSets F m l e) (nodeSet F lay m l e) then
        some s!" (its framed call node {l}'s set is not closed)"
      else
        let n := (Ss.filter fun S => !supportKeptB F lay Θ m l e Φ (prot l) S).length
        if n == 0 then none else some s!" (at its framed call node {l}, {n} of the supports it keeps fail the frame's check)").getD ""
end

/-- **The client obligation keeps every part**, decided: every change the
wire states by kind is `keep`. -/
def thetaKeepB (theta : List (Option Verification.Kind × Footprints.Change)) : Bool :=
  theta.all fun e => e.2 == .keep

/-- **A client obligation keeping every part keeps every part** (proved). -/
theorem thetaKeepB_keep {P : Package} {theta : List (Option Verification.Kind × Footprints.Change)}
    (h : thetaKeepB theta = true) (p : Part P) : (protocolOfKinds theta : Protocol P) p = .keep := by
  simp only [protocolOfKinds]
  cases hf : theta.find? (fun e => decide (e.1 = p.kind)) with
  | none => rfl
  | some e =>
    have hm := List.mem_of_find?_eq_some hf
    simp only [thetaKeepB, List.all_eq_true, beq_iff_eq] at h
    simp [h e hm]

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

/-- **The table of copies of a request's code** (`copiesOf`, which
`copiesB` checks): from its start at the plan's arity. -/
def copiesAt (r : SourceRequest σ ι) : CopyTable :=
  copiesOf (requestCode r).1 (requestCode r).2 r.start spec.arity TolerantFrames.ReadOnly.copyBound

/-- **The regions read as protected at a request's framed nodes**
(`protRegionB`): at a node whose callee is an argument's own value
(`calleeArgB`), a function the client passes, so its steps are outside
code's; at the component's protocol over the flow `F` joined with the
charges of the natives the realm does not model, the request's table of
copies and the plan's read-only positions; none at a request checked at
the contexts of its known calls (`inner`), whose calls cross nothing in. -/
def protAt {P : Package} [DecidableEq P.Site] [Hashable P.Site] (F : FFlow P) (r : SourceRequest σ ι) (l : Nat)
    (q : Footprints.Region) : Bool :=
  !spec.inner && calleeArgB (spec.copiesAt r) 0 spec.arity (requestCode r) l &&
    protRegionB (fun p => (componentProtocol F spec.lay p).max (nativeProtocol (nativeSites F spec.lay) p))
      (spec.copiesAt r) spec.arity spec.roPos (requestCode r) l q

/-- **A call of an argument's own value at an entry**: at a request
checked at its entry (no `inner`), a node whose callee is an argument's
own value (`calleeArgB`), the value its caller passed at the parameter's
type: outside code, or `C`'s own code calling the entry. -/
def clientCallee (r : SourceRequest σ ι) (l : Nat) : Bool :=
  !spec.inner && calleeArgB (spec.copiesAt r) 0 spec.arity (requestCode r) l

/-- **The effect bounding a framed node's call** (the Read-only frames
note, (B1)): at a call of an argument's own value at an entry (`clientCallee`),
its type's stated effect (`eff`, the callback row of the client
obligation); otherwise, where no node of the flow may call outside code
(`noOutB`), none, the call's segment being bounded by its charges at every
location; and otherwise the top effect. -/
def boundAt {P : Package} [DecidableEq P.Site] [Hashable P.Site] (F : FFlow P) (r : SourceRequest σ ι)
    (eff : Nat → Option Footprints.Footprint) (l : Nat) : Option (Option Footprints.Footprint) :=
  callBound (spec.clientCallee r l) (noOutB F) (eff l)

/-- **The returns of a code lie within `O`**, decided: at every context of
the code `m`, the values its runs return. -/
def retsInB {P : Package} [DecidableEq P.Site] [Hashable P.Site] (F : FFlow P) (m : Code) : Bool :=
  F.codes.all fun (m', cs) => m' != m || cs.all fun (_, fc) => decide (Sub fc.ret F.O)

/-- **The returns of a code lie within `O`** (proved). -/
theorem retsInB_sound {P : Package} [DecidableEq P.Site] [Hashable P.Site] {F : FFlow P} {m : Code}
    (h : retsInB F m = true) : ∀ c π, F.flow.code m c = some π → Sub π.ret F.flow.O := by
  intro c π hc
  obtain ⟨fc, hfc, rfl⟩ := FFlow.code_at hc
  obtain ⟨l, hl, hcl⟩ := FFlow.at_mem hfc
  simp only [retsInB, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  exact (h _ hl).resolve_left (by simp) _ hcl

/-- **The checks of a framed plan at its request** (the draft, "What the
pass checks"): its request's tag `C` (`compB`), its request's node
expressions source terms (`sourceTermsB`), its client obligation keeping
every part (`thetaKeepB`), its start a label of its program, its realized
code's proposals the request's at body labels (`realizedFlowB`) and the checks of its framed nodes at the
request's code (`framedNodesAt`), each node's call bounded as `boundAt`
reads it from the callee's stated effect `eff`, and, at a request checked
at the contexts of its known calls, the realized code's returns within `O`
(`retsInB`), at the flow the frame reads with its tags decided (`fflowC`). -/
def requestB (r : SourceRequest σ ι) (eff : Nat → Option Footprints.Footprint) : Bool :=
  compB spec.C r && sourceTermsB r && thetaKeepB spec.theta && decide (r.start < r.program.length) &&
    realizedFlowB spec.fflowC r &&
    framedNodesAt spec.fflowC spec.lay spec.theta spec.framed (requestCode r) (spec.boundAt spec.fflowC r eff)
      (spec.protAt spec.fflowC r) &&
    (!spec.inner || retsInB spec.fflowC (realizedCode r))

/-- **The callback row of the client obligation** (the owner's decision of
2026-11-19, the draft "The callback's type"): a function value outside code
passes to `C` at a function type meets that type, so a call at a framed
node `l` of the request's code whose callee is an argument's own value at
an entry (`clientCallee`, the value its caller passed, outside code or
`C`'s own) and whose type states the effect `Φ` (`eff`), from
a reached state entering it to the state its evaluation returns to, its
calls of `C` included, changes the heap within `Φ` at the node's slots. -/
def CallbacksWithin (r : SourceRequest σ ι) (eff : Nat → Option Footprints.Footprint) : Prop :=
  ∀ l Φ (b₀ a : Conf × Ghost ((spec.frame r).F.at (spec.frame r).C)) m e L d k x v,
    l ∈ spec.framed.map (·.1) → spec.clientCallee r l = true → eff l = some Φ → (spec.frame r).Reached b₀ →
    (requestCode r).1[l]? = some e →
    (requestCode r).2[l]? = some (k, x) → (∀ v ∈ L, isVal v = true) → isVal d = true →
    b₀.1.t = .frame (requestCode r).1 (requestCode r).2 (instantiate 0 (envOf L d) e) L d k x r.comp →
    Ex (spec.frame r).KStep (fun s => Inside (spec.frame r).F (spec.frame r).C (requestCode r).1 (requestCode r).2
      L d k x r.comp s.1.t) m b₀ a →
    a.1.t = .frame (requestCode r).1 (requestCode r).2 v L d k x r.comp → isVal v = true →
    TolerantFrames.Action Φ (envOf L d) b₀.1.s a.1.s
end FramedSpec
end

end Verification.SourceClaimJson
