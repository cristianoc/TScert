import Verification.Source.Claims.FlowProbe
import Verification.Source.Claims.MemberSettle

/-! # A framed plan's check, run beside the verdict

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "What the pass checks"). At each call
node of a member's main graph whose call may reach outside code (a framed
call, `framedCallNodes`), the supports the frame keeps are decided by the
read-only frame's check (`frameCheckAt`) at the call's protocol
$`\Psi_c`$ (`componentProtocol` with the depth charges of the call's
reach, `depthCharges`) and the callee's stated effect read at the caller's
slots (`callEffectAt`), at every context of the member's code in the flow
and every node of the call's continuation and handler that may call
outside code (`framedSupportsAt`). The supports offered are those of the
call's entry facts, in the pass's slot numbering (`SinglePass.framedAt`).
`FilePlans.framedCheck` runs the member's main graph with its framed calls
keeping the supports the check passes, settled as a member's run is
(`inferredNext`'s candidates left out at a head that lacks them); its
outcome is a report, and no verdict reads it: a framed plan stays refused
(`FilePlans.passMember`) until its obligations are discharged. -/

namespace Verification.SourceClaimJson
open Lean Verification.TolerantFrames.ReadOnly ControlFlow PositiveGraphs

/-- **The effect a call node's callee states**, read at the caller's slots
(`PromiseCalls.callerFrame`): the union over the callee type's signatures,
fixed and variadic; none where the node calls no slot of a function type. -/
def callEffectAt {ι : Type} [LabelStore.Labels ι] (G : NormalGraph ι) (c : CertificateProducer.PointClaim ι) (e : Tm) :
    Option Footprints.Footprint :=
  match e with
  | .invoke (.var j) _ _ => (c.context[j]?).bind fun T => match PositiveRules.expand G T with
    | [PositiveNormalization.Clause.arrs L S] | [PositiveNormalization.Clause.callable _ _ L S _] =>
      let effs := L.map (·.effect) ++ S.map (·.effect)
      if effs.isEmpty then none else some (effs.flatMap fun eff => PromiseCalls.callerFrame eff e)
    | _ => none
  | _ => none

section
variable {P : Package} [DecidableEq P.Site] [Hashable P.Site]

/-- The call sets of node `l` of code `m` at a context `c` of a flow. -/
def callsAtNode (F : FFlow P) (c : FCode P) (m : Code) (l : Nat) :
    List (Sites P × Sites P × List (Sites P)) :=
  match m.1[l]?, m.2[l]? with
  | some e, some kx => callSets F (flowSites F) (c.node l).envAt (fun i => c.sigAt ((c.node l).fnAt i))
      (c.flow.at l kx) (c.node l).cx 0 (fun _ => none) e
  | _, _ => []

/-- **A framed call** (`probeFrames`'s): a call of node `l` reaches outside
code at the context `c`. -/
def framedNodeAt (F : FFlow P) (host : Nat → Bool) (c : FCode P) (m : Code) (l : Nat) : Bool :=
  (callsAtNode F c m l).any fun (f, _, _) => reachesOut F (flowSites F) (segCodes F (flowSites F) host f) f

/-- **The framed call nodes of a code**: its call nodes framed at some
context of the code in the flow. -/
def framedCallNodes (F : FFlow P) (host : Nat → Bool) (m : Code) : List Nat :=
  (List.range m.1.length).filter fun l => (match m.1[l]? with | some (.invoke ..) => true | _ => false) &&
    (F.ctxs m).any fun (_, c) => framedNodeAt F host c m l

/-- **The supports a framed call keeps** (`probeFrames`'s check, decided):
of the supports `Ss` over node `l`'s slots, those passing `frameCheckAt` at
the call's protocol $`\Psi_c`$ and the callee's effect `Φ`, at every
context of code `m` and every node of the call's continuation and handler
that may call outside code or makes a framed call (the node itself where
none does). -/
def framedSupportsAt (F : FFlow P) (lay : List (Nat × Bool × Nat × Nat)) (host : Nat → Bool) (m : Code)
    (l : Nat) (Φ : Footprints.Footprint) (Ss : List Footprints.Footprint) : List Footprints.Footprint :=
  let top := flowSites F
  let kx := m.2[l]?
  let sharing := (List.range m.2.length).filter fun l' => m.2[l']? == kx
  Ss.filter fun S => (F.ctxs m).all fun (_, c) =>
    let required := sharing.filter fun l' => (c.node l').out || framedNodeAt F host c m l'
    let (Sf, Sr, args) := (callsAtNode F c m l).head?.getD ([], [], [])
    let seg := segCodes F top host Sf
    let L := callReach F lay seg Sf Sr args
    let Wc := depthCharges F seg L
    let Ψ : Protocol P := fun p => Footprints.Change.max (componentProtocol F lay p) (Wc p)
    (if required.isEmpty then [l] else required).all fun l' =>
      frameCheckAt classQuery Ψ Φ S F.flow.H (c.node l').envAt noKeys (fun _ => false)
end

/-- **A component's flow, as the frame's check reads it**: the flow the
solver proposes for the component's codes (`componentCodes`), read at the
marks its `O` gives (`remark`); each code's layout; the natives' codes; the
member's code. -/
structure ComponentFlow (ofC : ComponentTag → Bool) where
  O : List (Option Nat)
  flow : FFlow (markedPackage ofC O)
  lay : List (Nat × Bool × Nat × Nat)
  host : Nat → Bool
  member : Option Code

/-- The component flow of `mods` (`componentCodes`, `solveStart`,
`solveLoop`, `propose`, `remark`), at the member `member`. -/
def componentFlow (ofC : ComponentTag → Bool) (mods : List ProbeModule) (entryNames : List String)
    (member : String) (fuel : Nat := 10000000) : ComponentFlow ofC :=
  let cc := componentCodes ofC mods entryNames
  let s := solveStart cc.cs
  let (st, _, _) := solveLoop s fuel s.st
  let F := s.propose st
  let n := cc.mods.length
  let k := cc.hosts.length
  ⟨F.O, remark F, cc.cs.map fun c => (c.ar, c.rest, c.ncaps, c.start), fun i => n ≤ i && i < n + k,
    (cc.mods.find? (·.name == member)).map (·.code)⟩

/-- **A member's framed check** (the module's header): its framed call
nodes in the component's flow, the supports each keeps, and its main graph
run with them, settled; the report's lines. -/
def FilePlans.framedCheck {ofC : ComponentTag → Bool} (f : FilePlans) (fuel : Nat) (i : Nat)
    (cf : ComponentFlow ofC) : List String := Id.run do
  let some (.ok (.graph name _ r)) := f.plans[i]? | return ["framed check: no graph plan"]
  let some m := cf.member | return [s!"framed check, {name}: the member has no code in the flow"]
  let G : NormalGraph (EquationStore.CheckedLabel f.F.equations f.F.primitive) := LabelStore.StoreView.graph f.F.store
  let nodes := framedCallNodes cf.flow cf.host m
  let mut lines := [s!"framed check, {name}: framed call nodes {nodes}"]
  let mut g := f
  for _ in List.range 12 do
    -- each framed node's entry supports, and those its frame keeps, each
    -- node observed in the walk framing those found before it (a node
    -- the walk reaches only past a later framed node is taken again,
    -- once per framed node)
    let mut framed : List (Nat × List Footprints.Footprint) := []
    let mut shown : List String := []
    for _ in nodes do
      shown := []
      for l in nodes do
        let eff := match r.claims[l]?, r.program[l]? with
          | some c, some n => callEffectAt G c n.expression
          | _, _ => none
        let others := framed.filter (·.1 != l)
        match g.passMember fuel i (observe := some s!"node:{l}") (framed := others) with
        | .ok run => match (run.main.map (·.outcome)).getD run.outcome, eff with
          | .observed o, some Φ =>
            let atoms := o.before.indices.filter fun a => (a.fact.support? {}).isSome
            let Ss := atoms.filterMap fun a => a.fact.support? {}
            let kept := framedSupportsAt cf.flow cf.lay cf.host m l Φ Ss
            let lost := atoms.filter fun a => !SinglePass.supportedIn kept a.fact
            shown := shown ++ [s!"  node {l}: effect {(reprStr Φ).replace "\n" " "}; {kept.length} of {Ss.length} entry supports kept; dropped {(toJson lost).compress}"]
            framed := others ++ [(l, kept)]
          | .observed _, none => shown := shown ++ [s!"  node {l}: no stated effect of its callee"]
          | o, _ => shown := shown ++ [s!"  node {l} not observed: {o}"]
        | .error e => shown := shown ++ [s!"  node {l} not observed: {e}"]
    lines := lines ++ shown
    match g.passMember fuel i (framed := framed) with
    | .error e => return lines ++ [s!"  framed run: {e}"]
    | .ok run =>
      lines := lines ++ [s!"  framed run: {run.outcome}{outcomeLacks run.outcome}"]
      match run.outcome with
      | .refused _ (some (t, xs)) _ =>
        let held := match g.plans[i]? with
          | some (.ok (.graph _ _ r')) =>
            (r'.candidates.filter fun (p : Nat × List HeapKnowledge.IndexAtom) => p.1 == t).flatMap fun (p : Nat × List HeapKnowledge.IndexAtom) => p.2
          | _ => []
        let drop := held.filter xs.contains
        if drop.isEmpty then break
        lines := lines ++ [s!"  left out at head {t}: {(toJson drop).compress}"]
        g := g.dropCandidates i t drop
      | _ => break
  return lines

end Verification.SourceClaimJson
