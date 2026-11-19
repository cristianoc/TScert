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
(`inferredNext`'s candidates left out at a head that lacks them), a report
(`TSCERT_FRAMED`). The producer of a framed plan (`FilePlans.framedPlan`)
states the plan's restrictions (`framedRestriction`), the realm and the
initialization of the component (`componentInit`), and its document, which
the decoder (`FramedSpec.decode`) checks against the flow it recomputes;
`FilePlans.passMember` checks the plan and refuses it
(`FilePlans.framedRefusal`) until its obligations are discharged. -/

namespace Verification.SourceClaimJson
open Lean Verification.TolerantFrames.ReadOnly ControlFlow PositiveGraphs

/-- **A component's flow, as the frame's check reads it**: the flow the
solver proposes for the component's codes (`componentCodes`), read at the
marks its `O` gives (`remark`); each code's layout; the natives' codes; the
module functions' codes; the member's code. -/
structure ComponentFlow (ofC : ComponentTag → Bool) where
  O : List (Option Nat)
  flow : FFlow (markedPackage ofC O)
  lay : List (Nat × Bool × Nat × Nat)
  host : Nat → Bool
  codes : List Code
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
    cc.mods.map (·.code), (cc.mods.find? (·.name == member)).map (·.code)⟩

/-- **The supports each framed call node keeps**, as the producer proposes
them: each node's entry facts' supports, observed in the walk framing the
nodes found before it (none at a node the walk does not reach), those
passing the frame's check
(`framedSupportsAt`, at the client obligation `Θ`); with a line per node. -/
def FilePlans.framedSupports {ofC : ComponentTag → Bool} (f : FilePlans) (fuel i : Nat) (cf : ComponentFlow ofC)
    (Θ : Protocol (markedPackage ofC cf.O)) (r : SourceExtraction.SourceRequest (EquationStore.Checked f.F.equations f.F.primitive)
      (EquationStore.CheckedLabel f.F.equations f.F.primitive)) (m : Code) (nodes : List Nat) :
    List (Nat × List Footprints.Footprint) × List String := Id.run do
  let G : NormalGraph (EquationStore.CheckedLabel f.F.equations f.F.primitive) := LabelStore.StoreView.graph f.F.store
  -- (each node observed in the walk framing those found before it; a node
  -- the walk reaches only past a later framed node is taken again, once
  -- per framed node)
  let mut framed : List (Nat × List Footprints.Footprint) := []
  let mut shown : List String := []
  for _ in nodes do
    shown := []
    for l in nodes do
      let eff := match r.claims[l]?, r.program[l]? with
        | some c, some n => callEffectAt G c n.expression
        | _, _ => none
      let others := framed.filter (·.1 != l)
      match f.passMember fuel i (observe := some s!"node:{l}") (framed := others) with
      | .ok run => match (run.main.map (·.outcome)).getD run.outcome, eff with
        | .observed o, some Φ =>
          let atoms := o.before.indices.filter fun a => (a.fact.support? {}).isSome
          let Ss := atoms.filterMap fun a => a.fact.support? {}
          let kept := framedSupportsAt cf.flow cf.lay cf.host Θ m l Φ Ss
          let lost := atoms.filter fun a => !SinglePass.supportedIn kept a.fact
          shown := shown ++ [s!"  node {l}: effect {(reprStr Φ).replace "\n" " "}; {kept.length} of {Ss.length} entry supports kept; dropped {(toJson lost).compress}"]
          framed := others ++ [(l, kept)]
        | .observed _, none => shown := shown ++ [s!"  node {l}: no stated effect of its callee"]
        | o, _ => shown := shown ++ [s!"  node {l} not observed: {o}"]
      | .error e => shown := shown ++ [s!"  node {l} not observed: {e}"]
  -- (a node the walk does not reach keeps no support)
  return (nodes.map fun l => (l, ((framed.find? (·.1 == l)).map (·.2)).getD []), shown)

/-- **A member's framed check** (the module's header): its framed call
nodes in the component's flow, the supports each keeps, and its main graph
run with them, settled; the report's lines. -/
def FilePlans.framedCheck {ofC : ComponentTag → Bool} (f : FilePlans) (fuel : Nat) (i : Nat)
    (cf : ComponentFlow ofC) : List String := Id.run do
  let some (.ok (.graph name _ _)) := f.plans[i]? | return ["framed check: no graph plan"]
  let some m := cf.member | return [s!"framed check, {name}: the member has no code in the flow"]
  let nodes := framedCallNodes cf.flow cf.host m
  let mut lines := [s!"framed check, {name}: framed call nodes {nodes}"]
  let mut g := f
  for _ in List.range 12 do
    let (framed, shown) := match g.plans[i]? with
      | some (.ok (.graph _ _ r')) => g.framedSupports fuel i cf (fun _ => .keep) r' m nodes
      | _ => ([], [])
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

/-! ## The framed plan: its restrictions, its document and its decoder -/

/-- An intrinsic object of the realm, as a module's slot names it
(`[[Array.prototype]]`). -/
def intrinsicName (x : String) : Bool := x.startsWith "[[" && x.endsWith "]]"

/-- **The restrictions of a framed plan** (the draft, "Restrictions"), over
the component's module functions `mods`, the member `member` and the
`@clients` rows of its exported types: the member a realized module
function; no two module functions naming each other; every outside slot of
a module function an audited realm value (a native with a step model,
`hostModel?`, or an intrinsic object); every `@clients` entry a class
entry. The first violated, as its located refusal's text. -/
def framedRestriction (mods : List ProbeModule) (member : String) (clients : List Footprints.Footprint) :
    Option String :=
  if !(mods.any (·.name == member)) then some "a framed plan needs a realized entry"
  else if (closable mods).length != mods.length then
    some "a framed plan's component has module functions naming each other"
  else
  -- (a slot of the module's own, a cell or a constant, named before a
  -- native's)
  let slots := mods.flatMap fun g => g.siblings.map (g.name, ·)
  let slots := slots.filter (!·.2.startsWith "%") ++ slots.filter (·.2.startsWith "%")
  match slots.find? fun (_, x) => !(mods.any (·.name == x) || (hostModel? x).isSome || intrinsicName x) with
  | some (g, x) => some s!"a framed plan's module function {g} reads {x}, which is not an audited realm value"
  | none => if clients.all (·.all classEntry) then none
    else some "a framed plan's component states a `@clients` path key"

/-- **The realm and the initialization of a component** (the draft,
"Initialization", `initC`): the realm's heap, one identity per audited
realm value the module functions read; the initialization's code, each
module function's closure allocated after those it names (its captures
each named module function's slot or the realm value), then the array of
the entries. -/
def componentInit (tag : ComponentTag) (mods : List ProbeModule) (entries : List String) :
    Heap × List Tm × List (Continuation × Option Target) := Id.run do
  let realmNames := (mods.flatMap (·.siblings)).filter (fun x => !(mods.any (·.name == x))) |>.eraseDups
  let realmValue (x : String) : Tm :=
    let loc := realmNames.idxOf x
    match hostModel? x with
    | some (c, ar) => .objAt [] (.graph ar c.1 c.2 0 [] .call false tag) loc
    | none => .objAt [] .absent loc
  -- (the module functions in an order where each comes after those it names)
  let mut order : List ProbeModule := []
  for _ in mods do
    for g in mods do
      if !(order.any (·.name == g.name)) &&
          g.siblings.all fun x => !(mods.any (·.name == x)) || order.any (·.name == x) then
        order := order ++ [g]
  let slotOf (x : String) : Nat := order.findIdx (·.name == x)
  let closures : List Tm := order.map fun g =>
    .makeAt (.graph g.ar g.code.1 g.code.2 (g.code.1.length - 1)
      (g.siblings.map fun x => if mods.any (·.name == x) then .var (slotOf x) else realmValue x) .call false tag) [] []
  let exports : Tm := .arrLit (entries.map fun x => .var (slotOf x))
  return (realmNames.map fun _ => .nul, closures ++ [exports],
    (List.range order.length).map (fun k => (.bind ⟨k + 1, none⟩, none)) ++ [(.ret, none)])

/-- An object's fields, exactly `ks`, in any order. -/
def exactFields (j : Json) (ks : List String) (what : String) : Except String Unit := do
  let .obj kvs := j | throw s!"{what}: not an object"
  let have_ := kvs.toList.map (·.1)
  if let some k := have_.find? (!ks.contains ·) then throw s!"{what}: an unknown field {k}"
  if let some k := ks.find? (!have_.contains ·) then throw s!"{what}: no field {k}"

open Verification.TolerantFrames.ReadOnly in
/-- **The decoder of a framed plan's document**: its fields exactly those
of `framedDocument`; the flow recomputed from the component's codes
(`cf`, the request's code beside the realized code, `FFlow.withCode`); the
document refused where it disagrees with it: its component or entries
other than the plan's, its framed call nodes other than the flow's
(`framedCallNodes`), or a support it keeps failing the frame's check
(`framedSupportsAt`); then the plan's proposals. -/
def FramedSpec.decode {ofC : ComponentTag → Bool} {σ ι : Type} [LabelStore.Labels ι] [LabelStore.StoreView σ ι]
    (G : NormalGraph ι) (cf : ComponentFlow ofC) (C : Nat) (entries : List String)
    (clients : List Footprints.Footprint) (realm : Heap) (initE : List Tm) (initK : List (Continuation × Option Target))
    (r : SourceExtraction.SourceRequest σ ι) (doc : Json) : Except String (FramedSpec ι) := do
  exactFields doc ["component", "entries", "framed"] "a framed plan's document"
  let C' ← doc.getObjValAs? Nat "component"
  let entries' ← doc.getObjValAs? (List String) "entries"
  let rows ← (← doc.getObjVal? "framed").getArr?
  let framed ← rows.toList.mapM fun row => do
    exactFields row ["node", "supports"] "a framed call node of the document"
    let l ← row.getObjValAs? Nat "node"
    let Ss ← (← row.getObjVal? "supports").getArr?
    return (l, ← Ss.toList.mapM (EffectCodec.frameOf 64))
  if C' != C then throw s!"the document's component {C'} is not the plan's {C}"
  if entries' != entries then throw s!"the document's entries {entries'} are not the component's {entries}"
  let m := realizedCode r
  let F := cf.flow.withCode m (requestCode r)
  let nodes := framedCallNodes F cf.host m
  if framed.map (·.1) != nodes then throw s!"the document's framed call nodes {framed.map (·.1)} are not the flow's {nodes}"
  for (l, Ss) in framed do
    let some Φ := (r.claims[l]?).bind fun c => (r.program[l]?).bind fun n => callEffectAt G c n.expression
      | throw s!"the document's framed call node {l} has no stated effect of its callee"
    let kept := framedSupportsAt F cf.lay cf.host (clientsProtocol clients) m l Φ Ss
    if kept.length != Ss.length then
      throw s!"at the document's framed call node {l}, {Ss.length - kept.length} of the supports it keeps fail the frame's check"
  return { C, readOnly := [], outType := [], realm, initE, initK, arity := r.inputs.length - r.siblings.length, ofC,
           marks := cf.O, checked := F, lay := cf.lay, host := cf.host, clients, codes := cf.codes, entries, framed }

/-- **A forged document** (`TSCERT_FORCE`, the controls'): `framed-doc-node`
names a node no call frames, `framed-doc-support` keeps a support the
frame's check fails, `framed-doc-component` and `framed-doc-entries` name
another component and entries, `framed-doc-field` adds a field and
`framed-doc-missing` drops the entries. -/
def forgeDocument (force : List String) (doc : Json) : Json := Id.run do
  let mut doc := doc
  if force.contains "framed-doc-node" then
    if let .ok rows := (doc.getObjVal? "framed").bind Json.getArr? then
      doc := doc.setObjVal! "framed" (Json.arr (rows.push (Json.mkObj [("node", toJson (0 : Nat)), ("supports", Json.arr #[])])))
  if force.contains "framed-doc-support" then
    if let .ok rows := (doc.getObjVal? "framed").bind Json.getArr? then
      doc := doc.setObjVal! "framed" (Json.arr (rows.map fun row => match (row.getObjVal? "supports").bind Json.getArr? with
        | .ok Ss => row.setObjVal! "supports" (Json.arr (Ss.push (EffectCodec.frameJ [(.all, .keep)])))
        | .error _ => row))
  if force.contains "framed-doc-component" then
    doc := doc.setObjVal! "component" (toJson (((doc.getObjValAs? Nat "component").toOption.getD 0) + 1))
  if force.contains "framed-doc-entries" then
    doc := doc.setObjVal! "entries" (toJson ["%forged%"])
  if force.contains "framed-doc-field" then doc := doc.setObjVal! "forged" (toJson true)
  if force.contains "framed-doc-missing" then
    if let .obj kvs := doc then doc := .obj (kvs.erase "entries")
  return doc

/-- **A member's framed plan, produced** (the draft, "The plan"): where the
member's component meets the restrictions (`framedRestriction`) and the
member has a framed call node in its component's flow, its document
(`framedDocument`, forged where `force` asks), decoded (`FramedSpec.decode`),
and the file's plans with the member's plan the framed plan. `none` where
the member has no framed call node; an error where a restriction or the
decoder refuses. -/
def FilePlans.framedPlan {ofC : ComponentTag → Bool} (f : FilePlans) (fuel i : Nat) (C : Nat) (mods : List ProbeModule)
    (entries : List String) (clients : List Footprints.Footprint) (force : List String) :
    Except String (Option (FilePlans × List String)) := do
  let some (.ok (.graph name pos r)) := f.plans[i]? | return none
  if let some w := framedRestriction mods name clients then throw w
  let cf := componentFlow ofC mods entries name
  let some m := cf.member | throw "a framed plan needs a realized entry"
  let F := cf.flow.withCode m (requestCode r)
  let nodes := framedCallNodes F cf.host m
  if nodes.isEmpty then return none
  let (framed, shown) := f.framedSupports fuel i { cf with flow := F } (clientsProtocol clients) r m nodes
  let doc := forgeDocument force (framedDocument C entries framed)
  let tag := (mods.find? (·.name == name)).map (·.comp) |>.getD none
  let (realm, initE, initK) := componentInit tag mods entries
  let G : NormalGraph (EquationStore.CheckedLabel f.F.equations f.F.primitive) := LabelStore.StoreView.graph f.F.store
  let spec ← (FramedSpec.decode G cf C entries clients realm initE initK r doc).mapError fun e =>
    s!"a framed plan's document is refused: {e}"
  return some (f.withPlan i (.framed name pos r spec), s!"framed plan, {name}: framed call nodes {nodes}" :: shown)

end Verification.SourceClaimJson
