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
  /-- Each module function's name, arity and the names its slots read. -/
  names : List (String × Nat × List String)
  member : Option Code

/-- The component flow of `mods` (`componentCodes`, `solveStart`,
`solveLoop`, `propose`, `remark`), at the member `member`, its allocation
sites numbered by the codes' bodies (`body`). -/
def componentFlow (ofC : ComponentTag → Bool) (mods : List ProbeModule) (entryNames : List String)
    (member : String) (fuel : Nat := 10000000) (body : Code → Code := id) : ComponentFlow ofC :=
  let cc := componentCodes ofC mods entryNames body
  let s := solveStart cc.cs
  let (st, _, _) := solveLoop s fuel s.st
  let F := s.propose st
  let n := cc.reps.length
  let k := cc.hosts.length
  ⟨F.O, remark F, cc.cs.map fun c => (c.ar, c.rest, c.ncaps, c.start), fun i => n ≤ i && i < n + k,
    cc.mods.map (·.code), cc.mods.map (fun g => (g.name, g.ar, g.siblings)),
    (cc.mods.find? (·.name == member)).map (·.code)⟩

/-- **The supports each framed call node keeps**, as the producer proposes
them: each node's entry facts' supports, observed in the walk framing the
nodes found before it (none at a node the walk does not reach), those
passing the frame's check
(`framedSupportsAt`, at the component's protocol `ΨC` and the client
obligation `Θ`); with a line per node. -/
def FilePlans.framedSupports {ofC : ComponentTag → Bool} (f : FilePlans) (fuel i : Nat) (cf : ComponentFlow ofC)
    (ΨC Θ : Protocol (markedPackage ofC cf.O)) (r : SourceExtraction.SourceRequest (EquationStore.Checked f.F.equations f.F.primitive)
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
    -- (a round that leaves the supports as it found them is a fixpoint:
    -- every later round repeats it)
    let start := framed
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
          let kept := framedSupportsAt cf.flow cf.lay cf.host ΨC Θ m l Φ Ss
          let lost := atoms.filter fun a => !SinglePass.supportedIn kept a.fact
          shown := shown ++ [s!"  node {l}: effect {(reprStr Φ).replace "\n" " "}; {kept.length} of {Ss.length} entry supports kept; dropped {(toJson lost).compress}"]
          framed := others ++ [(l, kept)]
        | .observed _, none => shown := shown ++ [s!"  node {l}: no stated effect of its callee"]
        | o, _ => shown := shown ++ [s!"  node {l} not observed: {o}"]
      | .error e => shown := shown ++ [s!"  node {l} not observed: {e}"]
    if framed == start then break
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
      | some (.ok (.graph _ _ r')) => g.framedSupports fuel i cf (componentProtocol cf.flow cf.lay) (fun _ => .keep) r' m nodes
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

/-- **The restrictions of a framed plan's component** (the draft,
"Restrictions"), over its module functions `mods` and the `@clients` rows
of its exported types: no two module functions naming each other; every
outside slot of a module function an audited realm value (a native with a
step model, `hostModel?`, or an intrinsic object); the rows stating class
keys only (`clientsByKindB`). The first violated, as its located refusal's
text. A framed plan's member is moreover a realized module function
(`FilePlans.framedPlan`). -/
def framedRestriction (mods : List ProbeModule) (rows : List ComponentWire.Clients) : Option String :=
  if (closable mods).length != mods.length then
    some "a framed plan's component has module functions naming each other"
  else
  -- (a slot of the module's own, a cell or a constant, named before a
  -- native's)
  let slots := mods.flatMap fun g => g.siblings.map (g.name, ·)
  let slots := slots.filter (!·.2.startsWith "%") ++ slots.filter (·.2.startsWith "%")
  match slots.find? fun (_, x) => !(mods.any (·.name == x) || (hostModel? x).isSome || intrinsicName x) with
  | some (g, x) => some s!"a framed plan's module function {g} reads {x}, which is not an audited realm value"
  | none => if clientsByKindB rows then none
    else some "a framed plan's component states a `@clients` path key"

/-- **The realm and the initialization of a component** (the draft,
"Initialization", `initC`): the realm's heap, one identity per audited
realm value the module functions read; the initialization's code, each
module function's closure allocated after those it names (its captures
each named module function's closure, read at the slot binding it, or the
realm value), then the array of the entries; and its order, the module functions by
name. Node `k`'s slots hold the closures nodes `0` to `k - 1` allocated,
the latest first. -/
def componentInit (tag : ComponentTag) (mods : List ProbeModule) (entries : List String) :
    Heap × List Tm × List (Continuation × Option Target) × List String := Id.run do
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
  -- (at node `k`, the closure of node `j < k` is at slot `k - 1 - j`)
  let closures : List Tm := order.zipIdx.map fun (g, k) =>
    .makeAt (.graph g.ar g.code.1 g.code.2 (g.code.1.length - 1)
      (g.siblings.map fun x => if mods.any (·.name == x) then .var (k - 1 - slotOf x) else realmValue x) .call false tag) [] []
  let exports : Tm := .arrLit (entries.map fun x => .var (order.length - 1 - slotOf x))
  return (realmNames.map fun _ => .nul, closures ++ [exports],
    (List.range order.length).map (fun k => (.bind ⟨k + 1, none⟩, none)) ++ [(.ret, none)], order.map (·.name))

/-- An object's fields, exactly `ks`, in any order. -/
def exactFields (j : Json) (ks : List String) (what : String) : Except String Unit := do
  let .obj kvs := j | throw s!"{what}: not an object"
  let have_ := kvs.toList.map (·.1)
  if let some k := have_.find? (!ks.contains ·) then throw s!"{what}: an unknown field {k}"
  if let some k := ks.find? (!have_.contains ·) then throw s!"{what}: no field {k}"

/-- The client obligation by kind the rows state (`rowsTheta`), each kind's
change but `keep`. -/
def rowsKinds (rows : List ComponentWire.Clients) : List (Option Verification.Kind × Footprints.Change) :=
  allKinds.filterMap fun k =>
    let c := rowsTheta (P := probePackage fun _ => false) rows ⟨none, k, none⟩
    if c == .keep then none else some (k, c)

/-- **The index of a component's protocol** (`componentProtocol`), built
once: its queries are the protocol (`componentIndex_query`). -/
@[noinline] def componentIndex {ofC : ComponentTag → Bool} {O : List (Option Nat)} (F : FFlow (markedPackage ofC O))
    (lay : List (Nat × Bool × Nat × Nat)) : ProtocolIndex (markedPackage ofC O) :=
  ProtocolIndex.ofWrites (flowWrites F) (capClose F (tokenCaps F lay) (captureSites F lay ++ F.O))

theorem componentIndex_query {ofC : ComponentTag → Bool} {O : List (Option Nat)} (F : FFlow (markedPackage ofC O))
    (lay : List (Nat × Bool × Nat × Nat)) : (componentIndex F lay).query = componentProtocol F lay := rfl

/-- A component's protocol at every part of its flow's sites, each part's
change but `keep` (`componentProtocol`, `partsU`). -/
def protocolParts {ofC : ComponentTag → Bool} {O : List (Option Nat)} (F : FFlow (markedPackage ofC O))
    (lay : List (Nat × Bool × Nat × Nat)) : List (Option Nat × Option Verification.Kind × Footprints.Change) :=
  -- (the protocol's index built once, its parts queried)
  let idx := componentIndex F lay
  (partsU (flowSites F)).filterMap fun p =>
    let c := idx.query p
    if c == .keep then none else some (p.site, p.kind, c)

/-- **A forged component** (`TSCERT_FORCE`, the controls'):
`framed-flow-site` swaps the object and array sites of the first
allocation of the first code's body throughout the flow (a renaming the
flow's own checks pass), and `framed-init-exports` reads the exports'
first closure one slot too far. -/
def forgeComponent {ofC : ComponentTag → Bool} (force : List String) (cf : ComponentFlow ofC) (initE : List Tm) :
    ComponentFlow ofC × List Tm := Id.run do
  let mut cf := cf
  let mut initE := initE
  if force.contains "framed-flow-site" then
    let k := 3 * cf.lay.length
    let swap (s : Nat) : Nat := if s == k then k + 1 else if s == k + 1 then k else s
    let O : List (Option Nat) := cf.O.map (·.map swap)
    let flow : FFlow (markedPackage ofC O) :=
      FFlow.mapSites (P := markedPackage ofC cf.O) (Q := markedPackage ofC O) swap swap cf.flow
    cf := { cf with O, flow }
  if force.contains "framed-init-exports" then
    initE := initE.map fun e => match e with
      | .arrLit (.var v :: xs) => .arrLit (.var (v + 1) :: xs)
      | e => e
  return (cf, initE)

/-- **A framed plan's component, prepared once per component** (the draft,
"The plan"): its index `C` among the family's components, the tags of its
code, its entries, its module functions, the family the declaration
document describes, the checked file's name and functions, its `@clients`
rows; the restriction its module functions or rows violate; its flow
(`framedComponentFlow`, solved once); its protocol as defined at its flow's
sites (`protocolParts`); its realm and initialization (`componentInit`);
and the refusal of the binding checks that read the component alone
(`componentBindingRefusal`). Each refused unit's framed plan reads it. -/
structure FramedComponent where
  C : Nat
  ofC : ComponentTag → Bool
  entries : List String
  mods : List ProbeModule
  family : ComponentWire.Components
  file : String
  fns : List (String × Span × Bool)
  rows : List ComponentWire.Clients
  restriction : Option String
  cf : ComponentFlow ofC
  psiDef : List (Option Nat × Option Verification.Kind × Footprints.Change)
  realm : Heap
  initE : List Tm
  initK : List (Continuation × Option Target)
  initOrder : List String
  /-- The refusal of the checks that read the component alone, with the
  evaluation it is where the component meets the restrictions. -/
  refusal : { w : Option String // restriction = none → w = componentBindingRefusal cf.flow cf.lay cf.codes
    cf.names entries realm.length initOrder initE initK family file fns C }

/-- **A framed plan's component flow**: the component flow of `mods`
(`componentFlow`), its allocation sites numbered by the codes' bodies
(`moduleBody`), each module function's request code beside its realized
code (`FFlow.withCode`). -/
def framedComponentFlow (ofC : ComponentTag → Bool) (mods : List ProbeModule) (entries : List String) :
    ComponentFlow ofC :=
  let codes := (mods.filter fun g => ofC g.comp).map (·.code)
  let cf := componentFlow ofC mods entries "" (body := moduleBody codes)
  { cf with flow := cf.codes.foldl (fun F m => F.withCode m (moduleBody cf.codes m)) cf.flow }

/-- **A framed plan's component, prepared** (`FramedComponent`): where the
module functions and rows meet the restrictions, the flow solved once and
the checks that read the component alone run once (forged where `force`
asks, `forgeComponent`). -/
def FramedComponent.of (C : Nat) (ofC : ComponentTag → Bool) (entries : List String) (mods : List ProbeModule)
    (family : ComponentWire.Components) (file : String) (fns : List (String × Span × Bool)) (force : List String) :
    FramedComponent :=
  let rows := componentRows family C
  let restriction := framedRestriction mods rows
  let cf := if restriction.isSome then componentFlow ofC [] entries "" else framedComponentFlow ofC mods entries
  let tag := (mods.head?.map (·.comp)).getD none
  let (realm, initE, initK, initOrder) := componentInit tag mods entries
  -- (forged where `force` asks, `forgeComponent`)
  let (cf, initE) := forgeComponent force cf initE
  let psiDef := if restriction.isSome then [] else protocolParts cf.flow cf.lay
  -- (evaluated once per component, where it meets the restrictions)
  let refusal := if restriction.isSome then none else
    componentBindingRefusal cf.flow cf.lay cf.codes cf.names entries realm.length initOrder initE initK family file fns C
  { C, ofC, entries, mods, family, file, fns, rows, restriction, cf, psiDef, realm, initE, initK, initOrder,
    refusal := ⟨refusal, fun h => by simp [refusal, h]⟩ }

/-- **The refusal of the checks that read the component alone, at the
component `C`**, with the evaluation it is: the component's, computed once,
at its own index; evaluated at another index; none where the component
fails a restriction. -/
def FramedComponent.refusalAt (fc : FramedComponent) (C : Nat) :
    Option { w : Option String // w = componentBindingRefusal fc.cf.flow fc.cf.lay fc.cf.codes fc.cf.names fc.entries
      fc.realm.length fc.initOrder fc.initE fc.initK fc.family fc.file fc.fns C } :=
  match hr : fc.restriction with
  | some _ => none
  | none => some (if hC : C = fc.C then ⟨fc.refusal.val, by subst hC; exact fc.refusal.property hr⟩ else ⟨_, rfl⟩)

open Verification.TolerantFrames.ReadOnly in
/-- **The decoder of a framed plan's document**: its fields exactly those
of `framedDocument`; the flow its component's (`fc`); the document refused
where it disagrees with it: its entries other than the component's, its
framed call nodes other than the flow's (`framedCallNodes`), or a support
it keeps failing the frame's check (`framedSupportsAt`, at the component's
protocol as defined and the `@clients` rows' obligation); then the plan's
proposals: the document's component, client obligation and protocol,
which the pass checks (`compB`, `clientsB`, `protocolAtLeastB`), and the
member's read-only inputs at their declared shapes (`readOnlyInputs`). -/
def FramedSpec.decode {σ ι : Type} [LabelStore.Labels ι] [LabelStore.StoreView σ ι]
    (G : NormalGraph ι) (fc : FramedComponent) (member : String)
    (r : SourceExtraction.SourceRequest σ ι) (doc : Json) : Except String (FramedSpec ι) := do
  exactFields doc ["component", "entries", "theta", "protocol", "framed"] "a framed plan's document"
  let C ← doc.getObjValAs? Nat "component"
  let entries' ← doc.getObjValAs? (List String) "entries"
  let theta ← (← (← doc.getObjVal? "theta").getArr?).toList.mapM fun e => do
    let #[k, c] := (← e.getArr?) | throw "an entry of the document's theta: not a kind and a change"
    return (← kindNameOf k, ← EffectCodec.changeOf c)
  let psi ← (← (← doc.getObjVal? "protocol").getArr?).toList.mapM fun e => do
    let #[s, k, c] := (← e.getArr?) | throw "an entry of the document's protocol: not a site, a kind and a change"
    return (← fromJson? (α := Option Nat) s, ← kindNameOf k, ← EffectCodec.changeOf c)
  let rows ← (← doc.getObjVal? "framed").getArr?
  let framed ← rows.toList.mapM fun row => do
    exactFields row ["node", "supports"] "a framed call node of the document"
    let l ← row.getObjValAs? Nat "node"
    let Ss ← (← row.getObjVal? "supports").getArr?
    return (l, ← Ss.toList.mapM (EffectCodec.frameOf 64))
  if entries' != fc.entries then throw s!"the document's entries {entries'} are not the component's {fc.entries}"
  let m := realizedCode r
  let F := fc.cf.flow
  let nodes := framedCallNodes F fc.cf.host m
  if framed.map (·.1) != nodes then throw s!"the document's framed call nodes {framed.map (·.1)} are not the flow's {nodes}"
  let ΨC : Protocol (markedPackage fc.ofC fc.cf.O) := protocolOfParts id (partsIndex fc.psiDef)
  let Θ : Protocol (markedPackage fc.ofC fc.cf.O) := rowsTheta (componentRows fc.family C)
  for (l, Ss) in framed do
    let some Φ := (r.claims[l]?).bind fun c => (r.program[l]?).bind fun n => callEffectAt G c n.expression
      | throw s!"the document's framed call node {l} has no stated effect of its callee"
    let kept := framedSupportsAt F fc.cf.lay fc.cf.host ΨC Θ m l Φ Ss
    if kept.length != Ss.length then
      throw s!"at the document's framed call node {l}, {Ss.length - kept.length} of the supports it keeps fail the frame's check"
  let some componentRefusal := fc.refusalAt C | throw (fc.restriction.getD "")
  return { C, readOnly := readOnlyInputs fc.family C member r.inputs, outType := [], realm := fc.realm,
           initE := fc.initE, initK := fc.initK, initOrder := fc.initOrder,
           arity := r.inputs.length - r.siblings.length, ofC := fc.ofC,
           marks := fc.cf.O, checked := F, lay := fc.cf.lay, host := fc.cf.host, family := fc.family,
           file := fc.file, fns := fc.fns, codes := fc.cf.codes, names := fc.cf.names, entries := fc.entries,
           theta, psi, psiDef := fc.psiDef, componentRefusal, framed }

/-- **A forged document** (`TSCERT_FORCE`, the controls'): `framed-doc-node`
names a node no call frames, `framed-doc-support` keeps a support the
frame's check fails, `framed-doc-component` and `framed-doc-entries` name
another component and entries, `framed-doc-theta` states a client
obligation the rows do not, `framed-doc-protocol` states no protocol,
`framed-doc-field` adds a field and `framed-doc-missing` drops the
entries. -/
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
  if force.contains "framed-doc-theta" then
    doc := doc.setObjVal! "theta" (Json.arr #[Json.arr #[kindNameJ (some .field), EffectCodec.changeJ .any]])
  if force.contains "framed-doc-protocol" then doc := doc.setObjVal! "protocol" (Json.arr #[])
  if force.contains "framed-doc-field" then doc := doc.setObjVal! "forged" (toJson true)
  if force.contains "framed-doc-missing" then
    if let .obj kvs := doc then doc := .obj (kvs.erase "entries")
  return doc

/-- **A forged plan** (`TSCERT_FORCE`, the controls'): `framed-spec-readonly`
reads the request's first input read-only. -/
def forgeSpec {ι : Type} (force : List String) (inputs : List (ProgramTyping.Ty ι)) (spec : FramedSpec ι) : FramedSpec ι :=
  if force.contains "framed-spec-readonly" then { spec with readOnly := inputs.take 1 } else spec

/-- **A member's framed plan, produced** (the draft, "The plan"): where the
member's component (`fc`, prepared once) meets the restrictions, the member
is a realized module function of it and has a framed call node in its
component's flow whose callee may be a value of outside code
(`outsideCalleeAt`), its document (`framedDocument`: the component, its
entries, the rows' client obligation by kind, the component's protocol at
its flow's sites and each framed call node's supports, forged where
`force` asks), decoded (`FramedSpec.decode`), and the file's plans with
the member's plan the framed plan (forged where `force` asks,
`forgeSpec`). `none` where the member has no such framed call node; an error
where a restriction or the decoder refuses. -/
def FilePlans.framedPlan (f : FilePlans) (fuel i : Nat) (fc : FramedComponent) (force : List String) :
    Except String (Option (FilePlans × List String)) := do
  let some (.ok (.graph name pos r)) := f.plans[i]? | return none
  if !(fc.mods.any (·.name == name)) then throw "a framed plan needs a realized entry"
  if let some w := fc.restriction then throw w
  let some m := (fc.cf.codes.zip fc.cf.names).find? (·.2.1 == name) |>.map (·.1)
    | throw "a framed plan needs a realized entry"
  let F := fc.cf.flow
  let nodes := framedCallNodes F fc.cf.host m
  -- (a framed plan keeps facts across a call of a value of outside code:
  -- none is formed where no framed call's callee may be one)
  if !(nodes.any fun l => (F.ctxs m).any fun (_, c) => outsideCalleeAt c m l) then return none
  let ΨC : Protocol (markedPackage fc.ofC fc.cf.O) := protocolOfParts id (partsIndex fc.psiDef)
  let Θ : Protocol (markedPackage fc.ofC fc.cf.O) := rowsTheta fc.rows
  let (framed, shown) := f.framedSupports fuel i fc.cf ΨC Θ r m nodes
  let doc := forgeDocument force (framedDocument fc.C fc.entries (rowsKinds fc.rows) fc.psiDef framed)
  let G : NormalGraph (EquationStore.CheckedLabel f.F.equations f.F.primitive) := LabelStore.StoreView.graph f.F.store
  let spec ← (FramedSpec.decode G fc name r doc).mapError fun e => s!"a framed plan's document is refused: {e}"
  return some (f.withPlan i (.framed name pos r (forgeSpec force r.inputs spec)), s!"framed plan, {name}: framed call nodes {nodes}" :: shown)

end Verification.SourceClaimJson
