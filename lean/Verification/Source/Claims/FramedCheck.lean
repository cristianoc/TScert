import Verification.Source.Claims.FlowProbe
import Verification.Source.Claims.MemberSettle

/-! # A framed plan's check, run beside the verdict

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "What the pass checks"). At each call
node of a member's main graph whose call may reach outside code (a framed
call, `framedCallNodes`), the supports the frame keeps are those the
check of the node the pass runs keeps (`framedNodeKeeps`, `supportKeptB`):
the read-only frame's check (`frameCheckAt`) at the node's protocol
$`\Psi_c(l)`$ (`nodeProtocol`: the client obligation, the component's
protocol and the depth charges at the node's set) and the callee's stated
effect read at the caller's slots (`callEffectAt`), at every context of
the request's code in the flow and every node of the call's continuation
and handler. The supports offered are those of the
call's entry facts, in the pass's slot numbering (`SinglePass.framedAt`).
`FilePlans.framedCheck` runs the member's main graph with its framed calls
keeping the supports the check passes, settled as a member's run is
(`inferredNext`'s candidates left out at a head that lacks them), a report
(`TSCERT_FRAMED`). The producer of a framed plan (`FilePlans.framedPlan`)
states the plan's restrictions (`framedRestriction`), the realm and the
initialization of the component (`componentInit`), and its document, which
the decoder (`FramedSpec.decode`) checks against the flow it recomputes;
`FilePlans.passMember` checks the plan and refuses it
(`FilePlans.framedRefusal`). -/

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
sites numbered by the codes' bodies (`body`), its initialization `init`
among its codes where one is given. -/
def componentFlow (ofC : ComponentTag → Bool) (mods : List ProbeModule) (entryNames : List String)
    (member : String) (fuel : Nat := 10000000) (body : Code → Code := id) (init : Option (Code × List String) := none) :
    ComponentFlow ofC :=
  let cc := componentCodes ofC mods entryNames body init
  let s := solveStart cc.cs
  let (st, _, _) := solveLoop s fuel s.st
  let F := s.propose st
  let n := cc.reps.length
  let k := cc.hosts.length
  ⟨F.O, remark F, cc.cs.map fun c => (c.ar, c.rest, c.ncaps, c.start), fun i => n ≤ i && i < n + k,
    cc.mods.map (·.code), cc.mods.map (fun g => (g.name, g.ar, g.siblings)),
    (cc.mods.find? (·.name == member)).map (·.code)⟩

/-- A property key, as a diagnostic names it. -/
def propKeyText : PropKey → String
  | .str s => s
  | .sym i => s!"symbol {i}"

/-- **A region**, as a diagnostic names it: its slot and the keys of its
path. -/
def regionText : Footprints.Region → String
  | .field x k => s!"slot {x}.{propKeyText k}"
  | .fields x => s!"slot {x}.fields"
  | .cells x => s!"slot {x}.cells"
  | .cls _ => "a class"
  | .all => "every location"
  | .path x p k => s!"slot {x}{String.join (p.map ("." ++ ·))}.{propKeyText k}"
  | .pathFields x p => s!"slot {x}{String.join (p.map ("." ++ ·))}.fields"
  | .pathCells x p => s!"slot {x}{String.join (p.map ("." ++ ·))}.cells"
  | .inCls r _ => s!"{regionText r} in a class"
  | .spine x p => s!"slot {x}{String.join (p.map ("." ++ ·))}.spine"

/-- A change, as a diagnostic names it. -/
def changeText (c : Footprints.Change) : String := ((EffectCodec.changeJ c).getStr?).toOption.getD ""

/-- **A part** (site, kind, key), as a diagnostic names it. -/
def partText {P : Package} (p : Part P) (site : P.Site → Nat) : String :=
  let s := match p.site with
    | none => "storage of code outside the component"
    | some n => s!"the site {site n}"
  let k := match p.kind with
    | some .field => "field" | some .cell => "cell" | some .elem => "element" | some .spine => "spine"
    | some .identity => "identity" | none => "no kind"
  let key := (p.key.map propKeyText).getD "no key"
  s!"({s}, {k}, {key})"

/-- **Why a framed node drops a support**, as a line (`supportFailure`). -/
def supportFailureText {P : Package} (site : P.Site → Nat) (l : Nat) :
    Footprints.Region × Option ((Footprints.Region × Footprints.Change) × Part P × Bool × Bool × Footprints.Change) →
      String
  | (r, none) => s!"framed node {l} drops a support: the region {regionText r} has no sites"
  | (_, some (e, p, inside, outside, ψ)) =>
    let why := (if inside then [s!"the node's protocol is {changeText ψ} there, above {changeText e.2}"] else []) ++
      (if outside then [s!"the callee's stated effect changes it beyond {changeText e.2}, the region read unprotected"]
        else [])
    s!"framed node {l} drops a support: {regionText e.1} at {changeText e.2} fails at the part {partText p site}: {"; ".intercalate why}"

/-- **The supports each framed call node keeps**, as the producer proposes
them: each node's entry facts' supports, observed in the walk framing the
nodes found before it (none at a node the walk does not reach), those the
node's check keeps (`framedNodeKeeps` at the request's code, the client
obligation `Θ`); with a line per node, and a line per node that drops a
support naming why it drops the first (`supportFailure`). -/
def FilePlans.framedSupports {ofC : ComponentTag → Bool} (f : FilePlans) (fuel i : Nat) (cf : ComponentFlow ofC)
    (Θ : Protocol (markedPackage ofC cf.O)) (r : SourceElaboration.SourceRequest (EquationStore.Checked f.F.equations f.F.primitive)
      (EquationStore.CheckedLabel f.F.equations f.F.primitive)) (nodes : List Nat) :
    List (Nat × List Footprints.Footprint) × List String × List String := Id.run do
  let G : NormalGraph (EquationStore.CheckedLabel f.F.equations f.F.primitive) := LabelStore.StoreView.graph f.F.store
  -- (each node observed in the walk framing those found before it; a node
  -- the walk reaches only past a later framed node is taken again, once
  -- per framed node)
  let mut framed : List (Nat × List Footprints.Footprint) := []
  let mut shown : List String := []
  let mut why : List (Nat × String) := []
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
          let m := requestCode r
          let kept := match m.1[l]? with
            | some e => framedNodeKeeps cf.flow cf.lay Θ m l e Φ Ss
            | none => []
          let reason := match m.1[l]? with
            | some e => (Ss.findSome? fun S => supportFailure cf.flow cf.lay Θ m l e Φ S).map (supportFailureText id l)
            | none => none
          why := why.filter (·.1 != l) ++ (reason.map fun w => (l, w)).toList
          let lost := atoms.filter fun a => !SinglePass.supportedIn kept a.fact
          shown := shown ++ [s!"  node {l}: effect {(reprStr Φ).replace "\n" " "}; {kept.length} of {Ss.length} entry supports kept; dropped {(toJson lost).compress}"]
          framed := others ++ [(l, kept)]
        | .observed _, none => shown := shown ++ [s!"  node {l}: no stated effect of its callee"]
        | o, _ => shown := shown ++ [s!"  node {l} not observed: {o}"]
      | .error e => shown := shown ++ [s!"  node {l} not observed: {e}"]
    if framed == start then break
  -- (a node the walk does not reach keeps no support)
  return (nodes.map fun l => (l, ((framed.find? (·.1 == l)).map (·.2)).getD []), shown, why.map (·.2))

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
    let (framed, shown, _) := match g.plans[i]? with
      | some (.ok (.graph _ _ r')) => g.framedSupports fuel i cf (fun _ => .keep) r' nodes
      | _ => ([], [], [])
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
of its exported types: no module function naming another (a linked
capture); no module function creating a closure; every outside slot of a module function an audited realm value (a native with a
step model, `hostModel?`, or an intrinsic object); the rows stating class
keys only (`clientsByKindB`); every module function of the module with
closure code (`unplanned` lists those without) and every entry a module
function. The first violated, as its located refusal's text. A framed
plan's member is moreover a realized module function
(`FilePlans.framedPlan`). -/
def framedRestriction (mods : List ProbeModule) (rows : List ComponentWire.Clients) (entries unplanned : List String) :
    Option String :=
  let named := mods.findSome? fun g => (g.siblings.find? fun x => mods.any (·.name == x)).map (g.name, ·)
  if let some (g, x) := named then
    some s!"a framed plan's module function {g} names the module function {x}, a linked capture"
  else if let some g := mods.find? fun g => !(g.code.1.flatMap (closureLayouts fun _ => true)).isEmpty then
    some s!"a framed plan's module function {g.name} creates a closure"
  else
  -- (a slot of the module's own, a cell or a constant, named before a
  -- native's)
  let slots := mods.flatMap fun g => g.siblings.map (g.name, ·)
  let slots := slots.filter (!·.2.startsWith "%") ++ slots.filter (·.2.startsWith "%")
  match slots.find? fun (_, x) => !(mods.any (·.name == x) || (hostModel? x).isSome || intrinsicName x) with
  | some (g, x) => some s!"a framed plan's module function {g} reads {x}, which is not an audited realm value"
  | none => if !clientsByKindB rows then some "a framed plan's component states a `@clients` path key"
    else if let some x := unplanned.head? then
      some s!"a framed plan's module function {x} has no closure code (it declares `this`, or its file plans it at no graph)"
    else (entries.find? fun x => !(mods.any (·.name == x))).map fun x =>
      s!"a framed plan's component exports {x}, which is no module function"

/-- **The realm's identity of a realm value** a module function reads, at
the realm's location `loc`: a native with a step model (`hostModel?`) is a
closure of its model's code, tagged `tag`; an intrinsic object an object. -/
def realmValueAt (tag : ComponentTag) (x : String) (loc : Nat) : Tm :=
  match hostModel? x with
  | some (c, ar) => .objAt [] (.graph ar c.1 c.2 0 [] .call false tag) loc
  | none => .objAt [] .absent loc

/-- **The realm and the initialization of a component** (the draft,
"Initialization", `initC`). -/
structure ComponentInit where
  /-- The realm's heap: one location per audited realm value the module
  functions read. -/
  realm : Heap
  initE : List Tm
  initK : List (Continuation × Option Target)
  /-- The module functions by name, in the order the initialization
  allocates their closures. -/
  order : List String
  /-- The realm's identities the initialization's slots hold at its entry,
  one per realm value, in order. -/
  initL : List Tm
  /-- The realm values' names, in order. -/
  realmNames : List String

/-- **The realm and the initialization of a component** (the draft,
"Initialization", `initC`): the realm's heap, one identity per audited
realm value the module functions read (`realmValueAt`), held by the
initialization's slots at its entry; the initialization's code, each
module function's closure allocated after those it names (its captures
each named module function's closure, read at the slot binding it, or the
realm value, read at the slot holding it), then the array of the entries;
and its order, the module functions by name. Node `k`'s slots hold the
closures nodes `0` to `k - 1` allocated, the latest first, then the realm's
identities. -/
def componentInit (tag : ComponentTag) (mods : List ProbeModule) (entries : List String) : ComponentInit := Id.run do
  let realmNames := (mods.flatMap (·.siblings)).filter (fun x => !(mods.any (·.name == x))) |>.eraseDups
  -- (the module functions in an order where each comes after those it names)
  let mut order : List ProbeModule := []
  for _ in mods do
    for g in mods do
      if !(order.any (·.name == g.name)) &&
          g.siblings.all fun x => !(mods.any (·.name == x)) || order.any (·.name == x) then
        order := order ++ [g]
  let slotOf (x : String) : Nat := order.findIdx (·.name == x)
  -- (at node `k`, the closure of node `j < k` is at slot `k - 1 - j`, the
  -- realm value `j` at slot `k + j`)
  let closures : List Tm := order.zipIdx.map fun (g, k) =>
    .makeAt (.graph g.ar g.code.1 g.code.2 (g.code.1.length - 1)
      (g.siblings.map fun x => if mods.any (·.name == x) then .var (k - 1 - slotOf x) else .var (k + realmNames.idxOf x))
      .call g.rest tag) [] []
  let exports : Tm := .arrLit (entries.map fun x => .var (order.length - 1 - slotOf x))
  return ⟨realmNames.map fun _ => .nul, closures ++ [exports],
    (List.range order.length).map (fun k => (.bind ⟨k + 1, none⟩, none)) ++ [(.ret, none)], order.map (·.name),
    realmNames.zipIdx.map fun (x, j) => realmValueAt tag x j, realmNames⟩

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
    let c := rowsAt rows k
    if c == .keep then none else some (k, c)

/-- Materialize the charges and the closed set of sites. Returning data
here keeps the native compiler from postponing the closure until a part is
queried. -/
@[noinline] def componentCharges {ofC : ComponentTag → Bool} {O : List (Option Nat)}
    (F : FFlow (markedPackage ofC O)) (lay : List (Nat × Bool × Nat × Nat)) :
    List Charge × Std.HashSet (Option Nat) :=
  (flowKinds F, Std.HashSet.ofList (capClose F (tokenCaps F lay) (captureSites F lay ++ F.O)))

def chargeAt {ofC : ComponentTag → Bool} {O : List (Option Nat)}
    (charges : List Charge × Std.HashSet (Option Nat)) : Protocol (markedPackage ofC O) :=
  fun p => if p.site.any (fun s => (markedPackage ofC O).mark s = .local) && !charges.2.contains p.site then .keep
    else if charges.1.contains (p.kind, p.key) then .any else .keep

def componentIndex {ofC : ComponentTag → Bool} {O : List (Option Nat)} (F : FFlow (markedPackage ofC O))
    (lay : List (Nat × Bool × Nat × Nat)) : Protocol (markedPackage ofC O) :=
  chargeAt (componentCharges F lay)

theorem componentIndex_eq {ofC : ComponentTag → Bool} {O : List (Option Nat)} (F : FFlow (markedPackage ofC O))
    (lay : List (Nat × Bool × Nat × Nat)) : componentIndex F lay = componentProtocol F lay := rfl

/-- A component's protocol at every part of its flow's sites and its
charges' keys, each part's change but `keep` (`componentProtocol`,
`partsU`); it is `keep` at every other key (`probeProtocol`). -/
def protocolParts {ofC : ComponentTag → Bool} {O : List (Option Nat)} (F : FFlow (markedPackage ofC O))
    (lay : List (Nat × Bool × Nat × Nat)) : List (Option Nat × Option Verification.Kind × Option PropKey × Footprints.Change) :=
  -- (the protocol's index built once, its parts queried)
  let charges := componentCharges F lay
  (partsU (flowSites F) (none :: charges.1.map (·.2)).eraseDups).filterMap fun p =>
    let c := chargeAt (ofC := ofC) (O := O) charges p
    if c == .keep then none else some (p.site, p.kind, p.key, c)

/-- **A forged component** (`--force-proposals`, the controls'):
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
document describes, its `@clients`
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
  rows : List ComponentWire.Clients
  restriction : Option String
  cf : ComponentFlow ofC
  psiDef : List (Option Nat × Option Verification.Kind × Option PropKey × Footprints.Change)
  realm : Heap
  initE : List Tm
  initK : List (Continuation × Option Target)
  initOrder : List String
  initL : List Tm
  /-- The refusal of the checks that read the component alone, with the
  evaluation it is where the component meets the restrictions. -/
  refusal : { w : Option String // restriction = none → w = componentBindingRefusal cf.flow cf.lay cf.codes
    cf.names entries realm initOrder initE initK initL C }

/-- **A framed plan's component flow**: the component flow of `mods`
(`componentFlow`), its allocation sites numbered by the codes' bodies
(`moduleBody`), each module function's request code beside its realized
code (`FFlow.withCode`), its initialization `init` among its codes. -/
def framedComponentFlow (ofC : ComponentTag → Bool) (mods : List ProbeModule) (entries : List String)
    (init : Code × List String) : ComponentFlow ofC :=
  let codes := (mods.filter fun g => ofC g.comp).map (·.code)
  let cf := componentFlow ofC mods entries "" (body := moduleBody codes) (init := some init)
  { cf with flow := cf.codes.foldl (fun F m => F.withCode m (moduleBody cf.codes m)) cf.flow }

/-- **A framed plan's component, prepared** (`FramedComponent`): where the
module functions and rows meet the restrictions, the flow solved once and
the checks that read the component alone run once (forged where `force`
asks, `forgeComponent`). -/
def FramedComponent.of (C : Nat) (ofC : ComponentTag → Bool) (entries : List String) (mods : List ProbeModule)
    (unplanned : List String) (family : ComponentWire.Components) (force : List String) : FramedComponent :=
  let rows := componentRows family C
  let restriction := framedRestriction mods rows entries unplanned
  let tag := (mods.head?.map (·.comp)).getD none
  let ci := componentInit tag mods entries
  let (realm, initK, initOrder, initL) := (ci.realm, ci.initK, ci.order, ci.initL)
  let cf := if restriction.isSome then componentFlow ofC [] entries ""
    else framedComponentFlow ofC mods entries ((ci.initE, initK), ci.realmNames)
  -- (forged where `force` asks, `forgeComponent`)
  let (cf, initE) := forgeComponent force cf ci.initE
  let psiDef := if restriction.isSome then [] else protocolParts cf.flow cf.lay
  -- (evaluated once per component, where it meets the restrictions)
  let refusal := if restriction.isSome then none else
    componentBindingRefusal cf.flow cf.lay cf.codes cf.names entries realm initOrder initE initK initL C
  { C, ofC, entries, mods, family, rows, restriction, cf, psiDef, realm, initE, initK, initOrder, initL,
    refusal := ⟨refusal, fun h => by simp [refusal, h]⟩ }

/-- **The refusal of the checks that read the component alone, at the
component `C`**, with the evaluation it is: the component's, computed once,
at its own index; evaluated at another index; none where the component
fails a restriction. -/
def FramedComponent.refusalAt (fc : FramedComponent) (C : Nat) :
    Option { w : Option String // w = componentBindingRefusal fc.cf.flow fc.cf.lay fc.cf.codes fc.cf.names fc.entries
      fc.realm fc.initOrder fc.initE fc.initK fc.initL C } :=
  match hr : fc.restriction with
  | some _ => none
  | none => some (if hC : C = fc.C then ⟨fc.refusal.val, by subst hC; exact fc.refusal.property hr⟩ else ⟨_, rfl⟩)

open Verification.TolerantFrames.ReadOnly in
/-- **The decoder of a framed plan's document**: its fields exactly those
of `framedDocument`; the flow its component's (`fc`); the document refused
where it disagrees with it: its entries other than the component's or its
framed call nodes other than the flow's (`framedCallNodes`); then the
plan's proposals: the document's component, client obligation and protocol,
which the pass checks (`compB`, `clientsB`, `protocolAtLeastB`), and the
member's read-only inputs at their declared shapes (`readOnlyInputs`). -/
def FramedSpec.decode {σ ι : Type} [LabelStore.Labels ι] [LabelStore.StoreView σ ι]
    (fc : FramedComponent) (member : String)
    (r : SourceElaboration.SourceRequest σ ι) (doc : Json) : Except String (FramedSpec ι) := do
  exactFields doc ["component", "entries", "theta", "protocol", "framed"] "a framed plan's document"
  let C ← doc.getObjValAs? Nat "component"
  let entries' ← doc.getObjValAs? (List String) "entries"
  let theta ← (← (← doc.getObjVal? "theta").getArr?).toList.mapM fun e => do
    let #[k, c] := (← e.getArr?) | throw "an entry of the document's theta: not a kind and a change"
    return (← kindNameOf k, ← EffectCodec.changeOf c)
  let psi ← (← (← doc.getObjVal? "protocol").getArr?).toList.mapM fun e => do
    let #[s, k, key, c] := (← e.getArr?)
      | throw "an entry of the document's protocol: not a site, a kind, a key and a change"
    return (← fromJson? (α := Option Nat) s, ← kindNameOf k, ← (if key.isNull then pure none else some <$> EffectCodec.keyOf key), ← EffectCodec.changeOf c)
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
  let some componentRefusal := fc.refusalAt C | throw (fc.restriction.getD "")
  return { C, readOnly := readOnlyInputs fc.family C member r.inputs, outType := [], realm := fc.realm,
           initE := fc.initE, initK := fc.initK, initOrder := fc.initOrder, initL := fc.initL,
           arity := r.inputs.length - r.siblings.length, ofC := fc.ofC,
           marks := fc.cf.O, checked := F, lay := fc.cf.lay, host := fc.cf.host, family := fc.family,
           codes := fc.cf.codes, names := fc.cf.names, entries := fc.entries,
           theta, psi, psiDef := fc.psiDef, componentRefusal, framed }

/-- **A forged document** (`--force-proposals`, the controls'): `framed-doc-node`
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

/-- **A forged plan** (`--force-proposals`, the controls'): `framed-spec-readonly`
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
`forgeSpec`), with the producer's lines and, for each framed node that
drops a support, why it drops the first. `none` where the member has no
such framed call node; an error where a restriction or the decoder
refuses. -/
def FilePlans.framedPlan (f : FilePlans) (fuel i : Nat) (fc : FramedComponent) (force : List String) :
    Except String (Option (FilePlans × List String × List String)) := do
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
  let Θ : Protocol (markedPackage fc.ofC fc.cf.O) := rowsTheta fc.rows
  let (framed, shown, why) := f.framedSupports fuel i fc.cf Θ r nodes
  let doc := forgeDocument force (framedDocument fc.C fc.entries (rowsKinds fc.rows) fc.psiDef framed)
  let spec ← (FramedSpec.decode fc name r doc).mapError fun e => s!"a framed plan's document is refused: {e}"
  return some (f.withPlan i (.framed name pos r (forgeSpec force r.inputs spec)),
    s!"framed plan, {name}: framed call nodes {nodes}" :: shown, why)

end Verification.SourceClaimJson
