import Verification.Source.Claims.CallbackInferencePlan

/-! Consumers of the experimental callback interface. The interface here
contains the producer's requirements and binding identity. The consumer
reads its own lowered calls and checked closure code only. -/
namespace Verification.SourceClaimJson.CallbackInterfaceCheck
open ControlFlow ProgramTyping RequestJson SourceElaboration LabelStore
open CallbackOrigins CallbackPreservation CallbackEffectInference
open Footprints

structure Published where
  name : String
  position : Option (Nat × Nat)
  receiver : Bool
  formals : Nat
  interface : CallbackInferencePlan.Interface

def publicRegion (width : Nat) : Region → Bool
  | .field i _ | .fields i | .cells i | .path i _ _ | .pathFields i _ | .pathCells i _
  | .spine i _ => i < width
  | .inCls r _ => publicRegion width r
  | .all | .cls _ => true

def Published.validate (p : Published) : Except String Published := do
  let valid := p.interface.demands.all fun d =>
    d.parameter < p.formals &&
      (d.support.normal ++ d.support.exceptional).all (fun e => publicRegion p.formals e.1) &&
      d.actualRoots.all (fun root => root.all (fun path => path.1 < p.formals))
  if !valid then throw s!"callback requirement for {p.name} refers outside its fixed parameters"
  return p

open Lean in
def Published.toJson (p : Published) : Json :=
  let demands := p.interface.demands.map fun d =>
    Json.mkObj [("parameter", Lean.toJson d.parameter),
      ("normal", EffectCodec.frameJ d.support.normal),
      ("exceptional", EffectCodec.frameJ d.support.exceptional), ("actualRoots", Lean.toJson d.actualRoots)]
  Json.mkObj [("name", Lean.toJson p.name), ("position", Lean.toJson p.position),
    ("receiver", Lean.toJson p.receiver), ("formals", Lean.toJson p.formals), ("demands", Json.arr demands.toArray)]

open Lean in
def Published.ofJson (j : Json) : Except String Published := do
  fieldsExactly j ["name", "position", "receiver", "formals", "demands"]
  let name ← j.getObjValAs? String "name"
  let pos ← j.getObjValAs? (Option (Nat × Nat)) "position"
  let receiver ← j.getObjValAs? Bool "receiver"
  let formals ← j.getObjValAs? Nat "formals"
  let demands ← (← jArr j "demands").mapM fun d => do
    fieldsExactly d ["parameter", "normal", "exceptional", "actualRoots"]
    let parameter ← d.getObjValAs? Nat "parameter"
    let normal ← EffectCodec.frameOf 32 (← jField d "normal")
    let exceptional ← EffectCodec.frameOf 32 (← jField d "exceptional")
    let actualRoots ← d.getObjValAs? (List (Option (Nat × List String))) "actualRoots"
    return (⟨parameter, ⟨normal, exceptional⟩, actualRoots⟩ : Demand)
  Published.validate ⟨name, pos, receiver, formals, ⟨demands⟩⟩

def originOf (slots : Slots) : Tm → Option Origin
  | .var slot => match slots[slot]? with | some [o] => some o | _ => none
  | _ => none

def identity (inputCount : Nat) : Origin → Option Nat
  | .input i => some i
  | .allocated label => some (inputCount + label)
  | _ => none

/-- Name a producer actual at the caller boundary. A field read receives
a slot for its evaluated value. The producer may replace the field before
invoking its callback. Evaluated slots have no separation evidence. -/
def operandRoot (inputs nodes : Nat) (slots : Slots) (position : Nat) (t : Tm) :
    Option (Nat × List String) := do
  let origin ← originOf slots t
  match origin with
  | .read _ => return (inputs + nodes + position, [])
  | named => (identity inputs named).map (·, [])

def argumentRoots (inputs nodes : Nat) (slots : Slots) (frame : List Tm) : RootMap :=
  fun position => frame[position]?.bind (operandRoot inputs nodes slots position)

/-- Only an input identity can occur in a forwarded public requirement. -/
def publicOperand (inputs : Nat) (roots : RootMap) : RootMap := fun position => do
  let (root, path) ← roots position
  if root < inputs then some (root, path) else none

/-- Instantiate the checked rows for a literal closure using its allocation frame. -/
def closure {ι : Type} [DecidableEq ι] (codes : Array (CheckedCode ι))
    (nodes : Array Node) (origins : Table) (inputs : Nat) (slots : Slots)
    (callRoots : List (Option (Nat × List String))) (argument : Tm) : Option Callback := do
  let .allocated label ← originOf slots argument | none
  let node ← nodes[label]?
  let .makeAt (.graph arity exprs conts start captures _ rest _) _ _ := node.expression | none
  let rows := codes.filter fun c =>
    c.entry.arity == arity && c.entry.start == start && c.entry.exprs == exprs && c.entry.conts == conts &&
      captures.length == c.entry.captures.length && c.entry.spine.isSome == rest
  let first ← rows[0]?
  let restSlots := if first.entry.spine.isSome then 1 else 0
  let firstCapture := arity + frameOffset first.entry.spine
  let effects := rows.foldl (fun (acc : CallEffects.Exits Footprint) code =>
    ⟨(acc.normal ++ code.summary.normal.getD []).eraseDups,
      (acc.exceptional ++ code.summary.exceptional.getD []).eraseDups⟩) ⟨[], []⟩
  let actuals := fun slot => do
    if slot < restSlots then none
    else if slot < firstCapture then
      let some (root, []) := callRoots[slot - restSlots]?.join | none
      some root
    else
      let cap ← captures[slot - firstCapture]?
      originOf (origins.at label) cap >>= identity inputs
  return ⟨effects, actuals⟩

def separation (inputs nodes : Nat) (slots : Slots) : SepEvidence :=
  let roots := ((slots.toList.flatten.filterMap (identity inputs)).filter (· < inputs + nodes)).eraseDups
  { facts := roots.flatMap fun a => roots.filterMap fun b =>
      if a != b && (inputs ≤ a || inputs ≤ b) then some (.spines (a, []) (b, [])) else none }

/-- Check each caller supplying a literal closure using its inferred effect
and the alias information at the lowered call. -/
def knownSiblings (inputs : Nat) (siblings : List String) (interfaces : List Published) : List (Nat × Published) :=
  siblings.zipIdx.filterMap fun (name,j) =>
    (interfaces.find? (·.name == name)).map fun iface => (inputs - siblings.length + j,iface)

def mayInput (marked : List Nat) (slots : Slots) (i : Nat) : Bool :=
  (slots.getD i []).any fun
    | .input root => marked.contains root
    | _ => false

def markedResult (tracked : Nat → Bool) : Tm → Bool
  | .var j => tracked j
  | _ => false

def markedEdge (nodes : Array Node) (table : Table) (marked : List Nat)
    (valid tracked : Nat → Bool) (target : Target) : Bool :=
  let dst := table.at target.label
  privateReady nodes table target.label && (List.range dst.size).all fun i =>
    let j := PointClaims.slot target.mapping i
    valid j && (!tracked j || mayInput marked dst i)

/-- Every direct copy of a marked sibling remains visible at its outgoing
slot. Both normal and handler remappings must preserve this may information. -/
def checkMayInputs (nodes : Array Node) (table : Table) (start inputs : Nat) (marked : List Nat) : Bool :=
  let edge := markedEdge nodes table marked
  let initial := table.at start
  privateReady nodes table start && inputs ≤ initial.size &&
    marked.all (fun i => i < inputs && mayInput marked initial i) &&
    (List.range nodes.size).all fun label =>
      match table[label]?.join with
      | none => true
      | some slots =>
        let node := nodes[label]!
        let tracked := mayInput marked slots
        let valid := fun j => decide (j < slots.size)
        let fresh := markedResult tracked node.expression
        (SinglePass.mentioned 0 node.expression).any (fun ids => ids.all (· < slots.size)) &&
          (CertificateProducer.successors node.continuation).all
          (edge (afterSlot valid (GraphCode.pushes node.continuation) true) (afterSlot tracked (GraphCode.pushes node.continuation) fresh)) &&
          node.handler.toList.all (edge (afterSlot valid true true) (afterSlot tracked true false))

def invocationBindings (demand : Demand) (toCaller : RootMap) : List (Option (Nat × List String)) :=
  demand.actualRoots.map fun source => do
    let (slot, path) ← source
    let (root, outerPath) ← toCaller slot
    return (root, outerPath ++ path)

def absentCallback {σ ι : Type} [Labels ι] [StoreView σ ι]
    (r : SourceRequest σ ι) (label : Nat) (frame : List Tm) (parameter : Nat) : Bool :=
  match frame[parameter]? with
    | none | some .undef => true
    | some (.var slot) => ((r.claims[label]?).bind (·.context[slot]?)).any fun ty =>
      PositiveRules.expand (RequestJson.graph r.toRequest) ty == [.undef]
    | _ => false

def checkedCallFrame (producer : Published) (receiver : Tm) (args : List Tm) : List Tm :=
  let fixedArgs := CallbackInferencePlan.positionalPrefix args
  (if producer.receiver then receiver :: fixedArgs else fixedArgs).take producer.formals

def checkDemand {σ ι : Type} [Labels ι] [StoreView σ ι]
    (r : SourceRequest σ ι) (codes : Array (CheckedCode ι)) (origins : Table) (forwarding : List Nat)
    (producer : Published) (label : Nat) (receiver : Tm) (args : List Tm) (demand : Demand) :
    Except String (Option Demand) := do
  let nodes := r.program.toArray
  let inputs := r.inputs.length
  let slots := origins.at label
  let fixedArgs := CallbackInferencePlan.positionalPrefix args
  let frame := checkedCallFrame producer receiver args
  let toCaller := argumentRoots inputs nodes.size slots frame
  if demand.support.normal.isEmpty && demand.support.exceptional.isEmpty then return none
  if frame[demand.parameter]?.isNone && fixedArgs.length < args.length then
    throw s!"a spread obscures callback argument {demand.parameter + 1} at call of {producer.name} (node {label})"
  let absent := absentCallback r label frame demand.parameter
  if absent then return none
  if let some (.input position) := frame[demand.parameter]?.bind (originOf slots) then
    if forwarding.contains position then
      let some rebased := demand.forward position (publicOperand inputs toCaller)
        | throw s!"the forwarded requirement at node {label} cannot name a caller input"
      return some rebased
  let actuals := invocationBindings demand toCaller
  let callbacks := fun parameter => (frame[parameter]?).bind (closure codes nodes origins inputs slots actuals)
  if !demand.check toCaller callbacks (separation inputs nodes.size slots) then
    throw s!"callback argument {demand.parameter + 1} at call of {producer.name} (node {label}) fails its inferred preservation requirement"
  return none

def escapesDeclaration (slots : Slots) (known : List (Nat × Published)) (node : Node) : Bool :=
  let referenced := fun (indices : List Nat) => indices.any fun slot =>
    (slots.getD slot []).any fun origin => match origin with
      | .input root => known.any (·.1 == root)
      | _ => false
  let reads := match node.expression with
    | .var slot => if node.continuation == Continuation.ret then some [slot] else some []
    | .invoke (.var fn) receiver actuals =>
      let possible := (slots.getD fn []).any fun origin => match origin with
        | .input root => known.any (·.1 == root)
        | _ => false
      if possible && !(originOf slots (.var fn)).isSome then none
      else SinglePass.mentionedAll 0 (receiver :: actuals)
    | term => SinglePass.mentioned 0 term
  reads.any referenced || (reads.isNone && !known.isEmpty)

def checkNode {σ ι : Type} [Labels ι] [StoreView σ ι]
    (r : SourceRequest σ ι) (codes : Array (CheckedCode ι)) (origins : Table) (known : List (Nat × Published))
    (forwarding : List Nat) (node : Node) (label : Nat) : Except String (Option (String × List Demand)) := do
  let slots := origins.at label
  if escapesDeclaration slots known node then
    throw s!"a marked declaration escapes direct application at node {label}"
  let .invoke callee receiver args := node.expression | return none
  let some (.input root) := originOf slots callee | return none
  let some (_, producer) := known.find? (·.1 == root) | return none
  let forwarded ← producer.interface.demands.filterMapM (checkDemand r codes origins forwarding producer label receiver args)
  return some (producer.name,forwarded)

def check (f : FilePlans) (i fuel : Nat) (interfaces : List Published)
    (forwarding : List Nat := []) : Except String (List Demand) := do
  let some plan := f.plans[i]? | throw "no caller at that position"
  let .graph _ _ r ← (← plan).certify | throw "the callback caller needs an ordinary graph"
  let (codes, _, _) ← inferCodes r fuel
  let nodes := r.program.toArray
  let inputs := r.inputs.length
  let some origins := CallbackOrigins.infer r.program (r.claims.map (·.context.length)).toArray r.start inputs
    | throw "caller origin analysis did not settle"
  let sites := CallbackOrigins.namedSites nodes
  let origins := CallbackOrigins.nameable sites origins
  if !CallbackOrigins.checkNames nodes sites r.start inputs origins then
    throw "caller origin names failed their entry or incoming edge check"
  -- Module realization stores the declared siblings after the function's
  -- ordinary inputs, in this order. Local variable copies use checked origins.
  if r.siblings.length > inputs then throw "the module sibling layout exceeds the caller inputs"
  let known := knownSiblings inputs r.siblings interfaces
  if !checkMayInputs nodes origins r.start inputs (known.map Prod.fst) then
    throw "marked declaration origins failed their entry or incoming edge check"
  let sites ← r.program.zipIdx.filterMapM fun (node,label) => checkNode r codes origins known forwarding node label
  if !interfaces.all (fun own => sites.any (fun site => site.1 == own.name)) then
    throw "a marked declaration is used outside a resolved direct call"
  return (sites.foldl (fun acc site => site.2.reverse ++ acc) []).eraseDups

/-- Produce the interface after the directly used declarations have
published theirs. A forwarded callback acquires the projected obligation
in the same interface as this definition's own invocations. -/
def writeInterface (f : FilePlans) (i fuel : Nat) (dependencies : List Published := []) :
    Except String Published := do
  let some (fn, _, _) := f.fr.units[i]? | throw "no marked producer"
  let params := fn.params.zipIdx.filterMap fun (param, slot) => if param.inferPreserves then some slot else none
  if params.isEmpty then throw "no marked parameter"
  if (f.fr.group i).length != 1 || (f.fr.mentions i).contains fn.name then
    throw "recursive callback interface checking is unavailable"
  let own ← CallbackInferencePlan.infer f i fuel params
  let forwarded ← if dependencies.isEmpty then pure [] else check f i fuel dependencies params
  Published.validate ⟨fn.name, some fn.namePos, fn.params.head?.any (·.name == "this"),
    (fn.params.takeWhile (!·.rest)).length,
    ⟨(own.demands ++ forwarded).eraseDups⟩⟩

end Verification.SourceClaimJson.CallbackInterfaceCheck
