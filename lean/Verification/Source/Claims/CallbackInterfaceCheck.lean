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
  interface : CallbackInferencePlan.Interface

open Lean in
def Published.toJson (p : Published) : Json :=
  let demands := p.interface.demands.map fun d =>
    Json.mkObj [("parameter", Lean.toJson d.parameter),
      ("normal", EffectCodec.frameJ d.support.normal),
      ("exceptional", EffectCodec.frameJ d.support.exceptional), ("actualRoots", Lean.toJson d.actualRoots)]
  Json.mkObj [("name", Lean.toJson p.name), ("position", Lean.toJson p.position),
    ("receiver", Lean.toJson p.receiver), ("demands", Json.arr demands.toArray)]

open Lean in
def Published.ofJson (j : Json) : Except String Published := do
  fieldsExactly j ["name", "position", "receiver", "demands"]
  let name ← j.getObjValAs? String "name"
  let pos ← j.getObjValAs? (Option (Nat × Nat)) "position"
  let receiver ← j.getObjValAs? Bool "receiver"
  let demands ← (← jArr j "demands").mapM fun d => do
    fieldsExactly d ["parameter", "normal", "exceptional", "actualRoots"]
    let parameter ← d.getObjValAs? Nat "parameter"
    let normal ← EffectCodec.frameOf 32 (← jField d "normal")
    let exceptional ← EffectCodec.frameOf 32 (← jField d "exceptional")
    let actualRoots ← d.getObjValAs? (List (Option (Nat × List String))) "actualRoots"
    return (⟨parameter, ⟨normal, exceptional⟩, actualRoots⟩ : Demand)
  return ⟨name, pos, receiver, ⟨demands⟩⟩

private def originOf (slots : Slots) : Tm → Option Origin
  | .var slot => match slots[slot]? with | some [o] => some o | _ => none
  | _ => none

private def identity (inputCount : Nat) : Origin → Option Nat
  | .input i => some i
  | .allocated label => some (inputCount + label)
  | _ => none

private def predecessors (nodes : Array Node) : Array (List Nat) := Id.run do
  let mut out := Array.replicate nodes.size []
  for (node, label) in nodes.toList.zipIdx do
    for edge in CertificateProducer.successors node.continuation ++ node.handler.toList do
      out := out.modify edge.label (label :: ·)
  return out

private def observesOnly : Tm → Bool
  | .readAt _ (.var _) => true
  | .makeAt _ _ initializers => initializers.all Purity.pureTerm
  | term => Purity.pureTerm term

/-- A copied field path names the same value at the call if the intervening
steps do not write. Traverse predecessors from the call to the read and
stop at that read, including through copies and joins. -/
private def unchanged (nodes : Array Node) (preds : Array (List Nat)) (read use : Nat) : Bool := Id.run do
  let mut pending := preds.getD use []
  let mut seen : Std.HashSet Nat := {}
  while let label :: rest := pending do
    pending := rest
    if label == read || seen.contains label then continue
    if label == use || !(nodes[label]?.any (observesOnly ·.expression)) then return false
    let before := preds.getD label []
    if before.isEmpty then return false
    seen := seen.insert label
    pending := before ++ pending
  return true

private def operandAt (inputs : Nat) (nodes : Array Node) (origins : Table)
    (preds : Array (List Nat)) : Nat → Nat → Tm → Option (Nat × List String)
  | 0, _, _ => none
  | fuel + 1, use, t => do
    let origin ← originOf (origins.at use) t
    match origin with
    | .read label =>
      let node ← nodes[label]?
      let .readAt (.str key) receiver := node.expression | none
      if !unchanged nodes preds label use then none else
        let (root, path) ← operandAt inputs nodes origins preds fuel label receiver
        return (root, path ++ [key])
    | root => (identity inputs root).map (·, [])

private def closure {ι : Type} [DecidableEq ι] (codes : Array (CheckedCode ι))
    (nodes : Array Node) (origins : Table) (inputs : Nat) (slots : Slots)
    (callRoots : List (Option (Nat × List String))) (argument : Tm) : Option Callback := do
  let .allocated label ← originOf slots argument | none
  let node ← nodes[label]?
  let .makeAt (.graph arity exprs conts start captures _ _ _) _ _ := node.expression | none
  let rows := codes.filter fun c =>
    c.entry.arity == arity && c.entry.start == start && c.entry.exprs == exprs && c.entry.conts == conts &&
      captures.length == c.entry.captures.length
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

private def separation (inputs : Nat) (slots : Slots) : SepEvidence :=
  let roots := (slots.toList.flatten.filterMap (identity inputs)).eraseDups
  { facts := roots.flatMap fun a => roots.filterMap fun b =>
      if a != b && (inputs ≤ a || inputs ≤ b) then some (.spines (a, []) (b, [])) else none }

/-- Check each caller supplying a literal closure using its inferred effect
and the alias information at the lowered call. -/
def check (f : FilePlans) (i fuel : Nat) (interfaces : List Published)
    (forwarding : List Nat := []) : Except String (List Demand) := do
  let some plan := f.plans[i]? | throw "no caller at that position"
  let .graph _ _ r ← (← plan).certify | throw "the callback caller needs an ordinary graph"
  let (codes, _, _) ← inferCodes r fuel
  let nodes := r.program.toArray
  let inputs := r.inputs.length
  let preds := predecessors nodes
  let some origins := CallbackOrigins.infer r.program (r.claims.map (·.context.length)).toArray r.start inputs
    | throw "caller origin analysis did not settle"
  -- Bind the callee's immutable declaration identity to a root of this
  -- graph's entry, then recognize copies of that root at applications.
  let known := (r.sourceMap.zipIdx.flatMap fun (entry, label) =>
    let slots := origins.at label
    entry.toList.flatMap fun e => e.context.zipIdx.filterMap fun (d, slot) => do
      let iface ← interfaces.find? fun own => d.name == own.name && (own.position.all fun pos => d.span == some pos)
      let some [.input root] := slots[slot]? | none
      return (root, iface)).foldl (fun seen (root, iface) =>
        if seen.any (·.1 == root) then seen else (root, iface) :: seen) []
  let mut calls := []
  let mut forwarded := []
  for (node, label) in r.program.zipIdx do
    let slots := origins.at label
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
    if reads.any referenced || (reads.isNone && !known.isEmpty) then
      throw s!"a marked declaration escapes direct application at node {label}"
    let .invoke callee receiver args := node.expression | continue
    let some (.input root) := originOf slots callee | continue
    let some (_, producer) := known.find? (·.1 == root) | continue
    let frame := if producer.receiver then receiver :: args else args
    let toCaller := fun position => (frame[position]?).bind (operandAt inputs nodes origins preds (nodes.size + 1) label)
    for demand in producer.interface.demands do
      if demand.support.normal.isEmpty && demand.support.exceptional.isEmpty then continue
      let absent : Bool := match frame[demand.parameter]? with
        | none | some .undef => true
        | some (.var slot) => ((r.claims[label]?).bind (·.context[slot]?)).any fun ty =>
          PositiveRules.expand (RequestJson.graph r.toRequest) ty == [.undef]
        | _ => false
      if absent then continue
      if let some (.input position) := frame[demand.parameter]?.bind (originOf slots) then
        if forwarding.contains position then
          let some rebased := demand.forward position (fun root => do
            let (input, path) ← toCaller root
            if input < inputs then some (input, path) else none)
            | throw s!"the forwarded requirement at node {label} cannot name a caller input"
          forwarded := rebased :: forwarded
          continue
      let actuals := demand.actualRoots.map fun source => do
        let (slot, path) ← source
        let (root, outerPath) ← toCaller slot
        return (root, outerPath ++ path)
      let callbacks := fun parameter => (frame[parameter]?).bind (closure codes nodes origins inputs slots actuals)
      if !demand.check toCaller callbacks (separation inputs slots) then
        throw s!"callback argument {demand.parameter + 1} at call of {producer.name} (node {label}) fails its inferred preservation requirement"
    calls := producer.name :: calls
  if !interfaces.all (fun own => calls.contains own.name) then
    throw "a marked declaration is used outside a resolved direct call"
  return forwarded.eraseDups

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
  return ⟨fn.name, some fn.namePos, fn.params.head?.any (·.name == "this"),
    ⟨(own.demands ++ forwarded).eraseDups⟩⟩

end Verification.SourceClaimJson.CallbackInterfaceCheck
