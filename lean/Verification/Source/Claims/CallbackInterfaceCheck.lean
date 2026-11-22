import Verification.Source.Claims.CallbackNameHistory
import Verification.Source.Claims.CallbackCodeRowsSound
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

def Published.referencesFixedParameters (p : Published) : Bool :=
  p.interface.demands.all fun d =>
    d.parameter < p.formals &&
      (d.support.normal ++ d.support.exceptional).all (fun e => publicRegion p.formals e.1) &&
      d.actualRoots.all (fun root => root.all (fun path => path.1 < p.formals))

def Published.validate (p : Published) : Except String Published := do
  if !p.referencesFixedParameters then
    throw (CallbackPreservation.scopeRefusal "referencesFixedParameters"
      s!"callback requirement for {p.name} refers outside its fixed parameters")
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
    throw (CallbackPreservation.scopeRefusal "fixedDirectApplication"
      s!"a spread obscures callback argument {demand.parameter + 1} at call of {producer.name} (node {label})")
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

/-- Check every use and the incoming-edge evidence on an already recovered
caller origin table. The proof-producing caller uses the same decision and
keeps the code and origin tables for its subsequent application checks. -/
@[nospecialize] def checkUses {σ ι : Type} [Labels ι] [StoreView σ ι]
    (r : SourceRequest σ ι) (codes : Array (CheckedCode ι)) (origins : Table)
    (interfaces : List Published) (forwarding : List Nat) : Except String (List Demand) := do
  let nodes := r.program.toArray
  let inputs := r.inputs.length
  let sites := CallbackOrigins.namedSites nodes
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

def check (f : FilePlans) (i fuel : Nat) (interfaces : List Published)
    (forwarding : List Nat := []) : Except String (List Demand) := do
  let some plan := f.plans[i]? | throw "no caller at that position"
  let .graph _ _ r ← (← plan).certify
  let (codes, _, _) ← inferCodes r fuel
  let nodes := r.program.toArray
  let inputs := r.inputs.length
  let some origins := CallbackOrigins.infer r.program (r.claims.map (·.context.length)).toArray r.start inputs
    | throw "caller origin analysis did not settle"
  checkUses r codes (CallbackOrigins.nameable (CallbackOrigins.namedSites nodes) origins) interfaces forwarding

def nonrecursiveDeclaration (front : Front) (member : Nat) (name : String) : Bool :=
  (front.group member).length == 1 && !(front.mentions member).contains name

/-- Produce the interface after the directly used declarations have
published theirs. A forwarded callback acquires the projected obligation
in the same interface as this definition's own invocations. -/
def writeInterface (f : FilePlans) (i fuel : Nat) (dependencies : List Published := []) :
    Except String Published := do
  let some (fn, _, _) := f.fr.units[i]? | throw "no marked producer"
  let params := fn.params.zipIdx.filterMap fun (param, slot) => if param.inferPreserves then some slot else none
  if params.isEmpty then throw "no marked parameter"
  if !nonrecursiveDeclaration f.fr i fn.name then
    throw (CallbackPreservation.scopeRefusal "nonrecursiveDeclaration" "recursive callback interface checking is unavailable")
  let own ← CallbackInferencePlan.infer f i fuel params
  let forwarded ← if dependencies.isEmpty then pure [] else check f i fuel dependencies params
  Published.validate ⟨fn.name, some fn.namePos, fn.params.head?.any (·.name == "this"),
    (fn.params.takeWhile (!·.rest)).length,
    ⟨(own.demands ++ forwarded).eraseDups⟩⟩

end Verification.SourceClaimJson.CallbackInterfaceCheck

namespace Verification.SourceClaimJson.CallbackInterfaceCheck
open CallbackPreservation CallbackOrigins Footprints CallEffects

/-- Interpret synthetic operand names by the values bound at producer entry.
Those values remain available even if the caller's heap paths have changed. -/
def operandEnv (cutoff : Nat) (named actual : Env) : Env := fun i =>
  if i < cutoff then named i else actual (i - cutoff)

theorem operandEnv_rootsOk {n} {W : WorldT n} {named actual : Env} (cutoff : Nat)
    (hn : RootsOk W named) (ha : RootsOk W actual) :
    RootsOk W (operandEnv cutoff named actual) := by
  intro i
  unfold operandEnv
  split
  · exact hn _
  · exact ha _

/-- The existing input and allocation names are below the synthetic range
and denote the evaluated operands to which the origin analysis assigns them.
Field reads require no hypothesis about the value now stored in the heap. -/
def NamedOperands (inputs nodes : Nat) (slots : Slots) (frame : List Tm) (named actual : Env) : Prop :=
  ∀ i t o j, frame[i]? = some t → originOf slots t = some o → identity inputs o = some j →
    j < inputs + nodes ∧ named j = actual i

theorem argumentRoots_realizes {inputs nodes slots frame named actual}
    (origins : NamedOperands inputs nodes slots frame named actual) (h : Heap) :
    RealizesRoots (argumentRoots inputs nodes slots frame) actual
      (operandEnv (inputs + nodes) named actual) h := by
  intro i j p binding
  obtain ⟨t,ht,operand⟩ := Option.bind_eq_some_iff.mp binding
  unfold operandRoot at operand
  cases ho : originOf slots t with
  | none => simp [ho] at operand
  | some o =>
    cases o with
    | read l =>
      simp [ho] at operand
      obtain ⟨rfl,rfl⟩ := operand
      simp [HeapKnowledge.readPath, operandEnv, show ¬ inputs + nodes + i < inputs + nodes by omega]
    | input l | allocated l =>
      all_goals
        simp [ho, identity] at operand
        obtain ⟨rfl,rfl⟩ := operand
        obtain ⟨below, eqv⟩ := origins i t _ _ ht ho rfl
        simp [HeapKnowledge.readPath, operandEnv, below, eqv]
    | other => simp [ho, identity] at operand

/-- Apply the executable demand check at callback entry even if heap fields
used to obtain producer arguments have since been reassigned. -/
theorem check_arguments_supported {inputs nodes slots frame named actual}
    {d : Demand} {callbacks : Nat → Option Callback} {cb : Callback} {ev : SepEvidence}
    {closure : Env} {before after : Heap} {n : Nat} {W : WorldT n} {μ} (exit : Completion)
    (accepted : d.check (argumentRoots inputs nodes slots frame) callbacks ev = true)
    (lookup : callbacks d.parameter = some cb)
    (origins : NamedOperands inputs nodes slots frame named actual)
    (actualsOK : ∀ i j, cb.actuals i = some j → operandEnv (inputs + nodes) named actual j = closure i)
    (evidenceOK : ev.Holds μ (operandEnv (inputs + nodes) named actual) before)
    (heapOK : HeapOk n W before) (namedOK : RootsOk W named) (argsOK : RootsOk W actual)
    (effect : Post (cb.effects.get exit) closure before after) :
    Supported (d.support.get exit) actual before after :=
  d.check_supported exit accepted lookup (argumentRoots_realizes origins before) actualsOK
    evidenceOK heapOK (operandEnv_rootsOk _ namedOK argsOK) effect

end Verification.SourceClaimJson.CallbackInterfaceCheck

namespace Verification.SourceClaimJson.CallbackInterfaceCheck
open CallbackPreservation CallbackOrigins CallbackEffectInference Footprints CallEffects ControlFlow ProgramTyping

private theorem rowFold_mem {ι : Type} (rows : List (CheckedCode ι)) (acc : Exits Footprint)
    (exit : Completion) (e : Region × Change)
    (h : e ∈ acc.get exit ∨ ∃ row ∈ rows, e ∈ (row.summary.get exit).getD []) :
    e ∈ (rows.foldl (fun (a : Exits Footprint) code =>
      ⟨(a.normal ++ code.summary.normal.getD []).eraseDups,
       (a.exceptional ++ code.summary.exceptional.getD []).eraseDups⟩) acc).get exit := by
  induction rows generalizing acc with
  | nil => simpa using h
  | cons head tail ih =>
    apply ih
    rcases h with prev | ⟨row, member, included⟩
    · left
      cases exit <;> simpa [Exits.get] using Or.inl (b := e ∈ _) prev
    · rcases List.mem_cons.mp member with rfl | rest
      · left
        cases exit <;> simpa [Exits.get] using Or.inr (a := e ∈ _) included
      · exact .inr ⟨row, rest, included⟩

private def literalActuals (inputs arity : Nat) (rest : Bool) (caps : List Tm) (slots : Slots)
    (roots : List (Option (Nat × List String))) (slot : Nat) : Option Nat := do
  let restSlots := if rest then 1 else 0
  if slot < restSlots then none
  else if slot < arity + (if rest then 2 else 1) then
    let some (root, []) := roots[slot - restSlots]?.join | none
    some root
  else
    let cap ← caps[slot - (arity + (if rest then 2 else 1))]?
    originOf slots cap >>= identity inputs

/-- The effect of every checked row matching this literal is included in
the exact callback returned by the source checker, independently on each exit. -/
private theorem closure_row_spec {ι : Type} [DecidableEq ι] {codes : Array (CheckedCode ι)}
    {nodes : Array Node} {origins inputs slots callRoots argument label}
    {node : Node} {row : CheckedCode ι} {captures kind component fields values}
    {cb : Callback} (picked : closure codes nodes origins inputs slots callRoots argument = some cb)
    (site : originOf slots argument = some (.allocated label)) (atSite : nodes[label]? = some node)
    (literal : node.expression = .makeAt (.graph row.entry.arity row.entry.exprs row.entry.conts
      row.entry.start captures kind row.entry.spine.isSome component) fields values)
    (width : captures.length = row.entry.captures.length) (checked : row ∈ codes)
    (exit : Completion) :
    (∀ e ∈ (row.summary.get exit).getD [], e ∈ cb.effects.get exit) ∧
    cb.actuals = literalActuals inputs row.entry.arity row.entry.spine.isSome captures (origins.at label) callRoots := by
  unfold closure at picked
  simp only [site, atSite, literal, bind, Option.bind] at picked
  generalize hr : Array.filter _ codes = rows at picked
  have inRows : row ∈ rows := by
    subst rows
    exact Array.mem_filter.mpr ⟨checked, by simp [width]⟩
  cases head : rows[0]? with
  | none => simp [head] at picked
  | some first =>
    simp only [head, pure, Option.some.injEq] at picked
    subst cb
    constructor
    · intro e he
      rw [← Array.foldl_toList]
      exact rowFold_mem _ _ exit e (.inr ⟨row,by simpa using inRows,he⟩)
    · have hm : first ∈ rows := Array.mem_of_getElem? head
      rw [← hr] at hm
      have rest := (Bool.and_eq_true_iff.mp (Array.mem_filter.mp hm).2).2
      have same : first.entry.spine.isSome = row.entry.spine.isSome := by simpa using rest
      funext i
      cases hf : first.entry.spine <;> simp [literalActuals, ← same, hf, frameOffset, Option.bind]

private theorem envOf_tail {pre tail : List Tm} {i} (h : pre.length ≤ i) :
    envOf (pre ++ tail) .nul i = envOf tail .nul (i-pre.length) := by
  simp only [envOf,List.getD_eq_getElem?_getD,List.getElem?_append_right h]

private theorem literalActuals_sound {inputs arity : Nat} {rest : Bool} {caps : List Tm} {slots : Slots}
    {roots : List (Option (Nat × List String))} {dst : Env} {recv self : Tm} {args : List Tm}
    {pre : List Tm} {allocation : Env}
    (layout : pre.length = (if rest then 1 else 0))
    (ordinary : ∀ p j, roots[p]?.join = some (j, []) → dst j = callEnv recv args p)
    (capture : ∀ (k : Nat) t o j, caps[k]? = some t → originOf slots t = some o →
      identity inputs o = some j → dst j = instantiate 0 allocation t) :
    ∀ i j, literalActuals inputs arity rest caps slots roots i = some j →
      dst j = envOf (pre ++ (recv :: CallArguments.parameters arity args ++
        (caps.map (instantiate 0 allocation) ++ [self]))) .nul i := by
  intro i j h
  unfold literalActuals at h
  dsimp only at h
  by_cases above : i < (if rest then 1 else 0)
  · simp [above] at h
  · rw [ite_eq_right above] at h
    have past : pre.length ≤ i := by omega
    by_cases fixed : i < arity + (if rest then 2 else 1)
    · rw [ite_eq_left fixed] at h
      split at h <;> try contradiction
      rename_i p atRoot
      cases h
      have range : i - pre.length ≤ arity := by cases rest <;> simp_all <;> omega
      rw [envOf_tail past, ← callEnv_frame range, layout]
      exact ordinary _ _ atRoot
    · rw [ite_eq_right fixed] at h
      obtain ⟨t,atCap,more⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨o,origin,name⟩ := Option.bind_eq_some_iff.mp more
      have n := capture _ t o j atCap origin name
      rw [n]
      let prefixValues := pre ++ (recv :: CallArguments.parameters arity args)
      have len : prefixValues.length = arity + (if rest then 2 else 1) := by
        cases rest <;> simp_all [prefixValues,Effect.parameters_length] <;> omega
      have pastCaps : prefixValues.length ≤ i := by omega
      change _ = envOf (pre ++ ((recv :: CallArguments.parameters arity args) ++ _)) .nul i
      rw [← List.append_assoc]
      change _ = envOf (prefixValues ++ _) .nul i
      rw [envOf_tail pastCaps,len]
      have hi := (List.getElem?_eq_some_iff.mp atCap).1
      rw [envOf,List.getD_eq_getElem?_getD,List.getElem?_append_left (by simpa using hi),
        List.getElem?_map,atCap]
      rfl

/-- Entry slots for the literal's graph run. The optional collected rest
value precedes the receiver. Captures are instantiated at allocation. -/
def literalEntry (pre : List Tm) (recv : Tm) (arity : Nat) (args caps : List Tm)
    (allocation : Env) (self : Tm) : Env :=
  envOf (pre ++ (recv :: CallArguments.parameters arity args ++
    (caps.map (instantiate 0 allocation) ++ [self]))) .nul

/-- The invocation argument map used by the caller's source check. -/
def invocationArguments (d : Demand) (toCaller : RootMap) : List (Option (Nat × List String)) :=
  d.actualRoots.map fun source => do
    let (slot, path) ← source
    let (root, outerPath) ← toCaller slot
    return (root, outerPath ++ path)

private theorem invocationArguments_sound {d : Demand} {toCaller : RootMap} {actual dst : Env}
    {before : Heap} {recv : Tm} {args : List Tm}
    (rootsOK : RealizesRoots toCaller actual dst before)
    (invocation : ∀ p x, d.actualRoots[p]? = some (some (x, [])) → actual x = callEnv recv args p)
    {p j} (maps : (invocationArguments d toCaller)[p]?.join = some (j, [])) :
    dst j = callEnv recv args p := by
  cases hs : d.actualRoots[p]? with
  | none => simp [invocationArguments,List.getElem?_map,hs] at maps
  | some source =>
    cases source with
    | none => simp [invocationArguments,List.getElem?_map,hs] at maps
    | some src =>
      obtain ⟨x,path⟩ := src
      cases ht : toCaller x with
      | none => simp [invocationArguments,List.getElem?_map,hs,ht] at maps
      | some out =>
        obtain ⟨y,outer⟩ := out
        simp [invocationArguments,List.getElem?_map,hs,ht] at maps
        obtain ⟨rfl,rfl,rfl⟩ := maps
        exact (Option.some.inj (rootsOK x _ [] ht)).trans (invocation _ _ hs)

/-- For a literal callback with a matching inferred row, the completed graph
run itself supplies the effect required by the demand checker. The executable
row join covers both exits and the formal slot substitution agrees with the
actual closure frame, including the captures from its allocation environment. -/
theorem checked_literal_execution_supported {ι : Type} [DecidableEq ι]
    {G : PositiveGraphs.NormalGraph ι} {q : RequestJson.CodeRequest ι}
    {records : Array SinglePass.VisitRecord} {summary : Summary} {codes : Array (CheckedCode ι)}
    {nodes : Array Node} {origins : Table} {inputs : Nat} {slots : Slots} {frame : List Tm}
    {d : Demand} {ev : SepEvidence}
    {argument : Tm} {label : Nat} {node : Node} {caps : List Tm} {kind component fields values}
    {named actual allocation : Env} {pre : List Tm} {recv self : Tm} {args : List Tm}
    {before after : Heap} {n : Nat} {W : WorldT n} {μ} {steps state}
    (exit : Completion) (v : Val)
    (accept : d.check (argumentRoots inputs nodes.size slots frame)
      (fun p => frame[p]?.bind (closure codes nodes origins inputs slots
        (invocationArguments d (argumentRoots inputs nodes.size slots frame)))) ev = true)
    (atArg : frame[d.parameter]? = some argument)
    (site : originOf slots argument = some (.allocated label)) (atSite : nodes[label]? = some node)
    (literal : node.expression = .makeAt (.graph q.entry.arity q.entry.exprs q.entry.conts
      q.entry.start caps kind q.entry.spine.isSome component) fields values)
    (width : caps.length = q.entry.captures.length)
    (member : (⟨q.entry,summary⟩ : CheckedCode ι) ∈ codes)
    (checked : inferChecked G q records = .ok summary)
    (layout : pre.length = (if q.entry.spine.isSome then 1 else 0))
    (arguments : NamedOperands inputs nodes.size slots frame named actual)
    (captures : NamedOperands inputs nodes.size (origins.at label) caps named
      (fun k => instantiate 0 allocation (caps.getD k .undef)))
    (invocation : ∀ p x, d.actualRoots[p]? = some (some (x, [])) → actual x = callEnv recv args p)
    (evidenceOK : ev.Holds μ (operandEnv (inputs + nodes.size) named actual) before)
    (heapOK : HeapOk n W before) (namedOK : RootsOk W named) (argsOK : RootsOk W actual)
    (visits : RecordedExitSound G q records (literalEntry pre recv q.entry.arity args caps allocation self) before)
    (run : Execution (GraphCode.program q.entry.exprs q.entry.conts) steps before
      (.at q.entry.start (literalEntry pre recv q.entry.arity args caps allocation self)) after state)
    (done : state = (match exit with | .normal => .done v | .exceptional => .raised v)) :
    Supported (d.support.get exit) actual before after := by
  let roots := invocationArguments d (argumentRoots inputs nodes.size slots frame)
  change d.check _ (fun p => frame[p]?.bind (closure codes nodes origins inputs slots roots)) ev = true at accept
  cases picked : closure codes nodes origins inputs slots roots argument with
  | none => simp [Demand.check,atArg,picked] at accept
  | some cb =>
    have lookup : frame[d.parameter]?.bind (closure codes nodes origins inputs slots roots) = some cb := by
      simp [atArg,picked]
    obtain ⟨includes,substitution⟩ := closure_row_spec (row := ⟨q.entry,summary⟩)
      picked site atSite literal width member exit
    obtain ⟨bound,found,post⟩ := inferChecked_execution checked visits run exit v done
    apply check_arguments_supported exit accept lookup arguments _ evidenceOK heapOK namedOK argsOK
      (post.mono (cl := fun _ _ => none) (Footprint.le_of_subset ?_) (by intro _ _ _ _ miss; contradiction))
    · rw [substitution]
      apply literalActuals_sound layout (fun _ _ => invocationArguments_sound (argumentRoots_realizes arguments before) invocation)
      intro k t o j ht ho hj
      obtain ⟨below, denotation⟩ := captures k t o j ht ho hj
      simpa [operandEnv,below,List.getD_eq_getElem?_getD,ht] using denotation
    · intro e he
      exact includes e (by simpa [found] using he)

/-- The caller's checked separation demand holds for the actual closure row
returned by the source inference loop at the completed invocation. -/
theorem inferCodes_literal_execution_supported {τ ι : Type} [LabelStore.Labels ι] [LabelStore.StoreView τ ι]
    {request : SourceElaboration.SourceRequest τ ι} {fuel known final} {q : RequestJson.CodeRequest ι}
    {summary : Summary} {codes : Array (CheckedCode ι)}
    {nodes : Array Node} {origins : Table} {inputs : Nat} {slots : Slots} {frame : List Tm}
    {d : Demand} {ev : SepEvidence}
    {argument : Tm} {label : Nat} {node : Node} {caps : List Tm} {kind component fields values}
    {named actual allocation : Env} {pre : List Tm} {recv self : Tm} {args : List Tm}
    {before after : Heap} {n : Nat} {W : WorldT n} {μ} {steps state}
    (exit : Completion) (v : Val)
    (accept : d.check (argumentRoots inputs nodes.size slots frame)
      (fun p => frame[p]?.bind (closure codes nodes origins inputs slots
        (invocationArguments d (argumentRoots inputs nodes.size slots frame)))) ev = true)
    (atArg : frame[d.parameter]? = some argument)
    (site : originOf slots argument = some (.allocated label)) (atSite : nodes[label]? = some node)
    (literal : node.expression = .makeAt (.graph q.entry.arity q.entry.exprs q.entry.conts
      q.entry.start caps kind q.entry.spine.isSome component) fields values)
    (width : caps.length = q.entry.captures.length)
    (member : (⟨q.entry,summary⟩ : CheckedCode ι) ∈ codes)
    (checked : inferCodes request fuel = .ok (codes,known,final))
    (layout : pre.length = (if q.entry.spine.isSome then 1 else 0))
    (arguments : NamedOperands inputs nodes.size slots frame named actual)
    (captures : NamedOperands inputs nodes.size (origins.at label) caps named
      (fun k => instantiate 0 allocation (caps.getD k .undef)))
    (invocation : ∀ p x, d.actualRoots[p]? = some (some (x, [])) → actual x = callEnv recv args p)
    (evidenceOK : ev.Holds μ (operandEnv (inputs + nodes.size) named actual) before)
    (heapOK : HeapOk n W before) (namedOK : RootsOk W named) (argsOK : RootsOk W actual)
    (world : WorldAdm W) (room : steps ≤ n) (positive : 0 < n)
    (entryTyped : EnvOk (RequestJson.graph request.toRequest)
      (codeFrame q.entry.arity q.entry.row q.entry.captures q.entry.spine)
      (literalEntry pre recv q.entry.arity args caps allocation self) n W)
    (entryRefs : RootsOk W (literalEntry pre recv q.entry.arity args caps allocation self))
    (entryIndices : HeapKnowledge.IndexHolds ⟨literalEntry pre recv q.entry.arity args caps allocation self,before⟩
      (GraphCode.codeEntryIndices q.entry) (literalEntry pre recv q.entry.arity args caps allocation self) before)
    (run : Execution (GraphCode.program q.entry.exprs q.entry.conts) steps before
      (.at q.entry.start (literalEntry pre recv q.entry.arity args caps allocation self)) after state)
    (done : state = (match exit with | .normal => .done v | .exceptional => .raised v)) :
    Supported (d.support.get exit) actual before after := by
  let roots := invocationArguments d (argumentRoots inputs nodes.size slots frame)
  change d.check _ (fun p => frame[p]?.bind (closure codes nodes origins inputs slots roots)) ev = true at accept
  cases picked : closure codes nodes origins inputs slots roots argument with
  | none => simp [Demand.check,atArg,picked] at accept
  | some cb =>
    have lookup : frame[d.parameter]?.bind (closure codes nodes origins inputs slots roots) = some cb := by
      simp [atArg,picked]
    obtain ⟨includes,substitution⟩ := closure_row_spec (row := ⟨q.entry,summary⟩)
      picked site atSite literal width member exit
    obtain ⟨bound,found,post⟩ := inferCodes_rows_sound checked _ member
      ⟨n,W,before,positive,world,heapOK⟩ _ entryTyped entryRefs entryIndices room run exit v done
    apply check_arguments_supported exit accept lookup arguments _ evidenceOK heapOK namedOK argsOK
      (post.mono (cl := fun _ _ => none) (Footprint.le_of_subset ?_) (by intro _ _ _ _ miss; contradiction))
    · rw [substitution]
      apply literalActuals_sound layout (fun _ _ => invocationArguments_sound (argumentRoots_realizes arguments before) invocation)
      intro k t o j ht ho hj
      obtain ⟨below, denotation⟩ := captures k t o j ht ho hj
      simpa [operandEnv,below,List.getD_eq_getElem?_getD,ht] using denotation
    · intro e he
      exact includes e (by simpa [found] using he)

end Verification.SourceClaimJson.CallbackInterfaceCheck

namespace Verification.SourceClaimJson.CallbackInterfaceCheck
open CallbackOrigins ControlFlow

theorem namedOrigin_slot {slots : Slots} {t o} (found : originOf slots t = some o) :
    ∃ i, t = .var i ∧ slots[i]? = some [o] := by
  cases t <;> try contradiction
  rename_i i
  change (match slots[i]? with | some [v] => some v | _ => none) = some o at found
  split at found <;> try contradiction
  cases found
  exact ⟨i,rfl,by assumption⟩

private theorem historyNamedOperands {P table entry inputs history slots ρ}
    (valid : historyHolds P table entry inputs history) (holds : slotsHold history entry inputs slots ρ)
    (frame : List Tm) :
    NamedOperands inputs P.length slots frame (historyEnv entry inputs history)
      (fun i => instantiate 0 ρ (frame.getD i .undef)) := by
  intro i t o j atI hO hJ
  obtain ⟨slot,rfl,atSlot⟩ := namedOrigin_slot hO
  cases o with
  | input p =>
    cases hJ
    obtain ⟨⟨bound,eq⟩,_⟩ := holds slot (.input j) (by simp [namedAt,atSlot])
    exact ⟨by omega,by simpa [historyEnv,bound,List.getD_eq_getElem?_getD,atI,instantiate] using eq⟩
  | allocated p =>
    cases hJ
    obtain ⟨⟨b,hb,eq⟩,_⟩ := holds slot (.allocated p) (by simp [namedAt,atSlot])
    obtain ⟨same,born,_⟩ := valid p b hb
    have below := (List.getElem?_eq_some_iff.mp born.1).1
    rw [same] at below
    refine ⟨by omega,?_⟩
    simpa [historyEnv,List.getD_eq_getElem?_getD,atI,instantiate,hb,show ¬ inputs+p < inputs by omega] using eq
  | other | read => contradiction

/-- A reached caller's named arguments and the literal's captures use the
same valuation, including captures no direct operand currently holds. -/
theorem namedArguments_and_captureFrame {P table entry inputs l ρ h}
    (reached : atHistory P table entry inputs mark l ρ h) {frame : List Tm} {arg site}
    (origin : originOf (table.at l) arg = some (.allocated site)) :
    ∃ history b, historyHolds P table entry inputs history ∧ history site = some b ∧ b.Valid P ∧
      instantiate 0 ρ arg = b.value ∧
      NamedOperands inputs P.length (table.at l) frame (historyEnv entry inputs history)
        (fun i => instantiate 0 ρ (frame.getD i .undef)) ∧
      ∀ caps, NamedOperands inputs P.length (table.at site) caps (historyEnv entry inputs history)
        (fun i => instantiate 0 b.allocation (caps.getD i .undef)) := by
  obtain ⟨hist,valid,_,_,_,held⟩ := reached
  obtain ⟨i,rfl,hs⟩ := namedOrigin_slot origin
  obtain ⟨⟨b,hb,val⟩,_⟩ := held i (.allocated site) (by simp [namedAt,hs])
  exact ⟨hist,b,valid,hb,(valid site b hb).2.1,by simpa [instantiate] using val.symm,
    historyNamedOperands valid held frame,historyNamedOperands valid (valid site b hb).2.2⟩

end Verification.SourceClaimJson.CallbackInterfaceCheck

namespace Verification.SourceClaimJson.CallbackInterfaceCheck
open CallbackOrigins Footprints

private def usedName (inputs : Nat) (slots : Slots) (frame : List Tm) (j : Nat) : Prop :=
  ∃ (i : Nat) (t : Tm) (o : Origin), frame[i]? = some t ∧ originOf slots t = some o ∧ identity inputs o = some j

private theorem sparseNames {inputs nodes slots frame named actual kept}
    [DecidablePred kept] (names : NamedOperands inputs nodes slots frame named actual)
    (live : ∀ j, usedName inputs slots frame j → kept j) :
    NamedOperands inputs nodes slots frame (fun j => if kept j then named j else .undef) actual := by
  intro i t o j ht ho hj
  obtain ⟨lo,eq⟩ := names i t o j ht ho hj
  exact ⟨lo,by simp [live j ⟨i,t,o,ht,ho,hj⟩,eq]⟩

private theorem sparseRoots {inputs nodes slots capsSlots frame caps named actual captured n} {W : WorldT n}
    (args : NamedOperands inputs nodes slots frame named actual) (cap : NamedOperands inputs nodes capsSlots caps named captured)
    (argsOK : RootsOk W actual) (capOK : RootsOk W captured) :
    let kept := fun j => usedName inputs slots frame j ∨ usedName inputs capsSlots caps j
    let sparse := fun j => @ite _ (kept j) (Classical.propDecidable _) (named j) .undef
    RootsOk W sparse := by
  intro kept sparse j
  classical
  by_cases alive : kept j
  · have eq : sparse j = named j := ite_eq_left alive
    rw [eq]
    rcases alive with ⟨i,t,o,ht,ho,hj⟩ | ⟨i,t,o,ht,ho,hj⟩
    · rw [(args i t o j ht ho hj).2]; exact argsOK i
    · rw [(cap i t o j ht ho hj).2]; exact capOK i
  · have eq : sparse j = .undef := ite_eq_right alive
    rw [eq]
    intro r hr; contradiction

private theorem callerSeparation {P table entry inputs history mark current}
    (valid : historyHolds P table entry inputs history) (time : Chronology history mark current)
    (initial : ∀ i < inputs, ∀ l, spineOf (entry i) = some l → l < mark)
    (kept : Nat → Prop) [DecidablePred kept] (slots : Slots) (actual : Env) (h : Heap) :
    (separation inputs P.length slots).Holds (fun _ => 0)
      (operandEnv (inputs+P.length) (fun j => if kept j then historyEnv entry inputs history j else .undef) actual) h := by
  refine ⟨by intro _ _ _ _ impossible; contradiction,
    ⟨by intros; contradiction,by intros; contradiction⟩,fun _ _ _ => Nat.le_refl _,
    by intro _ impossible; contradiction,?_⟩
  intro fact included
  simp only [separation,List.mem_flatMap,List.mem_filterMap,List.mem_eraseDups,List.mem_filter,
    decide_eq_true_eq] at included
  obtain ⟨a,⟨_,smallA⟩,b,⟨_,smallB⟩,select⟩ := included
  split at select <;> try contradiction
  rename_i apart
  cases select
  intro u w l hu hw ua wb
  simp only [HeapKnowledge.readPath,Option.some.injEq,operandEnv,smallA,smallB,ite_true] at hu hw
  subst u
  subst w
  split at ua <;> try contradiction
  split at wb <;> try contradiction
  simp only [Bool.and_eq_true,bne_iff_ne,Bool.or_eq_true,decide_eq_true_eq] at apart
  exact historyNamesApart valid time initial apart.1 apart.2 ua wb

end Verification.SourceClaimJson.CallbackInterfaceCheck

namespace Verification.SourceClaimJson.CallbackInterfaceCheck
open CallbackOrigins CallbackPreservation CallbackEffectInference ControlFlow Footprints CallEffects ProgramTyping

private theorem captureRoots {pre recv arity args caps allocation self n} {W : WorldT n}
    (refs : RootsOk W (literalEntry pre recv arity args caps allocation self)) :
    RootsOk W (fun i => instantiate 0 allocation (caps.getD i .undef)) := by
  intro i
  cases ht : caps[i]? with
  | none =>
    simp only [List.getD_eq_getElem?_getD,ht,Option.getD_none,instantiate]
    intro _ hx; contradiction
  | some t =>
    simp only [List.getD_eq_getElem?_getD,ht,Option.getD_some]
    let prefixValues := pre ++ (recv :: CallArguments.parameters arity args)
    have look := refs (prefixValues.length+i)
    have index : i < caps.length := (List.getElem?_eq_some_iff.mp ht).1
    change RefsOk W (envOf (pre ++ ((recv :: CallArguments.parameters arity args) ++ _)) .nul _) at look
    rw [← List.append_assoc] at look
    change RefsOk W (envOf (prefixValues ++ _) .nul _) at look
    rw [envOf_tail (by omega : prefixValues.length ≤ prefixValues.length+i)] at look
    simpa [envOf,List.getD_eq_getElem?_getD,List.getElem?_append_left (by simpa using index :
      i < (caps.map (instantiate 0 allocation)).length),List.getElem?_map,ht] using look

/-- At a caller node reached from a checked entry, the executable separation
and names of a supplied literal, including its captures, come from one
allocation history. A completed invocation of the matching code row then
preserves the support demanded by the producer on the actual exit. -/
theorem checkedCaller_literal_supported {τ ι : Type} [LabelStore.Labels ι] [LabelStore.StoreView τ ι]
    {request : SourceElaboration.SourceRequest τ ι} {fuel codes known final}
    {q : RequestJson.CodeRequest ι} {summary : Summary} {P : Program} {table : Table}
    {inputs start entry l ρ h₀ h k n₀} {W₀ : WorldT n₀}
    (checkNames : CallbackOrigins.checkNames P.toArray (namedSites P.toArray) start inputs table = true)
    (callerValues : ∀ i < inputs, isVal (entry i) = true) (callerRoots : RootsOk W₀ entry) (callerHeap : HeapOk n₀ W₀ h₀)
    (reached : Execution P k h₀ (.at start entry) h (.at l ρ))
    {frame : List Tm} {d : Demand} {argument : Tm} {site : Nat} {node : Node}
    {caps kind component fields vals} {actual : Env} {pre : List Tm} {recv self : Tm} {args : List Tm}
    {before after : Heap} {n : Nat} {W : WorldT n} {steps state} (exit : Completion) (v : Val)
    (accept : d.check (argumentRoots inputs P.length (table.at l) frame)
      (fun p => frame[p]?.bind (closure codes P.toArray table inputs (table.at l)
        (invocationArguments d (argumentRoots inputs P.length (table.at l) frame))))
      (separation inputs P.length (table.at l)) = true)
    (atArg : frame[d.parameter]? = some argument)
    (atSite : originOf (table.at l) argument = some (.allocated site)) (lookup : P[site]? = some node)
    (literal : node.expression = .makeAt (.graph q.entry.arity q.entry.exprs q.entry.conts q.entry.start caps kind
      q.entry.spine.isSome component) fields vals)
    (width : caps.length = q.entry.captures.length)
    (member : (⟨q.entry,summary⟩ : CheckedCode ι) ∈ codes)
    (inferred : inferCodes request fuel = .ok (codes,known,final))
    (layout : pre.length = (if q.entry.spine.isSome then 1 else 0))
    (passed : ∀ i t o j, frame[i]? = some t → originOf (table.at l) t = some o →
      identity inputs o = some j → actual i = instantiate 0 ρ t)
    (invocation : ∀ p x, d.actualRoots[p]? = some (some (x, [])) → actual x = callEnv recv args p)
    (heapOK : HeapOk n W before) (argsOK : RootsOk W actual) (world : WorldAdm W) (room : steps ≤ n) (pos : 0 < n)
    (evaluated : ∀ allocation,
      (∃ fs oid, instantiate 0 ρ argument = .objAt fs (.graph q.entry.arity q.entry.exprs q.entry.conts
        q.entry.start (instantiateArgs 0 allocation caps) kind q.entry.spine.isSome component) oid) →
      let closureEnv := literalEntry pre recv q.entry.arity args caps allocation self
      EnvOk (RequestJson.graph request.toRequest) (codeFrame q.entry.arity q.entry.row q.entry.captures q.entry.spine)
        closureEnv n W ∧ RootsOk W closureEnv ∧
      HeapKnowledge.IndexHolds ⟨closureEnv,before⟩ (GraphCode.codeEntryIndices q.entry) closureEnv before ∧
      Execution (GraphCode.program q.entry.exprs q.entry.conts) steps before (.at q.entry.start closureEnv) after state)
    (done : state = (match exit with | .normal => .done v | .exceptional => .raised v)) :
    Supported (d.support.get exit) actual before after := by
  classical
  obtain ⟨hist,valid,time,_,_,held⟩ := checkedNames_reached checkNames callerValues reached
  obtain ⟨i,rfl,slot⟩ := namedOrigin_slot atSite
  obtain ⟨⟨b,hb,same⟩,_⟩ := held i (.allocated site) (by simp [namedAt,slot])
  obtain ⟨siteEq,birth,capHeld⟩ := valid site b hb
  have hnode := birth.1
  rw [siteEq,lookup] at hnode
  have lit := literalBirth birth ((Option.some.inj hnode).symm ▸ literal)
  obtain ⟨fs,oid,obj⟩ := lit
  obtain ⟨typed,entryRefs,indices,run⟩ := evaluated b.allocation ⟨fs,oid,by simpa [instantiate] using same.symm.trans obj⟩
  have namedArg : NamedOperands inputs P.length (table.at l) frame (historyEnv entry inputs hist) actual := by
    intro j t o x hj ho hx
    obtain ⟨bd,agree⟩ := historyNamedOperands valid held frame j t o x hj ho hx
    exact ⟨bd,by simpa [passed _ _ _ _ hj ho hx,List.getD_eq_getElem?_getD,hj] using agree⟩
  have namedCap := historyNamedOperands valid capHeld caps
  let kept := fun j => usedName inputs (table.at l) frame j ∨ usedName inputs (table.at site) caps j
  have sep := callerSeparation valid time (fun _ _ _ => inputSpinesBelow callerRoots callerHeap) kept (table.at l) actual before
  have namedOK := sparseRoots namedArg namedCap argsOK (captureRoots entryRefs)
  exact inferCodes_literal_execution_supported exit v (by simpa using accept) atArg atSite (by simpa using lookup) literal width
    member inferred layout (sparseNames namedArg (fun _ h => Or.inl h)) (sparseNames namedCap (fun _ h => Or.inr h))
    invocation sep heapOK (by
      intro j
      by_cases hj : usedName inputs (table.at l) frame j ∨ usedName inputs (table.at site) caps j
      · simpa only [ite_eq_left hj] using namedOK j
      · simpa only [ite_eq_right hj] using namedOK j) argsOK world room pos typed entryRefs indices run done

end Verification.SourceClaimJson.CallbackInterfaceCheck
