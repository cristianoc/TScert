import Verification.Source.Claims.CallbackInterfaceCheck

/-! The rules Adapt and FreshRead of the inferred callback preservation note,
on the experimental consumer path. Adapt checks a closure literal whose
calls of a captured marked input are replaced by the empty effect, and
forwards the demand to that input. FreshRead separates a value read from
the heap from an allocation no exposure reaches before the read. -/
namespace Verification.SourceClaimJson.CallbackAdaptation
open ControlFlow ProgramTyping RequestJson SourceElaboration LabelStore
open CallbackOrigins CallbackPreservation CallbackEffectInference CallbackInterfaceCheck
open Footprints CallEffects PositiveGraphs PositiveCertificates

/-- The join of two optional footprints, as closure inference joins visits. -/
def joinFootprint (old new : Option Footprint) : Option Footprint :=
  match old, new with
  | none, a | a, none => a
  | some a, some b => some ((a ++ b).eraseDups)

/-- A call in closure code of the closure's own entry slot `callee`.
`operands` are the entry roots of its receiver and fixed arguments. -/
structure Relied where
  callee : Nat
  operands : List (Option (Nat × List String))
  deriving DecidableEq, Repr

structure AdaptedCode (ι : Type) where
  entry : CodeEntry ι
  summary : Summary
  relied : List Relied
  /-- Some node of the code has a handler: a relied call's throw can reach
  the closure's normal exit. -/
  handles : Bool

section
variable {ι : Type} [DecidableEq ι]

/-- The entry root of an operand at a label, from the argument-path facts. -/
def entryRoot (facts : List GraphCode.ArgumentPathTracking.Fact) : Tm → Option (Nat × List String)
  | .var s => (facts.find? (·.slot == s)).map fun f => (f.region.position, f.region.path)
  | _ => none

/-- A relied call: a read-only invocation of a capture's entry value with
fixed operands. -/
def reliedAt (firstCapture : Nat) (facts : List GraphCode.ArgumentPathTracking.Fact) : Tm → Option Relied
  | t@(.invoke callee recv args) => do
    guard (CallbackInferencePlan.readCall t)
    let fixed := CallbackInferencePlan.positionalPrefix args
    guard (fixed.length == args.length)
    let (pos, path) ← entryRoot facts callee
    guard (path.isEmpty && firstCapture ≤ pos)
    return ⟨pos, (recv :: fixed).map (entryRoot facts)⟩
  | _ => none

/-- `inferChecked` with the summary of every relied call replaced by the
empty footprint on both exits. -/
def inferAdapted (G : NormalGraph ι) (q : CodeRequest ι) (records : Array SinglePass.VisitRecord) :
    Except String (Summary × List Relied) := do
  let nodes := GraphCode.program q.entry.exprs q.entry.conts
  let inputs := codeFrame q.entry.arity q.entry.row q.entry.captures q.entry.spine
  let origins := (List.range inputs.length).map fun slot =>
    ({ position := slot, path := [] } : ArgumentSpineRegion)
  let entries := q.claims.map fun c => ({ sequent := some ⟨c.context, .undef, c.type⟩, edges := [] } : NodeEvidence ι)
  let facts := certifiedRootTable nodes q.entry.start inputs.length (regionTable nodes entries q.entry.start origins) |>.toArray
  let firstCapture := q.entry.arity + frameOffset q.entry.spine
  let ns := nodes.toArray
  let claims := q.claims.toArray
  let (locals, relied) ← records.foldlM (init := (Array.replicate ns.size none, ([] : List Relied)))
    fun (acc, relied) record => do
      let some node := ns[record.label]? | throw "closure effect record has no graph node"
      let some claim := claims[record.label]? | throw "closure effect record has no point claim"
      let here := facts.getD record.label []
      let (frame, relied) := match reliedAt firstCapture here node.expression with
        | some call => ((⟨some [], some []⟩ : Summary), call :: relied)
        | none => (step G node claim here record.certificate, relied)
      let combined := match acc.getD record.label none with
        | none => frame
        | some old => ⟨joinFootprint old.normal frame.normal, joinFootprint old.exceptional frame.exceptional⟩
      return (acc.setIfInBounds record.label (some combined), relied)
  return (← composeChecked nodes q.entry.start locals, relied.eraseDups)

end

/-- `inferCodeRows` with the adapted summaries. The ordinary rows stay the
checked table; these rows serve only the Adapt check. -/
def adaptedRows {σ ι : Type} [Labels ι] [StoreView σ ι] [CertificateProducer.Instantiates ι]
    (r : SourceRequest σ ι) (fuel : Nat) (known : List (ProgramCertificates.Evidence ι))
    (accepted : List (CodeEntry ι)) (table : Array (AdaptedCode ι))
    (answers : CertificateProducer.Answered (RequestJson.graph r.toRequest)) :
    List (CodeRequest ι × Nat) → Except String (Array (AdaptedCode ι))
  | [] => .ok table
  | (q,code) :: rest => do
    let G := RequestJson.graph r.toRequest
    let images := StoreView.images r.types
    let labels := r.searchLabels
    if !codeConditions q.entry || !asyncAdmits q.async q.entry.row.effect then
      throw s!"closure {code} did not meet its signature conditions"
    let rq := q.asRequest r.toRequest
    let hints := (r.codeHints[code]?).getD {}
    let pool := CertificateProducer.vocabulary G labels rq.claims rq.inputs
    let (outcome, counts, next, _) := SinglePass.run G images pool fuel rq.program rq.claims rq.start
      rq.inputs q.entry.goal hints.requirements hints.cuts hints.candidates rq.entryIndices
      [] known (GraphCode.admits accepted) r.aliases .ordinary answers
      (bound := codeBound q.entry) (grading := true)
    let .accepted := outcome | throw s!"closure {code} was refused: {outcome}"
    let (summary, relied) ← if q.async then
      pure (⟨some Footprints.Closed.top.fp, some Footprints.Closed.top.fp⟩, [])
      else (inferAdapted G q counts.grades).mapError fun msg => s!"closure {code}: {msg}"
    let handles := (GraphCode.program q.entry.exprs q.entry.conts).any (·.handler.isSome)
    adaptedRows r fuel known (accepted ++ [q.entry]) (table.push ⟨q.entry, summary, relied, handles⟩) next rest

def adaptedCodes {σ ι : Type} [Labels ι] [StoreView σ ι] [CertificateProducer.Instantiates ι]
    (r : SourceRequest σ ι) (fuel : Nat) (known : List (ProgramCertificates.Evidence ι)) :
    Except String (Array (AdaptedCode ι)) := do
  let G := RequestJson.graph r.toRequest
  let images := StoreView.images r.types
  let labels := r.searchLabels
  let valid := StoreView.valid r.types
  let (_, answers) ← match ExpressionClaims.produceUsing G images labels valid
      (StoreView.projection r.types) fuel r.obligations {} with
    | .ok result => pure result
    | .error _ => throw "the member's expression obligations did not pass"
  let (_, answers) := ExpressionClaims.renderKnownUsing G images labels valid r.nodePlans answers
  adaptedRows r fuel known [] #[] answers r.codes.zipIdx

/-- The literal closure under Adapt: the joined adapted summaries of its
matching rows, its substitution, and for each relied call the marked
input it calls with the call's public operand roots. -/
def adaptedClosure {ι : Type} [DecidableEq ι] (codes : Array (AdaptedCode ι))
    (nodes : Array Node) (origins : Table) (inputs : Nat) (slots : Slots) (forwarding : List Nat)
    (callRoots : List (Option (Nat × List String))) (argument : Tm) :
    Option (Callback × Bool × List (Nat × List (Option (Nat × List String)))) := do
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
  let callerRoot := fun (entry : Option (Nat × List String)) => do
    let (pos, path) ← entry
    if pos < restSlots then none
    else if pos < firstCapture then
      let (root, outer) ← callRoots[pos - restSlots]?.join
      if root < inputs then some (root, outer ++ path) else none
    else
      let cap ← captures[pos - firstCapture]?
      let .input root ← originOf (origins.at label) cap | none
      some (root, path)
  let relied ← (rows.toList.flatMap (·.relied)).eraseDups.mapM fun call => do
    let cap ← captures[call.callee - firstCapture]?
    let .input q ← originOf (origins.at label) cap | none
    guard (forwarding.contains q)
    return (q, call.operands.map callerRoot)
  return (⟨effects, actuals⟩, rows.any (·.handles), relied)

/-- A field location holds a value, so a field region restricted to the
value category still contains it. -/
def fieldRegion : Region → Region
  | .inCls r c => if c.value then fieldRegion r else .inCls r c
  | r => r

/-- The field regions a path is read through, at each of its prefixes. -/
def pathFieldsKept (support : Footprint) (x : Nat) (p : List String) : Bool :=
  (List.range p.length).all fun n =>
    let pre := p.take n
    let k := PropKey.str p[n]!
    support.any fun (r, c) => c == .keep &&
      (fieldRegion r == (if pre.isEmpty then .field x k else .path x pre k) ||
        fieldRegion r == (if pre.isEmpty then .fields x else .pathFields x pre))

/-- Path-closed: every path a region reads goes through fields the support keeps. -/
def pathClosed (support : Footprint) : Bool :=
  let rec closed : Region → Bool
    | .path x p _ | .pathFields x p | .pathCells x p | .spine x p => pathFieldsKept support x p
    | .inCls r _ => closed r
    | _ => true
  support.all fun (r, _) => closed r

/-- Allocation labels exposed on some path to each label: an exposing
node's allocations reach every label its successors reach. -/
def exposedBefore (nodes : Array Node) (table : Table) : Array (List Nat) := Id.run do
  let succ := fun l => SinglePass.nodeSucc nodes l
  let mut out := Array.replicate nodes.size ([] : List Nat)
  for (node, label) in nodes.toList.zipIdx do
    let some slots := table.getD label none | continue
    let readSlots := match node.expression with
      | .var j => if node.continuation == Continuation.ret then some [j] else some []
      | .readAt _ (.var _) => some []
      | .writeAt _ (.var _) value => SinglePass.mentioned 0 value
      | term => SinglePass.mentioned 0 term
    let values := match readSlots with
      | some js => js.flatMap (slots.getD · [])
      | none => slots.toList.flatten
    let exposed := values.filterMap fun o => match o with | .allocated a => some a | _ => none
    if exposed.isEmpty then continue
    -- every label reachable from a successor of this node
    let mut seen : Array Bool := Array.replicate nodes.size false
    let mut stack := succ label
    for _ in [0:nodes.size * (nodes.size + 1) + 1] do
      match stack with
      | [] => break
      | l :: rest =>
        stack := rest
        if seen.getD l true then continue
        seen := seen.set! l true
        stack := succ l ++ stack
    for l in [0:nodes.size] do
      if seen.getD l false then out := out.modify l fun xs => (exposed ++ xs).eraseDups
  return out

/-- FreshRead: a field-read operand at call position `i`, read at `lr`, is
apart from every single-site allocation named at the call that no exposure
reaches before `lr`. -/
def freshReads (inputs nodes : Nat) (exposed : Array (List Nat)) (slots : Slots) (frame : List Tm) :
    List SepFact :=
  let allocations := (slots.toList.filterMap fun os => match os with
    | [.allocated a] => some a
    | _ => none).eraseDups
  frame.zipIdx.flatMap fun (t, i) =>
    match originOf slots t with
    | some (.read lr) => allocations.filterMap fun a =>
        if (exposed.getD lr []).contains a then none
        else some (.spines (inputs + nodes + i, []) (inputs + a, []))
    | _ => []

/-- The experimental demand check: the ordinary decision, then Use with the
FreshRead facts, then Adapt for a closure calling captured marked inputs. -/
def checkDemand {σ ι : Type} [Labels ι] [StoreView σ ι]
    (r : SourceRequest σ ι) (codes : Array (CheckedCode ι))
    (adapted : Thunk (Except String (Array (AdaptedCode ι))))
    (exposed : Thunk (Array (List Nat))) (origins : Table) (forwarding : List Nat)
    (producer : Published) (label : Nat) (receiver : Tm) (args : List Tm) (demand : Demand) :
    Except String (List Demand) := do
  match CallbackInterfaceCheck.checkDemand r codes origins forwarding producer label receiver args demand with
  | .ok out => return out.toList
  | .error reason =>
    let nodes := r.program.toArray
    let inputs := r.inputs.length
    let slots := origins.at label
    let frame := checkedCallFrame producer receiver args
    let some callback := frame[demand.parameter]? | throw reason
    let toCaller := argumentRoots inputs nodes.size slots frame
    let actuals := invocationBindings demand toCaller
    let evidence : SepEvidence := { (separation inputs nodes.size slots) with
      facts := (separation inputs nodes.size slots).facts ++ freshReads inputs nodes.size exposed.get slots frame }
    let callbacks := fun parameter => (frame[parameter]?).bind (closure codes nodes origins inputs slots actuals)
    if demand.check toCaller callbacks evidence then return []
    let some (cb, handles, relied) := adaptedClosure (← adapted.get) nodes origins inputs slots forwarding actuals callback
      | throw reason
    if relied.isEmpty then throw reason
    let some normal := project (publicOperand inputs toCaller) demand.support.normal
      | throw s!"Adapt at node {label}: the requirement of {producer.name} cannot name a caller input"
    let some exceptional := project (publicOperand inputs toCaller) demand.support.exceptional
      | throw s!"Adapt at node {label}: the requirement of {producer.name} cannot name a caller input"
    -- A relied call's normal return can end the closure either way; its
    -- throw ends the closure with a throw unless the closure handles it.
    let afterNormal := (normal ++ exceptional).eraseDups
    let afterThrow := if handles then afterNormal else exceptional
    if !pathClosed afterNormal then
      throw s!"Adapt at node {label}: the requirement of {producer.name} reads a path through a field it does not keep"
    let adaptedCallbacks := fun parameter =>
      if parameter == demand.parameter then some cb else callbacks parameter
    if !demand.check toCaller adaptedCallbacks evidence then
      throw s!"Adapt at node {label}: the closure passed to {producer.name} changes a location its requirement keeps"
    return relied.map fun (q, operands) => ⟨q, ⟨afterNormal, afterThrow⟩, operands⟩

def checkNode {σ ι : Type} [Labels ι] [StoreView σ ι]
    (r : SourceRequest σ ι) (codes : Array (CheckedCode ι))
    (adapted : Thunk (Except String (Array (AdaptedCode ι))))
    (exposed : Thunk (Array (List Nat))) (origins : Table) (known : List (Nat × Published))
    (forwarding : List Nat) (node : Node) (label : Nat) : Except String (Option (String × List Demand)) := do
  let slots := origins.at label
  if escapesDeclaration slots known node then
    throw s!"a marked declaration escapes direct application at node {label}"
  let .invoke callee receiver args := node.expression | return none
  let some (.input root) := originOf slots callee | return none
  let some (_, producer) := known.find? (·.1 == root) | return none
  let forwarded ← producer.interface.demands.mapM
    (checkDemand r codes adapted exposed origins forwarding producer label receiver args)
  return some (producer.name, forwarded.flatten)

/-- `CallbackInterfaceCheck.checkUses` with the experimental demand check. -/
def checkUses {σ ι : Type} [Labels ι] [StoreView σ ι]
    (r : SourceRequest σ ι) (codes : Array (CheckedCode ι))
    (adapted : Thunk (Except String (Array (AdaptedCode ι))))
    (origins : Table) (interfaces : List Published) (forwarding : List Nat) : Except String (List Demand) := do
  let nodes := r.program.toArray
  let inputs := r.inputs.length
  let sites := CallbackOrigins.namedSites nodes
  if !CallbackOrigins.checkNames nodes sites r.start inputs origins then
    throw "caller origin names failed their entry or incoming edge check"
  if r.siblings.length > inputs then throw "the module sibling layout exceeds the caller inputs"
  let known := knownSiblings inputs r.siblings interfaces
  if !checkMayInputs nodes origins r.start inputs (known.map Prod.fst) then
    throw "marked declaration origins failed their entry or incoming edge check"
  -- Computed only where the ordinary check of a demand fails.
  let exposed := Thunk.mk fun _ => exposedBefore nodes origins
  let sites ← r.program.zipIdx.filterMapM fun (node,label) =>
    checkNode r codes adapted exposed origins known forwarding node label
  if !interfaces.all (fun own => sites.any (fun site => site.1 == own.name)) then
    throw "a marked declaration is used outside a resolved direct call"
  return (sites.foldl (fun acc site => site.2.reverse ++ acc) []).eraseDups

/-- `CallbackInterfaceCheck.check` on the experimental path. -/
def check (f : FilePlans) (i fuel : Nat) (interfaces : List Published)
    (forwarding : List Nat := []) : Except String (List Demand) := do
  let some plan := f.plans[i]? | throw "no caller at that position"
  let .graph _ _ r ← (← plan).certify
  let (codes, known, _) ← inferCodes r fuel
  -- The second closure walk runs only where Adapt is tried.
  let adapted := Thunk.mk fun _ => adaptedCodes r fuel known
  let nodes := r.program.toArray
  let inputs := r.inputs.length
  let some origins := CallbackOrigins.infer r.program (r.claims.map (·.context.length)).toArray r.start inputs
    | throw "caller origin analysis did not settle"
  checkUses r codes adapted (CallbackOrigins.nameable (CallbackOrigins.namedSites nodes) origins) interfaces forwarding

/-- `CallbackInterfaceCheck.writeInterface` with forwarding checked on the
experimental path, so a closure calling a marked input forwards by Adapt. -/
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

end Verification.SourceClaimJson.CallbackAdaptation
