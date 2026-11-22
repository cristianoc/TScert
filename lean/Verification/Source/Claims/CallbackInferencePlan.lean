import Verification.Source.Claims.CallbackOrigins
import Verification.Source.Claims.CallbackEffectInference

/-! The annotation-driven producer reads the same flow and facts as the
ordinary pass. It proposes support at marked invocations and reruns the
body under its completed interface. This experimental check has no theorem
connecting its verdict to the ordinary safety theorem. -/
namespace Verification.SourceClaimJson.CallbackInferencePlan
open ControlFlow ProgramTyping RequestJson SourceElaboration PositiveGraphs
open PositiveCertificates LabelStore Footprints HeapKnowledge CertificateProducer
open CallbackPreservation CallbackOrigins

structure Interface where
  demands : List Demand
  deriving Repr

structure Candidate where
  supports : List Footprint
  demand : Demand

private def ownPrivate (slots : Slots) (privateRoots : List Nat) : Region → Bool
  | .field slot _ | .path slot [] _ =>
    match slots[slot]? with
    | some [.allocated label] => privateRoots.contains label
    | _ => false
  | .inCls region _ => ownPrivate slots privateRoots region
  | _ => false

private def invocation (slots : Slots) (params : List Nat) : Tm → Option Nat
  | .invoke (.var fn) .. =>
    match slots[fn]? with
    | some [.input entry] => if params.contains entry then some entry else none
    | _ => none
  | _ => none

private def supportAt (slots : Slots) (privateRoots : List Nat) (atom : IndexAtom) :
    Option (Footprint × Footprint) := do
  if atom.cond.isSome then none else do
    let support ← atom.fact.support? {}
    if support.isEmpty then none else do
      let residual := support.filter fun (r, _) => !ownPrivate slots privateRoots r
      return (support, ← project (entryRoot slots) residual)

private def supportsAt (slots : Slots) (privateRoots : List Nat) (entry : SinglePass.State) :
    List (Footprint × Footprint) :=
  let width := slots.size
  let k := (SinglePass.materialize entry width (List.range width) true).1
  k.indices.filterMap (supportAt slots privateRoots)

private def ordinaryActual : Tm → Bool
  | .spread _ => false
  | _ => true

/-- Actuals before the first spread keep their positions in the runtime call.
The spread may supply any number of arguments, including zero. -/
def positionalPrefix (args : List Tm) : List Tm :=
  args.takeWhile ordinaryActual

private def atCall (slots : Slots) (privateRoots : List Nat) (parameter : Nat)
    (entry : SinglePass.State) (expression : Tm) : Candidate :=
  let candidates := supportsAt slots privateRoots entry
  let supports := (candidates.map Prod.fst).reverse.eraseDups
  let demand := (candidates.flatMap fun c => c.2.map fun (r, _) => (r, .keep)).eraseDups
  let roots := match expression with
    | .invoke _ receiver args => (receiver :: positionalPrefix args).map fun
        | .var slot => entryRoot slots slot
        | _ => none
    | _ => []
  ⟨supports, ⟨parameter, ⟨demand, []⟩, roots⟩⟩

private def covers (published : Interface) (required : Demand) : Bool :=
  let entries := (published.demands.filter fun d => d.parameter == required.parameter &&
    d.actualRoots == required.actualRoots).flatMap (·.support.normal)
  required.support.normal.all fun (r, change) =>
    entries.any fun (s, bound) => decide (s = r) && bound.le change

section
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

/-- Execute a lowered body with inferred support on opted-in calls. On the
checking run only entries covered by the already published interface can
be preserved. The ordinary walk supplies all other checks. -/
def visit (G : NormalGraph ι) (images : InstanceImageCheck G) (env : SinglePass.WalkEnv ι G images)
    (origins : Table) (privateRoots params : List Nat) (published : Option Interface)
    (state : SinglePass.WalkState ι G) (label : Nat) :
    Except String (SinglePass.WalkState ι G × Option Demand) := do
  let slots := origins.at label
  let node := env.nodes[label]!
  let candidate ← match invocation slots params node.expression with
    | none => pure none
    | some param =>
      match SinglePass.visitEntry G images env state label with
      | .ok entry => pure (some (atCall slots privateRoots param entry.entry node.expression))
      | .error stop => throw (toString stop.outcome.outcome)
  if let (some iface, some candidate) := (published, candidate) then
    if !covers iface candidate.demand then
      throw s!"the inferred interface does not cover callback invocation at node {label}"
  let env := { env with framed := candidate.toList.map fun c => (label, c.supports) }
  match SinglePass.visit G images env state label with
  | .ok next => pure (next, candidate.map (·.demand))
  | .error stop => throw s!"{stop.outcome.outcome}; node {label}; missing {reprStr (stop.trace.missing.filterMap fun | .index a => some a | _ => none)}"

private def walk (G : NormalGraph ι) (images : InstanceImageCheck G) (env : SinglePass.WalkEnv ι G images)
    (initial : SinglePass.WalkState ι G) (origins : Table) (privateRoots params : List Nat)
    (published : Option Interface) : Except String Interface := do
  let mut state := initial
  let mut demands := []
  for _ in List.range (env.nodes.size + 1) do
    let label :: queue := state.queue | break
    let (next, demand) ← visit G images env origins privateRoots params published { state with queue } label
    demands := demands ++ demand.toList
    state := next
  if !state.queue.isEmpty || state.walk.visited < (env.reached.toList.filter id).length then
    throw "callback preservation did not visit every reachable label"
  return ⟨demands.eraseDups⟩

end

/-- Produce the annotated declaration's interface from its body alone.
Only publish a proposal that survives a check at that interface. -/
def infer (f : FilePlans) (i fuel : Nat) (params : List Nat) : Except String Interface := do
  let some plan := f.plans[i]? | throw "no member at that position"
  let .graph _ _ r ← (← plan).certify | throw "the marked member needs an ordinary graph"
  if r.qualification.isSome || r.async then
    throw "callback preservation needs a synchronous ordinary member"
  if r.regional.isSome then throw "callback preservation of a stated regional bound is unavailable"
  let G := StoreView.graph f.F.store
  let images := StoreView.images f.F.store
  let labels := r.searchLabels
  for position in params do
    let some ty := r.inputs[position]? | throw "InferPreserves parameter is outside the entry frame"
    let arms := PositiveRules.expand G ty
    let callable := fun
      | PositiveNormalization.Clause.arrs arrows rest | .callable _ _ arrows rest _ =>
        !arrows.isEmpty || !rest.isEmpty
      | _ => false
    if !arms.any callable || !arms.all (fun arm => (arm matches .undef) || callable arm) then
      throw s!"InferPreserves parameter {position + 1} needs a callback type"
  let (codes, known, answers) ← CallbackEffectInference.inferCodes r fuel
  let pool := CertificateProducer.vocabulary G labels r.claims r.inputs
  let widths := (r.claims.map (·.context.length)).toArray
  let some origins := CallbackOrigins.infer r.program widths r.start r.inputs.length
    | throw "callback origin analysis did not settle"
  let privateRoots := privateAllocations r.program origins
  let bound := if r.stated.isSome || r.fresh then
    some (RunBound.ofRequest r.footprint r.onThrow r.fresh) else none
  let (env, initial) ← match SinglePass.setup G images pool fuel r.program r.claims r.start r.inputs r.goal
      r.assertions r.cuts [] r.entryIndices [] known (GraphCode.admits (codes.toList.map (·.entry)))
      r.aliases .ordinary answers (bound := bound) (tracing := true) (ensures := r.ensures) (entrySeparation := r.entrySeparation) with
    | .ok pair => pure pair
    | .error stop => throw (toString stop.outcome.outcome)
  let published ← walk G images env initial origins privateRoots params none
  let _ ← walk G images env initial origins privateRoots params (some published)
  return published

end Verification.SourceClaimJson.CallbackInferencePlan
