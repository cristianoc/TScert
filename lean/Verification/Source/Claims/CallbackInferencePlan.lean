import Verification.Source.Claims.CallbackPrivateOrigins
import Verification.Programs.TolerantFramesGuaranteeTarget
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

def ownPrivate (slots : Slots) (privateRoots : List Nat) : Region → Bool
  | .field slot _ | .path slot [] _ =>
    match slots[slot]? with
    | some [.allocated label] => privateRoots.contains label
    | _ => false
  | .inCls region _ => ownPrivate slots privateRoots region
  | _ => false

/-- A framed call evaluates only heap reads before dispatch. Splices can
expand a checked read into already stored values. -/
def readActual : Tm → Bool
  | .spread t => Purity.readTerm t
  | t => Purity.readTerm t

def readCall : Tm → Bool
  | .invoke f recv args => Purity.readTerm f && Purity.readTerm recv && args.all readActual
  | _ => false

def invocation (slots : Slots) (params : List Nat) : Tm → Option Nat
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

def atCall (slots : Slots) (privateRoots : List Nat) (parameter : Nat)
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

/-- The proposal records the label, supports and demand together. The
origin of each row is erased when compiling the inference pass. -/
structure Row (nodes : Array Node) (origins : Table) (privateRoots params : List Nat) where
  label : Nat
  candidate : Candidate
  prepared : readCall nodes[label]!.expression = true
  source : ∃ parameter state,
    invocation (origins.at label) params nodes[label]!.expression = some parameter ∧
    candidate = atCall (origins.at label) privateRoots parameter state nodes[label]!.expression

def publication {nodes origins privateRoots params} (rows : List (Row nodes origins privateRoots params)) : Interface :=
  ⟨(rows.map (·.candidate.demand)).eraseDups⟩

def framesOf {nodes origins privateRoots params} (rows : List (Row nodes origins privateRoots params)) :=
  rows.map fun row => (row.label, row.candidate.supports)

def visit (G : NormalGraph ι) (images : InstanceImageCheck G) (env : SinglePass.WalkEnv ι G images)
    (origins : Table) (privateRoots params : List Nat)
    (state : SinglePass.WalkState ι G) (label : Nat) :
    Except String (SinglePass.WalkState ι G × Option (Row env.nodes origins privateRoots params)) := do
  let slots := origins.at label
  let node := env.nodes[label]!
  let row ← match hinv : invocation slots params node.expression with
    | none => pure none
    | some param =>
      -- Select ordinary frame-free transfer before visiting an ineligible call.
      if ready : readCall node.expression then
        match SinglePass.visitEntry G images env state label with
        | .ok entry => pure (some (Row.mk label (atCall slots privateRoots param entry.entry node.expression)
            ready ⟨param,entry.entry,hinv,rfl⟩ : Row env.nodes origins privateRoots params))
        | .error stop => throw (toString stop.outcome.outcome)
      else pure none
  let env := { env with framed := row.toList.map fun r => (r.label, r.candidate.supports) }
  match SinglePass.visit G images env state label with
  | .ok next => pure (next, row)
  | .error stop => throw s!"{stop.outcome.outcome}; node {label}; missing {reprStr (stop.trace.missing.filterMap fun | .index a => some a | _ => none)}"

private def walk (G : NormalGraph ι) (images : InstanceImageCheck G) (env : SinglePass.WalkEnv ι G images)
    (initial : SinglePass.WalkState ι G) (origins : Table) (privateRoots params : List Nat) :
    Except String (List (Row env.nodes origins privateRoots params)) := do
  let mut state := initial
  let mut rows := []
  for _ in List.range (env.nodes.size + 1) do
    let label :: queue := state.queue | break
    let (next, row) ← visit G images env origins privateRoots params { state with queue } label
    rows := rows ++ row.toList
    state := next
  if !state.queue.isEmpty || state.walk.visited < (env.reached.toList.filter id).length then
    throw "callback preservation did not visit every reachable label"
  return rows

end

/-- Replay the proposed supports through the ordinary pass, then check
all read summaries used by the accepted producer. -/
def replay {σ ι : Type} [Labels ι] [StoreView σ ι] {G : NormalGraph ι} {I : InstanceImageCheck G}
    (r : SourceRequest σ ι) (call : TolerantFrames.Target.RunCall G I) (published : Interface) :
    Except String Interface := do
  let (outcome, _, after, _) := call.result
  let .accepted := outcome | throw s!"callback producer replay was refused: {outcome}"
  if !summariesChecked r after.summaries.toList then
    throw "invalid callback producer replay read summaries"
  return published

/-- Produce the annotated declaration's interface from its body alone.
Only publish a proposal that survives a check at that interface. -/
def infer (f : FilePlans) (i fuel : Nat) (params : List Nat) : Except String Interface := do
  let some plan := f.plans[i]? | throw "no member at that position"
  let .graph _ _ r ← (← plan).certify
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
  let sites := Array.replicate r.program.length true
  if !checkNames r.program.toArray sites r.start r.inputs.length origins then
    throw "invalid callback origin evidence in producer"
  let privateRoots := certifiedPrivate r.program.toArray origins (privateAllocations r.program origins)
  let bound := if r.stated.isSome || r.fresh then
    some (RunBound.ofRequest r.footprint r.onThrow r.fresh) else none
  let (env, initial) ← match SinglePass.setup G images pool fuel r.program r.claims r.start r.inputs r.goal
      r.assertions r.cuts [] r.entryIndices [] known (GraphCode.admits (codes.toList.map (·.entry)))
      r.aliases .ordinary answers (bound := bound) (tracing := true) (ensures := r.ensures) (entrySeparation := r.entrySeparation) with
    | .ok pair => pure pair
    | .error stop => throw (toString stop.outcome.outcome)
  let rows ← walk G images env initial origins privateRoots params
  let published := publication rows
  let frames := framesOf rows
  let call : TolerantFrames.Target.RunCall G images :=
    ⟨pool, fuel, r.program, r.claims, r.start, r.inputs, r.goal, r.assertions, r.cuts, [], r.entryIndices,
      [], known, GraphCode.admits (codes.toList.map (·.entry)), r.aliases, .ordinary, answers, #[],
      1000000000, bound, #[], #[], r.ensures, #[], r.entrySeparation, none, true, false, none, frames⟩
  replay r call published

end Verification.SourceClaimJson.CallbackInferencePlan
