import Verification.Source.Claims.CallbackPrivateOrigins
import Verification.Programs.TolerantFramesGuaranteeTarget
import Verification.Source.Claims.CallbackNameHistory
import Verification.Source.Claims.CallbackOrigins
import Verification.Source.Claims.CallbackEffectInference
import Verification.Source.Claims.CallbackPreservationSound
import Verification.Programs.TolerantFramesComposeYields

/-! The annotation-driven producer reads the same flow and facts as the
ordinary pass. It proposes support at marked invocations and reruns the
body under its completed interface. Its checked publication is interpreted in
`CallbackProducerVerdict`. -/
namespace Verification.SourceClaimJson.CallbackInferencePlan
open ControlFlow ProgramTyping RequestJson SourceElaboration PositiveGraphs
open PositiveCertificates LabelStore Footprints HeapKnowledge CertificateProducer
open CallbackPreservation CallbackOrigins

structure Interface where
  demands : List Demand
  deriving Repr

/-- Read the callback's single fixed call signature. An optional callback
can also have an undefined arm, which contributes no call signature. -/
@[nospecialize] def fixedCallbackSignature (G : NormalGraph ι) (ty : Ty ι) : Option (CallEffects.Arrow (Ty ι)) :=
  match (PositiveRules.expand G ty).filter (fun c => !(c matches .undef)) with
  | [.arrs [signature] []] | [.callable _ _ [signature] [] _] => some signature
  | _ => none

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

private theorem inputSlot {slots : Slots} {i p} (lookup : slots[i]? = some [.input p])
    {history entry inputs ρ} (names : slotsHold history entry inputs slots ρ) :
    entry p = ρ i := (names i (.input p) (by simp [namedAt,lookup])).1.2

theorem reached_invocation {P : Program} {table entry inputs start h₀ h l ρ k}
    (checked : checkNames P.toArray (namedSites P.toArray) start inputs table = true)
    (values : ∀ i < inputs, isVal (entry i) = true)
    (run : Execution P k h₀ (.at start entry) h (.at l ρ)) {fn receiver args p params}
    (marked : invocation (table.at l) params (.invoke (.var fn) receiver args) = some p) :
    p ∈ params ∧ entry p = ρ fn := by
  obtain ⟨_,_,_,_,_,names⟩ := checkedNames_reached checked values run
  simp only [invocation] at marked
  split at marked
  next i lookup =>
    split at marked
    next mem =>
      cases marked
      exact ⟨List.contains_iff_mem.mp mem,inputSlot lookup names⟩
    next => contradiction
  next => contradiction

theorem reached_entryRoots {P : Program} {table entry inputs start h₀ h l ρ k}
    (checked : checkNames P.toArray (namedSites P.toArray) start inputs table = true)
    (values : ∀ i < inputs, isVal (entry i) = true)
    (run : Execution P k h₀ (.at start entry) h (.at l ρ)) :
    RealizesRoots (entryRoot (table.at l)) ρ entry h := by
  obtain ⟨_,_,_,_,_,names⟩ := checkedNames_reached checked values run
  intro x y p hx
  unfold entryRoot at hx
  split at hx
  next i lookup =>
    cases hx
    simp [readPath,inputSlot lookup names]
  next => contradiction

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

private theorem supportAt_project {slots : Slots} {privateRoots : List Nat} {atom : IndexAtom}
    {support projected : Footprint}
    (chosen : supportAt slots privateRoots atom = some (support, projected)) :
    project (entryRoot slots) (support.filter fun e => !ownPrivate slots privateRoots e.1) =
      some projected := by
  unfold supportAt at chosen
  split at chosen
  · contradiction
  cases known : atom.fact.support? {} with
  | none => simp [known] at chosen
  | some whole =>
    cases exactProjection : project (entryRoot slots)
        (whole.filter fun e => !ownPrivate slots privateRoots e.1) with
    | none => simp [known, exactProjection] at chosen
    | some residual =>
      simp [known, exactProjection] at chosen
      rcases chosen.2 with ⟨rfl, rfl⟩
      exact exactProjection

/-- The demand computed at a call, together with private field preservation,
supports each fact selected for the normal continuation. -/
theorem atCall_supported {slots : Slots} {privateRoots : List Nat} {parameter : Nat}
    {entry : SinglePass.State} {expression : Tm} {body iface : Env} {before after : Heap}
    (rootsOK : RealizesRoots (entryRoot slots) body iface before)
    (localFrame : ∀ e : Region × Change, ownPrivate slots privateRoots e.1 = true →
      Supported [e] body before after)
    (demand : Supported (atCall slots privateRoots parameter entry expression).demand.support.normal
      iface before after) :
    ∀ S ∈ (atCall slots privateRoots parameter entry expression).supports,
      Supported S body before after := by
  intro S chosen
  simp only [atCall, List.mem_eraseDups, List.mem_reverse, List.mem_map] at chosen
  obtain ⟨⟨support, projected⟩, candidate, rfl⟩ := chosen
  have projectedBy := List.mem_filterMap.mp candidate
  obtain ⟨atom, _, projectedBy⟩ := projectedBy
  apply supported_of_private_and_published rootsOK support (ownPrivate slots privateRoots)
    (supportAt_project projectedBy)
  · intro e member
    exact localFrame e (List.mem_filter.mp member).2 e (by simp)
  · apply supported_sub demand
    intro e member
    simp only [atCall, List.mem_eraseDups, List.mem_flatMap]
    exact ⟨(support, projected), candidate, member⟩

private def covers (published : Interface) (required : Demand) : Bool :=
  let entries := (published.demands.filter fun d => d.parameter == required.parameter &&
    d.actualRoots == required.actualRoots).flatMap (·.support.normal)
  required.support.normal.all fun (r, change) =>
    entries.any fun (s, bound) => decide (s = r) && bound.le change

/-- Replay may use the union of supports published for the same callback
parameter and its invocation arguments. A published bound can discharge
a weaker required bound on the same region. -/
theorem covers_supported {published : Interface} {required : Demand} {ρ : Env} {h h' : Heap}
    (covered : covers published required = true)
    (publishedHolds : ∀ d ∈ published.demands, d.parameter = required.parameter →
      d.actualRoots = required.actualRoots → Supported d.support.normal ρ h h') :
    Supported required.support.normal ρ h h' := by
  rintro ⟨r, change⟩ member l v regionCell before
  have hits := List.all_eq_true.mp covered (r, change) member
  obtain ⟨⟨s, bound⟩, candidate, compatible⟩ := List.any_eq_true.mp hits
  obtain ⟨d, relevant, entry⟩ := List.mem_flatMap.mp candidate
  obtain ⟨inInterface, sameCall⟩ := List.mem_filter.mp relevant
  simp only [Bool.and_eq_true, beq_iff_eq] at sameCall
  change (decide (s = r) && bound.le change) = true at compatible
  simp only [Bool.and_eq_true, decide_eq_true_eq] at compatible
  obtain ⟨sameRegion, weaker⟩ := compatible
  subst s
  obtain ⟨v', after, allowed⟩ :=
    publishedHolds d inInterface sameCall.1 sameCall.2 (r, bound) entry l v regionCell before
  exact ⟨v', after, allowed.mono weaker⟩

/-- At a replayed callback invocation, the published demands and the
private fields suffice for the index facts that the framed step keeps. -/
theorem replay_preserves {slots : Slots} {privateRoots : List Nat} {parameter : Nat}
    {entry : SinglePass.State} {expression : Tm} {published : Interface}
    {body iface : Env} {before after : Heap} {knowledge : Knowledge}
    {ε : EntryState} {value : Tm}
    (rootsOK : RealizesRoots (entryRoot slots) body iface before)
    (localFrame : ∀ e : Region × Change, ownPrivate slots privateRoots e.1 = true →
      Supported [e] body before after)
    (covered : covers published (atCall slots privateRoots parameter entry expression).demand = true)
    (publishedHolds : ∀ d ∈ published.demands, d.parameter = parameter →
      d.actualRoots = (atCall slots privateRoots parameter entry expression).demand.actualRoots →
      Supported d.support.normal iface before after)
    (knowledgeHolds : IndexHolds ε knowledge.indices body before) :
    IndexHolds ε
      (SinglePass.framedKept (atCall slots privateRoots parameter entry expression).supports knowledge)
      (push value body) after := by
  apply TolerantFrames.framedKept_holds knowledgeHolds
  apply atCall_supported rootsOK localFrame (covers_supported covered ?_)
  exact publishedHolds

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

/-- Every support in the replay table comes from a published demand for
the same invocation. A concrete path supplies its entry-root equalities. -/
theorem frames_supported {P : Program} {origins entry inputs start h₀ before l body k}
    {privateRoots params} (rows : List (Row P.toArray origins privateRoots params))
    (checked : checkNames P.toArray (namedSites P.toArray) start inputs origins = true)
    (values : ∀ i < inputs, isVal (entry i) = true)
    (run : Execution P k h₀ (.at start entry) before (.at l body))
    {supports after} (frame : SinglePass.framedAt (framesOf rows) l = some supports)
    (localFrame : ∀ e : Region × Change, ownPrivate (origins.at l) privateRoots e.1 = true →
      Supported [e] body before after)
    (callbacks : ∀ parameter state, invocation (origins.at l) params P.toArray[l]!.expression = some parameter →
      let d := (atCall (origins.at l) privateRoots parameter state P.toArray[l]!.expression).demand
      d ∈ (publication rows).demands → Supported d.support.normal entry before after) :
    ∀ S ∈ supports, Supported S body before after := by
  unfold SinglePass.framedAt at frame
  obtain ⟨pair, found, rfl⟩ := Option.map_eq_some_iff.mp frame
  have atLabel := List.find?_some found
  have member := List.mem_of_find?_eq_some found
  obtain ⟨row, hr, rfl⟩ := List.mem_map.mp member
  simp only [beq_iff_eq] at atLabel
  subst l
  obtain ⟨parameter,state,hi,hc⟩ := row.source
  rw [hc]
  apply atCall_supported (reached_entryRoots checked values run) localFrame
  apply callbacks parameter state hi
  simp only [publication,List.mem_eraseDups,List.mem_map]
  exact ⟨row,hr,congrArg Candidate.demand hc⟩

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

theorem replay_accepted {σ ι : Type} [Labels ι] [StoreView σ ι] {G : NormalGraph ι} {I : InstanceImageCheck G}
    {r : SourceRequest σ ι} {call : TolerantFrames.Target.RunCall G I} {published output : Interface}
    (ok : replay r call published = .ok output) :
    output = published ∧ ∃ after, call.AcceptsWalk after ∧ summariesChecked r after.summaries.toList = true := by
  generalize hr : call.result = result
  obtain ⟨outcome,counts,after,trace⟩ := result
  cases outcome <;> simp [replay,hr,Except.pure,Except.bind,Bind.bind,Pure.pure,throw] at ok
  split at ok <;> try contradiction
  cases ok
  exact ⟨rfl,after,⟨counts,trace,hr⟩,by simpa using ‹¬summariesChecked r after.summaries.toList = false›⟩

/-- The framed replay checks every exit bound claimed by the source, including
a bound inferred by ordinary elaboration. -/
def producerRunBound [Labels ι] [StoreView σ ι] (r : SourceRequest σ ι) : Option RunBound :=
  if r.footprint != .top || r.onThrow || r.fresh || r.stated.isSome then
    some (RunBound.ofRequest r.footprint r.onThrow r.fresh)
  else none

/-- Produce the annotated declaration's interface from its body alone.
Only publish a proposal that survives a check at that interface. -/
def infer (f : FilePlans) (i fuel : Nat) (params : List Nat) : Except String Interface := do
  let some plan := f.plans[i]? | throw "no member at that position"
  let .graph _ _ r ← (← plan).certify
  if r.qualification.isSome || r.async then
    throw (CallbackPreservation.scopeRefusal "ordinaryProducerGraph" "callback preservation needs a synchronous ordinary member")
  if r.regional.isSome then throw (CallbackPreservation.scopeRefusal "ordinaryProducerGraph" "callback preservation of a stated regional bound is unavailable")
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
  let bound := producerRunBound r
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

namespace Verification.SourceClaimJson.CallbackInferencePlan

/-- An operand named in the syntactic prefix retains its index and value
through one expansion, irrespective of how many elements were supplied. -/
theorem positionalPrefix_splice {pre post : List Tm} {t : Tm} {i : Nat} {a : Tm}
    (named : (positionalPrefix (pre ++ .spread t :: post))[i]? = some a)
    (elements : List Tm) : (pre ++ elements ++ post)[i]? = some a := by
  induction pre generalizing i with
  | nil => simp [positionalPrefix, ordinaryActual] at named
  | cons head tail ih =>
    by_cases regular : ordinaryActual head = true
    · cases i with
      | zero => simpa [positionalPrefix, List.takeWhile, regular] using named
      | succ i =>
        apply ih
        simpa [positionalPrefix, List.takeWhile, regular] using named
    · simp [positionalPrefix, regular] at named

end Verification.SourceClaimJson.CallbackInferencePlan
