import Verification.Programs.CellClaims
import Verification.Source.SourceRequests
import Verification.Source.SourceClaims
import Verification.Source.Fragment
import Verification.Source.ExpressionPlan
import Verification.Source.SourceFacts

/-! Owns lexical slots and the mutable graph construction state. -/
namespace Verification.SourceExtraction
open CallEffects (Arrow RestArrow Contract Effect)
open Lean ProgramTyping PositiveRules ControlFlow CertificateProducer RequestJson
open Fragment LabelStore
open EquationGraphs (Tree)

section
variable {ι : Type} [Labels ι]

/-- Whether no two of `xs` are equal (`xs.eraseDups.length == xs.length`),
decided in one pass. -/
def distinct [BEq α] [Hashable α] (xs : List α) : Bool :=
  (xs.foldlM (init := ({} : Std.HashSet α)) fun (seen : Std.HashSet α) x =>
    if seen.contains x then none else some (seen.insert x)).isSome

/-- What a scope slot holds. A value slot holds the value itself. A cell slot
holds the identity of a private cell this lowering allocated: `contract` is the
stable storage type every assignment is checked against, and `reference` is the
slot's own type, interned once when the binding was declared so that building
an environment stays a pure projection.

(Storage ι) comes from source declarations and assignments. A producer's
claim about `x` describes what the cell currently holds, which is exactly what
must not become the type of the slot holding its identity. -/
inductive Storage (ι : Type) where
  | value
  /-- A mutable binding every closure that mentions it sees at its value when
  the closure was created (`cellLocals`): a slot of its activation, rebound
  by each write, whose value is checked against `contract`. What the
  producer says `x` is at a point is this slot's type there. -/
  | slot (contract : Ty ι)
  | cell (contract : Ty ι) (reference : Ty ι)
  /-- An early binding (SOURCE-ELABORATION.md, "Lexical bindings before
  initialization"): a cell allocated where its statement list is entered,
  holding the activation's uninitialized marker until the declaration
  writes it, at the contract `contract ∪ U`; `reference` is the cell's own
  type. Every mention is a checked access: the contents are tested for the
  marker's key, a throw where it is held, the contents at `contract`
  otherwise. `mutable` is false for a `const`, which only its declaration
  writes. -/
  | early (contract : Ty ι) (reference : Ty ι) (mutable : Bool)
  deriving Repr, Inhabited

/-- A scope slot: how the source names it, and what it holds. `Descriptor` is
explanatory source-map data that cannot affect acceptance, so the storage that
decides lowering lives here and is projected away before anything is emitted. -/
structure ScopeBinding (ι : Type) where
  source : Descriptor
  storage : Storage ι := .value
  /-- A module function's slot: its type is its own source signature, never a
  producer claim, and it is a value slot, so no assignment can reach it. -/
  fixed : Option (Ty ι) := none
  /-- A `let`'s cell: the types of the slots below it when it was allocated,
  whose records' fields its fresh location differs from. -/
  apart : Option (List (Ty ι)) := none
  /-- A constant bound to an object or array it allocated: its fields are
  fresh, so they differ from every older cell's location. -/
  fresh : Bool := false
  /-- A parameter: bound before the body runs, so before any cell the body
  allocates, and at the same time as an assigned parameter's cell. -/
  param : Bool := false
  /-- A closure's capture: a cell it holds was allocated by the code that
  created the closure, so no fact of that allocation holds at the closure's
  entry. -/
  captured : Bool := false
  /-- A module cell of the unit's module (SOURCE-ELABORATION.md, "Module
  cells"), by its binding's name: two module cells are two locations, which
  the unit's entry assumes (`moduleCellSeparation`). A closure's capture of
  it states no such fact. -/
  moduleCell : Option String := none
  /-- An administrative value saved from a named member path. -/
  witness : Option (String × List PropKey) := none
  /-- A `for...of` loop's iterator: a fresh object, every own location of
  which differs from the fields the records of the slots below it named
  when it was created (`apart`). -/
  iterator : Bool := false
  deriving Repr

@[nospecialize] def held (d : Descriptor) : ScopeBinding ι := { source := d }

/-- Explanatory projection: what a reader is shown, with the storage dropped. -/
@[nospecialize] def sources (scope : List (ScopeBinding ι)) : List Descriptor := scope.map (·.source)

/-- Name lookup is unchanged: descriptors carry the same names in the same
order, and an unnamed one can never match a source identifier. -/
@[nospecialize] def names (scope : List (ScopeBinding ι)) : List String := scope.map (·.source.name)

/-- The first slot named `name`: `(names scope).idxOf? name`, read in one
pass over the scope. -/
@[nospecialize] def nameIndex (scope : List (ScopeBinding ι)) (name : String) : Option Nat :=
  scope.findIdx? (·.source.name == name)

/-- Whether a slot is named `name`: `(names scope).contains name`. -/
@[nospecialize] def hasName (scope : List (ScopeBinding ι)) (name : String) : Bool :=
  scope.any (·.source.name == name)

/-- The first slot described by `d`: `(sources scope).idxOf? d`. -/
@[nospecialize] def sourceIndex (scope : List (ScopeBinding ι)) (d : Descriptor) : Option Nat :=
  scope.findIdx? (·.source == d)

@[nospecialize] private def resolveFrom (name : String) : List (ScopeBinding ι) → Nat → Option (Nat × Storage ι)
  | [], _ => none
  | b :: bs, i => if b.source.name == name then some (i, b.storage) else resolveFrom name bs (i + 1)

/-- The one place a source name becomes a slot, so no site can decide for
itself whether a name denotes a value or a location: the first slot named
`name`, with its storage. -/
@[nospecialize] def resolve (scope : List (ScopeBinding ι)) (name : String) : Option (Nat × (Storage ι)) :=
  resolveFrom name scope 0

/-- Only slots holding the value itself may be substituted by a guard's saved
value: an immutable one, or a mutable one no write has rebound since the
value was saved (a write clears the saved aliases, `executePlanTail`). -/
@[nospecialize] def valueSlot (scope : List (ScopeBinding ι)) (name : String) : Option Nat := do
  match ← resolve scope name with
  | (i, .value) | (i, .slot _) => return i
  | (_, .cell ..) | (_, .early ..) => none

/-- Where a linear fact's term rooted at a binding reads (ARITHMETIC.md,
"Terms for bindings held in cells"): a value or a slot at its own slot; a
cell at its slot, its contents' field `value` first. An early binding, whose
cell may hold the uninitialized marker, roots none. -/
@[nospecialize] def termRoot (scope : List (ScopeBinding ι)) (name : String) : Option (Nat × List String) := do
  match ← resolve scope name with
  | (i, .value) | (i, .slot _) => return (i, [])
  | (i, .cell ..) => return (i, ["value"])
  | (_, .early ..) => none

/-- Paths identify source reads independently of their occurrence spans. -/
def memberPath : Fragment.Expr → Option (String × List PropKey)
  | .var _ name => some (name, [])
  | .read _ field receiver => do
    let (root, fields) ← memberPath receiver
    return (root, fields ++ [field])
  | _ => none

/-- A path's witness: its root a slot holding the value itself
(`valueSlot`), which identifies one receiver across reads until a write
rebinds it; a link from the root's slot, which every incoming edge checks,
ends at that write. -/
@[nospecialize] def pathWitness (scope : List (ScopeBinding ι)) (e : Fragment.Expr) : Option Nat := do
  let path ← memberPath e
  if path.2.isEmpty then none else do
    let _ ← valueSlot scope path.1
    scope.findIdx? (·.witness == some path)

/-- Read paths in an execution plan, including both arms and their tests. -/
partial def planPaths : SourceExecution.Plan → List (String × List PropKey)
  | .observe _ p => planPaths p
  | .sequence _ _ p q => planPaths p ++ planPaths q
  | .choose _ _ _ _ p y n => planPaths p ++ planPaths y ++ planPaths n
  | .atom _ (.evaluate e _ _) =>
    match memberPath e with
    | some p => if p.2.isEmpty then [] else [p]
    | none => []
  | .atom .. => []

partial def testedPaths : SourceExecution.Plan → List (String × List PropKey)
  | .observe _ p => testedPaths p
  | .sequence _ _ p q => testedPaths p ++ testedPaths q
  | .choose _ _ _ _ p y n => planPaths p ++ testedPaths y ++ testedPaths n
  | .atom .. => []

/-- State local to one compiled graph. A closure begins with an empty frame
and restores its enclosing frame as a whole. -/
private structure GraphFrame where
  /-- The graph's nodes, claims and source-map slots, one per node and
  extended at the end: lists once the graph is complete (`graphOutput`). -/
  program : Array ControlFlow.Node := #[]
  /-- Computed types of saved execution-plan values, scoped to their bindings. -/
  executionTypes : List (String × Ty Tree) := []
  /-- Immutable aliases retained by evaluated operands for predicate refinement. -/
  executionOrigins : List (String × Fragment.Expr) := []
  /-- Saved values read from a member path, each with the path's witness
  slot, which holds the value read: a promise about the saved value is one
  about the witness, a claim the graph's edges check. Read by promise
  narrowing alone, never by predicates or dispatch. -/
  executionWitnesses : List (String × String) := []
  /-- Prepared atoms consume saved operands; the plan owns source observations. -/
  atomicPrepared : Bool := false
  /-- Source metadata for a primitive whose executable operands are saved values. -/
  executionOriginal : Option Fragment.Expr := none
  /-- A saved method call passes this already evaluated receiver. -/
  executionReceiver : Option String := none
  /-- One source statement whose ownership gate permits a fresh local copy. -/
  executionOwned : Option Span := none
  claims : Array (PointClaim Tree) := #[]
  sourceMap : Array (Option SourceMapEntry) := #[]
  assertions : Array (Nat × HeapKnowledge.Knowledge) := #[]
  /-- The index facts the producer supplies at each statement entry, apart
  from its assertion: candidates a search keeps where every edge into the
  entry establishes them. -/
  candidates : Array (Nat × List HeapKnowledge.IndexAtom) := #[]
  /-- Statement entries; absent assertions mean empty knowledge. -/
  cuts : List Nat := []
  /-- While a `try` body or handler is compiled: where a throw out of a node
  goes, as a target over the handler's scope (the thrown value's slot, then
  the scope of the `try`), and the length of the `try`'s scope. Every node
  emitted meanwhile whose expression may throw names it. -/
  handler : Option (Target × Nat) := none
  /-- The `let` declarations of the graph's body held in cells
  (`cellLocals`), by name and declaring statement. -/
  cells : List (String × Option Span) := []
  /-- While a type guard's body is compiled: a return is claimed at its
  value's own type, the answer its promise is checked against. -/
  answers : Bool := false
  /-- While a constant's function-literal initializer is compiled: the
  constant, which the literal's body may read as its self entry. -/
  selfConstant : Option String := none
  /-- The graph's constants holding a condition's value, by name (the
  fragment admits no shadowing), with the condition: where one is `true`,
  the lowering proposes what the condition narrows, which the checker
  establishes through the constant's implications. -/
  conditionConstants : List (String × Fragment.Expr) := []

/-- Inclusion for source contracts through the common subtype operation,
retaining the execution outcome. -/
@[nospecialize] def withinResult (T : EquationStore.State) (C A : List Tree) :
    PositiveCertificates.ComparisonResult Unit :=
  (CertificateProducer.comparisonUsing (SourceTypes.graph T) (StoreView.images T) C A).map fun _ => ()

/-- Optional inference probes use only established inclusion. -/
@[nospecialize] def within (T : EquationStore.State) (C A : List Tree) : Bool :=
  (withinResult T C A).accepted

/-- Equation growth, obligations and nested code are shared across graph frames. -/
private structure Built extends GraphFrame where
  /-- The graph under construction: the claims' table, grown by annotations. -/
  types : EquationStore.State
  /-- How many steps have changed `types`: `lower` is the one that does. -/
  generation : Nat := 0
  /-- `within`'s answers at `types`, each pair's computed once: `lower`
  empties them, and a restored state restores them with `types`. -/
  withinAnswers : Std.HashMap (List Tree × List Tree) Bool := {}
  /-- `commonFields`' answers at `types`: `lower` empties them. -/
  fieldAnswers : Std.HashMap (List Tree) (List PropKey) := {}
  flowTargets : List (Nat × Target) := []
  obligations : Array (ExpressionClaims.Required Tree) := #[]
  /-- Labels the program mentions but no claim does, such as a pattern's
  literal index: search hints, never part of what is checked. -/
  hints : List Tree := []
  /-- The graph code the body creates, nested code first, each at each
  signature it offers, and what the source says of each code's graph. -/
  codes : Array (CodeRequest Tree) := #[]
  codeSources : Array CodeSource := #[]
  /-- Plans for nodes whose derivation the lowering already knows: search
  hints only, rendered where they can be and never obligations. -/
  nodePlans : Array (DirectProof.Plan Tree) := #[]
  /-- The key-adding write sites of the body (`growSites`): the writes that
  may add a key, by copying their owned object, and the bindings holding it. -/
  grows : List GrowSite := []
  /-- Native constructor bindings whose audited contract allocates an
  unpublished object identity, beyond own-location freshness. -/
  freshConstructors : List (String × Span) := []
  /-- The module cells whose objects the module owns (`ownedModuleCells`):
  a key-adding write on one is the copy of its object written to the cell. -/
  moduleOwned : List String := []

/-- Source-validation failures that already know their source site use the same
structured channel as proof obligations. Keeping the diagnostic construction
here prevents an adapter check from degrading into an unlocated exception. -/
def locatedRefusal (T : EquationStore.State) (pos : Span)
    (role : DirectObligation.SourceRole) (reason : String) : String :=
  RequestJson.withDiagnostic s!"source refusal at [{pos.1},{pos.2}): {reason}"
    ([("kind",toJson "source-refusal"),("phase",toJson "request-validation"),
     ("outcome",toJson RequestJson.DiagnosticOutcome.notEstablished),("id",toJson s!"refusal:{pos.1}"),
     ("sourceMap",toJson (SourceMapEntry.mk pos role.wire none [])),
     ("reason",toJson reason),("fuel",toJson 0)] ++ (StoreView.projection T []).fields)

/-- Lowering actions compose through their operations. The constructor and raw
runner belong to this module; consumers have no general state instance. -/
structure Compiler (α : Type) where
  private mk ::
  private run : StateT Built (Except String) α

/-- Partial lowering functions have a failure action at every result type. -/
instance : Inhabited (Compiler α) := ⟨⟨fun _ => .error ""⟩⟩

instance : Monad Compiler where
  pure a := ⟨fun s => .ok (a,s)⟩
  bind action next := ⟨fun s => do
    let (a,s) ← action.run s
    (next a).run s⟩

instance : MonadExceptOf String Compiler where
  throw reason := ⟨fun _ => .error reason⟩
  tryCatch action handler := ⟨fun s =>
    match action.run s with
    | .ok result => .ok result
    | .error reason => (handler reason).run s⟩

instance : MonadLift (Except String) Compiler where
  monadLift action := ⟨fun s => do return (← action,s)⟩

private def readBuilt (f : Built → α) : Compiler α := ⟨fun s => .ok (f s,s)⟩

private def updateBuilt (f : Built → Built) : Compiler Unit := ⟨fun s => .ok ((),f s)⟩

/-- The scope owner restores precisely its temporary fields, `save`d at its
entry. Shared successful updates survive; a failure carries no state, and a
catch resumes at its entry. Only the saved fields stay referenced while the
action runs, so the graph's arrays are extended in place. -/
private def scopeState (save : Built → σ) (enter : Built → Built) (restore : σ → Built → Built)
    (action : Compiler α) : Compiler α := ⟨fun before => do
  let saved := save before
  let (value,after) ← action.run (enter before)
  return (value,restore saved after)⟩

/-- Compile a graph in a fresh frame and resume the enclosing graph frame. -/
def withFreshGraph (action : Compiler α) : Compiler α :=
  scopeState (·.toGraphFrame) (fun before => { before with toGraphFrame := {} })
    (fun frame after => { after with toGraphFrame := frame }) action

@[nospecialize] def table : Compiler EquationStore.State := readBuilt (·.types)

@[nospecialize] def lower (m : SourceTypes.Lowering α) : Compiler α := ⟨fun s => do
  let (a,T) ← m.run s.types
  return (a,{ s with types := T, generation := s.generation + 1, withinAnswers := {}, fieldAnswers := {} })⟩

/-- The store with its generation: `withinAt` reads `within`'s answers at
it while no step has changed it since. -/
@[nospecialize] def tableAt : Compiler (EquationStore.State × Nat) := readBuilt fun s => (s.types, s.generation)

/-- `within T`, for the store `T` of generation `gen` (`tableAt`): read from
the answers at the store while it is still that generation's. -/
@[nospecialize] def withinAt (T : EquationStore.State) (gen : Nat) (C A : List Tree) : Compiler Bool := ⟨fun s =>
  if s.generation != gen then .ok (within T C A, s) else
  match s.withinAnswers[(C, A)]? with
  | some b => .ok (b, s)
  | none =>
    let b := within T C A
    .ok (b, { s with withinAnswers := s.withinAnswers.insert (C, A) b })⟩

/-- The fields every record of a type names: where each of its clauses is a
record naming them, the locations of an object of the type. -/
@[nospecialize] def commonFields (G : Verification.PositiveGraphs.NormalGraph ι) (A : Ty ι) : List PropKey :=
  match PositiveRules.expand G A with
  | cs@((.refs fs _ vs _ _ _ _) :: _) =>
    -- The fields in order, each at its first occurrence.
    let (_, fields) := (fs.map Prod.fst ++ vs.map Prod.fst).foldl (init := (({} : Std.HashSet PropKey), #[]))
      fun (seen, out) k => if seen.contains k then (seen, out) else (seen.insert k, out.push k)
    fields.toList.filter (HeapExpressionRules.fieldOperand cs)
  | _ => []

/-- `commonFields` of each of `As` at the store, each type's computed once
while no step changes the store: a function answering each of them. -/
@[nospecialize] def commonFieldsOf (As : List (Ty Tree)) : Compiler (Ty Tree → List PropKey) := ⟨fun s =>
  let G := SourceTypes.graph s.types
  let answers := As.foldl (init := s.fieldAnswers) fun m A =>
    if m.contains A then m else m.insert A (commonFields G A)
  .ok ((fun A => answers[A]?.getD (commonFields G A)), { s with fieldAnswers := answers })⟩

/-- The type of an early binding's uninitialized marker, `U` (SOURCE-ELABORATION.md,
"Lexical bindings before initialization"): the object owning the marker's
key, at `undefined`. -/
@[nospecialize] def uninitializedTy : Compiler (Ty Tree) :=
  lower (do return [← CellClaims.reference [(uninitializedKey, [Labels.undef])]])

/-- A write of a `const` early binding outside its declaration: JavaScript
throws a `TypeError` there (SetMutableBinding of an immutable binding), a
throw the model does not state, so the write is refused at its location. -/
def constantWriteRefusal (pos : Span) (name : String) : Compiler String := do
  return locatedRefusal (← table) pos .expressionClaim
    s!"a write of the constant '{name}': JavaScript throws a TypeError where a `const` is assigned"

/-- An early binding's contract without the marker: what a checked access
yields and what a write is checked at. -/
@[nospecialize] def initializedContract (stored : Ty Tree) : Compiler (Ty Tree) := do
  let U ← uninitializedTy
  return stored.filter (!U.contains ·)

/-- The contract of a module cell whose object the module owns
(`ownedModuleCells`): its annotation `C`, each object clause stating that the
object's own keys exclude the prototype field and the host key, as an object
literal's do: an ordinary object of the default prototype. Every value the cell
holds is the literal or a copy of it at string keys, and the cell's every
write is checked at this contract. -/
@[nospecialize] def plainContract (C : Ty Tree) : Compiler (Ty Tree) := do
  let G := SourceTypes.graph (← table)
  let plain : KeyBound := ⟨false, [SourceTypes.protoField, hostKey]⟩
  let mut labels : List Tree := []
  for c in PositiveRules.expand G C do
    let c := match c with
      | .refs fs rs vs os ms ks st => .refs fs rs vs os ms (ks ++ [plain]) st
      | c => c
    labels := labels ++ [← lower (SourceTypes.use c)]
  return labels.eraseDups

/-- Saved values and their predicate aliases at one execution-plan continuation. -/
structure ExecutionBindings where
  types : List (String × Ty Tree)
  origins : List (String × Fragment.Expr)

def executionBindings : Compiler ExecutionBindings :=
  readBuilt fun s => ⟨s.executionTypes,s.executionOrigins⟩

def executionType (name : String) : Compiler (Option (Ty Tree)) :=
  readBuilt fun s => s.executionTypes.lookup name

def executionOrigins : Compiler (List (String × Fragment.Expr)) := readBuilt (·.executionOrigins)

def executionWitnesses : Compiler (List (String × String)) := readBuilt (·.executionWitnesses)

/-- The witness a saved value read from a member path names, where that read
is the witness's newest (`executionWitnesses` lists the newest first): a
later read of the path rebinds the witness, which then holds that read's
value. -/
def newestWitness (witnesses : List (String × String)) (name : String) : Option String := do
  let w ← witnesses.lookup name
  if (witnesses.find? (fun (p : String × String) => p.2 == w)).map Prod.fst == some name then some w else none

/-- A saved value read from a member path names the path's witness for its
continuation (`executionWitnesses`). -/
def withExecutionWitness (name witness : String) (action : Compiler α) : Compiler α :=
  scopeState (·.executionWitnesses) (fun s => { s with executionWitnesses := (name,witness)::s.executionWitnesses })
    (fun saved after => { after with executionWitnesses := saved }) action

/-- A saved binding's computed type is visible for its continuation. -/
def withExecutionType (name : String) (A : Ty Tree) (action : Compiler α) : Compiler α :=
  scopeState (·.executionTypes) (fun s => { s with executionTypes := (name,A)::s.executionTypes })
    (fun saved after => { after with executionTypes := saved }) action

/-- A branch's saved values and aliases are visible within that branch. -/
def withExecutionBindings (bindings : ExecutionBindings) (action : Compiler α) : Compiler α :=
  scopeState (fun s => (s.executionTypes, s.executionOrigins))
    (fun s => { s with executionTypes := bindings.types, executionOrigins := bindings.origins })
    (fun (types, origins) after => { after with
      executionTypes := types
      executionOrigins := origins }) action

def withExecutionOrigins (origins : List (String × Fragment.Expr)) (action : Compiler α) : Compiler α :=
  scopeState (·.executionOrigins) (fun s => { s with executionOrigins := origins })
    (fun saved after => { after with executionOrigins := saved }) action

/-- An atom is prepared by its execution plan or names a saved plan value. -/
def isPreparedAtom (e : Fragment.Expr) : Compiler Bool := readBuilt fun s =>
  s.atomicPrepared || (match e with
    | .var _ name => (s.executionTypes.lookup name).isSome
    | _ => false)

def originalExpression : Compiler (Option Fragment.Expr) := readBuilt (·.executionOriginal)
def savedReceiver : Compiler (Option String) := readBuilt (·.executionReceiver)
def ownedWrite : Compiler (Option Span) := readBuilt (·.executionOwned)

def withPreparedAtom (original : Fragment.Expr) (action : Compiler α) : Compiler α :=
  scopeState (fun s => (s.atomicPrepared, s.executionOriginal))
    (fun s => { s with atomicPrepared := true, executionOriginal := some original })
    (fun (prepared, original) after => { after with
      atomicPrepared := prepared
      executionOriginal := original }) action

def withSavedInvocation (original : Fragment.Expr) (receiver : String)
    (action : Compiler α) : Compiler α :=
  scopeState (fun s => (s.atomicPrepared, s.executionOriginal, s.executionReceiver))
    (fun s => { s with
      atomicPrepared := true
      executionOriginal := some original
      executionReceiver := some receiver })
    (fun (prepared, original, receiver) after => { after with
      atomicPrepared := prepared
      executionOriginal := original
      executionReceiver := receiver }) action

/-- The ownership gate covers one source statement's elaboration. -/
def withOwnedWrite (source : Span) (enabled : Bool) (action : Compiler α) : Compiler α :=
  scopeState (·.executionOwned) (fun s => if enabled then { s with executionOwned := some source } else s)
    (fun saved after => { after with executionOwned := saved }) action

/-- Every throwing node emitted in the scope names this handler. -/
def withHandler (handler : Option (Target × Nat)) (action : Compiler α) : Compiler α :=
  scopeState (·.handler) (fun s => { s with handler := handler })
    (fun saved after => { after with handler := saved }) action

/-- The body compiled in the scope is a type guard's when `answers` holds. -/
def withAnswers (answers : Bool) (action : Compiler α) : Compiler α :=
  scopeState (·.answers) (fun s => { s with answers := answers })
    (fun saved after => { after with answers := saved }) action

/-- The initializer compiled in the scope is the function literal of the
constant `name`, whose body may read it as its self entry. -/
def withSelfConstant (name : Option String) (action : Compiler α) : Compiler α :=
  scopeState (·.selfConstant) (fun s => { s with selfConstant := name })
    (fun saved after => { after with selfConstant := saved }) action

def currentSelfConstant : Compiler (Option String) := readBuilt (·.selfConstant)

def recordConditionConstant (name : String) (init : Fragment.Expr) : Compiler Unit :=
  updateBuilt fun s => { s with conditionConstants := (name, init) :: s.conditionConstants }

def conditionConstants : Compiler (List (String × Fragment.Expr)) := readBuilt (·.conditionConstants)

/-- The claim of a return of a value of type `A` in a body returning `R`. -/
def returnClaim (A R : Ty ι) : Compiler (Ty ι) := do
  return if (← readBuilt (·.answers)) then A else R

def currentHandler : Compiler (Option (Target × Nat)) := readBuilt (·.handler)

/-- The body compiled in this frame holds these `let`s in cells. -/
def withLocalCells (cells : List (String × Option Span)) (action : Compiler α) : Compiler α :=
  scopeState (·.cells) (fun s => { s with cells := cells })
    (fun saved after => { after with cells := saved }) action

def localCells : Compiler (List (String × Option Span)) := readBuilt (·.cells)

/-- A recursive source body owns its memo of cyclic graph entries. -/
def withFreshFlowTargets (action : Compiler α) : Compiler α :=
  scopeState (·.flowTargets) (fun s => { s with flowTargets := [] })
    (fun saved after => { after with flowTargets := saved }) action

def flowTarget (id : Nat) : Compiler (Option Target) := readBuilt fun s => s.flowTargets.lookup id

def rememberFlowTarget (id : Nat) (target : Target) : Compiler Unit :=
  updateBuilt fun s => { s with flowTargets := (id,target)::s.flowTargets }

/-- The refusal of a write that may add a key through the parameter `n`. -/
def parameterGrowth (write n : String) : String :=
  s!"{write} through the parameter '{n}' may add the key: the caller may hold the object at a \
    type that leaves the key absent, or optional at another type, and see it added at this one"

/-- Whether `n` names a module cell whose object the module owns
(`ownedModuleCells`). -/
def moduleOwnedName (n : String) : Compiler Bool := readBuilt fun s => s.moduleOwned.contains n

/-- The slot and storage of the module cell `n` holds, where the module owns
its object (`ownedModuleCells`) and `n` names that cell here, an early
binding's. -/
def moduleOwnedCell (scope : List (ScopeBinding Tree)) (n : String) :
    Compiler (Option (Nat × Storage Tree)) := do
  if !(← moduleOwnedName n) then return none
  match resolve scope n with
  | some (i, storage@(.early _ _ true)) => return some (i, storage)
  | _ => return none

/-- The bindings holding the object a key-adding write at `span` copies, where
it is a site (`growSites`). -/
def growthHolders (span : Span) : Compiler (Option (List Holder)) :=
  readBuilt fun s => (s.grows.find? (·.span == span)).map (·.holders)

/-- Node allocation appends its claim and source-map slot at the same index. -/
def appendNode (node : ControlFlow.Node) (claim : PointClaim Tree) : Compiler Target := ⟨fun s =>
  .ok (⟨s.program.size,none⟩,{ s with
    program := s.program.push node
    claims := s.claims.push claim
    sourceMap := s.sourceMap.push none })⟩

def recordNodeSource (target : Target) (source : SourceMapEntry) : Compiler Unit :=
  updateBuilt fun s => { s with sourceMap := s.sourceMap.setIfInBounds target.label (some source) }

/-- Complete a reserved cyclic entry with its already elaborated successor. -/
def completeFlowEntry (reserved target : Target) : Compiler Unit :=
  updateBuilt fun s => { s with program := s.program.setIfInBounds reserved.label ⟨.nul,.effect target,none⟩ }

def recordAssertion (target : Target) (knowledge : HeapKnowledge.Knowledge) : Compiler Unit :=
  updateBuilt fun s => { s with assertions := s.assertions.push (target.label,knowledge) }

def recordCandidates (target : Target) (atoms : List HeapKnowledge.IndexAtom) : Compiler Unit :=
  updateBuilt fun s => { s with candidates := s.candidates.push (target.label,atoms) }

def recordCut (target : Target) : Compiler Unit :=
  updateBuilt fun s => { s with cuts := target.label::s.cuts }

def recordObligation (required : ExpressionClaims.Required Tree) : Compiler Unit :=
  updateBuilt fun s => { s with obligations := s.obligations.push required }

def recordNodePlan (plan : DirectProof.Plan Tree) : Compiler Unit :=
  updateBuilt fun s => { s with nodePlans := s.nodePlans.push plan }

def recordHints (labels : List Tree) : Compiler Unit :=
  updateBuilt fun s => { s with hints := labels ++ s.hints }

/-- A nested code request and its source account occupy the same table index. -/
def recordCode (request : CodeRequest Tree) (source : CodeSource) : Compiler Unit :=
  updateBuilt fun s => { s with codes := s.codes.push request, codeSources := s.codeSources.push source }

/-- Read-only outputs of one compiled graph. -/
structure LoweredGraph where
  program : Program
  claims : List (PointClaim Tree)
  source : CodeSource

private def graphOutput (s : Built) : LoweredGraph :=
  ⟨s.program.toList,s.claims.toList,⟨s.sourceMap.toList,s.assertions.toList,s.candidates.toList,s.cuts⟩⟩

def graphResult : Compiler LoweredGraph := readBuilt graphOutput

/-- Extraction receives the graph and shared outputs through this projection. -/
structure LoweringResult extends LoweredGraph where
  types : EquationStore.State
  obligations : List (ExpressionClaims.Required Tree)
  hints : List Tree
  codes : List (CodeRequest Tree)
  codeSources : List CodeSource
  nodePlans : List (DirectProof.Plan Tree)

/-- Whether the callee resolves to an audited native allocation binding.
Shadowing locals and parameters have different declaration descriptors. -/
def freshNativeConstructor (scope : List (ScopeBinding Tree)) (callee : Fragment.Expr) : Compiler Bool := do
  let .var _ name := callee | return false
  let some (i, _) := resolve scope name | return false
  let some binding := scope[i]? | return false
  readBuilt fun s => s.freshConstructors.any fun (n, p) => binding.source == ⟨n, some p⟩

/-- Run one source unit with its equation table and admitted ownership sites. -/
def runCompiler (types : EquationStore.State) (grows : List GrowSite) (action : Compiler α)
    (freshConstructors : List (String × Span) := []) (moduleOwned : List String := []) :
    Except String (α × LoweringResult) := do
  let (value,s) ← action.run
    { types := types, grows := grows, freshConstructors := freshConstructors, moduleOwned := moduleOwned }
  return (value,{
    toLoweredGraph := graphOutput s
    types := s.types
    obligations := s.obligations.toList
    hints := s.hints
    codes := s.codes.toList
    codeSources := s.codeSources.toList
    nodePlans := s.nodePlans.toList })

end
end Verification.SourceExtraction
