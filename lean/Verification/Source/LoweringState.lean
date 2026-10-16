import Verification.Source.SourceRequests
import Verification.Source.SourceClaims
import Verification.Source.Fragment
import Verification.Source.SourceFacts

/-! Owns lexical slots and the mutable graph construction state. -/
namespace Verification.SourceExtraction
open CallEffects (Arrow RestArrow Contract Effect)
open Lean ProgramTyping PositiveRules ControlFlow CertificateProducer RequestJson
open Fragment LabelStore
open EquationGraphs (Tree)

section
variable {ι : Type} [Labels ι]

def distinct [BEq α] (xs : List α) : Bool := xs.eraseDups.length == xs.length

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
  deriving Repr

@[nospecialize] def held (d : Descriptor) : ScopeBinding ι := { source := d }

/-- Explanatory projection: what a reader is shown, with the storage dropped. -/
@[nospecialize] def sources (scope : List (ScopeBinding ι)) : List Descriptor := scope.map (·.source)

/-- Name lookup is unchanged: descriptors carry the same names in the same
order, and an unnamed one can never match a source identifier. -/
@[nospecialize] def names (scope : List (ScopeBinding ι)) : List String := scope.map (·.source.name)

/-- The one place a source name becomes a slot, so no site can decide for
itself whether a name denotes a value or a location. -/
@[nospecialize] def resolve (scope : List (ScopeBinding ι)) (name : String) : Option (Nat × (Storage ι)) := do
  let i ← (names scope).idxOf? name
  let b ← scope[i]?
  return (i, b.storage)

/-- Only slots holding the value itself may be substituted by a guard's saved
value: an immutable one, or a mutable one no write has rebound since the
value was saved (a write clears the saved aliases, `executePlanTail`). -/
@[nospecialize] def valueSlot (scope : List (ScopeBinding ι)) (name : String) : Option Nat := do
  match ← resolve scope name with
  | (i, .value) | (i, .slot _) => return i
  | (_, .cell ..) => none

/-- State local to one compiled graph. A closure begins with an empty frame
and restores its enclosing frame as a whole. -/
private structure GraphFrame where
  program : Program := []
  /-- Computed types of saved execution-plan values, scoped to their bindings. -/
  executionTypes : List (String × Ty Tree) := []
  /-- Immutable aliases retained by evaluated operands for predicate refinement. -/
  executionOrigins : List (String × Fragment.Expr) := []
  /-- Prepared atoms consume saved operands; the plan owns source observations. -/
  atomicPrepared : Bool := false
  /-- Source metadata for a primitive whose executable operands are saved values. -/
  executionOriginal : Option Fragment.Expr := none
  /-- A saved method call passes this already evaluated receiver. -/
  executionReceiver : Option String := none
  /-- One source statement whose ownership gate permits a fresh local copy. -/
  executionOwned : Option Span := none
  claims : List (PointClaim Tree) := []
  sourceMap : SourceMap := []
  assertions : List (Nat × HeapKnowledge.Knowledge) := []
  /-- Full statement-entry interfaces; absent assertions mean empty knowledge. -/
  cuts : List Nat := []
  /-- While a `try` body or handler is compiled: where a throw out of a node
  goes, as a target over the handler's scope (the thrown value's slot, then
  the scope of the `try`), and the length of the `try`'s scope. Every node
  emitted meanwhile whose expression may throw names it. -/
  handler : Option (Target × Nat) := none
  /-- The `let` declarations of the graph's body held in cells
  (`cellLocals`), by name and declaring statement. -/
  cells : List (String × Option Span) := []

/-- Equation growth, obligations and nested code are shared across graph frames. -/
private structure Built extends GraphFrame where
  /-- The graph under construction: the claims' table, grown by annotations. -/
  types : EquationStore.State
  flowTargets : List (Nat × Target) := []
  obligations : List (ExpressionClaims.Required Tree) := []
  /-- Labels the program mentions but no claim does, such as a pattern's
  literal index: search hints, never part of what is checked. -/
  hints : List Tree := []
  /-- The graph code the body creates, nested code first, each at each
  signature it offers, and what the source says of each code's graph. -/
  codes : List (CodeRequest Tree) := []
  codeSources : List CodeSource := []
  /-- Plans for nodes whose derivation the lowering already knows: search
  hints only, rendered where they can be and never obligations. -/
  nodePlans : List (DirectProof.Plan Tree) := []
  /-- The key-adding write sites of the body (`growSites`): the writes that
  may add a key, by copying their owned object, and the bindings holding it. -/
  grows : List GrowSite := []

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

/-- The scope owner restores precisely its temporary fields. Shared successful
updates survive; a failure carries no state, and a catch resumes at its entry. -/
private def scopeState (enter : Built → Built) (restore : Built → Built → Built)
    (action : Compiler α) : Compiler α := ⟨fun before => do
  let (value,after) ← action.run (enter before)
  return (value,restore before after)⟩

/-- Compile a graph in a fresh frame and resume the enclosing graph frame. -/
def withFreshGraph (action : Compiler α) : Compiler α :=
  scopeState (fun before => { before with toGraphFrame := {} })
    (fun before after => { after with toGraphFrame := before.toGraphFrame }) action

@[nospecialize] def table : Compiler EquationStore.State := readBuilt (·.types)

@[nospecialize] def lower (m : SourceTypes.Lowering α) : Compiler α := ⟨fun s => do
  let (a,T) ← m.run s.types
  return (a,{ s with types := T })⟩

/-- Saved values and their predicate aliases at one execution-plan continuation. -/
structure ExecutionBindings where
  types : List (String × Ty Tree)
  origins : List (String × Fragment.Expr)

def executionBindings : Compiler ExecutionBindings :=
  readBuilt fun s => ⟨s.executionTypes,s.executionOrigins⟩

def executionType (name : String) : Compiler (Option (Ty Tree)) :=
  readBuilt fun s => s.executionTypes.lookup name

def executionOrigins : Compiler (List (String × Fragment.Expr)) := readBuilt (·.executionOrigins)

/-- A saved binding's computed type is visible for its continuation. -/
def withExecutionType (name : String) (A : Ty Tree) (action : Compiler α) : Compiler α :=
  scopeState (fun s => { s with executionTypes := (name,A)::s.executionTypes })
    (fun before after => { after with executionTypes := before.executionTypes }) action

/-- A branch's saved values and aliases are visible within that branch. -/
def withExecutionBindings (bindings : ExecutionBindings) (action : Compiler α) : Compiler α :=
  scopeState (fun s => { s with executionTypes := bindings.types, executionOrigins := bindings.origins })
    (fun before after => { after with
      executionTypes := before.executionTypes
      executionOrigins := before.executionOrigins }) action

def withExecutionOrigins (origins : List (String × Fragment.Expr)) (action : Compiler α) : Compiler α :=
  scopeState (fun s => { s with executionOrigins := origins })
    (fun before after => { after with executionOrigins := before.executionOrigins }) action

/-- An atom is prepared by its execution plan or names a saved plan value. -/
def isPreparedAtom (e : Fragment.Expr) : Compiler Bool := readBuilt fun s =>
  s.atomicPrepared || (match e with
    | .var _ name => (s.executionTypes.lookup name).isSome
    | _ => false)

def originalExpression : Compiler (Option Fragment.Expr) := readBuilt (·.executionOriginal)
def savedReceiver : Compiler (Option String) := readBuilt (·.executionReceiver)
def ownedWrite : Compiler (Option Span) := readBuilt (·.executionOwned)

def withPreparedAtom (original : Fragment.Expr) (action : Compiler α) : Compiler α :=
  scopeState (fun s => { s with atomicPrepared := true, executionOriginal := some original })
    (fun before after => { after with
      atomicPrepared := before.atomicPrepared
      executionOriginal := before.executionOriginal }) action

def withSavedInvocation (original : Fragment.Expr) (receiver : String)
    (action : Compiler α) : Compiler α :=
  scopeState (fun s => { s with
      atomicPrepared := true
      executionOriginal := some original
      executionReceiver := some receiver })
    (fun before after => { after with
      atomicPrepared := before.atomicPrepared
      executionOriginal := before.executionOriginal
      executionReceiver := before.executionReceiver }) action

/-- The ownership gate covers one source statement's elaboration. -/
def withOwnedWrite (source : Span) (enabled : Bool) (action : Compiler α) : Compiler α :=
  scopeState (fun s => if enabled then { s with executionOwned := some source } else s)
    (fun before after => { after with executionOwned := before.executionOwned }) action

/-- Every throwing node emitted in the scope names this handler. -/
def withHandler (handler : Option (Target × Nat)) (action : Compiler α) : Compiler α :=
  scopeState (fun s => { s with handler := handler })
    (fun before after => { after with handler := before.handler }) action

def currentHandler : Compiler (Option (Target × Nat)) := readBuilt (·.handler)

/-- The body compiled in this frame holds these `let`s in cells. -/
def withLocalCells (cells : List (String × Option Span)) (action : Compiler α) : Compiler α :=
  scopeState (fun s => { s with cells := cells })
    (fun before after => { after with cells := before.cells }) action

def localCells : Compiler (List (String × Option Span)) := readBuilt (·.cells)

/-- A recursive source body owns its memo of cyclic graph entries. -/
def withFreshFlowTargets (action : Compiler α) : Compiler α :=
  scopeState (fun s => { s with flowTargets := [] })
    (fun before after => { after with flowTargets := before.flowTargets }) action

def flowTarget (id : Nat) : Compiler (Option Target) := readBuilt fun s => s.flowTargets.lookup id

def rememberFlowTarget (id : Nat) (target : Target) : Compiler Unit :=
  updateBuilt fun s => { s with flowTargets := (id,target)::s.flowTargets }

/-- The refusal of a write that may add a key through the parameter `n`. -/
def parameterGrowth (write n : String) : String :=
  s!"{write} through the parameter '{n}' may add the key: the caller may hold the object at a \
    type that leaves the key absent, or optional at another type, and see it added at this one"

/-- The bindings holding the object a key-adding write at `span` copies, where
it is a site (`growSites`). -/
def growthHolders (span : Span) : Compiler (Option (List Holder)) :=
  readBuilt fun s => (s.grows.find? (·.span == span)).map (·.holders)

/-- Node allocation appends its claim and source-map slot at the same index. -/
def appendNode (node : ControlFlow.Node) (claim : PointClaim Tree) : Compiler Target := ⟨fun s =>
  .ok (⟨s.program.length,none⟩,{ s with
    program := s.program ++ [node]
    claims := s.claims ++ [claim]
    sourceMap := s.sourceMap ++ [none] })⟩

def recordNodeSource (target : Target) (source : SourceMapEntry) : Compiler Unit :=
  updateBuilt fun s => { s with sourceMap := s.sourceMap.set target.label (some source) }

/-- Complete a reserved cyclic entry with its already elaborated successor. -/
def completeFlowEntry (reserved target : Target) : Compiler Unit :=
  updateBuilt fun s => { s with program := s.program.set reserved.label ⟨.nul,.effect target,none⟩ }

def recordAssertion (target : Target) (knowledge : HeapKnowledge.Knowledge) : Compiler Unit :=
  updateBuilt fun s => { s with assertions := s.assertions ++ [(target.label,knowledge)] }

def recordCut (target : Target) : Compiler Unit :=
  updateBuilt fun s => { s with cuts := target.label::s.cuts }

def recordObligation (required : ExpressionClaims.Required Tree) : Compiler Unit :=
  updateBuilt fun s => { s with obligations := s.obligations ++ [required] }

def recordNodePlan (plan : DirectProof.Plan Tree) : Compiler Unit :=
  updateBuilt fun s => { s with nodePlans := s.nodePlans ++ [plan] }

def recordHints (labels : List Tree) : Compiler Unit :=
  updateBuilt fun s => { s with hints := labels ++ s.hints }

/-- A nested code request and its source account occupy the same table index. -/
def recordCode (request : CodeRequest Tree) (source : CodeSource) : Compiler Unit :=
  updateBuilt fun s => { s with codes := s.codes ++ [request], codeSources := s.codeSources ++ [source] }

/-- Read-only outputs of one compiled graph. -/
structure LoweredGraph where
  program : Program
  claims : List (PointClaim Tree)
  source : CodeSource

private def graphOutput (s : Built) : LoweredGraph :=
  ⟨s.program,s.claims,⟨s.sourceMap,s.assertions,s.cuts⟩⟩

def graphResult : Compiler LoweredGraph := readBuilt graphOutput

/-- Extraction receives the graph and shared outputs through this projection. -/
structure LoweringResult extends LoweredGraph where
  types : EquationStore.State
  obligations : List (ExpressionClaims.Required Tree)
  hints : List Tree
  codes : List (CodeRequest Tree)
  codeSources : List CodeSource
  nodePlans : List (DirectProof.Plan Tree)

/-- Run one source unit with its equation table and admitted ownership sites. -/
def runCompiler (types : EquationStore.State) (grows : List GrowSite) (action : Compiler α) :
    Except String (α × LoweringResult) := do
  let (value,s) ← action.run { types := types, grows := grows }
  return (value,{
    toLoweredGraph := graphOutput s
    types := s.types
    obligations := s.obligations
    hints := s.hints
    codes := s.codes
    codeSources := s.codeSources
    nodePlans := s.nodePlans })

end
end Verification.SourceExtraction
