-- Lowering/State.lean owns lexical slots and the mutable graph construction state.
import Verification.Source.Lowering.State
-- Lowering/Types.lean resolves source claims and type-directed expression operations.
import Verification.Source.Lowering.Types
-- Lowering/Observations.lean emits graph nodes and checks source heap observations.
import Verification.Source.Lowering.Observations
-- Lowering/Plans.lean builds direct proof plans for values, predicates and members.
import Verification.Source.Lowering.Plans
-- Lowering/Control.lean builds control transfers and their scope mappings.
import Verification.Source.Lowering.Control
-- Lowering/ClosureSetup.lean prepares closure signatures, parameters and captures.
import Verification.Source.Lowering.ClosureSetup
-- Lowering/Operands.lean elaborates saved spread and method operands.
import Verification.Source.Lowering.Operands
-- Lowering/Callbacks.lean declares the recursive lowering entry points.
import Verification.Source.Lowering.Callbacks
-- Lowering/Closures.lean lowers each closure signature and its parameter prologue.
import Verification.Source.Lowering.Closures
-- Lowering/Expression.lean builds compositional expression proof plans.
import Verification.Source.Lowering.Expression
-- Lowering/Atoms.lean elaborates atomic expressions and predicates.
import Verification.Source.Lowering.Atoms
-- Lowering/Execution.lean follows operand execution plans.
import Verification.Source.Lowering.Execution
-- Lowering/Bindings.lean follows binding and default schedules.
import Verification.Source.Lowering.Bindings
-- Lowering/Flow.lean lowers statement control-flow nodes.
import Verification.Source.Lowering.Flow
-- SourceFacts.lean supplies assignment and ownership analyses used by lowering.
import Verification.Source.SourceFacts
-- SourceRequests.lean defines the requests and validates their evidence.
import Verification.Source.SourceRequests
import Verification.Source.Fragment
-- FlowGraph.lean owns the execution identities and control destinations that typed elaboration consumes.
import Verification.Source.FlowGraph
-- ExpressionPlan.lean owns operand execution order; typed atoms elaborate its saved values.
import Verification.Source.ExpressionPlan
-- BindingPlan.lean owns persistent bindings and the conditional execution of pattern and parameter defaults.
import Verification.Source.BindingPlan
import Verification.Source.SourceClaims
import Verification.Source.FragmentTypes

/-! Source extraction for the stateful consumer: it lowers a unit of the
Fragment AST (`Fragment`) to a calculus program with its point claims. Names
are resolved against initialized local bindings. Supplied expression types and
source annotations become distinct obligations. The consumer reconstructs the
request from source and claims; evidence never supplies the program it is
checked against.

Active-name shadowing is refused here: the parser gives a shadowing local a
name of its own (SOURCE-ELABORATION.md, "Shadowing"). This compiler remains a reviewed
extraction boundary, not a proved TypeScript semantics. Its output is checked by the proved calculus consumer. -/
namespace Verification.SourceExtraction
open CallEffects (Arrow RestArrow Contract Effect)
open Lean ProgramTyping PositiveRules ControlFlow CertificateProducer RequestJson
open Fragment LabelStore
open EquationGraphs (Tree)

section
variable {ι : Type} [Labels ι]

mutual
@[nospecialize] private partial def compileExpr (fc : SourceClaims.Function Tree)
    (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
    (e : Fragment.Expr) (next : Target) : Compiler Target :=
  LoweringExecution.compileExpr
    { compileExpr := compileExpr, executeBindingPlan := executeBindingPlan, body := body }
    fc scope Γ e next

@[nospecialize] private partial def executeBindingPlan (fc : SourceClaims.Function Tree)
    (original wanted scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
    (plan : SourceExecution.BindingPlan)
    (k : List (ScopeBinding Tree) → List (Ty Tree) → Compiler Target) : Compiler Target :=
  LoweringBindings.executeBindingPlan
    { compileExpr := compileExpr, executeBindingPlan := executeBindingPlan, body := body }
    fc original wanted scope Γ plan k

@[nospecialize] private partial def body (owner : Span) (fc : SourceClaims.Function Tree)
    (R : Ty Tree) (scope : List (ScopeBinding Tree)) (stmts : List Fragment.Stmt) : Compiler Target :=
  LoweringFlow.body
    { compileExpr := compileExpr, executeBindingPlan := executeBindingPlan, body := body }
    owner fc R scope stmts
end

end

section
variable {ι : Type} [Labels ι]

/-- The type a code unit reads a module value at: a source type (a function's
signature), or an initializer claim together with any written annotation.
The initialization unit checks both contracts where the constant is bound. -/
inductive ModuleType (ι : Type) where
  | written (ty : Json)
  | claimed (A : SourceClaims.Candidate ι) (annotation : Option Json := none)
  /-- A module cell (SOURCE-ELABORATION.md, "Module cells"): the initialization
  unit's early binding, its cell at the contract the unit's claims state. -/
  | cell (contract : SourceClaims.Candidate ι)

/-- A value of the module a code unit reaches: its name, its declaration's
position, and its type, or why it has none. -/
abbrev ModuleValue (ι : Type) := String × Span × Except String (ModuleType ι)

/-- The table is the one the claims were lowered into; annotations the claims
did not mention grow it, and the request carries the result. -/
@[nospecialize] def extractNormalizedFn (T : EquationStore.State) (f : Fragment.Fn) (fc : SourceClaims.Function Tree)
    (module : List (ModuleValue Tree) := []) (classes : List String := [])
    (freshConstructors : List (String × Span) := []) (moduleOwned : List String := []) :
    Except String (SourceRequest EquationStore.State Tree) := do
  if f.name != fc.name || f.namePos != fc.namePos then throw "function claim identity mismatch"
  let scope : List (ScopeBinding Tree) := f.params.map (fun p => held ⟨p.name,none⟩)
  -- The module functions this body mentions, outermost: a parameter or local
  -- of the same name shadows one, as in JavaScript.
  let mentioned := moduleReadNames f.body
  let siblings := module.filter fun g => mentioned.contains g.1
  if f.name == "undefined" || (names scope).contains "undefined" then
    throw "shadowing undefined is outside the fragment"
  if !distinct (names scope) then throw "duplicate source parameter name"
  if f.params.length != fc.params.length then throw "parameter claim count mismatch"
  if !distinct (fc.points.map Prod.fst) || fc.points.any (fun (_, row) =>
      !distinct (row.envs.map Prod.fst) || !distinct (row.exprs.map Prod.fst)) then
    throw "duplicate execution point, statement or expression claim"
  let ((inputs, R, entry, promise, entrySeparation, entryIndices), built) ← runCompiler T (growSites classes f.body (module := f.name == "")) (freshConstructors := freshConstructors)
      (moduleOwned := moduleOwned) do
    -- One binding per source parameter, and one request input per position a
    -- caller writes: a rest parameter is one binding, and its tuple's required
    -- elements are the positions. The array itself is allocated at entry.
    let bindings ← f.params.mapM (fun (p : Fragment.Param) =>
      lower (Fragment.translate p.ty))
    -- A sloppy function reading `this` binds its receiver as a sloppy call
    -- does: an object unchanged, any other converted (the global object, a
    -- wrapper), which the model does not have. Its receiver annotation, the
    -- entry's assumption, then admits objects only, as sloppy closure code's
    -- does (`ProgramTyping.kindOffers`).
    if let (some p, some R) := (f.params.head?, bindings.head?) then
      if p.name == "this" && f.convertsReceiver && (f.body.flatMap stmtNames).contains "this" &&
          !ProgramTyping.kindOffers (SourceTypes.graph (← table)) .sloppy R then
        throw (locatedRefusal (← table) f.namePos .bindingAnnotation Fragment.sloppyReceiverReason)
    let siblingStorage ← siblings.mapM fun (value : ModuleValue Tree) => do
      match value.2.2 with
        | Except.ok (.cell C) => do
          let contract ← (SourceClaims.resolve (← table) C).mapError fun msg =>
            s!"module cell '{value.1}': {msg}"
          let contract ← if ← moduleOwnedName value.1 then plainContract contract else pure contract
          let stored := (contract ++ (← uninitializedTy)).eraseDups
          let reference ← lower (do return [← CellClaims.reference [(valueField, stored)]])
          pure (some (Storage.early stored reference true, reference))
        | _ => pure none
    let siblingTypes ← (siblings.zip siblingStorage).mapM fun (value, storage) => do
      let (_, pos, ty) := value
      if let some (_, reference) := storage then return reference
      do
        match ty with
        | Except.ok (.cell _) => throw "internal extraction error: a module cell's storage"
        | Except.ok (.written ty) => lower (Fragment.translate ty)
        | Except.ok (.claimed A annotation) => do
          let inferred ← (SourceClaims.resolve (← table) A).mapError fun msg =>
            s!"module constant '{value.1}': {msg}"
          match annotation with
          | none => pure inferred
          | some ty =>
            let written ← lower (Fragment.translate ty)
            try lower (EquationStore.meet [written, inferred])
            catch reason => throw (locatedRefusal (← table) pos .bindingAnnotation reason)
        | Except.error reason => throw (locatedRefusal (← table) pos .bindingAnnotation reason)
    let siblingScope : List (ScopeBinding Tree) :=
      ((siblings.zip siblingTypes).zip siblingStorage).map fun ((value, A), storage) =>
        match storage with
        | some (s, _) =>
          { source := ⟨value.1, some value.2.1⟩, fixed := some A, storage := s, captured := true,
            moduleCell := some value.1 }
        | none => { source := ⟨value.1, some value.2.1⟩, fixed := some A }
    if f.params.dropLast.any (fun (p : Fragment.Param) => p.rest) then
      throw "a rest parameter must be the last one"
    -- A mutable `T[]` rest is an ordinary input: the body is checked for every
    -- array of that contract, the fresh one a call collects among them.
    let tupleRest := match f.params.getLast? with
      | some p => p.rest && (Fragment.arrayElement p.ty (readonly := true)).isNone
      | none => false
    let restElements : List (Ty Tree) ← match f.params.getLast? with
      | some p =>
        if tupleRest then do
          let es ← match Fragment.tupleRequired p.ty with
            | .ok es => pure es
            | .error reason => throw (locatedRefusal (← table) f.namePos .bindingAnnotation reason)
          es.mapM fun ty => lower (Fragment.translate ty)
        else pure []
      | none => pure []
    let hasRest := tupleRest
    let inputs := (if hasRest then bindings.dropLast else bindings) ++ restElements ++ siblingTypes
    -- A parameter's annotation is the assumption its caller makes, and the
    -- soundness theorem (`RequestJson.verify_safe_at`) takes it as given for
    -- every environment, world and heap meeting it. Each annotation is
    -- assumed at the model's meaning of its type: a primitive is that value,
    -- an arrow is a function whose invocations respect its contract over
    -- admissible heaps, and a record is a reference to a location whose
    -- fields hold the stated types, which the read and write rules then use
    -- exactly as for a record allocated here. Two such references may alias;
    -- the heap rules are stated over locations, so nothing here assumes they
    -- do not. What a JavaScript value must be for that meaning to hold (a
    -- plain data object, not an accessor or proxy) is part of the interpreted
    -- caller contract, as it is for arrows (DESIGN.md, "Trust surface").
    for ((p, A), (name, claimed)) in (f.params.zip bindings).zip fc.params do
      if p.name != name then throw "parameter claim name or order mismatch"
      let B ← SourceClaims.resolve (← table) claimed
      let T ← table
      requireSameMeaning T f.namePos .entryClaim A B
          s!"claimed parameter type differs from the source annotation for '{name}'"
    -- The result annotation, each signature of a returned function stating
    -- the footprint the claim proposes for it, which every return meets.
    let ret ← match resultWithFootprint (← table) f.ret fc.resultFootprint with
      | .ok ret => pure ret
      | .error reason => throw (locatedRefusal (← table) f.namePos .returnContract reason)
    let R ← lower (Fragment.translate ret)
    let claimedR ← SourceClaims.resolve (← table) fc.ret
    requireSameMeaning (← table) f.namePos .returnContract R claimedR
        "claimed return type differs from the source annotation"
    -- A guard's promise is about the input its parameter takes; an assertion
    -- function's returns are `undefined`, where they are checked.
    let receiver := f.params.head?.any (·.name == "this")
    let promise ← f.guard.mapM fun g => do
      return (g.asserts, g.param + (if receiver then 1 else 0), ← lower (Fragment.translate g.type))
    let returned := if f.guard.any (·.asserts) then [Labels.undef] else R
    let stmts := f.body
    let paramScope : List (ScopeBinding Tree) ← (scope.zip bindings).mapM fun (pair : ScopeBinding Tree × Ty Tree) => do
      let (b,contract) := pair
      if stmts.any (assignsStmt b.source.name) then
        let b := { b with param := true }
        if heldInCell b.source.name stmts then
          let reference ← lower (do return [← CellClaims.reference [(valueField, contract)]])
          pure { b with storage := .cell contract reference }
        else pure { b with storage := .slot contract }
      else pure { b with param := true }
    let bodyScope := paramScope ++ siblingScope
    let slotTypes := bindings ++ siblingTypes
    let fullScope := scope ++ siblingScope
    let mut first ← withAnswers (f.guard.any (!·.asserts))
      (body (if f.name.isEmpty then (0,0) else f.namePos) fc returned bodyScope stmts)
    -- Each assigned parameter gets one fresh private cell at function entry.
    -- Replace its slot in place; the caller still supplies the original value
    -- and the function's public input contract does not mention these cells.
    for (b,i) in bodyScope.zipIdx.reverse do
      if let .cell _ reference := b.storage then
        if hasRest && i == scope.length - 1 then
          throw "an assigned rest parameter is outside the fragment"
        let Γ := (bodyScope.zip slotTypes).zipIdx.map fun (entry : ((ScopeBinding Tree) × Ty Tree) × Nat) =>
          let ((binding,A),j) := entry
          if j < i then match binding.storage with
            | .cell _ ref | .early _ ref _ => ref | .value | .slot _ => A
          else A
        let mapping := (List.range fullScope.length).map fun j => if j == i then 0 else j+1
        first ← emitAt f.namePos (.makeAt .absent [valueField] [.var i])
          (.bind ⟨first.label,some mapping⟩) Γ reference "parameter-allocation"
          (scope := fullScope)
    -- A rest parameter's array is allocated once, on entry, before the body
    -- runs: the store holding the surplus arguments, then the object that
    -- holds the store. The body's environment binds the array where its name
    -- is; the request's inputs remain the positions a caller writes.
    if hasRest then
      let some restTy := bindings.getLast? | throw "a rest parameter needs a parameter"
      let some S := storeOf (SourceTypes.graph (← table)) restTy
        | throw "a rest parameter needs an array contract"
      let fixed := bindings.length - 1
      let anonymous := held ⟨"",some f.namePos⟩
      let restScope := scope.dropLast ++ restElements.map (fun _ => anonymous) ++ siblingScope
      -- Body slots before the array read the caller's positions; the module
      -- functions after it follow the collected positions.
      let bodyMapping := (List.range slotTypes.length).map fun j =>
        if j == fixed then 0 else if j < fixed then j + 2 else j + 1 + restElements.length
      let proto ← prototypeSlot (anonymous :: restScope)
      let _ ← arrayObject S
      let object ← emitAt f.namePos (arrayTerm proto)
        (.bind ⟨first.label, some bodyMapping⟩) (S :: inputs) restTy "rest-allocation"
        (scope := anonymous :: restScope)
      let store ← emitAt f.namePos
        (.arrLit ((List.range restElements.length).map fun j => .var (fixed + j)))
        (.bind ⟨object.label, some ((List.range (inputs.length + 1)).map
          fun j => if j == 0 then 0 else j)⟩)
        inputs S "rest-allocation" (scope := restScope)
      first := store
    -- The module cells' separation, which the unit assumes of its entry.
    let base := inputs.length - siblingScope.length
    let entrySeparation := moduleCellSeparation inputs.length
      (siblingScope.zipIdx.filterMap fun (b, j) => b.moduleCell.map (base + j, ·))
    -- The precondition, which the unit assumes of its inputs: each
    -- call position at the input slot that holds it, the receiver at slot 0
    -- where a `this` parameter declares it, each parameter after it.
    let receiverInput := (f.params.head?.map (·.name == "this")).getD false
    let slotOf : Nat → Option Nat := fun p => if receiverInput then some p else if p = 0 then none else some (p - 1)
    let T ← table
    let entryIndices ← f.requires.mapM fun F => match F.mapM slotOf with
      | some G => pure ({ fact := G } : HeapKnowledge.IndexAtom)
      | none => throw (locatedRefusal T f.namePos .bindingAnnotation
          "a precondition names the receiver, which the function does not declare")
    let entry ← emit .nul (.effect first) inputs [Labels.nul]
    if !entrySeparation.facts.isEmpty || !entryIndices.isEmpty then
      recordAssertion entry ⟨[], [], [], entrySeparation, [], entryIndices⟩
    return (inputs, R, entry, promise, entrySeparation, entryIndices)
  -- The postcondition its unit proves at each return: position `0` the
  -- result, each call position `p` (`i + 1` of the signature's `ensures`)
  -- at `q + 1` for the input slot `q` that holds it on entry.
  let receiverInput := (f.params.head?.map (·.name == "this")).getD false
  let ensuresSlot : Nat → Option Nat := fun i =>
    if i = 0 then some 0
    else if receiverInput then some i else if i = 1 then none else some (i - 1)
  let some ensures := f.ensures.mapM (·.mapM ensuresSlot)
    | throw "a result fact names the receiver, which the function does not declare"
  -- The stores a stated frame excepts, each call position at the input slot
  -- that holds it on entry.
  let regionSlot : Nat → Option Nat := fun p => if receiverInput then some p else if p = 0 then none else some (p - 1)
  let some regional := (f.stated.bind fun (s : CallEffects.Effect) =>
      if s.regions.isEmpty then none else some (s.closed, s.regions)).mapM
        fun ((c, rs) : Footprints.Closed × List Footprints.ArgumentStoreRegion) =>
          (rs.mapM fun (r : Footprints.ArgumentStoreRegion) => (regionSlot r.position).map fun q =>
            (⟨q, r.path⟩ : Footprints.ArgumentStoreRegion)).map (c, ·)
    | throw "a stated store region names the receiver, which the function does not declare"
  return {
    toRequest := ⟨built.types, built.program, built.claims, R, entry.label, inputs, built.codes, promise,
      entrySeparation, entryIndices⟩
    obligations := built.obligations
    sourceMap := built.source.sourceMap
    assertions := built.source.assertions
    cuts := built.source.cuts
    hints := built.hints
    codeSources := built.codeSources
    nodePlans := built.nodePlans
    footprint := fc.footprint
    onThrow := fc.onThrow
    fresh := f.stated.any (·.fresh)
    regional := regional
    ensures := ensures
    async := f.async
    stated := f.stated }

end

end Verification.SourceExtraction
