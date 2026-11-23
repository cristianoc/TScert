import Verification.Source.Lowering.Execution
import Verification.Source.Lowering.Control
import Verification.Source.FragmentTypes

namespace Verification.SourceElaboration
open CallEffects (Arrow RestArrow Contract Effect)
open Lean ProgramTyping PositiveRules ControlFlow CertificateProducer RequestJson
open Fragment LabelStore
open EquationGraphs (Tree)

namespace LoweringBindings

set_option maxHeartbeats 1000000

/-- Whether a callee's contract states a fresh result: every signature its
type selects keeps the heap and states its normal result a fresh object, the
premise of `call-fresh`. -/
@[nospecialize] def freshResultContract (G : PositiveGraphs.NormalGraph Tree) (A : Ty Tree) : Bool :=
  let cs := PositiveRules.expand G A
  !cs.isEmpty && cs.all fun
    | .arrs arrows _ => !arrows.isEmpty && arrows.all fun ⟨_, _, _, effect⟩ =>
        PromiseCalls.keepsHeap effect && effect.schema.normal.freshObjectResult
    | .ctors signatures _ _ _ _ => !signatures.isEmpty && signatures.all fun s =>
        PromiseCalls.keepsHeap s.effect && s.effect.schema.normal.freshObjectResult
    | _ => false

/-- Whether the value an initializer yields is fresh: the result of a step
whose rule states its own locations apart from the fields of the slots below
it, an allocation (an object or array literal) or a call whose callee's
contract states a fresh result (`call-fresh`); a form whose value is one of
its operands' (`e as T`, a conditional) yields a fresh value where each
operand it may yield does. Every other form yields a value its rule states
nothing of, and is not fresh. -/
@[nospecialize] partial def allocates (fc : SourceClaims.Function Tree) : Fragment.Expr → Compiler Bool
  | .alloc .. | .build .. | .arrayLit .. => pure true
  | .cast _ _ e => allocates fc e
  | .ifBody _ _ thn els => do return (← allocates fc thn) && (← allocates fc els)
  | .construct _ callee _ _ _ | .call _ callee _ _ _ | .invoke _ callee _ _ _ => do
    return freshResultContract (SourceTypes.graph (← table)) (← exprType fc callee)
  | _ => pure false

/-- One immutable declaration commits the value whose initializer schedule
    the graph action owns. The annotation is a separate checked obligation. -/
@[nospecialize] partial def constant (recursive : RecursiveLowering) (fc : SourceClaims.Function Tree) (pos : Span)
    (after : List (ScopeBinding Tree) → Compiler Target) (scope : List (ScopeBinding Tree))
    (Γ : List (Ty Tree)) (b : Fragment.Binding) : Compiler Target := do
  if b.name == "undefined" then throw "shadowing undefined is outside the fragment"
  if hasName scope b.name then throw s!"duplicate or shadowing local declaration '{b.name}'"
  let A ← exprType fc b.init
  let B ← match b.annot with | none => pure A | some ty => lower (Fragment.translate ty)
  let allocated ← allocates fc b.init
  let G := SourceTypes.graph (← table)
  let readOrigin := do
    let .read _ field (.var _ name) := b.init | none
    let i ← valueSlot scope name
    let receiver ← scope[i]?
    let T ← Γ[i]?
    -- A view's length is computed from the spine, rather than read from a field.
    guard (field != lengthKey || !lengthViewed G T)
    pure (receiver.source, field)
  let bound : ScopeBinding Tree :=
    { source := ⟨b.name,some pos⟩, allocated, apart := if allocated then some Γ else none, readOrigin }
  -- The condition as its tests run it: an equality with a claimed singleton
  -- is that singleton's tag test (`comparisonsExpr`), which
  -- `constantImplications` narrows by as the test's own edge does.
  recordConditionConstant b.name (← try comparisonsExpr fc b.init catch _ => pure b.init)
  let next ← after (bound::scope)
  -- A function literal reading the constant: its self entry
  -- (SOURCE-ELABORATION.md, "Recursive constants").
  let self := match b.init with
    | .lambda .. => if b.init.freeNames.contains b.name then some b.name else none
    | _ => none
  -- The value at the type its path states, where that is within the
  -- initializer's claim: a `false` arm of a condition is `false` there,
  -- which the constant's implications read (`meetImplications`).
  withSelfConstant self (LoweringExecution.compileExprThenAt recursive fc scope Γ b.init fun Γ V =>
    let V := match V with
      | some V => if !V.isEmpty && V.all A.contains && BranchRefinement.onlyBoolean G A then V else A
      | none => A
    emitAt b.init.span (.var 0) (.effect next) (V::Γ) B "binding-annotation" (some pos.1)
      (scope := held ⟨b.name,some b.init.span⟩::scope))

/-- A mutable declaration allocates one private cell at its explicit lifetime
    contract, with obligations for the annotation and initializer. -/
@[nospecialize] partial def mutableBinding (recursive : RecursiveLowering) (fc : SourceClaims.Function Tree) (pos : Span)
    (after : List (ScopeBinding Tree) → Compiler Target) (scope : List (ScopeBinding Tree))
    (Γ : List (Ty Tree)) (b : Fragment.Binding) : Compiler Target := do
  if b.name == "undefined" then throw "shadowing undefined is outside the fragment"
  if hasName scope b.name then throw "shadowing is outside the fragment"
  let A ← exprType fc b.init
  let some candidate := fc.contracts.lookup (b.init.span, b.name)
    | throw s!"no claimed storage contract for '{b.name}' at {b.init.span.1}"
  let contract ← (SourceClaims.resolve (← table) candidate).mapError fun msg =>
    s!"storage contract for '{b.name}' at {b.init.span.1}: {msg}"
  if let some annotation := b.annot then
    let written ← lower (Fragment.translate annotation)
    requireSameMeaning (← table) b.init.span .bindingAnnotation contract written
      s!"claimed storage contract differs from the source annotation for '{b.name}'"
  if !(← localCells).contains (b.name, some pos) then
    -- A slot: the initializer's value, checked at the contract, is the
    -- binding's first value.
    let binding : ScopeBinding Tree := { source := ⟨b.name,some pos⟩, storage := .slot contract }
    let continued ← after (binding::scope)
    return ← LoweringExecution.compileExprThen recursive fc scope Γ b.init fun Γ =>
      emitAt b.init.span (.var 0) (.effect continued) (A::Γ) contract
        "storage-contract" (some pos.1) (scope := held ⟨"",some b.init.span⟩::scope)
  let reference ← lower (do return [← CellClaims.reference [(valueField, .cell, contract)]])
  let binding : ScopeBinding Tree :=
    { source := ⟨b.name,some pos⟩, storage := .cell contract reference, allocated := true, apart := some Γ, reachable := false }
  let continued ← after (binding::scope)
  let drop := ⟨continued.label, some ((continued.mapping.getD (List.range (Γ.length+1))).map
    (fun j => if j == 0 then 0 else j+1))⟩
  LoweringExecution.compileExprThen recursive fc scope Γ b.init fun Γ => do
    let allocate ← emitAt b.init.span (.makeAt .absent [valueField] [.var 0]) (.bind drop)
      (A::Γ) reference "binding-storage" (some pos.1) (scope := held ⟨"",some b.init.span⟩::scope)
    emitAt b.init.span (.var 0) (.effect allocate) (A::Γ) contract
      "storage-contract" (some pos.1) (scope := held ⟨"",some b.init.span⟩::scope)

/-- A binding schedule's continuation receives lexical bindings and its
    original frame; intermediate expression values are projected away. -/
@[nospecialize] partial def executeBindingPlan (recursive : RecursiveLowering) (fc : SourceClaims.Function Tree)
    (original : List (ScopeBinding Tree)) (wanted scope : List (ScopeBinding Tree))
    (Γ : List (Ty Tree)) (plan : SourceExecution.BindingPlan)
    (k : List (ScopeBinding Tree) → List (Ty Tree) → Compiler Target)
    (savedReceiver : Option (String × Descriptor) := none) : Compiler Target := do
  let save := fun (source : Span) (value : SourceExecution.Saved) (T : Ty Tree)
      (term : Tm) (next : SourceExecution.BindingPlan) (readOrigin : Option (Descriptor × PropKey)) => do
    let bound : ScopeBinding Tree := { source := ⟨value.name,some value.source⟩, fixed := some T, readOrigin }
    let next ← withExecutionType value.name T
      (executeBindingPlan recursive fc original wanted (bound::scope) (T::Γ) next k savedReceiver)
    emitAt source term (.bind next) Γ T "pattern-read" (scope := scope)
  match plan with
  | .finish =>
    let added := wanted.length - original.length
    let locals ← (wanted.take added).mapM fun binding => do
      let some i := scope.findIdx? (fun other => other.source == binding.source)
        | throw s!"internal binding plan: lost lexical binding '{binding.source.name}'"
      pure i
    let indices := locals ++ (List.range original.length).map
      (fun i => scope.length - original.length + i)
    let types := indices.map (Γ[·]!)
    let next ← k wanted types
    let mapping := (next.mapping.getD (List.range wanted.length)).map (indices[·]!)
    emitAt (0,0) .nul (.effect ⟨next.label,some mapping⟩) Γ [Labels.nul] "binding-completion" (scope := scope)
  | .evaluate value plan next =>
    -- Object destructuring first saves its receiver. Associate a saved
    -- source binding with that receiver so a field read can name it later.
    let savedReceiver := do
      let .observe _ (.atom _ (.evaluate (.var _ name) _ _)) := plan | none
      let receiver ← valueSlot scope name >>= (scope[·]?)
      pure (value.name, receiver.source)
    LoweringExecution.executePlanTail recursive fc scope Γ plan fun scope' Δ _ => do
      let some T := Δ.head? | throw "internal binding plan: no evaluated value"
      let bound : ScopeBinding Tree := { source := ⟨value.name,some value.source⟩, fixed := some T }
      withExecutionType value.name T
        (executeBindingPlan recursive fc original wanted (bound::scope'.tail) Δ next k savedReceiver)
  | .bind name origin value next =>
    if name == "undefined" then throw "shadowing undefined is outside the fragment"
    if hasName wanted name then
      throw s!"duplicate or shadowing local declaration '{name}'"
    let (i,T) ← LoweringExecution.executionSaved scope Γ value
    let bound : ScopeBinding Tree :=
      { source := ⟨name,some origin⟩, readOrigin := scope[i]?.bind (·.readOrigin) }
    let wanted := bound :: wanted.filter (fun b => b.source.name != name)
    let next ← executeBindingPlan recursive fc original wanted (bound::scope) (T::Γ) next k savedReceiver
    emitAt value.source (.var i) (.bind next) Γ T "pattern-binding" (scope := scope)
  | .input _ index value next =>
    let i := scope.length - original.length + 1 + index
    let some T := Γ[i]? | throw "internal binding plan: invalid parameter input"
    save value.source value T (.var i) next none
  | .readField source receiver field value next =>
    let (i,T) ← LoweringExecution.executionSaved scope Γ receiver
    let G := SourceTypes.graph (← table)
    if let .error reason := noMethodRead G T field then
      throw (locatedRefusal (← table) source .bindingAnnotation reason)
    -- The proposed read type is checked at this read, with the live heap
    -- observations. Subsequent pattern operations receive its saved value.
    let R ← claimAt fc source
    -- `length` through a view tests the object (`lenView`), as a member
    -- access does.
    if field == lengthKey && lengthViewed G T then
      save source value R (lengthRead i) next none
    else
      let readOrigin := do
        let (saved, descriptor) ← savedReceiver
        guard (saved == receiver.name)
        pure (descriptor, field)
      save source value R (.readAt field (.var i)) next readOrigin
  | .readPosition source array index value next =>
    let (i,T) ← LoweringExecution.executionSaved scope Γ array
    let R ← tryCatch (positionRead (SourceTypes.graph (← table)) T index) fun reason => do
      throw (locatedRefusal (← table) source .bindingAnnotation reason)
    save source value R (.elemAt (.readAt SourceTypes.spineField (.var i)) (.num (bitsOfNat index))) next none
  | .objectRest source receiver drop value next =>
    let (i,T) ← LoweringExecution.executionSaved scope Γ receiver
    let E ← groupType [] []
    let _ ← mergeType E (← boundOf T) (drop.map PropKey.str)
    let R ← claimAt fc source
    save source value R (.merge (drop.map PropKey.str) (.makeAt .absent [] []) (.var i)) next none
  | .arrayRest source array start slice value next =>
    let (i,T) ← LoweringExecution.executionSaved scope Γ array
    if slice then
      save source value (← claimAt fc source) (← sliceCall scope i start) next none
    else
      let (spine,S,R) ← restArray fc T i start source
      let stored := held ⟨"",some source⟩ :: scope
      let bound : ScopeBinding Tree := { source := ⟨value.name,some value.source⟩, fixed := some R }
      let target ← withExecutionType value.name R
        (executeBindingPlan recursive fc original wanted (bound::stored) (R::S::Γ) next k savedReceiver)
      let proto ← prototypeSlot stored
      let object ← emitAt source (arrayTerm proto) (.bind target) (S::Γ) R "pattern-rest" (scope := stored)
      emitAt source spine (.bind object) Γ S "pattern-rest" (scope := scope)
  | .defaultValue value result fallback next =>
    let (i,R) ← LoweringExecution.executionSaved scope Γ value
    let R ← byClause R
    let G := SourceTypes.graph (← table)
    -- A proved defined value is retained without evaluating the default or
    -- asking for claims about its unreachable expressions.
    if decide (Answers G R .isUndef false) then
      return ← save value.source result R (.var i) next (scope[i]?.bind (·.readOrigin))
    let present := BranchRefinement.tagSlice G R .isUndef false
    let absent := BranchRefinement.tagSlice G R .isUndef true
    -- A default that rebinds a slot continues on each arm with the frame
    -- that arm leaves: the slot holds what the default wrote only where it
    -- ran.
    if !(LoweringExecution.executionRebound scope fallback).isEmpty then
      let continueAt := fun (A : Ty Tree) (Δ : List (Ty Tree)) =>
        let bound : ScopeBinding Tree := { source := ⟨result.name,some result.source⟩, fixed := some A }
        withExecutionType result.name A
          (executeBindingPlan recursive fc original wanted (bound::scope) (A::Δ) next k savedReceiver)
      let kept ← continueAt present Γ
      let presentBinding : ScopeBinding Tree := { source := ⟨value.name,some value.source⟩, fixed := some present }
      let yes ← emitAt value.source (.var 0) (.bind ⟨kept.label, some ((kept.mapping.getD
          (List.range (Γ.length+1))).map fun j => if j == 0 then 0 else j+1)⟩)
        (present::Γ) present "pattern-default-join" (scope := presentBinding::scope)
      let absentBinding : ScopeBinding Tree := { source := ⟨value.name,some value.source⟩, fixed := some absent }
      let no ← withExecutionType value.name absent do
        LoweringExecution.executePlanTail recursive fc (absentBinding::scope) (absent::Γ) fallback fun inner Δ _ => do
          let extra := Δ.length - Γ.length
          let some A := Δ.head? | throw "internal binding plan: no default value"
          let written ← continueAt A (Δ.drop extra)
          let mapping := (written.mapping.getD (List.range (Γ.length+1))).map
            (fun j => if j == 0 then 0 else j+extra)
          emitAt result.source (.var 0) (.bind ⟨written.label,some mapping⟩)
            Δ A "pattern-default-join" (scope := inner)
      return ← emitAt value.source (.var i) (.tagBind .isUndef no yes) Γ R
        "pattern-default-dispatch" (scope := scope)
    let D ← LoweringExecution.executionPlanType fc scope Γ fallback
    let T := (present ++ D).eraseDups
    let resultBinding : ScopeBinding Tree := { source := ⟨result.name,some result.source⟩, fixed := some T }
    let joined ← withExecutionType result.name T
      (executeBindingPlan recursive fc original wanted (resultBinding::scope) (T::Γ) next k savedReceiver)
    let mapping := (joined.mapping.getD (List.range (Γ.length+1))).map
      (fun j => if j == 0 then 0 else j+1)
    let presentBinding : ScopeBinding Tree := { source := ⟨value.name,some value.source⟩, fixed := some present }
    let yes ← emitAt value.source (.var 0) (.bind ⟨joined.label,some mapping⟩)
      (present::Γ) T "pattern-default-join" (scope := presentBinding::scope)
    let absentBinding : ScopeBinding Tree := { source := ⟨value.name,some value.source⟩, fixed := some absent }
    let no ← withExecutionType value.name absent do
      LoweringExecution.executePlanTail recursive fc (absentBinding::scope) (absent::Γ) fallback fun inner Δ _ => do
        let extra := Δ.length - Γ.length
        let mapping := (joined.mapping.getD (List.range (Γ.length+1))).map
          (fun j => if j == 0 then 0 else j+extra)
        emitAt result.source (.var 0) (.bind ⟨joined.label,some mapping⟩)
          Δ T "pattern-default-join" (scope := inner)
    emitAt value.source (.var i) (.tagBind .isUndef no yes) Γ R
      "pattern-default-dispatch" (scope := scope)


end LoweringBindings
end Verification.SourceElaboration
