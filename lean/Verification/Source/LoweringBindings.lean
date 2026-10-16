import Verification.Source.LoweringExecution
import Verification.Source.LoweringControl

namespace Verification.SourceExtraction
open CallEffects (Arrow RestArrow Contract Effect)
open Lean ProgramTyping PositiveRules ControlFlow CertificateProducer RequestJson
open Fragment LabelStore
open EquationGraphs (Tree)

namespace LoweringBindings

set_option maxHeartbeats 1000000

/-- One immutable declaration commits the value whose initializer schedule
    the graph action owns. The annotation is a separate checked obligation. -/
@[nospecialize] partial def constant (recursive : RecursiveLowering) (fc : SourceClaims.Function Tree) (pos : Span)
    (after : List (ScopeBinding Tree) → Compiler Target) (scope : List (ScopeBinding Tree))
    (Γ : List (Ty Tree)) (b : Fragment.Binding) : Compiler Target := do
  if b.name == "undefined" then throw "shadowing undefined is outside the fragment"
  if (names scope).contains b.name then throw s!"duplicate or shadowing local declaration '{b.name}'"
  let A ← exprType fc b.init
  let B ← match b.annot with | none => pure A | some ty => lower (Fragment.translate ty)
  let fresh := match b.init with | .alloc .. | .arrayLit .. => true | _ => false
  let bound : ScopeBinding Tree := { source := ⟨b.name,some pos⟩, fresh := fresh }
  let next ← after (bound::scope)
  let annotation ← emitAt b.init.span (.var 0) (.effect next) (A::Γ) B "binding-annotation" (some pos.1)
    (scope := held ⟨b.name,some b.init.span⟩::scope)
  LoweringExecution.compileExpr recursive fc scope Γ b.init annotation

/-- A mutable declaration allocates one private cell at its explicit lifetime
    contract, with obligations for the annotation and initializer. -/
@[nospecialize] partial def mutableBinding (recursive : RecursiveLowering) (fc : SourceClaims.Function Tree) (pos : Span)
    (after : List (ScopeBinding Tree) → Compiler Target) (scope : List (ScopeBinding Tree))
    (Γ : List (Ty Tree)) (b : Fragment.Binding) : Compiler Target := do
  if b.name == "undefined" then throw "shadowing undefined is outside the fragment"
  if (names scope).contains b.name then throw "shadowing is outside the fragment"
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
    let stored ← emitAt b.init.span (.var 0) (.effect continued) (A::Γ) contract
      "storage-contract" (some pos.1) (scope := held ⟨"",some b.init.span⟩::scope)
    return ← LoweringExecution.compileExpr recursive fc scope Γ b.init stored
  let reference ← lower (do return [← CellClaims.reference [(valueField, contract)]])
  let binding : ScopeBinding Tree := { source := ⟨b.name,some pos⟩, storage := .cell contract reference, apart := some Γ }
  let continued ← after (binding::scope)
  let drop := ⟨continued.label, some ((continued.mapping.getD (List.range (Γ.length+1))).map
    (fun j => if j == 0 then 0 else j+1))⟩
  let allocate ← emitAt b.init.span (.makeAt .absent [valueField] [.var 0]) (.bind drop)
    (A::Γ) reference "binding-storage" (some pos.1) (scope := held ⟨"",some b.init.span⟩::scope)
  let stored ← emitAt b.init.span (.var 0) (.effect allocate) (A::Γ) contract
    "storage-contract" (some pos.1) (scope := held ⟨"",some b.init.span⟩::scope)
  LoweringExecution.compileExpr recursive fc scope Γ b.init stored

/-- A binding schedule's continuation receives lexical bindings and its
    original frame; intermediate expression values are projected away. -/
@[nospecialize] partial def executeBindingPlan (recursive : RecursiveLowering) (fc : SourceClaims.Function Tree)
    (original : List (ScopeBinding Tree)) (wanted scope : List (ScopeBinding Tree))
    (Γ : List (Ty Tree)) (plan : SourceExecution.BindingPlan)
    (k : List (ScopeBinding Tree) → List (Ty Tree) → Compiler Target) : Compiler Target := do
  let save := fun (source : Span) (value : SourceExecution.Saved) (T : Ty Tree)
      (term : Tm) (next : SourceExecution.BindingPlan) => do
    let bound : ScopeBinding Tree := { source := ⟨value.name,some value.source⟩, fixed := some T }
    let next ← withExecutionType value.name T
      (executeBindingPlan recursive fc original wanted (bound::scope) (T::Γ) next k)
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
    LoweringExecution.executePlanTail recursive fc scope Γ plan fun scope' Δ _ => do
      let some T := Δ.head? | throw "internal binding plan: no evaluated value"
      let bound : ScopeBinding Tree := { source := ⟨value.name,some value.source⟩, fixed := some T }
      withExecutionType value.name T
        (executeBindingPlan recursive fc original wanted (bound::scope'.tail) Δ next k)
  | .bind name origin value next =>
    if name == "undefined" then throw "shadowing undefined is outside the fragment"
    if (names wanted).contains name then
      throw s!"duplicate or shadowing local declaration '{name}'"
    let (i,T) ← LoweringExecution.executionSaved scope Γ value
    let bound := held ⟨name,some origin⟩
    let wanted := bound :: wanted.filter (fun b => b.source.name != name)
    let next ← executeBindingPlan recursive fc original wanted (bound::scope) (T::Γ) next k
    emitAt value.source (.var i) (.bind next) Γ T "pattern-binding" (scope := scope)
  | .input _ index value next =>
    let i := scope.length - original.length + 1 + index
    let some T := Γ[i]? | throw "internal binding plan: invalid parameter input"
    save value.source value T (.var i) next
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
    let read := if field == lengthKey && lengthViewed G T then lengthRead i else .readAt field (.var i)
    save source value R read next
  | .readPosition source array index value next =>
    let (i,T) ← LoweringExecution.executionSaved scope Γ array
    let R ← tryCatch (positionRead (SourceTypes.graph (← table)) T index) fun reason => do
      throw (locatedRefusal (← table) source .bindingAnnotation reason)
    save source value R (.elemAt (.readAt SourceTypes.storeField (.var i)) (.num (bitsOfNat index))) next
  | .objectRest source receiver drop value next =>
    let (i,T) ← LoweringExecution.executionSaved scope Γ receiver
    let E ← groupType [] []
    let _ ← mergeType E T (drop.map PropKey.str)
    let R ← claimAt fc source
    save source value R (.merge (drop.map PropKey.str) (.makeAt .absent [] []) (.var i)) next
  | .arrayRest source array start slice value next =>
    let (i,T) ← LoweringExecution.executionSaved scope Γ array
    if slice then
      save source value (← claimAt fc source) (← sliceCall scope i start) next
    else
      let (store,S,R) ← restArray fc T i start source
      let stored := held ⟨"",some source⟩ :: scope
      let bound : ScopeBinding Tree := { source := ⟨value.name,some value.source⟩, fixed := some R }
      let target ← withExecutionType value.name R
        (executeBindingPlan recursive fc original wanted (bound::stored) (R::S::Γ) next k)
      let proto ← prototypeSlot stored
      let object ← emitAt source (arrayTerm proto) (.bind target) (S::Γ) R "pattern-rest" (scope := stored)
      emitAt source store (.bind object) Γ S "pattern-rest" (scope := scope)
  | .defaultValue value result fallback next =>
    let (i,R) ← LoweringExecution.executionSaved scope Γ value
    let R ← byClause R
    let G := SourceTypes.graph (← table)
    -- A proved defined value is retained without evaluating the default or
    -- asking for claims about its unreachable expressions.
    if decide (Answers G R .isUndef false) then
      return ← save value.source result R (.var i) next
    let present := BranchRefinement.tagSlice G R .isUndef false
    let absent := BranchRefinement.tagSlice G R .isUndef true
    let D ← LoweringExecution.executionPlanType fc scope Γ fallback
    let T := (present ++ D).eraseDups
    let resultBinding : ScopeBinding Tree := { source := ⟨result.name,some result.source⟩, fixed := some T }
    let joined ← withExecutionType result.name T
      (executeBindingPlan recursive fc original wanted (resultBinding::scope) (T::Γ) next k)
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
end Verification.SourceExtraction
