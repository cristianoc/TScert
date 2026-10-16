import Verification.Source.LoweringState
import Verification.Source.LoweringTypes
import Verification.Source.LoweringObservations
import Verification.Source.LoweringPlans
import Verification.Source.ExpressionPlan

/-! Elaborates saved spread and method operands. -/
namespace Verification.SourceExtraction
open CallEffects (Arrow RestArrow Contract Effect)
open Lean ProgramTyping PositiveRules ControlFlow CertificateProducer RequestJson
open Fragment LabelStore
open EquationGraphs (Tree)

section
variable {ι : Type} [Labels ι]

/-- A copied spread holds an internal argument store. Its type is computed
from the checked operand and callee contracts, independently of a source claim
for the synthetic copy. -/
@[nospecialize] private def executionSnapshotType (fc : SourceClaims.Function Tree)
    (value : SourceExecution.Saved) (call : Fragment.Expr) : Compiler (Ty Tree) := do
  -- Into an array literal, a copy at the literal's element type, which every
  -- element the literal holds meets.
  if let .arrayLit .. := call then
    let G := SourceTypes.graph (← table)
    let some S := storeOf G (← exprType fc call) | throw "an array literal needs an array claim"
    let [.list ⟨[], [], some E, _, _⟩ []] := PositiveRules.expand G S
      | throw "an array literal with a spread needs an array claim of one element type"
    let C ← lower (SourceTypes.use (.list ⟨[], [], some E, false, .dense⟩ []))
    recordHints [C]
    return [C]
  let callee ← match call with
    | .call _ callee _ _ _ | .invoke _ callee _ _ _ | .construct _ callee _ _ _ => pure callee
    | _ => throw "internal execution plan: a spread snapshot requires a call"
  let B ← exprType fc callee
  let original ← exprType fc (.var value.source value.name)
  let G := SourceTypes.graph (← table)
  let signatures := ProgramTyping.restSigs G B
  if let .construct .. := call then
    if let some S := storeOf G original then
      if let [.list T []] := PositiveRules.expand G S then
        if T.optional.isEmpty && T.rest.isNone then return S
    -- Into a variadic construct signature's element rest, a copy at that
    -- element type.
    if let [.ctors _ ((_, P, _) :: _) _ _ _] := PositiveRules.expand G B then
      if let some E := PositiveRules.restElem G P then
        let C ← lower (SourceTypes.use (.list ⟨[], [], some E, false, .dense⟩ []))
        recordHints [C]
        return [C]
    throw "a constructor spread needs a tuple contract of required positions"
  if signatures.isEmpty then
    throw (locatedRefusal (← table) call.span .bindingAnnotation
      "a spread into fixed parameters followed by an actual that runs code is outside the fragment")
  if let some S := storeOf G original then
    if let [.list T []] := PositiveRules.expand G S then
      if T.optional.isEmpty && T.rest.isNone then return S
  let some ⟨_, (_, P), _, _⟩ := signatures.head? | throw "a spread needs a variadic callee"
  let some E := PositiveRules.restElem G P
    | throw "a spread into a rest needs an element rest"
  if !E.contains Labels.undef then
    throw (locatedRefusal (← table) call.span .bindingAnnotation
      "a spread copied before a later actual runs needs a rest element type that admits `undefined`")
  let C ← lower (SourceTypes.use (.list ⟨[], [], some E, false, .dense⟩ []))
  recordHints [C]
  return [C]

@[nospecialize] private def compileSpreadSnapshot (fc : SourceClaims.Function Tree)
    (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
    (original : Fragment.Expr) (value : SourceExecution.Saved) (call : Fragment.Expr)
    (next : Target) : Compiler Target := do
  let some (i, .value) := resolve scope value.name
    | throw "internal execution plan: missing saved spread value"
  let C ← executionSnapshotType fc value call
  let inits ← match PositiveRules.expand (SourceTypes.graph (← table)) C with
    | [.list T []] =>
      if T.optional.isEmpty && T.rest.isNone then
        (List.range T.required.length).mapM fun j => do
          return Tm.elemAt (.readAt SourceTypes.storeField (.var i)) (← indexTerm j)
      else pure [.spread (.readAt SourceTypes.storeField (.var i))]
    | _ => throw "a spread copy needs an array store contract"
  emitAt original.span (.arrLit inits) (.bind next) Γ C "spread-copy" (scope := scope)

@[nospecialize] def snapshotPlanType (fc : SourceClaims.Function Tree)
    (_scope : List (ScopeBinding Tree)) (_Γ : List (Ty Tree))
    (operation : SourceExecution.Operation) : Compiler (Ty Tree) := do
  match operation with
  | .snapshotSpread _ value call => executionSnapshotType fc value call
  | .snapshotObject _ value =>
    let B ← exprType fc (.var value.source value.name)
    mergeType (← groupType [] []) B
  | _ => throw "internal execution plan: expected a snapshot operation"

@[nospecialize] def compileSnapshotOperation (fc : SourceClaims.Function Tree)
    (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
    (operation : SourceExecution.Operation) (next : Target) : Compiler Target := do
  match operation with
  | .snapshotSpread original value call => compileSpreadSnapshot fc scope Γ original value call next
  | .snapshotObject original value =>
    let some (i, .value) := resolve scope value.name
      | throw "internal execution plan: missing saved object spread"
    let C ← snapshotPlanType fc scope Γ operation
    emitAt original.span (.merge [] (.makeAt .absent [] []) (.var i)) (.bind next) Γ C
      "object-spread-copy" (scope := scope)
  | _ => throw "internal execution plan: expected a snapshot operation"

/-- Primitive alternatives retain the receiver/member correlation. The source
arguments must be inert for the deferred primitive member lookup. -/
@[nospecialize] def executionDispatch (fc : SourceClaims.Function Tree)
    (call : Fragment.Expr) : Compiler (Option PropKey) := do
  match call with
  | .invoke _ callee@(.read _ fld receiver) args [] _ =>
    let O ← exprType fc receiver
    let B ← exprType fc callee
    let plain : Fragment.Expr → Bool := fun a => match a with
      | .var .. | .lit .. => true
      | _ => false
    let G := SourceTypes.graph (← table)
    pure (if O.length > 1 && B.length > 1 && args.all plain &&
      (ProgramTyping.restSigs G B).isEmpty then some fld else none)
  | _ => pure none

/-- A method operation reads the member before argument evaluation. A primitive
dispatch retains its receiver as the correlated dispatch value. -/
@[nospecialize] def executionMethod (fc : SourceClaims.Function Tree)
    (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
    (original : Fragment.Expr) (receiver : SourceExecution.Saved)
    (_key : Option SourceExecution.Saved) (call : Fragment.Expr) : Compiler (Ty Tree × Tm) := do
  let some (i, .value) := resolve scope receiver.name
    | throw "internal execution plan: missing saved method receiver"
  let O ← exprType fc (.var receiver.source receiver.name)
  let B ← exprType fc original
  let typeArgs := match call with | .invoke _ _ _ _ ts => ts | _ => []
  let G := SourceTypes.graph (← table)
  let resolved ← comparisonsExpr fc original
  let (fld, read) ← match resolved with
    | .read _ fld _ | .index _ (some fld) _ _ => do
      explicitInstance call.span O B fld typeArgs
      pure (some fld, memberHead G O fld (.var i))
    | .elemAt _ _ key => do
      if !typeArgs.isEmpty then
        throw (locatedRefusal (← table) call.span .schemeElimination
          ("explicit type arguments on an element call are outside the fragment: an element that " ++
            "is a generic closure is claimed at a quantified callable, which the claim format does not encode"))
      let index ← arrayKeyTerm (← exprType fc key)
      pure (none, Tm.elemAt (.readAt SourceTypes.storeField (.var i)) index)
    | _ => throw "a method call's target must name a field or an element"
  if (← executionDispatch fc call).isSome then return (O, .var i)
  let term ← match fld with
    | none => pure read
    | some fld => do
      let arms ← primitiveArms scope Γ O fld
      pure (if arms.isEmpty then read else dispatchTerm arms fld i (.readAt fld (.var i)))
  if let .bindWithReceiver .. := call then
    if fld.any (fun key => (ProgramTyping.memberOf G O key).isSome) then
      return (← exprType fc call, term)
  return (B, term)

end
end Verification.SourceExtraction
