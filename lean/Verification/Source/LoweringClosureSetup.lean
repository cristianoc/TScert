import Verification.Source.LoweringState
import Verification.Source.LoweringTypes
import Verification.Source.LoweringObservations
import Verification.Source.LoweringPlans

/-! Prepares closure signatures, parameters and captures. -/
namespace Verification.SourceExtraction
open CallEffects (Arrow RestArrow Contract Effect)
open Lean ProgramTyping PositiveRules ControlFlow CertificateProducer RequestJson
open Fragment LabelStore
open EquationGraphs (Tree)

section
variable {ι : Type} [Labels ι]

/-- How a closure's frame binds its rest parameter (`closureCode`). -/
inductive RestEntry (ι : Type) where
  /-- Code collecting a rest: the store of the further actuals, in the frame's
  slot 0, at `S`, and the array wrapping it, at `array`. -/
  | store (S array : Ty ι)
  /-- A rest standing for the required positions of its tuple contract, taken
  as parameters at `elements`: the store of them at `S`, the array at `array`. -/
  | tuple (elements : List (Ty ι)) (S array : Ty ι)

@[nospecialize] def RestEntry.array : RestEntry ι → Ty ι
  | .store _ a | .tuple _ _ a => a

/-- Which signatures a lambda's code is checked at (`lambdaCode`): a
function's claim, a class value's construct signatures with the `undefined`
type for the receiver, or an annotation's arrows. -/
inductive CodeMode (ι : Type) where
  | fn
  | ctor (undef : Ty ι)
  | annotated (F : Ty ι)

/-- A lambda's checked graph code, as its creation names it: the code, the
captured slots with the types it was checked with, whether it collects a rest
and the rest-store type at each signature, and the type the code offers. -/
structure LambdaCode (ι : Type) where
  arity : Nat
  exprs : List Tm
  conts : List (ControlFlow.Continuation × Option ControlFlow.Target)
  start : Nat
  captures : List (Ty ι × Nat)
  kind : Invoke
  rest : Bool
  arrays : List (Ty ι)
  type : Ty ι

@[nospecialize] def LambdaCode.code (c : LambdaCode ι) (kind : Verification.Invoke) : CallCode :=
  .graph c.arity c.exprs c.conts c.start (c.captures.map fun (_, i) => .var i) kind c.rest

@[nospecialize] def LambdaCode.capturePlans (c : LambdaCode ι) (Γ : List (Ty ι)) : List (DirectProof.Plan ι) :=
  c.captures.map fun (C, i) => DirectProof.var Γ i C

/-- A source-level refusal from a pure pass, in the compiler. -/
@[nospecialize] def liftSource (x : Except String α) : Compiler α :=
  match x with
  | .ok a => pure a
  | .error e => throw e

/-- `if (x.f !== c) return x.f;`, the arm one `return` of the tested read:
the scope with the read saved, at the slice of its type the test's arm
admits, its context, the read, the test over the saved value, the returned
read and the `return`'s span. The saved read can stand for the returned one:
between the two nothing runs (the other operand is a literal, a name or a
field read), so both read the same value. Only a tag test, which refines the
saved slot on its edge, and a slice within the returned read's own claim. -/
@[nospecialize] def guardedReturn (fc : SourceClaims.Function Tree) (scope : List (ScopeBinding Tree))
    (Γ : List (Ty Tree)) (cond : Fragment.Expr) (thn : List Fragment.Stmt) :
    Compiler (Option (List (ScopeBinding Tree) × List (Ty Tree) × Fragment.Expr × Fragment.Expr ×
      Fragment.Expr × Span)) := do
  let some (snapshot, read, tested) := readGuard scope cond | return none
  let [.ret rp e@(.read _ fld (.var _ name))] := thn | return none
  if readSnapshot name fld != some snapshot then return none
  let B ← exprType fc read
  let K := B :: Γ
  let probe := held ⟨snapshot, some read.span⟩ :: scope
  let G := SourceTypes.graph (← table)
  let some (0, tag, equal) := conditionTag G probe K tested | return none
  let slice := BranchRefinement.tagSlice G B tag equal
  let T ← table
  if sameMeaning T slice B || !within T slice (← exprType fc e) then return none
  let ds := { held ⟨snapshot, some read.span⟩ with fixed := some slice } :: scope
  return some (ds, K, read, tested, e, rp)

/-- What a lambda's graph code is checked with (`lambdaSetup`): the
signatures, each with the store its rest is collected into and its rest's
array type; the captured slots; the parameters and the entry schedule. -/
structure LambdaSetup (ι : Type) where
  pos : Span
  body : Fragment.Expr
  receiverName : String
  kind : Invoke
  fixedParams : List (String × Json)
  restParam : Option (String × Json)
  restElements : Nat
  defaults : List (Nat × Fragment.Expr)
  order : List Nat
  rows : List ((Arrow (Ty ι)) × Option (Ty ι) × Ty ι)
  overlays : List (SourceClaims.Overlay ι)
  captures : List (ScopeBinding ι)
  capSlots : List (Ty ι × Nat)
  arity : Nat
  rest : Bool
  offered : Ty ι

/-- **A lambda's graph code.** Its code is the graph its body compiles to
(`CallCode.graph`), checked at each signature the code offers from that
signature's frame, the captures at their types here: one code request per
signature, whose certificate the unit's code table records. The captures are
the named bindings in scope the lambda reads (its defaults included); a
closure reads nothing else. Which signatures (`mode`): a function's claim, an
arrow type or a scheme row, whose binders are then parameter rows (`fn`); a
class value's construct signatures, with `undefined` for the receiver `new`
passes (`ctor`); or an annotation's arrows, a callable object's (`annotated`).
Code collecting an array rest offers its own variadic signature, at the
source's annotations, which the claim is reached from by subtyping; or a
scheme row's variadic signatures. -/
@[nospecialize] def lambdaSetup (fc : SourceClaims.Function Tree) (scope : List (ScopeBinding Tree))
    (Γ : List (Ty Tree)) (lam : Fragment.Expr) (A : Ty Tree) (mode : CodeMode Tree) :
    Compiler (LambdaSetup Tree) := do
  let .lambda pos receiverAnnot typeParams params defaults hasRest ret body := lam
    | throw "internal extraction error: a closure's code is a lambda's"
  let G := SourceTypes.graph (← table)
  let paramNames := params.map Prod.fst
  if !distinct paramNames || paramNames.any (fun name => name == "" || name == "undefined" || (names scope).contains name) then
    throw "shadowing or duplicate closure parameter is outside the fragment"
  -- An ordinary function's receiver is `this` in its body; an arrow's is
  -- anonymous, so its `this` is the one it captures. A class value's code
  -- reads no receiver.
  let receiverName := if receiverAnnot.isSome then "this" else ""
  -- The code's kind: an arrow's and a class value's code is `call`.
  let kind := (receiverAnnot.map Prod.snd).getD .call
  let top ← lower (SourceTypes.use .source)
  let scheme := match mode with
    | .fn => ProgramCertificates.schemeOf G A
    | _ => none
  -- A generic closure is graph code at its scheme row, which its claim names
  -- (`closureRows`); its annotations read its binders as the row's.
  if scheme.isNone && !typeParams.isEmpty then
    throw "a quantified closure is checked at its scheme row, which its claim does not name"
  let overlays := (fc.arrowClaims.lookup pos).getD []
  let Rsource ← match receiverAnnot with
    | some (annot, _) => lower (Fragment.callableType annot)
    | none => pure [top]
  let fixedParams := if hasRest then params.dropLast else params
  let restParam := if hasRest then params.getLast? else none
  -- A rest whose contract is an array collects any number of actuals: the
  -- code collects them into a store (`rest`). Any other rest stands for the
  -- required positions of its tuple contract, which the code takes as
  -- parameters and allocates the array from at entry.
  let arrayRest := restParam.bind fun (_, j) => Fragment.arrayElement j (readonly := true)
  let restElements : List Json ← match restParam, arrayRest with
    | some (_, ty), none => match Fragment.tupleRequired ty with
      | .ok es => pure es
      | .error reason => throw (locatedRefusal (← table) pos .bindingAnnotation reason)
    | _, _ => pure []
  let defaulted := defaults.map Prod.fst
  if restParam.isSome && arrayRest.isNone && !typeParams.isEmpty then
    throw "a rest parameter is neither defaulted nor quantified"
  -- The parameters the source annotates, a defaulted one's advertised type
  -- with `undefined`: a call may omit it.
  let sourceDs : List (Ty Tree) ← do
    let fixed ← fixedParams.mapM fun p => lower (Fragment.callableType p.2)
    let elements ← restElements.mapM fun ty => lower (Fragment.callableType ty)
    pure ((fixed ++ elements).zipIdx.map fun (D,i) =>
      if defaulted.contains i then ((D ++ [Labels.undef]).mergeSort Labels.le).eraseDups else D)
  let ctorReceiver := match mode with
    | .ctor U => some U
    | _ => none
  -- The rest's array type: the annotation's, a binder read as its row.
  let restAt : Compiler (Ty Tree) := do
    let some (_, ty) := restParam | pure []
    lower (Fragment.translate ty)
  -- The rows the code is checked at, each with the store it collects its rest
  -- into and its rest's array type, and the type the code offers them at.
  let (rows, offered) ← match arrayRest with
    | some elementJson => do
      match scheme with
      | some (_, s) =>
        if !s.signatures.isEmpty then
          throw "a closure collecting a rest array offers no fixed signature"
        pure (s.variadic.map (fun sig => (sig.fixed, some sig.arguments.2)), A)
      | none =>
        let E ← lower (Fragment.callableType elementJson)
        let some ret := ret
          | throw (locatedRefusal (← table) pos .bindingAnnotation
              "a closure collecting a rest array needs its result annotation")
        let R ← lower (Fragment.callableType ret)
        let restPack ← lower (SourceTypes.use (.pack ⟨[], [], some E, false, .dense⟩ []))
        let own ← lower (SourceTypes.use (.arrs [] [⟨Rsource, (sourceDs, [restPack]), R, .unrestricted⟩]))
        recordHints [own]
        pure ([(⟨Rsource, sourceDs, R, .unrestricted⟩, some [restPack])], [own])
    | none => do
      let (L, S) ← match mode, scheme with
        | .ctor U, _ => match PositiveRules.expand G A with
          | [.ctors L S _ _] => do
            -- A variadic signature with an element rest is checked at the row
            -- binding the code's further positions at the element or
            -- `undefined` (`ProgramTyping.ctorRestParams`).
            let codeArity := fixedParams.length + restElements.length
            let variadic ← S.mapM fun (Qs, P, Ri) => do
              let some El := PositiveRules.restElem G P
                | throw (locatedRefusal (← table) pos .bindingAnnotation
                    "a variadic construct signature needs an element rest")
              pure (⟨U, ProgramTyping.ctorRestParams codeArity Qs El U, Ri, .unrestricted⟩ : Arrow (Ty Tree))
            pure (L.map (fun (Di, Ri) => ⟨U, Di, Ri, .unrestricted⟩) ++ variadic, [])
          | _ => throw "a class value's claim must name construct signatures"
        | .annotated F, _ => match PositiveRules.expand G F with
          | [.arrs L _] => pure (L, [])
          | _ => throw "initializer requires a free function annotation"
        | .fn, some (_, s) => pure (s.signatures, s.variadic)
        | .fn, none => match PositiveRules.expand G A with
          | [.arrs L S] => pure (L, S)
          | _ => throw "closure claim must name a source arrow"
      pure ((ProgramTyping.offerRows L S).map (·, none), match mode with | .annotated F => F | _ => A)
  if rows.isEmpty then
    throw (match mode with
      | .ctor _ => "construct signature claim is outside the source annotation"
      | _ => "closure claim must name a source arrow")
  -- Each arrow's rest: its array type, and, for code collecting it, the store
  -- the call collects its further actuals into, which the arrow's rest pack
  -- must fit (`RestStore`).
  let restTy ← restAt
  let restTys := rows.map fun _ => restTy
  let stores ← (rows.zip restTys).mapM fun ((_, P), restTy) => do
    let some P := P | pure none
    let G := SourceTypes.graph (← table)
    let some S := storeOf G restTy | throw "a rest parameter needs an array contract"
    if !decide (ProgramTyping.RestStore G S P) then
      throw "a closure collecting a rest array is claimed at a signature its store does not meet"
    recordHints (restTy ++ S)
    pure (some S)
  let rows := rows.map Prod.fst
  -- The positions the code takes: the fixed parameters, and a tuple rest's.
  let arity := fixedParams.length + restElements.length
  let T ← table
  -- A claim may offer more parameters than the closure takes: calls discard
  -- the actuals past them. The ones it takes are the source's.
  let reason := match mode with
    | .ctor _ => "construct signature claim is outside the source annotation"
    | _ => "closure signature claim is outside the source annotation"
  for row in rows do
    if arity > row.arguments.length then throw (locatedRefusal T pos .bindingAnnotation reason)
    for (D, B) in (row.arguments.take arity).zip sourceDs do
      requireWithin T pos .bindingAnnotation D B reason
  -- An ordinary function may be claimed at fewer receivers than it states,
  -- never at more: its body reads the one it is given.
  if Rsource != [top] then
    for row in rows do
      requireWithin T pos .bindingAnnotation row.receiver Rsource
        "closure receiver claim is outside the source annotation"
  -- Sloppy code reading `this` binds an object receiver unchanged and
  -- converts any other (the global object, a wrapper), which the model has no
  -- term for: each signature it offers admits objects only (`kindOffers`).
  if kind == .sloppy then
    let G := SourceTypes.graph T
    for R in Rsource :: rows.map (·.receiver) do
      if !ProgramTyping.kindOffers G .sloppy R then
        throw (locatedRefusal T pos .bindingAnnotation Fragment.sloppyReceiverReason)
  if !overlays.isEmpty && overlays.length != rows.length then
    throw "per-arrow interior claims do not match the claimed arrows"
  -- The captures: the named bindings in scope the lambda reads (a class's
  -- method binding, `C.m`, which `super.m(...)` reads, included), and the
  -- prototypes a literal or a primitive's member reads through. A read
  -- snapshot is an observation of this point, not a binding the body reads:
  -- no source read names one.
  let reads := lam.freeNames
  let caps := scope.zipIdx.filter fun (b, _) =>
    b.source.name != "" &&
      (reads.contains b.source.name || SourceTypes.prototypeNames.contains b.source.name)
  let Cs ← caps.mapM fun (_, i) => match Γ[i]? with
    | some C => pure C
    | none => throw "internal closure slot mismatch"
  -- A captured receiver keeps its type here: no statement claim names `this`.
  let captures : List (ScopeBinding Tree) := (caps.zip Cs).map fun ((b, _), C) =>
    if b.source.name == "this" then { b with fixed := some C, captured := true } else { b with captured := true }
  -- The rest is bound after every fixed parameter: a default reading it reads
  -- a binding JavaScript has not yet initialized, and throws.
  if let some (restName, _) := restParam then
    if defaults.any (fun (_, d) => d.freeNames.contains restName) then
      throw (locatedRefusal (← table) pos .bindingAnnotation
        "parameter default may only read initialized earlier parameters and captures; the rest parameter is initialized last")
  let order ← if defaults.isEmpty then pure (List.range fixedParams.length) else
    match Fragment.parameterOrder fixedParams defaults with
    | .ok order => pure order
    | .error reason => throw (locatedRefusal (← table) pos .bindingAnnotation reason)
  let receiverName := if ctorReceiver.isSome then "" else receiverName
  let signatures := ((rows.zip stores).zip restTys).map fun ((r, S), t) => (r, S, t)
  let capSlots := (caps.zip Cs).map fun ((_, i), C) => (C, i)
  return ⟨pos, body, receiverName, kind, fixedParams, restParam, restElements.length, defaults, order,
    signatures, overlays, captures, capSlots, arity, arrayRest.isSome, offered⟩


end
end Verification.SourceExtraction
