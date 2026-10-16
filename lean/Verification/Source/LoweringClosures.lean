import Verification.Source.LoweringCallbacks
import Verification.Source.LoweringClosureSetup
import Verification.Source.SourceFacts
import Verification.Source.FlowGraph

namespace Verification.SourceExtraction
open CallEffects (Arrow RestArrow Contract Effect)
open Lean ProgramTyping PositiveRules ControlFlow CertificateProducer RequestJson
open Fragment LabelStore
open EquationGraphs (Tree)

namespace LoweringClosures

set_option maxHeartbeats 1000000

/-- Expression-body parameter defaults follow the shared binding schedule.
    Inputs retain their original frame indices while names enter source scope
    in the parameter order supplied by extraction. -/
@[nospecialize] private partial def defaultEntry (recursive : RecursiveLowering) (fc : SourceClaims.Function Tree) (pos : Span)
    (params : List (String × Ty Tree)) (defaults : List (Nat × Fragment.Expr))
    (k : List (ScopeBinding Tree) → List (Ty Tree) → Compiler Target) :
    List Nat → Nat → List (ScopeBinding Tree) → List (Ty Tree) → Compiler Target
  | order, _, scope, Γ => do
    if defaults.isEmpty then return ← k scope Γ
    let parameters ← order.mapM fun i => do
      let some (name, _) := params[i]? | throw "invalid parameter schedule"
      pure (name,pos,i,defaults.lookup i)
    let some plan := SourceExecution.bindingPrologue pos parameters
      | return ← k scope Γ
    recursive.executeBindingPlan fc scope scope scope Γ plan k

/-- One graph a closure's code runs, at one of its signatures, into a program
of its own. Its entry is the frame the signature describes (`codeFrame`: the
receiver, the parameters the code takes, the captures, and, for code
collecting a rest, the store of the further actuals first); a prologue binds
the source's parameters from it, then the body runs, compiled as a function
body is. The prologue, in order: a rest's array, allocated around the store
the call collected, or from the positions of its tuple contract, as a
function's rest array is at its entry; an expression body's defaults
(`defaultEntry`; a block body's are its first statements already); and a
private cell for each parameter the body assigns. The unit's program and its
state resume afterwards. -/
@[nospecialize] private partial def closureCode (recursive : RecursiveLowering) (fc : SourceClaims.Function Tree) (pos : Span) (receiver : ScopeBinding Tree)
    (params : List (String × Ty Tree)) (rest : Option (String × (RestEntry Tree)))
    (defaults : List (Nat × Fragment.Expr)) (order : List Nat)
    (captures : List (ScopeBinding Tree)) (Cs : List (Ty Tree)) (Rt R : Ty Tree) (bodyExpr : Fragment.Expr) :
    Compiler (Program × Nat × List (PointClaim Tree) × CodeSource) := withFreshGraph do
  -- The layout the rest's array is bound in: the receiver, the parameters,
  -- the array, then the captures. While an expression body has defaults, its
  -- parameters are named where the schedule reaches them.
  let named := defaults.isEmpty
  let paramScope : List (ScopeBinding Tree) :=
    params.map fun (n, _) => held ⟨if named then n else "", some pos⟩
  let restScope : List (ScopeBinding Tree) := (rest.map fun (n, _) => held ⟨n, some pos⟩).toList
  let layout := receiver :: paramScope ++ restScope ++ captures
  let inputs := Rt :: params.map Prod.snd ++ (rest.map fun (_, r) => r.array).toList ++ Cs
  let arity := params.length + restScope.length
  let mut first ← match bodyExpr with
    | .block _ stmts => do
      -- A parameter the body assigns is a private cell, allocated at entry
      -- in place of its slot, as a function's is; the caller still supplies
      -- the value.
      let bodyScope ← layout.zipIdx.mapM fun (b, i) => do
        if i == 0 || i > arity then return b
        let some contract := inputs[i]? | throw "internal closure slot mismatch"
        if stmts.any (assignsStmt b.source.name) then
          if heldInCell b.source.name stmts then
            let reference ← lower (do return [← CellClaims.reference [(valueField, contract)]])
            pure { b with storage := .cell contract reference }
          else pure { b with storage := .slot contract }
        else pure b
      let mut first ← recursive.body bodyExpr.span fc R bodyScope stmts
      for (b,i) in bodyScope.zipIdx.reverse do
        if let .cell _ reference := b.storage then
          if i == 0 || i > arity then continue
          let Γ := (bodyScope.zip inputs).zipIdx.map fun (entry : ((ScopeBinding Tree) × Ty Tree) × Nat) =>
            let ((binding,A),j) := entry
            if j < i then match binding.storage with
              | .cell _ ref => if j == 0 || j > arity then A else ref | .value | .slot _ => A
            else A
          let mapping := (List.range layout.length).map fun j => if j == i then 0 else j+1
          first ← emitAt pos (.makeAt .absent [valueField] [.var i])
            (.bind ⟨first.label,some mapping⟩) Γ reference "parameter-allocation"
            (scope := layout)
      pure first
    | e => do
      let order := if named then List.range params.length else order
      let graph ← liftSource (SourceFlow.build e.span [] [.ret e.span e])
      let fc := fc.atPoint (SourceFlow.pointId e.span graph.entry)
      let A ← exprType fc e
      -- The expression's nodes, as a `return e` statement's, ending in the
      -- return of its value.
      defaultEntry recursive fc pos params defaults (fun scope Γ => do
          let done ← emitAt e.span (.var 0) .ret (A::Γ) R "return-contract"
            (scope := held ⟨"",some e.span⟩ :: scope)
          recursive.compileExpr fc scope Γ e done)
        order 0 layout inputs
  -- The frame the call enters, and the rest's array bound from it into the
  -- layout: the mapping takes each slot of the layout from the frame's.
  let f := params.length
  let (frameScope, frameInputs) ← match rest with
    | none => pure (layout, inputs)
    | some (_, .store S restTy) => do
      let frameScope := held ⟨"", some pos⟩ :: receiver :: paramScope ++ captures
      let frameInputs := S :: Rt :: params.map Prod.snd ++ Cs
      let proto ← liftSource (prototypeSlot frameScope)
      let _ ← arrayObject S
      -- Past the binding: the array, the store, the receiver, the parameters,
      -- the captures.
      let mapping := (first.mapping.getD (List.range layout.length)).map fun j =>
        if j == 0 then 2 else if j ≤ f then j + 2 else if j == f + 1 then 0 else j + 1
      first ← emitAt pos (arrayTerm proto) (.bind ⟨first.label, some mapping⟩) frameInputs restTy
        "rest-allocation" (scope := frameScope)
      pure (frameScope, frameInputs)
    | some (_, .tuple elements S restTy) => do
      let e := elements.length
      let frameScope := receiver :: paramScope ++ elements.map (fun _ => held ⟨"", some pos⟩) ++ captures
      let frameInputs := Rt :: params.map Prod.snd ++ elements ++ Cs
      let objectScope := held ⟨"", some pos⟩ :: frameScope
      let proto ← liftSource (prototypeSlot objectScope)
      let _ ← arrayObject S
      -- Past the object's binding: the array, the store, the receiver, the
      -- parameters, the positions, the captures.
      let mapping := (first.mapping.getD (List.range layout.length)).map fun j =>
        if j == 0 then 2 else if j ≤ f then j + 2 else if j == f + 1 then 0 else j + 1 + e
      let object ← emitAt pos (arrayTerm proto) (.bind ⟨first.label, some mapping⟩) (S :: frameInputs)
        restTy "rest-allocation" (scope := objectScope)
      first ← emitAt pos (.arrLit ((List.range e).map fun j => .var (1 + f + j))) (.bind ⟨object.label, none⟩)
        frameInputs S "rest-allocation" (scope := frameScope)
      pure (frameScope, frameInputs)
  -- A body of statements is entered at a node of its own, before its first
  -- statement's entry; an expression's first node is at the frame already.
  let entry ← match bodyExpr, first.mapping with
    | .block .., _ | _, some _ =>
      emitAt pos .nul (.effect first) frameInputs [Labels.nul] "closure-entry" (scope := frameScope)
    | _, none => pure first
  let graph ← graphResult
  return (graph.program, entry.label, graph.claims, graph.source)

/-- **A lambda's graph code**, checked at each signature `lambdaSetup` finds:
one code request per signature, the graph `closureCode` compiles from that
signature's frame, whose certificate the unit's code table records. -/
@[nospecialize] partial def lambdaCode (recursive : RecursiveLowering) (fc : SourceClaims.Function Tree) (scope : List (ScopeBinding Tree))
    (Γ : List (Ty Tree)) (lam : Fragment.Expr) (A : Ty Tree) (mode : CodeMode Tree) :
    Compiler (LambdaCode Tree) := do
  let s ← lambdaSetup fc scope Γ lam A mode
  let Cs := s.capSlots.map Prod.fst
  let mut code : Option (Program × Nat) := none
  for ((sig, store, restTy), i) in s.rows.zipIdx do
    let ⟨Rt, Di, Ri, _⟩ := sig
    let row := match s.overlays[i]? with
      | some o => fc.withOverlay o
      | none => fc
    let receiver : ScopeBinding Tree := { source := ⟨s.receiverName, some s.pos⟩, fixed := some Rt }
    let ps := (s.fixedParams.map Prod.fst).zip (Di.take s.fixedParams.length)
    let restEntry : Option (String × (RestEntry Tree)) ← s.restParam.mapM fun (name, _) => do
      match store with
      | some S => pure (name, .store S restTy)
      | none =>
        let some S := storeOf (SourceTypes.graph (← table)) restTy
          | throw "a rest parameter needs an array contract"
        pure (name, .tuple ((Di.drop s.fixedParams.length).take s.restElements) S restTy)
    let (P, start, claims, source) ←
      closureCode recursive row s.pos receiver ps restEntry s.defaults s.order s.captures Cs Rt Ri s.body
    match code with
    | some c =>
      if c != (P, start) then
        throw "a closure's body lowers differently under one of its signatures"
    | none => code := some (P, start)
    let entry : CodeEntry Tree := ⟨s.arity, P.map (·.expression), P.map fun n => (n.continuation, n.handler),
      start, Cs, sig, store⟩
    recordCode ⟨entry, claims⟩ source
  let some (P, start) := code | throw "closure claim must name a source arrow"
  let exprs := P.map fun n => n.expression
  let conts := P.map fun n => (n.continuation, n.handler)
  return (⟨s.arity, exprs, conts, start, s.capSlots, s.kind, s.rest, s.rows.filterMap (·.2.1), s.offered⟩ :
    (LambdaCode Tree))

/-- **A closure whose body is a graph** (`Rule.funGraph`): the allocation of its
code (`lambdaCode`) with the captured slots. -/
@[nospecialize] partial def graphClosure (recursive : RecursiveLowering) (fc : SourceClaims.Function Tree) (scope : List (ScopeBinding Tree))
    (Γ : List (Ty Tree)) (lam : Fragment.Expr) (A : Ty Tree) : Compiler (DirectProof.Plan Tree) := do
  let c ← lambdaCode recursive fc scope Γ lam A .fn
  pure (DirectProof.node Γ (Tm.makeFn (c.code c.kind) .nul) c.type (.funGraph c.arrays) (c.capturePlans Γ))



end LoweringClosures
end Verification.SourceExtraction
