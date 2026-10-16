import Verification.Source.LoweringBindings
import Verification.Source.LoweringClosureSetup
import Verification.Source.LoweringControl
import Verification.Source.FlowGraph

namespace Verification.SourceExtraction
open CallEffects (Arrow RestArrow Contract Effect)
open Lean ProgramTyping PositiveRules ControlFlow CertificateProducer RequestJson
open Fragment LabelStore
open EquationGraphs (Tree)

namespace LoweringFlow

set_option maxHeartbeats 1000000

/-- Project lexical graph identities onto typed slots. Ambient parameters and
    captures are shared by every action of a body. -/
@[nospecialize] private partial def flowScope (ambient incoming : List (ScopeBinding Tree))
    (node : SourceFlow.Node) : Compiler (List (ScopeBinding Tree)) := do
  let locals ← node.scope.mapM fun descriptor => do
    let some binding := incoming.find? (fun b => b.source == descriptor)
      | throw s!"internal flow error: lost binding '{descriptor.name}'"
    pure binding
  pure (locals ++ ambient)

/-- Elaborate one immutable control-flow action. Reserved entries permit
    cyclic edges; every entry retains the context required of its predecessors. -/
@[nospecialize] private partial def flowNode (recursive : RecursiveLowering) (graph : SourceFlow.Graph)
    (ambient : List (ScopeBinding Tree)) (base : SourceClaims.Function Tree)
    (R : Ty Tree) (incoming : List (ScopeBinding Tree)) (id : Nat) : Compiler Target := do
  let some node := graph.nodes[id]? | throw "internal flow error: missing node"
  let scope ← flowScope ambient incoming node
  if let some target := (← flowTarget id) then
    return ← jumpTo incoming target scope
  let fc := base.atPoint (SourceFlow.pointId graph.owner id)
  let Γ ← env fc node.source.1 scope
  let reserved ← withHandler none (emitAt node.source .nul .ret Γ [Labels.nul]
    "flow-entry" (some node.source.1) scope)
  rememberFlowTarget id reserved
  let handler ← match node.handler with
    | none => pure none
    | some h => do
      let top ← lower (SourceTypes.use .source)
      let captured ← h.scope.mapM fun descriptor => do
        let some binding := scope.find? (fun b => b.source == descriptor)
          | throw s!"internal flow error: lost handler binding '{descriptor.name}'"
        pure binding
      let caught : ScopeBinding Tree := if h.binding.name.startsWith "%" then
        { source := h.binding, fixed := some [top] } else held h.binding
      let handlerScope := caught :: captured ++ ambient
      let entry ← flowNode recursive graph ambient base R handlerScope h.target
      pure (some (entry, captured.length + ambient.length))
  let action := node.action
  let target ← withHandler handler do
    let successor := fun (next : Nat) (bindings : List (ScopeBinding Tree)) =>
      flowNode recursive graph ambient base R bindings next
    match action with
    | .finish => emitAt node.source .undef .ret Γ R "completion" (scope := scope)
    | .jump next =>
      let next ← successor next scope
      if Γ.any (·.isEmpty) then emitAt node.source .undef .ret Γ R "unreachable" (scope := scope)
      else emitAt node.source .nul (.effect next) Γ [Labels.nul] (scope := scope)
    | .returnValue (.ret pos e) =>
      let A ← exprType fc e
      let done ← emitAt e.span (.var 0) .ret (A::Γ) R "return-contract" (some pos.1)
        (scope := held ⟨"",some e.span⟩ :: scope)
      LoweringExecution.compileExpr recursive fc scope Γ e done
    | .saveReturn (.ret _ e) descriptor next =>
      let A ← exprType fc e
      let binding : ScopeBinding Tree := { source := descriptor, fixed := some A }
      let next ← successor next (binding :: scope)
      LoweringExecution.compileExpr recursive fc scope Γ e next
    | .returnHeld descriptor =>
      let some i := (sources scope).idxOf? descriptor | throw "internal flow error: lost return"
      emitAt node.source (.var i) .ret Γ R "return-contract" (scope := scope)
    | .rethrow descriptor =>
      let some i := (sources scope).idxOf? descriptor | throw "internal flow error: lost thrown value"
      emitAt node.source (.throw (.var i)) .ret Γ R "rethrow" (scope := scope)
    | .discardThrow _ next =>
      let next ← successor next scope
      emitAt node.source .nul (.effect next) Γ [Labels.nul] "rethrow" (scope := scope)
    | .statement (.throw pos e) _ =>
      let A ← exprType fc e
      let raise ← emitAt e.span (.throw (.var 0)) .ret (A::Γ) R "throw" (some pos.1)
        (scope := held ⟨"",some e.span⟩ :: scope)
      LoweringExecution.compileExpr recursive fc scope Γ e raise
    | .declaration pos mutable binding next =>
      if mutable then LoweringBindings.mutableBinding recursive fc pos (successor next) scope Γ binding
      else LoweringBindings.constant recursive fc pos (successor next) scope Γ binding
    | action@(.statement (.destructure ..) next) =>
      let some plan := SourceExecution.bindingAction action
        | throw "internal binding plan: missing destructuring schedule"
      LoweringBindings.executeBindingPlan recursive fc scope scope scope Γ plan fun bindings _ => successor next bindings
    | .statement (.effect _ e) nextId =>
      let next ← successor nextId scope
      let owned ← if let .objectAssign _ (.var _ name) _ := e then do
          -- The call's copy is rebound to its target's slot alone: the
          -- target is the object's one holder, a constant.
          let some [(_, .value)] ← ownedSlots scope e.span name
            | throw (locatedRefusal (← table) e.span .expressionClaim
                "Object.assign onto an object another reference may hold adds keys that reference would see: it is lowered on a local's own fresh object that nothing else has reached, outside any loop its declaration does not enclose")
          pure true
        else do if (← computedGrowth fc scope e).isSome then pure true else (·.isSome) <$> growingWrite fc scope e
      withOwnedWrite e.span owned do
        LoweringExecution.executePlanTail recursive fc scope Γ (SourceExecution.build e) fun inner Δ _ => do
          let offset := Δ.length - Γ.length
          let mapping := (next.mapping.getD (List.range Γ.length)).map (·+offset)
          emitAt e.span .nul (.effect ⟨next.label,some mapping⟩) Δ [Labels.nul]
            "expression-discard" (scope := inner)
    | .branch statement yesId noId =>
      let cond ← match statement with
        | .ite _ cond _ _ | .loop _ cond _ _ => pure cond
        | _ => throw "internal flow error: malformed branch"
      let guarded ← match statement, graph.nodes[yesId]? with
        | .ite _ _ thn _, some { action := .returnValue _, .. } =>
          let yesClaims := base.atPoint (SourceFlow.pointId graph.owner yesId)
          guardedReturn { fc with exprs := fc.exprs ++ yesClaims.exprs } scope Γ cond thn
        | _, _ => pure none
      match guarded with
      | some (ds, K, read, tested, e, rp) =>
        let yesClaims := base.atPoint (SourceFlow.pointId graph.owner yesId)
        let Γy ← env yesClaims rp.1 ds
        let e ← comparisonsExpr yesClaims e
        let p ← LoweringExpression.closureExpr recursive yesClaims ds Γy e
        let yes ← emitPlanned e.span p .ret Γy R "return-contract" (scope := ds)
        let no ← successor noId scope
        let no : Target := ⟨no.label, some ((no.mapping.getD (List.range scope.length)).map (·+1))⟩
        let A ← exprType fc cond
        let branch ← emitBranch ds K tested A yes no
        let predicate ← LoweringExecution.compileExpr recursive fc ds K tested branch
        LoweringExecution.compileExpr recursive fc scope Γ read predicate
      | none =>
        let yes ← successor yesId scope
        let no ← successor noId scope
        LoweringExecution.compileCondition recursive fc scope Γ cond yes no
    | .iteratorStart (.forOf pos _ _ iterate iterable _) descriptor next =>
      let some (iterateSlot, _) := resolve scope iterate
        | throw "internal flow error: missing iteration intrinsic"
      let A ← exprType fc iterable
      let N ← exprType fc (.var pos iterate)
      let binding : ScopeBinding Tree := { source := descriptor, fixed := some N }
      let head ← successor next (binding :: scope)
      let mapping := (head.mapping.getD (List.range (scope.length+1))).map
        (fun i => if i == 0 then 0 else i+1)
      let start ← emitAt pos (Tm.call (.var (iterateSlot+1)) [.var 0])
        (.bind ⟨head.label, some mapping⟩) (A::Γ) N "for-of-iterator"
        (scope := held ⟨"",some iterable.span⟩ :: scope)
      LoweringExecution.compileExpr recursive fc scope Γ iterable start
    | .iteratorStep (.forOf pos name namePos _ _ _) descriptor element yes no =>
      let some i := (sources scope).idxOf? descriptor | throw "internal flow error: lost iterator"
      let N := Γ[i]?.getD []
      let T ← exprType fc (.var namePos name)
      let G := SourceTypes.graph (← table)
      let [.arrs [⟨_, [], S, _⟩] _] := PositiveRules.expand G N
        | throw (locatedRefusal (← table) pos .bindingAnnotation "a for...of step is one call of no parameters")
      let present := BranchRefinement.tagSlice G S .isNul false
      let first ← successor yes (held element :: scope)
      let exit ← successor no scope
      let bindElement := ⟨first.label, some ((first.mapping.getD (List.range (scope.length+1))).map
        (fun j => if j == 0 then 0 else j+1))⟩
      let read ← emitAt namePos (.readAt (.str "value") (.var 0)) (.bind bindElement)
        (present::Γ) T "for-of-element" (scope := held ⟨"",some pos⟩ :: scope)
      let toElement : Target := ⟨read.label, some ((List.range (scope.length+1)).map
        (fun j => if j == 0 then 0 else j+1))⟩
      let toExit : Target := ⟨exit.label, some ((exit.mapping.getD (List.range scope.length)).map (·+2))⟩
      let dispatch ← emitAt pos (.var 0) (.tagBind .isNul toExit toElement) (S::Γ) S
        "for-of-dispatch" (scope := held ⟨"",some pos⟩ :: scope)
      emitAt pos (Tm.call (.var i) []) (.bind dispatch) Γ S "for-of-step" (scope := scope)
    | _ => throw "internal flow error: malformed action"
  completeFlowEntry reserved target
  let facts ← entryFacts fc node.source.1 scope
  let links := distinctLinks (SourceTypes.graph (← table)) scope Γ
  if !facts.isEmpty || !links.isEmpty then
    recordAssertion reserved ⟨facts, [], links⟩
  recordCut reserved
  return ← jumpTo incoming reserved scope

/-- Typed lowering consumes the same claim-independent graph exported to the
    producer. Each recursive body owns a separate memo of cyclic entries. -/
@[nospecialize] partial def body (recursive : RecursiveLowering) (owner : Span) (fc : SourceClaims.Function Tree) (R : Ty Tree)
    (scope : List (ScopeBinding Tree)) (stmts : List Fragment.Stmt) : Compiler Target := do
  let graph ← liftSource (SourceFlow.build owner [] stmts)
  -- The module's initialization is the body whose owner is `(0,0)`.
  withLocalCells (cellLocals [] stmts (module := owner == (0,0)))
    (withFreshFlowTargets (flowNode recursive graph scope fc R scope graph.entry))

end LoweringFlow
end Verification.SourceExtraction
