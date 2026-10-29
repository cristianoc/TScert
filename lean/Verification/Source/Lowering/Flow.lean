import Verification.Source.Lowering.Bindings
import Verification.Source.Lowering.ClosureSetup
import Verification.Source.Lowering.Control
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

/-- A refused flow action retains all destinations and their lexical slots.
New slots are diagnostic values at their supplied contracts; cells keep their
reference representation. Every such action is recorded as an opaque region. -/
@[nospecialize] private def recoverAction (graph : SourceFlow.Graph) (base : SourceClaims.Function Tree)
    (R : Ty Tree) (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
    (node : SourceFlow.Node) (successor : Nat → List (ScopeBinding Tree) → Compiler Target) : Compiler Target := do
  let top ← lower (SourceTypes.use .source)
  let destination := fun (id : Nat) => do
    let some target := graph.nodes[id]? | throw "internal diagnostic flow: missing destination"
    let fc := base.atPoint (SourceFlow.pointId graph.owner id)
    let missing := target.scope.filter fun d => !(sources scope).contains d
    let added ← missing.mapM fun d => do
      let C ← recoverDiagnostic node.source (do
        let some claim := (fc.envs.lookup target.source.1).bind (·.lookup d.name)
          | throw s!"no diagnostic contract for '{d.name}'"
        SourceClaims.resolve (← table) claim) (pure [top])
      let early := match node.action with
        | .early bs _ => (bs.find? fun (p, _, b) => d == ⟨b.name, some p⟩).map (·.2.1)
        | _ => none
      if early.isSome || graph.cells.contains d then
        let reference ← lower (do return [← CellClaims.reference [(valueField, C)]])
        return (({ source := d, storage := match early with
          | some m => .early C reference m
          | none => .cell C reference } : ScopeBinding Tree), reference)
      let mutable := match node.action with
        | .declaration _ m b _ => m && b.name == d.name
        | _ => false
      return (({ source := d, storage := if mutable then .slot C else .value } : ScopeBinding Tree), C)
    let inner := added.map (·.1) ++ scope
    let mut next ← successor id inner
    for i in List.range added.length do
      let some (_, C) := added[i]? | throw "internal diagnostic flow: missing binding"
      next ← emitAt node.source .undef (.bind next) ((added.drop (i+1)).map (·.2) ++ Γ) C
        "diagnostic-binding-hole" (scope := (added.drop (i+1)).map (·.1) ++ scope)
    return next
  let forward := fun id => do
    let next ← destination id
    emitAt node.source .undef (.effect next) Γ [top] "diagnostic-action-hole" (scope := scope)
  match node.action with
  | .finish | .returnValue _ | .returnHeld _ | .rethrow _ =>
    emitAt node.source .undef .ret Γ R "diagnostic-action-hole" (scope := scope)
  | .jump next | .statement _ next | .declaration _ _ _ next | .early _ next
  | .saveReturn _ _ next | .discardThrow _ next | .iteratorStart _ _ next => forward next
  | .branch _ yes no | .iteratorStep _ _ _ yes no =>
    let yes ← destination yes
    let no ← destination no
    emitAt node.source .undef (.branch yes no) Γ [Labels.tru, Labels.fls]
      "diagnostic-branch-hole" (scope := scope)

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
  let Γ ← env fc node.source scope
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
  let target ← withHandler handler <| recoverDiagnostic node.source (do
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
      let done ← emitAt e.span (.var 0) .ret (A::Γ) (← returnClaim A R) "return-contract" (some pos.1)
        (scope := held ⟨"",some e.span⟩ :: scope)
      LoweringExecution.compileExpr recursive fc scope Γ e done
    | .saveReturn (.ret _ e) descriptor next =>
      let A ← exprType fc e
      let binding : ScopeBinding Tree := { source := descriptor, fixed := some A }
      let next ← successor next (binding :: scope)
      LoweringExecution.compileExpr recursive fc scope Γ e next
    | .returnHeld descriptor =>
      let some i := (sources scope).idxOf? descriptor | throw "internal flow error: lost return"
      emitAt node.source (.var i) .ret Γ (← returnClaim (Γ[i]?.getD R) R) "return-contract" (scope := scope)
    | .rethrow descriptor =>
      let some i := (sources scope).idxOf? descriptor | throw "internal flow error: lost thrown value"
      emitAt node.source (.throw (.var i)) .ret Γ [] "rethrow" (scope := scope)
    | .discardThrow _ next =>
      let next ← successor next scope
      emitAt node.source .nul (.effect next) Γ [Labels.nul] "rethrow" (scope := scope)
    | .statement (.throw pos e) _ =>
      let A ← exprType fc e
      -- A throw returns no value: its claim is the empty type.
      let raise ← emitAt e.span (.throw (.var 0)) .ret (A::Γ) [] "throw" (some pos.1)
        (scope := held ⟨"",some e.span⟩ :: scope)
      LoweringExecution.compileExpr recursive fc scope Γ e raise
    | .early bindings next =>
      -- The list's early bindings (SOURCE-ELABORATION.md, "Lexical bindings before
      -- initialization"): the activation's marker, then each binding's cell
      -- holding it, at the binding's contract with the marker's type.
      let U ← uninitializedTy
      let contracts ← bindings.mapM fun (_, _, b) => do
        let some candidate := fc.contracts.lookup (b.init.span, b.name)
          | throw s!"no claimed storage contract for the early binding '{b.name}' at {b.init.span.1}"
        let C ← (SourceClaims.resolve (← table) candidate).mapError fun msg =>
          s!"storage contract for '{b.name}' at {b.init.span.1}: {msg}"
        -- The stated type: the annotation, or the function literal's
        -- parameter and result annotations, a defaulted parameter optional,
        -- and an ordinary function's receiver annotation.
        let reason := s!"the early binding '{b.name}' needs its type stated: an annotation, or a function literal's parameter and result annotations"
        match b.annot, b.init with
        | some annotation, _ =>
          let written ← lower (Fragment.translate annotation)
          requireSameMeaning (← table) b.init.span .bindingAnnotation C written
            s!"claimed storage contract differs from the source annotation for '{b.name}'"
        | none, .lambda _ receiver [] params defaults false (some result) _ _ _ _ =>
          let Ds ← params.zipIdx.mapM fun ((_, j), i) => do
            let D ← lower (Fragment.translate j)
            pure (if defaults.any (·.1 == i) then (D ++ [Labels.undef]).eraseDups else D)
          let R ← lower (Fragment.translate result)
          let G := SourceTypes.graph (← table)
          let [.arrs [sig] []] := PositiveRules.expand G C
            | throw (locatedRefusal (← table) b.init.span .bindingAnnotation reason)
          if sig.arguments.length != Ds.length then
            throw (locatedRefusal (← table) b.init.span .bindingAnnotation reason)
          let differs := s!"claimed storage contract differs from the function literal's annotations for '{b.name}'"
          for (A, D) in sig.arguments.zip Ds do
            requireSameMeaning (← table) b.init.span .bindingAnnotation A D differs
          requireSameMeaning (← table) b.init.span .bindingAnnotation sig.result R differs
          if let some (this, _) := receiver then
            requireSameMeaning (← table) b.init.span .bindingAnnotation sig.receiver
              (← lower (Fragment.translate this)) differs
        | none, _ => throw (locatedRefusal (← table) b.init.span .bindingAnnotation reason)
        let stored := (C ++ U).eraseDups
        let reference ← lower (do return [← CellClaims.reference [(valueField, stored)]])
        pure (stored, reference)
      let n := bindings.length
      let cells : List (ScopeBinding Tree) := (bindings.zip contracts).zipIdx.map
        fun (((pos, mutable, b), (stored, reference)), idx) =>
          { source := ⟨b.name, some pos⟩, storage := .early stored reference mutable,
            apart := some ((contracts.take idx).reverse.map (·.2) ++ Γ) }
      let inner := cells.reverse ++ scope
      let target ← successor next inner
      -- The cells, last first, then the marker, then the scope: each target
      -- slot below `n` is a cell, every later one a slot past the marker.
      let toTarget : Target := ⟨target.label, some ((target.mapping.getD (List.range inner.length)).map
        fun j => if j < n then j else j+1)⟩
      let mut k := toTarget
      for idx in (List.range n).reverse do
        let some (_, reference) := contracts[idx]? | throw "internal flow error: early binding contracts"
        let ctx := (contracts.take idx).reverse.map (·.2) ++ [U] ++ Γ
        let marker := held ⟨"",some node.source⟩
        k ← emitAt node.source (.makeAt .absent [valueField] [.var idx]) (.bind k) ctx reference
          "binding-storage" (scope := (cells.take idx).reverse ++ marker :: scope)
      emitAt node.source (.makeAt .absent [uninitializedKey] [.undef]) (.bind k) Γ U
        "uninitialized-marker" (scope := scope)
    | .declaration pos _ binding next =>
      if binding.early then
        -- The declaration initializes its cell: the initializer's value,
        -- checked at the contract, written in place of the marker.
        let some (i, .early stored _ _) := resolve scope binding.name
          | throw s!"internal flow error: the early binding '{binding.name}' has no cell"
        -- A function literal's reads of the binding run when it is called,
        -- through the cell it captures, each a checked access; any other
        -- initializer reading it is refused.
        let literal := match binding.init with | .lambda .. => true | _ => false
        if binding.init.freeNames.contains binding.name && !literal then
          throw (locatedRefusal (← table) binding.init.span .bindingAnnotation
            "an early binding whose initializer reads it is outside the fragment")
        let C ← initializedContract stored
        let continued ← successor next scope
        let A ← exprType fc binding.init
        let value := held ⟨"",some binding.init.span⟩ :: scope
        LoweringExecution.compileExprThen recursive fc scope Γ binding.init fun Γ => do
          let written ← emitAt binding.init.span (.writeAt valueField (.var (i+1)) (.var 0))
            (.effect ⟨continued.label, some ((continued.mapping.getD (List.range Γ.length)).map (·+1))⟩)
            (A::Γ) [Labels.nul] "binding-storage" (some pos.1) (scope := value)
          emitAt binding.init.span (.var 0) (.effect written) (A::Γ) C "storage-contract"
            (some pos.1) (scope := value)
      else if let .declaration _ true _ _ := action then
        LoweringBindings.mutableBinding recursive fc pos (successor next) scope Γ binding
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
        let Γy ← env yesClaims rp ds
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
    | _ => throw "internal flow error: malformed action")
    (recoverAction graph base R scope Γ node (fun next bindings =>
      flowNode recursive graph ambient base R bindings next))
  completeFlowEntry reserved target
  let facts ← entryFacts fc node.source.1 scope
  let separation := separationFacts (SourceTypes.graph (← table)) scope Γ
  let links ← witnessLinks Γ fc node.source.1 scope
  if !facts.isEmpty || !links.isEmpty || !separation.facts.isEmpty then
    recordAssertion reserved ⟨facts, [], links, separation⟩
  recordCut reserved
  return ← jumpTo incoming reserved scope

private def actionPaths (a : SourceFlow.Action) : List (String × List PropKey) :=
  let expressions := match a with
    | .branch (.ite _ e _ _) _ _ | .branch (.loop _ e _ _) _ _
    | .returnValue (.ret _ e) | .saveReturn (.ret _ e) _ _
    | .statement (.effect _ e) _ | .statement (.throw _ e) _
    | .iteratorStart (.forOf _ _ _ _ e _) _ _ => [e]
    | .declaration _ _ b _ => [b.init]
    | _ => []
  -- A call statement's member-path actuals: an assertion function's call
  -- narrows the actual's read, the path's witness, from its return on
  -- (`promiseNarrowing`), which the next statement's entry carries.
  let actuals : Fragment.Expr → List (String × List PropKey)
    | .call _ _ args _ _ | .invoke _ _ args _ _ => args.filterMap fun arg =>
        (memberPath arg).bind fun p => if p.2.isEmpty then none else some p
    | _ => []
  expressions.flatMap fun e => match a with
    | .branch .. => planPaths (SourceExecution.buildCondition e)
    | .statement (.effect _ _) _ => testedPaths (SourceExecution.build e) ++ actuals e
    | _ => testedPaths (SourceExecution.build e)

/-- Typed lowering consumes the same claim-independent graph exported to the
    producer. Each recursive body owns a separate memo of cyclic entries. -/
@[nospecialize] partial def body (recursive : RecursiveLowering) (owner : Span) (fc : SourceClaims.Function Tree) (R : Ty Tree)
    (scope : List (ScopeBinding Tree)) (stmts : List Fragment.Stmt) : Compiler Target := do
  let graph ← liftSource (SourceFlow.build owner [] stmts)
  -- The module's initialization is the body whose owner is `(0,0)`.
  -- A path's witness at an entry reads its last field from its prefix's
  -- (HOST-FAMILIES.md, "Entries"), so every prefix has a witness too.
  let paths := (graph.nodes.toList.flatMap fun n => (actionPaths n.action).flatMap fun (root, fields) =>
    (List.range fields.length).map fun k => (root, fields.take (k+1))).eraseDups
  let top ← lower (SourceTypes.use .source)
  let witnesses : List (ScopeBinding Tree) := paths.zipIdx.map fun (p,i) =>
    { source := ⟨s!".path:{i}", some owner⟩, fixed := some [top], witness := some p }
  let inner := witnesses ++ scope
  let start ← withLocalCells (cellLocals [] stmts (module := owner == (0,0)))
    (withFreshFlowTargets (flowNode recursive graph inner fc R inner graph.entry))
  let mut target := start
  let some entry := graph.nodes[graph.entry]? | throw "internal flow error: missing entry"
  let Γ ← env (fc.atPoint (SourceFlow.pointId graph.owner graph.entry)) entry.source scope
  for i in List.range witnesses.length do
    let remaining := witnesses.drop (i+1) ++ scope
    target ← emitAt owner .undef (.bind target)
      (List.replicate (witnesses.length-i-1) [top] ++ Γ) [top]
      "path-witness" (scope := remaining)
  return target

end LoweringFlow
end Verification.SourceExtraction
