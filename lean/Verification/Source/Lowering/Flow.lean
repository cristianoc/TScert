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

/-- The execution points of the nodes the flow reaches from `id` by one or
more steps: an action's destinations and a node's handler. -/
private def reachablePoints (graph : SourceFlow.Graph) (id : Nat) : List String := Id.run do
  let next := fun (n : Nat) => match graph.nodes[n]? with
    | none => []
    | some node =>
      let own := match node.action with
        | .finish | .returnValue _ | .returnHeld _ | .rethrow _ => []
        | .jump m | .statement _ m | .declaration _ _ _ m | .early _ m
        | .saveReturn _ _ m | .discardThrow _ m | .iteratorStart _ _ m => [m]
        | .branch _ yes no | .iteratorStep _ _ _ yes no => [yes, no]
      own ++ (node.handler.map (·.target)).toList
  let mut seen : Array Bool := Array.replicate graph.nodes.size false
  let mut work := next id
  let mut found : List Nat := []
  for _ in [0:graph.nodes.size + 1] do
    match work with
    | [] => break
    | _ =>
      let mut later : List Nat := []
      for n in work do
        if !(seen[n]?.getD true) then
          seen := seen.set! n true
          found := n :: found
          later := next n ++ later
      work := later
  return found.reverse.map (SourceFlow.pointId graph.owner)

/-- Clause terms use a binding's value, including the `value` field of a
cell. Integer claims over a cell are defined linear terms, as entry facts
are; all array paths, bounds, guards and free body terms use the same map. -/
private def invariantFact (root : Nat → Option (Nat × List String))
    (F : HeapKnowledge.IndexFact) : Option HeapKnowledge.IndexFact :=
  let term := fun (t : HeapKnowledge.Term) => do
    let (s, p) ← root t.slot
    pure { t with slot := s, path := p ++ t.path }
  match F with
  | .int x => do
    let (s, p) ← root x
    pure (if p.isEmpty then .int s else .linear (.le [(⟨.value, s, p⟩, 1)] (2 ^ 53 - 1)))
  | .linear G => (G.mapVars term).map .linear
  | .guarded x p tag G => do
    let (s, pre) ← root x
    pure (.guarded s (pre ++ p) tag (← invariantFact root G))
  | .every x p stop body => do
    let (s, pre) ← root x
    let body ← body.mapM fun G => G.mapVars fun
      | .index => some .index
      | .elem => some .elem
      | .free t => (term t).map .free
    pure (.every s (pre ++ p) (← term stop) body)
  | F => F.mapM fun x => do
    let (s, p) ← root x
    if p.isEmpty then some s else none

/-- Elaborate one immutable control-flow action. Reserved entries permit
    cyclic edges; every entry retains the context required of its predecessors. -/
@[nospecialize] private partial def flowNode (recursive : RecursiveLowering) (graph : SourceFlow.Graph)
    (ambient : List (ScopeBinding Tree)) (base : SourceClaims.Function Tree)
    (R : Ty Tree) (incoming : List (ScopeBinding Tree)) (id : Nat) : Compiler Target := do
  let some node := graph.nodes[id]? | throw "internal flow error: missing node"
  let scope ← flowScope ambient incoming node
  if let some target := (← flowTarget id) then
    return ← jumpTo incoming target scope
  let fc := { base.atPoint (SourceFlow.pointId graph.owner id) with reachable := some (reachablePoints graph id) }
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
        let reason := s!"the early binding '{b.name}' needs its type stated: an annotation, a `let`'s Boolean, number, string or bigint literal, or a function literal's parameter and result annotations"
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
        let C ← if ← moduleOwnedName b.name then plainContract C else pure C
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
        | .ite _ cond _ _ | .loop _ cond _ _ _ => pure cond
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
        LoweringExecution.compileCondition recursive fc scope Γ cond
          (successor yesId scope) (successor noId scope)
    | .iteratorStart (.forOf pos _ _ iterate iterable _) descriptor next =>
      let some (iterateSlot, _) := resolve scope iterate
        | throw "internal flow error: missing iteration intrinsic"
      let A ← exprType fc iterable
      let N ← exprType fc (.var pos iterate)
      -- An iterator whose step changes only its own locations is a fresh
      -- object, separated from the fields of the slots below it, which its
      -- own locations differ from; the edge from the intrinsic's call
      -- establishes that separation where its effect states a fresh object.
      let fresh := match PositiveRules.expand (SourceTypes.graph (← table)) N with
        | [.arrs [⟨_, _, _, effect⟩] _] => effect.receiverOwn
        | _ => false
      let apart : Option (List (Ty Tree)) := if fresh then some Γ else none
      let binding : ScopeBinding Tree := { source := descriptor, fixed := some N, iterator := fresh, apart }
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
      -- The step is called with the iterator as its receiver.
      emitAt pos (.invoke (.var i) (.var i) []) (.bind dispatch) Γ S "for-of-step" (scope := scope)
    | _ => throw "internal flow error: malformed action"
  completeFlowEntry reserved target
  let facts ← entryFacts fc node.source.1 scope
  let separation := separationFacts (SourceTypes.graph (← table)) scope Γ
  let links ← witnessLinks fc node.source.1 scope
  -- A bound: the index binding's value is an array index at most the length
  -- of the array binding's store, below it where strict (PROGRAM-TYPING.md,
  -- "Writes at a checked index"). Both name value bindings; a claim naming
  -- any other is refused rather than dropped.
  let bounds ← ((fc.entryBounds.lookup node.source.1).getD []).mapM fun (array, index, strict) =>
    match valueSlot scope array, valueSlot scope index with
    | some x, some k => pure ({ fact := .bound x k strict } : HeapKnowledge.IndexAtom)
    | none, _ => do throw (locatedRefusal (← table) node.source .entryClaim
        s!"a bound names '{array}' as its array, which is no value binding")
    | _, none => do throw (locatedRefusal (← table) node.source .entryClaim
        s!"a bound names '{index}' as its index, which is no value binding")
  -- The linear facts the producer proposes (PROGRAM-TYPING.md, "Linear
  -- facts"): each term rooted at a value binding, its path the fields read
  -- from it, or at a binding held in a cell, its path read from the cell's
  -- `value` (`termRoot`); a fact whose coefficients are all zero states only that its
  -- terms denote integers: a binding's value a safe integer, a path's value
  -- one at most `2^53 - 1`, a length or typed-array length one at least `0`.
  -- A guarded fact (PROGRAM-TYPING.md, "Guarded clauses") is each such fact
  -- in a guarded fact of each guard, the first outermost, its path read
  -- from a value binding.
  let linear ← ((fc.entryFacts.lookup node.source.1).getD []).flatMapM fun (guards, terms, bound) => do
    let form ← terms.mapM fun (name, path, kind, c) => match termRoot scope name with
      | some (x, pre) => pure ((⟨kind, x, pre ++ path⟩ : HeapKnowledge.Term), c)
      | none => do throw (locatedRefusal (← table) node.source .entryClaim
          s!"a linear fact names '{name}', which is no value binding or cell")
    let guards ← guards.mapM fun (name, path, tag) => match termRoot scope name with
      | some (x, pre) => pure (x, pre ++ path, tag)
      | none => do throw (locatedRefusal (← table) node.source .entryClaim
          s!"a linear fact's guard names '{name}', which is no value binding or cell")
    let wrap := fun (F : HeapKnowledge.IndexFact) =>
      guards.foldr (fun (x, path, tag) B => HeapKnowledge.IndexFact.guarded x path tag B) F
    if form.all (·.2 == 0) && 0 ≤ bound then
      pure (form.map fun (t, _) => ({ fact := wrap (match t.kind, t.path with
        | .value, [] => .int t.slot
        | .value, _ :: _ => .linear (.le [(t, 1)] (2 ^ 53 - 1))
        | _, _ => .linear (.le [(t, -1)] 0)) } : HeapKnowledge.IndexAtom))
    else pure [({ fact := wrap (.linear (.le form bound)) } : HeapKnowledge.IndexAtom)]
  -- The quantified facts the producer proposes (PROGRAM-TYPING.md,
  -- "Quantified clauses"): the array, its bound and each body term rooted
  -- at a value binding or a cell, as a linear fact's.
  let root := fun (name : String) (path : List String) => do
    match termRoot scope name with
    | some (x, pre) => pure (x, pre ++ path)
    | none => throw (locatedRefusal (← table) node.source .entryClaim
        s!"a quantified fact names '{name}', which is no value binding or cell")
  let quantified ← ((fc.entryEvery.lookup node.source.1).getD []).mapM fun ((name, path), (sn, sp, sk), body) => do
    let (x, p) ← root name path
    let (y, q) ← root sn sp
    let body ← body.mapM fun (terms, bound) => do
      let form ← terms.mapM fun (v, c) => do
        let b : HeapKnowledge.Bound ← match v with
          | .index => pure .index
          | .elem => pure .elem
          | .term n path kind => do let (z, r) ← root n path; pure (.free ⟨kind, z, r⟩)
        pure (b, c)
      pure (Linear.Fact.le form bound)
    pure ({ fact := .every x p ⟨sk, y, q⟩ body } : HeapKnowledge.IndexAtom)
  -- The region facts the producer proposes (FOOTPRINTS.md, "Element
  -- regions"): both sides value bindings; a claim naming any other is
  -- refused rather than dropped.
  let apart ← ((fc.entryApart.lookup node.source.1).getD []).mapM fun (name, other) =>
    match valueSlot scope name, valueSlot scope other with
    | some x, some y => pure ({ fact := .apart x y } : HeapKnowledge.IndexAtom)
    | none, _ => do throw (locatedRefusal (← table) node.source .entryClaim
        s!"a region fact names '{name}', which is no value binding")
    | _, none => do throw (locatedRefusal (← table) node.source .entryClaim
        s!"a region fact names '{other}', which is no value binding")
  -- A loop's invariant (PROGRAM-TYPING.md, "Loop invariants"): at its head,
  -- each fact at the slots of the value bindings it names, which every edge
  -- into the head establishes.
  let invariant ← match node.action with
    | .branch (.loop _ _ _ _ (names, facts)) _ _ => facts.mapM fun F => do
      match invariantFact (fun p => names[p]? >>= termRoot scope) F with
      | some G => pure ({ fact := G } : HeapKnowledge.IndexAtom)
      | none => throw (locatedRefusal (← table) node.source .entryClaim
          "a loop invariant names a binding that is no value binding or initialized cell at the loop's head")
    | _ => pure []
  -- Each atom once, as the knowledge a search reaches holds it: a cut's
  -- knowledge is its assertion exactly (`checkAssertions`), and two claimed
  -- facts may lower to one atom (a cell's value term stated an integer and
  -- bounded by `2^53 - 1`).
  let bounds := (bounds ++ linear ++ quantified ++ apart ++ invariant).eraseDups
  if !facts.isEmpty || !links.isEmpty || !separation.facts.isEmpty || !bounds.isEmpty then
    recordAssertion reserved ⟨facts, [], links, separation, [], bounds⟩
  recordCut reserved
  return ← jumpTo incoming reserved scope

private def actionPaths (a : SourceFlow.Action) : List (String × List PropKey) :=
  let expressions := match a with
    | .branch (.ite _ e _ _) _ _ | .branch (.loop _ e _ _ _) _ _
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
