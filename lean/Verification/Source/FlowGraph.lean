-- typed source elaboration consumes one syntax-owned graph of normal and exceptional control transfers.
import Verification.Source.Fragment
import Verification.Source.RequestJson

/-! Claim-independent control-flow construction for source code units. -/
namespace Verification.SourceFlow
open Fragment RequestJson

abbrev Scope := List Descriptor

def pointId (owner : Span) (id : Nat) : String :=
  s!"{owner.1}:{owner.2}:{id}"

/-- Control destinations preserve lexical identities; slot adaptation belongs
    to typed elaboration. -/
structure Handler where
  target : Nat
  scope : Scope
  binding : Descriptor

/-- An action owns its expression occurrences. Structural control transfers
    are resolved by construction, before any claimed type is consulted. -/
inductive Action where
  | finish
  | jump (target : Nat)
  | statement (statement : Stmt) (next : Nat)
  | declaration (source : Span) (mutable : Bool) (binding : Binding) (next : Nat)
  | branch (statement : Stmt) (yes no : Nat)
  | returnValue (statement : Stmt)
  | saveReturn (statement : Stmt) (binding : Descriptor) (next : Nat)
  | returnHeld (binding : Descriptor)
  | rethrow (binding : Descriptor)
  | discardThrow (binding : Descriptor) (next : Nat)
  | iteratorStart (statement : Stmt) (binding : Descriptor) (next : Nat)
  | iteratorStep (statement : Stmt) (binding element : Descriptor) (yes no : Nat)

structure Node where
  source : Span
  scope : Scope
  handler : Option Handler
  action : Action

structure Graph where
  owner : Span
  bodySpans : List Span
  entry : Nat
  nodes : Array Node
  /-- The body's mutable bindings held in cells (`SourceExtraction.cellLocals`):
  a `let` named with its declaring statement, an assigned parameter with
  the body's owner. Every other one is a slot of the body's activation. -/
  cells : Scope := []

private structure Finalizer where
  statements : List Stmt
  source : Span
  scope : Scope
  handler : Option Handler
  loop : Option (Nat × Nat)
  labels : List (String × Nat)
  loopDepth : Nat
  labelDepths : List (String × Nat)

private structure Routes where
  handler : Option Handler := none
  loop : Option (Nat × Nat) := none
  labels : List (String × Nat) := []
  finalizers : List Finalizer := []
  loopDepth : Nat := 0
  labelDepths : List (String × Nat) := []

private abbrev Builder := StateT (Array Node) (Except String)

private def emit (source : Span) (scope : Scope) (r : Routes) (action : Action) : Builder Nat := do
  let nodes ← get
  set (nodes.push ⟨source, scope, r.handler, action⟩)
  return nodes.size

private def patch (id : Nat) (action : Action) : Builder Unit :=
  modify fun nodes => nodes.modify id fun node => { node with action }

private def bind (name : String) (source : Span) : Descriptor := ⟨name, some source⟩

private partial def patternBindingsOrder (source : Span) : Pattern Expr → Scope
  | .name name _ => [bind name source]
  | .object _ props rest =>
      ((props.flatMap fun (_, target, _) => patternBindingsOrder source target) ++
        (rest.toList.flatMap fun (_, target) => patternBindingsOrder source target))
  | .array _ positions rest =>
      ((positions.flatMap fun (_, target, _) => patternBindingsOrder source target) ++
        (rest.toList.flatMap fun (_, _, _, target) => patternBindingsOrder source target))

private def bindingsAfter (scope : Scope) : Stmt → Scope
  | .constants pos bs | .mutables pos bs =>
      (bs.map fun b => bind b.name pos).reverse ++ scope
  | .destructure pos target _ _ => (patternBindingsOrder pos target).reverse ++ scope
  | _ => scope

private partial def abrupt (ss : List Stmt) : Bool :=
  match ss.getLast? with
  | some (.ret ..) | some (.throw ..) | some (.brk ..) | some (.cont ..) => true
  | some (.ite _ _ t (some e)) => abrupt t && abrupt e
  | some (.block _ none b) => abrupt b
  | some (.tryStmt _ b h f) =>
      (f.map abrupt).getD false || (abrupt b && (h.map (abrupt ·.2)).getD true)
  | some (.closing _ _ b) => abrupt b
  | _ => false

private def finalizerRoutes (r : Routes) (i : Nat) (f : Finalizer) : Routes :=
  ⟨f.handler, f.loop, f.labels, r.finalizers.drop (i+1), f.loopDepth, f.labelDepths⟩

/-- Declaration entries expose each initializer and the progressive lexical scope
    shared by both consumers of the graph. -/
private partial def declarations (source : Span) (mutable : Bool) (scope : Scope)
    (bindings : List Binding) (next : Nat) (r : Routes) : Builder Nat := do
  match bindings with
  | [] => pure next
  | binding :: rest =>
    let after ← declarations source mutable (bind binding.name source :: scope) rest next r
    emit source scope r (.declaration source mutable binding after)

/-- The builder copies finalizers at each distinct completion route. A copy
    has its own execution identities even when its source spans coincide. -/
private partial def sequence (owner : Span) (scope : Scope) (ss : List Stmt)
    (next : Nat) (r : Routes) : Builder Nat := do
  match ss with
  | [] => return next
  | s :: rest =>
    match s with
    | .brk pos _ | .cont pos =>
      if !rest.isEmpty then throw "statements after break or continue are outside the fragment"
      let destination ← match s, r.loop with
        | .brk _ (some name), _ =>
          match r.labels.lookup name with
          | some target => pure target
          | none => throw s!"break to '{name}' outside a block of that label"
        | .brk _ none, some (_, target) => pure target
        | .cont _, some (target, _) => pure target
        | _, _ => throw "break or continue outside a source loop"
      let depth := match s with
        | .brk _ (some name) => (r.labelDepths.lookup name).getD 0
        | _ => r.loopDepth
      let passed := r.finalizers.take (r.finalizers.length - depth)
      let mut after := destination
      for i in (List.range passed.length).reverse do
        let some fin := passed[i]? | throw "internal flow error: finalizer index"
        after ← sequence owner fin.scope fin.statements after (finalizerRoutes r i fin)
      emit pos scope r (.jump after)
    | .ret pos e =>
      if !rest.isEmpty then throw "statements after return are outside the fragment"
      match r.finalizers with
      | [] => emit pos scope r (.returnValue s)
      | fins =>
        let saved := bind s!"%return@{pos.1}%" e.span
        let some outer := fins.getLast? | throw "internal flow error: no finalizer"
        let mut after ← emit e.span (saved :: outer.scope) { r with handler := outer.handler }
          (.returnHeld saved)
        for i in (List.range fins.length).reverse do
          let some fin := fins[i]? | throw "internal flow error: finalizer index"
          after ← sequence owner (saved :: fin.scope) fin.statements after (finalizerRoutes r i fin)
        emit pos scope r (.saveReturn s saved after)
    | .throw pos _ =>
      if !rest.isEmpty then throw "statements after throw are outside the fragment"
      emit pos scope r (.statement s next)
    | .constants pos bs | .mutables pos bs =>
      let after ← sequence owner (bindingsAfter scope s) rest next r
      let mutable := match s with | .mutables .. => true | _ => false
      declarations pos mutable scope bs after r
    | .block _ label inner =>
      let after ← sequence owner scope rest next r
      let routes := match label with
        | none => r
        | some name => { r with labels := ((name, after) :: r.labels), labelDepths := (name, r.finalizers.length) :: r.labelDepths }
      sequence owner scope inner after routes
    | .ite pos _ yes no =>
      let after ← sequence owner scope rest next r
      let yes ← sequence owner scope yes after r
      let no ← sequence owner scope (no.getD []) after r
      emit pos scope r (.branch s yes no)
    | .loop pos _ inner update =>
      let after ← sequence owner scope rest next r
      let head ← emit pos scope r (.jump 0)
      let again ← sequence owner scope update head r
      let routes := { r with loop := some (again, after), loopDepth := r.finalizers.length }
      let yes ← sequence owner scope inner again routes
      patch head (.branch s yes after)
      return head
    | .forOf pos name namePos _ _ inner =>
      let after ← sequence owner scope rest next r
      let stepper := bind s!"%next@{pos.1}%" pos
      let element := bind name namePos
      let loopScope := stepper :: scope
      let head ← emit pos loopScope r (.jump 0)
      let routes := { r with loop := some (head, after), loopDepth := r.finalizers.length }
      let yes ← sequence owner (element :: loopScope) inner head routes
      patch head (.iteratorStep s stepper element yes after)
      emit pos scope r (.iteratorStart s stepper head)
    | .tryStmt pos inner caught finalizer =>
      let after ← sequence owner scope rest next r
      let completes := !abrupt inner || (caught.map (fun h => !abrupt h.2)).getD false
      let (completed, onThrow, finals) ← match finalizer with
        | none => pure (after, r.handler, r.finalizers)
        | some statements => do
          let normal ← if completes then sequence owner scope statements after r
            else do
              let dead ← emit pos [] { r with handler := none } (.jump 0)
              patch dead (.jump dead)
              pure dead
          let thrown := bind s!"%thrown@{pos.1}%" pos
          let rethrow ← emit pos (thrown :: scope) r (.rethrow thrown)
          let entry ← sequence owner (thrown :: scope) statements rethrow r
          let fin : Finalizer := ⟨statements, pos, scope, r.handler, r.loop, r.labels,
            r.loopDepth, r.labelDepths⟩
          pure (normal, some ⟨entry, scope, thrown⟩, fin :: r.finalizers)
      let handler ← match caught with
        | none => pure onThrow
        | some (param, statements) => do
          let binding := match param with
            | some (name, namePos) => bind name namePos
            | none => bind s!"%caught@{pos.1}%" pos
          let routes := { r with handler := onThrow, finalizers := finals }
          let entry ← sequence owner (binding :: scope) statements completed routes
          pure (some ⟨entry, scope, binding⟩)
      sequence owner scope inner completed { r with handler, finalizers := finals }
    | .closing pos close inner =>
      let after ← sequence owner scope rest next r
      let some (again, exit) := r.loop
        | throw "internal flow error: an iterator's close outside its loop"
      let closed ← sequence owner scope close exit r
      let thrown := bind s!"%thrown@{pos.1}%" pos
      let thrownScope := thrown :: scope
      let rethrow ← emit pos thrownScope r (.rethrow thrown)
      let dropped := bind s!"%dropped@{pos.1}%" pos
      let discard ← emit pos (dropped :: thrownScope) r (.discardThrow thrown rethrow)
      let quietRoutes := { r with handler := some ⟨discard, thrownScope, dropped⟩ }
      let quiet ← sequence owner thrownScope close rethrow quietRoutes
      let fin : Finalizer := ⟨close, pos, scope, r.handler, r.loop, r.labels,
        r.loopDepth, r.labelDepths⟩
      let routes := { r with handler := some ⟨quiet, scope, thrown⟩, finalizers := fin :: r.finalizers, loop := some (again, closed), loopDepth := r.finalizers.length+1 }
      sequence owner scope inner after routes
    | _ =>
      let after ← sequence owner (bindingsAfter scope s) rest next r
      emit s.pos scope r (.statement s after)

/-- One graph for one executable body. Construction consults syntax and lexical
    bindings only; the same graph is consumed by typed elaboration. -/
def build (owner : Span) (scope : Scope) (body : List Stmt) : Except String Graph := do
  let (entry, nodes) ← (do
    let finish ← emit owner scope {} .finish
    sequence owner scope body finish {}).run #[]
  return ⟨owner, body.map Stmt.pos, entry, nodes, []⟩

end Verification.SourceFlow
