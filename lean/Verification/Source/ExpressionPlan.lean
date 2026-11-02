-- expression elaboration consumes a syntax-owned execution plan with explicit sequencing and branch choices.
import Verification.Source.Fragment

/-! Execution plans separate source operand evaluation from typed primitive
    elaboration. Saved values retain their source origin for claim lookup. -/
namespace Verification.SourceExecution
open Fragment

inductive Effect where
  | none
  | havoc
  | cellWrite (name : String) (value : Span)
  | cellUpdate (name : String) (source : Span)

structure Saved where
  id : Nat
  name : String
  source : Span
  role : String := "value"

inductive Test where
  | truthy
  | nullish
  | defined
  deriving BEq

inductive Reference where
  | local (name : String) (source : Span)
  | field (original : Expr) (receiver : Saved) (key : Option Saved)

/-- An atom's syntax contains saved-value reads in place of executable operands.
    The original syntax supplies annotation and source-admission metadata. -/
inductive Operation where
  | evaluate (original prepared : Expr) (effect : Effect)
  | methodRead (original : Expr) (receiver : Saved) (key : Option Saved)
      (call : Expr)
  | invokeSaved (original prepared : Expr) (receiver method : Saved)
  | snapshotSpread (original : Expr) (value : Saved) (call : Expr)
  | snapshotObject (original : Expr) (value : Saved)
  | referenceRead (source : Span) (reference : Reference)
  | referenceWrite (source : Span) (reference : Reference) (value : Saved)
  | updateSaved (original : Expr) (reference : Reference) (previous : Saved) (rhs : Option Saved)
  | positionRead (source : Span) (array : Saved) (index : Nat)
  | arrayRest (source : Span) (array : Saved) (start : Nat) (slice : Bool)
  | emptyObject (source : Span)
  | addField (original : Expr) (base : Saved) (key : PropKey) (value : Saved) (final : Bool)
  | mergeObjects (source : Span) (left right : Saved) (final assign : Bool)
  deriving Nonempty

inductive Plan where
  | observe (source : Span) (evaluate : Plan)
  | atom (source : Span) (operation : Operation)
  | sequence (source : Span) (binding : Saved) (evaluate next : Plan)
  | choose (source condition : Span) (test : Test) (binding : Saved)
      (evaluate yes no : Plan)
  deriving Nonempty

private abbrev Builder := StateM Nat

private def saved (root : Span) (origin : Span) (role : String := "value") : Builder Saved := do
  let id ← get
  set (id+1)
  return ⟨id, s!"%eval@{root.1}:{root.2}:{id}%", origin, role⟩

private def readSaved (binding : Saved) : Expr := .var binding.source binding.name

/-- The span of a negation's `!`, its first code unit: no source expression
has it, an expression starting there being the negation itself. -/
def negationMark (negation : Span) : Span := (negation.1, negation.1 + 1)

/-- The span of a residual whose value is no source expression's: an
expression a derived form builds that the source does not contain, such as
`b && c` of `(a && b) && c` read as `a && (b && c)`. A nonempty span
observed in a plan is the entry of the source expression owning it; such a
residual is placed at the empty span where its first operand starts, which
no source expression and no claim has (`Claims.Wire` refuses an empty claim
span), and its operands keep their own. A residual computing the value of
the source expression it is derived from (`b && c` of `(a, b) && c`) keeps
that expression's span and claim and is not observed. -/
def residual (first : Expr) : Span := (first.span.1, first.span.1)

/-- A test: an expression whose value is a Boolean by its form. -/
def testForm : Expr → Bool
  | .shapeTest .. | .tagMember .. | .equality .. | .singletonTest .. | .not .. | .inKeys .. => true
  | .arith _ op _ _ => op == .lt || op == .le || op == .gt || op == .ge || op == .eq
  | .logical _ _ a b => testForm a && testForm b
  | _ => false

/-- Whether a condition's left operand is dispatched as a test: a negation
is one where its operand is, and `logicalTruth` dispatches on the truthiness
of any other left operand. -/
def leftTestForm : Expr → Bool
  | .not _ e => testForm e
  | e => testForm e

private def effect : Expr → Effect
  | .assign _ name _ rhs => .cellWrite name rhs.span
  | .construct .. | .call .. | .invoke .. | .callWithReceiver .. | .applyWithReceiver ..
  | .write .. | .indexWrite .. | .elemWrite .. | .objectAssign ..
  => .havoc
  | _ => .none



mutual
private partial def operand (root : Span) (e : Expr) (role : String)
    (next : Saved → Builder Plan) : Builder Plan := do
  let binding ← saved root e.span role
  let value ← expression root e
  return .sequence root binding value (← next binding)

private partial def operands (root : Span) (es : List Expr)
    (next : List Saved → Builder Plan) : Builder Plan :=
  match es with
  | [] => next []
  | e :: rest => operand root e "value" fun binding =>
      operands root rest fun bindings => next (binding :: bindings)

private partial def reference (root : Span) (target : Expr)
    (next : Reference → Builder Plan) : Builder Plan :=
  match target with
  | .var source name => next (.local name source)
  | .read _ _ receiver => operand root receiver "receiver" fun receiver =>
      next (.field target receiver none)
  | .index _ _ receiver key | .elemAt _ receiver key =>
      operand root receiver "receiver" fun receiver =>
        operand root key "key" fun key => next (.field target receiver (some key))
  | _ => next (.local "" target.span)

/-- `e`'s plan, observed at its span unless `e` is a residual keeping the
    span of the source expression whose value it computes, which is
    observed where it starts (`residual`). -/
private partial def expression (root : Span) (e : Expr) (observed : Bool := true) : Builder Plan := do
  let atom := fun prepared => Plan.atom e.span (.evaluate e prepared (effect e))
  let core : Plan ← match e with
    | .var .. | .lit .. | .lambda .. | .ctor .. | .block .. => pure (atom e)
    | .not pos a => operand root a "value" fun a => do pure (atom (.not pos (readSaved a)))
    | .unary pos op a => operand root a "value" fun a => do pure (atom (.unary pos op (readSaved a)))
    | .cast pos annot a => operand root a "value" fun a => do pure (atom (.cast pos annot (readSaved a)))
    | .shapeTest pos tag equal a => operand root a "value" fun a => do
        pure (atom (.shapeTest pos tag equal (readSaved a)))
    | .tagMember pos domain field tags u a => operand root a "value" fun a => do
        pure (atom (.tagMember pos domain field tags u (readSaved a)))
    | .read pos field a => operand root a "receiver" fun a => do pure (atom (.read pos field (readSaved a)))
    | .equality pos equal left right => operand root left "value" fun left => do
        operand root right "value" fun right => do pure (atom (.equality pos equal (readSaved left) (readSaved right)))
    | .singletonTest pos tag equal testLeft left right => operand root left "value" fun left => do
        operand root right "value" fun right => do
          pure (atom (.singletonTest pos tag equal testLeft (readSaved left) (readSaved right)))
    | .arith pos op left right => operand root left "value" fun left => do
        operand root right "value" fun right => do pure (atom (.arith pos op (readSaved left) (readSaved right)))
    | .index pos field receiver key => operand root receiver "receiver" fun receiver => do
        operand root key "key" fun key => do pure (atom (.index pos field (readSaved receiver) (readSaved key)))
    | .elemAt pos receiver key => operand root receiver "receiver" fun receiver => do
        operand root key "key" fun key => do pure (atom (.elemAt pos (readSaved receiver) (readSaved key)))
    | .inKeys pos key object => operand root key "key" fun key => do
        operand root object "receiver" fun object => do pure (atom (.inKeys pos (readSaved key) (readSaved object)))
    | .assign pos name namePos rhs => operand root rhs "value" fun rhs => do
        pure (atom (.assign pos name namePos (readSaved rhs)))
    | .write pos field receiver rhs => operand root receiver "receiver" fun receiver => do
        operand root rhs "value" fun rhs => do pure (atom (.write pos field (readSaved receiver) (readSaved rhs)))
    | .indexWrite pos field receiver key rhs => operand root receiver "receiver" fun receiver => do
        operand root key "key" fun key => do operand root rhs "value" fun rhs => do
          pure (atom (.indexWrite pos field (readSaved receiver) (readSaved key) (readSaved rhs)))
    | .elemWrite pos receiver key rhs => operand root receiver "receiver" fun receiver => do
        operand root key "key" fun key => do operand root rhs "value" fun rhs => do
          pure (atom (.elemWrite pos (readSaved receiver) (readSaved key) (readSaved rhs)))
    | .alloc pos names es => operands root es fun es => do pure (atom (.alloc pos names (es.map readSaved)))
    -- A spread followed by an element that runs code is copied where it is
    -- written, as a call's is.
    | .arrayLit pos es [] => operands root es fun es => do pure (atom (.arrayLit pos (es.map readSaved) []))
    | .arrayLit pos es spreads => callArguments root e es spreads 0 fun es => do
        pure (atom (.arrayLit pos (es.map readSaved) spreads))
    | .comma _ left right => operand root left "discard" fun _ => do
        operand root right "value" fun right => do pure (atom (.var e.span right.name))
    -- `(a, b) && c` is `a, (b && c)`, `||` alike: `a` runs, then the
    -- operator over `b`, whose test then refines `c`'s operands. `b && c`
    -- computes the whole's value, at the whole's claim, and is observed
    -- only as the whole, around `a` and itself.
    | .logical p andOp (.comma _ l r) right =>
        operand root l "discard" fun _ => expression root (.logical p andOp r right) (observed := false)
    | .logical _ andOp left right => logical root e left right andOp "condition"
    | .coalesce _ left right =>
        let binding ← saved root left.span "condition"
        pure (.choose e.span left.span .nullish binding (← expression root left)
          (← expression root right) (atom (.var e.span binding.name)))
    | .ifBody _ condition yes no =>
        let binding ← saved root condition.span "condition"
        pure (.choose e.span condition.span .truthy binding (← truthOf root condition)
          (← expression root yes) (← expression root no))
    | .optional _ mark receiver body =>
        let binding ← saved root mark "optional"
        let binding := { binding with name := chainName }
        pure (.choose e.span receiver.span .nullish binding (← expression root receiver)
          (atom (.lit e.span .vundef)) (← expression root body))
    -- `o.m?.(a)`'s object, saved under `objectName` for the body, which
    -- reads the method off it and passes it as the call's receiver.
    | .withObject _ mark object body =>
        let binding ← saved root mark "receiver"
        let binding := { binding with name := objectName }
        pure (.sequence e.span binding (← expression root object) (← expression root body))
    | .nullishAssign _ name namePos rhs =>
        let target := Expr.var namePos name
        reference root target fun location => do
          let previous ← saved root namePos "condition"
          let write ← operand root rhs "value" fun value => do
            pure (.atom e.span (.referenceWrite e.span location value))
          pure (.choose e.span namePos .nullish previous
            (.atom namePos (.referenceRead namePos location)) write (atom (.var e.span previous.name)))
    | .logicalAssign _ op target rhs => reference root target fun location => do
        let previous ← saved root target.span "condition"
        let read := Plan.atom target.span (.referenceRead target.span location)
        let write ← operand root rhs "value" fun value => do
          pure (.atom e.span (.referenceWrite e.span location value))
        let keep := atom (.var e.span previous.name)
        let test := if op == .nullish then Test.nullish else .truthy
        pure (.choose e.span target.span test previous read
          (if op == .orElse then keep else write) (if op == .orElse then write else keep))
    | .update _ _ target rhs _ => reference root target fun location => do
        let previous ← saved root target.span "previous"
        let read := Plan.atom target.span (.referenceRead target.span location)
        let update ← match rhs with
          | none => pure (Plan.atom e.span (.updateSaved e location previous none))
          | some rhs => operand root rhs "value" fun rhs => do
            pure (.atom e.span (.updateSaved e location previous (some rhs)))
        pure (.sequence e.span previous read update)
    | .withValue pos fn initial functionType bagType =>
      match fn, initial with
      | .lambda .., .alloc initialPos names fields =>
        operands root fields fun fields => pure
          (atom (.withValue pos fn (.alloc initialPos names (fields.map readSaved)) functionType bagType))
      | _, _ => pure (atom e)
    | .construct pos callee args spreads typeArgs => operand root callee "callee" fun callee => do
        callArguments root e args spreads 0 fun args => do
          pure (atom (.construct pos (readSaved callee) (args.map readSaved) spreads typeArgs))
    | .bindWithReceiver pos callee receiver args =>
        match callee, receiver, args with
        | .read _ _ object@(.var _ x), .var _ y, [] =>
          if x == y then
            operand root object "receiver" fun object => do
              let method ← saved root callee.span "method"
              let read := Plan.atom callee.span (.methodRead callee object none e)
              let after ← operand root receiver "receiver" fun receiver => do
                pure (atom (.bindWithReceiver pos (readSaved method) (readSaved receiver) []))
              pure (.sequence e.span method read after)
          else operand root callee "callee" fun callee => do
            operand root receiver "receiver" fun receiver => do
              pure (atom (.bindWithReceiver pos (readSaved callee) (readSaved receiver) []))
        | _, _, _ => operand root callee "callee" fun callee => do
            operand root receiver "receiver" fun receiver => do operands root args fun args => do
              pure (atom (.bindWithReceiver pos (readSaved callee) (readSaved receiver) (args.map readSaved)))
    | .callWithReceiver pos callee receiver args => operand root callee "callee" fun callee => do
        operand root receiver "receiver" fun receiver => do operands root args fun args => do
          pure (atom (.callWithReceiver pos (readSaved callee) (readSaved receiver) (args.map readSaved)))
    | .applyWithReceiver pos callee receiver list requiredList => operand root callee "callee" fun callee => do
        operand root receiver "receiver" fun receiver => do match list with
        | none => pure (atom (.applyWithReceiver pos (readSaved callee) (readSaved receiver) none requiredList))
        | some list => operand root list "value" fun list => do
            pure (atom (.applyWithReceiver pos (readSaved callee) (readSaved receiver) (some (readSaved list)) requiredList))
    | .call pos callee args spreads typeArgs => operand root callee "callee" fun callee => do
        callArguments root e args spreads 0 fun args => do
          pure (atom (.call pos (readSaved callee) (args.map readSaved) spreads typeArgs))
    | .invoke pos callee args spreads typeArgs =>
        let prepare := fun receiver key => do
          let method ← saved root callee.span "method"
          let read := Plan.atom callee.span (.methodRead callee receiver key e)
          let call ← callArguments root e args spreads 0 fun args => do
            pure (.atom e.span (.invokeSaved e (.invoke pos callee (args.map readSaved) spreads typeArgs) receiver method))
          pure (.sequence e.span method read call)
        match callee with
        | .read _ _ receiver => operand root receiver "receiver" fun receiver => do prepare receiver none
        | .index _ _ receiver key | .elemAt _ receiver key =>
            operand root receiver "receiver" fun receiver => do operand root key "key" fun key => do prepare receiver (some key)
        | _ => pure (atom e)
    | .build _ names es =>
        let empty ← saved root e.span "object"
        let body ← objectParts root e names es empty
        pure (.sequence e.span empty (.atom e.span (.emptyObject e.span)) body)
    | .objectAssign _ target sources => operand root target "receiver" fun target => do
        objectSources root e sources target
    | .arrayAssign _ targets rest rhs => operand root rhs "receiver" fun array => do
        arrayAssignments root e array targets rest
  return if observed then .observe e.span core else core

/-- `a && b` and `a || b`: the left operand, saved, then the right one where
    it is truthy (`&&`) or falsy (`||`), else the saved left value. -/
private partial def logical (root : Span) (e left right : Expr) (andOp : Bool) (role : String) :
    Builder Plan := do
  let binding ← saved root left.span role
  let lhs ← expression root left
  let rhs ← expression root right
  let keep := Plan.atom e.span (.evaluate e (.var e.span binding.name) (effect e))
  pure (.choose e.span left.span .truthy binding lhs
    (if andOp then rhs else keep) (if andOp then keep else rhs))

/-- A condition, whose truthiness alone its consumer reads. `&&` or `||`
    whose left operand is no test (`testForm`) yields its left operand's
    value where that decides; read for its truthiness, the operator's left
    dispatch is its truthiness (role `truth`), whose arms rebind the
    outcome, a Boolean. The plan's value is then that synthetic truth, never
    the operator's value: it carries no source obligation, so it is placed
    at an empty span no claim names, and the operands keep their own. -/
private partial def truthOf (root : Span) (cond : Expr) (observed : Bool := true) : Builder Plan :=
  match cond with
  -- `a, b` as a condition: `a` runs for its effects, then `b` is the
  -- condition, its tests refining in the state `a` leaves (JavaScript's
  -- comma); `(a, b) && c`, `(a, b) || c` and `!(a, b)` likewise run `a`
  -- first, then `b && c`, `b || c` or `!b`, which compute the whole's value
  -- at the whole's claim after `a` and so are not observed as it.
  | .comma _ left right => operand root left "discard" fun _ => truthOf root right
  | .logical p andOp (.comma _ l r) right =>
    operand root l "discard" fun _ => truthOf root (.logical p andOp r right) (observed := false)
  | .not p (.comma _ l r) =>
    operand root l "discard" fun _ => truthOf root (.not p r) (observed := false)
  -- `(a || b) || c` is `a || (b || c)` for its truthiness and its
  -- evaluation, `&&` alike: the left operand's operands are dispatched on
  -- in turn, the same operator's right operand its new right one's. The
  -- regrouped whole computes the whole's value where it starts and keeps
  -- its span; `b || c`, evaluated where `a` answered, is a residual.
  -- A left operand stays grouped where both its operands are tests, its
  -- first judged as a left operand (`leftTestForm`): `(!g(x) || b) || c`,
  -- `g(x)` a guard's call, regroups as `!g(x) || (b || c)`.
  | .logical p andOp (.logical _ andOp' l1 l2) right =>
    if andOp == andOp' && !(leftTestForm l1 && testForm l2) then
      truthOf root (.logical p andOp l1 (.logical (residual l2) andOp l2 right)) observed
    else logicalTruth root cond observed
  | _ => logicalTruth root cond observed
where
  logicalTruth (root : Span) (cond : Expr) (observed : Bool) : Builder Plan :=
  match cond with
  -- A negated operand that is no test, `!a || b` or `!a && b`: the left
  -- dispatch is `a`'s truthiness, its arms exchanged. Where `!a` decides,
  -- the outcome is that answer, `true` for `||` and `false` for `&&`, a
  -- literal at the span of the `!` (`negationMark`), which no source
  -- expression has and the producer claims at that literal; elsewhere it is
  -- `b`'s. `a` is evaluated once, then `b` exactly where `!a` does not
  -- decide, as the operator evaluates them.
  | .logical _ andOp (.not negation left) right =>
    if leftTestForm (.not negation left) then expression root cond observed
    else do
      let truth : Span := (cond.span.1, cond.span.1)
      let binding ← saved root left.span "truth"
      let lhs ← expression root left
      let rhs ← truthOf root right
      let mark := negationMark negation
      let decided := Expr.lit mark (.vbool (!andOp))
      let keep := Plan.atom mark (.evaluate decided decided .none)
      return .choose truth left.span .truthy binding lhs
        (if andOp then keep else rhs) (if andOp then rhs else keep)
  | .logical _ andOp left right =>
    if leftTestForm left then expression root cond observed
    else do
      let truth : Span := (cond.span.1, cond.span.1)
      let binding ← saved root left.span "truth"
      let lhs ← expression root left
      let rhs ← truthOf root right
      let keep := Plan.atom truth (.evaluate (.var truth binding.name) (.var truth binding.name) .none)
      return .choose truth left.span .truthy binding lhs
        (if andOp then rhs else keep) (if andOp then keep else rhs)
  | _ => expression root cond observed

private partial def callArguments (root : Span) (call : Expr) (args : List Expr) (spreads : List Nat) (index : Nat)
    (next : List Saved → Builder Plan) : Builder Plan :=
  match args with
  | [] => next []
  | e :: rest => operand root e "argument" fun value => do
      if spreads.contains index && rest.any (fun arg => match arg with | .var .. | .lit .. => false | _ => true) then
        let copied ← saved root e.span "spread"
        let after ← callArguments root call rest spreads (index+1) fun values => next (copied :: values)
        pure (.sequence root copied (.atom e.span (.snapshotSpread e value call)) after)
      else callArguments root call rest spreads (index+1) fun values => next (value :: values)

private partial def objectParts (root : Span) (original : Expr) (names : List (Option String))
    (es : List Expr) (base : Saved) : Builder Plan :=
  match names, es with
  | name :: names, e :: es => operand root e "value" fun value => do
      let merged ← saved root original.span "object"
      let operation := match name with
        | some key => Operation.addField original base (.str key) value es.isEmpty
        | none => .mergeObjects original.span base value es.isEmpty false
      let after ← objectParts root original names es merged
      pure (.sequence original.span merged (.atom original.span operation) after)
  | _, _ => pure (.atom original.span (.evaluate original (.var original.span base.name) .none))

private partial def objectSources (root : Span) (original : Expr) (sources : List Expr)
    (base : Saved) : Builder Plan :=
  match sources with
  | [] => pure (.atom original.span (.evaluate original (.var original.span base.name) .none))
  | e :: rest => operand root e "value" fun value => do
      let merged ← saved root original.span "object"
      let after ← objectSources root original rest merged
      pure (.sequence original.span merged (.atom original.span (.mergeObjects original.span base value rest.isEmpty true)) after)

private partial def arrayAssignments (root : Span) (original : Expr) (array : Saved)
    (targets : List (ArrayElem Expr)) (rest : Option (Span × Bool × ArrayElem Expr)) : Builder Plan :=
  match targets with
  | [] => match rest with
      | none => pure (.atom original.span (.evaluate original (.var original.span array.name) .none))
      | some (source, slice, target) => reference root target.target fun location => do
        let value ← saved root source "rest"
        let after := Plan.atom original.span (.evaluate original (.var original.span array.name) .none)
        let discard ← saved root original.span "discard"
        pure (.sequence original.span value (.atom source (.arrayRest source array target.index slice))
          (.sequence original.span discard
            (.atom source (.referenceWrite source location value)) after))
  | target :: targets => reference root target.target fun location => do
      let place := target.target.span
      let value ← saved root place "element"
      let read := Plan.atom place (.positionRead place array target.index)
      let read ← match target.default_ with
        | none => pure read
        | some fallback => do
          let test ← saved root place "condition"
          pure (.choose place place .defined test read
            (.atom place (.evaluate (.var place test.name) (.var place test.name) .none))
            (← expression root fallback))
      let discard ← saved root original.span "discard"
      let after ← arrayAssignments root original array targets rest
      pure (.sequence original.span value read (.sequence original.span discard
        (.atom place (.referenceWrite place location value)) after))
end

/-- The source expression's execution tree, with unique internal values scoped
    to this root. Construction consults syntax only. -/
def build (e : Expr) : Plan := (expression e.span e).run' 0

/-- A condition's execution tree: its truthiness alone is read. -/
def buildCondition (e : Expr) : Plan := (truthOf e.span e).run' 0

end Verification.SourceExecution
