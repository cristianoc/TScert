import Verification.Source.SourceExtraction
import Verification.Source.Claims.Schemes

/-! # The types of a function's declarations and expressions, computed

One forward walk over a function's fragment body, in evaluation order, that
computes the type of each expression occurrence and of each binding at each
statement entry from the types the source writes (parameters, annotated
declarations, signatures of the module values it reads) and the language's
typing of each construct. What it computes is a proposal: the proved rules
check every type the lowering states, so nothing here adds trust.

Evolving declarations use the producer's four bounded contract-growth
rounds and its unique-use fallback (proposal.ml:19-47). Each resulting
contract is a proposal checked from the declaration onwards. A construct
whose type the direct rule does not determine is recorded as undetermined.
A loop body is walked once, from the loop head, where each binding the loop
assigns holds its declared type (its annotation, or its initializer's type
widened as a `let` widens it); at a merge a binding holds the union of what
the arms give it.

`compareUnit` sets the computed types beside the claims document's at every
expression occurrence and statement entry the claims name. -/
namespace Verification.SourceExtraction.Synthesis
open Lean ProgramTyping PositiveRules LabelStore Fragment
open EquationGraphs (Tree)

/-- What a binding holds at a point: its current type, its declared type, and
the narrowed types of the member paths read from it. -/
structure Env where
  vars : List (String × Ty Tree) := []
  decl : List (String × Ty Tree) := []
  paths : List ((String × List PropKey) × Ty Tree) := []
  /-- Reached only through an arm a test leaves no value of a binding it
  held (an exhaustive test's remaining arm): walked for its entries, where
  it completes or returns unreached. -/
  ghost : Bool := false

/-- What ends a narrowed member path: anything (a call that may change a
value of the heap, a write of an unknown key), a write of a field the path
reads, an assignment of its root. -/
inductive PathEnd where
  | all
  | field (k : PropKey)
  | root (n : String)

/-- A generic module function: its binders' names and its signature at
given binder types, in claim form (`Instantiable.instantiate`). -/
structure Generic where
  binders : List String
  /-- Source binders with no declared bound, for primitive candidate widening. -/
  widenBinders : List String := []
  instantiate : List (String × Json) → SourceTypes.Lowering Json
  /-- Its binders a resolution qualifies, by position: each one's input,
  observation and result. -/
  resolution : List PositiveGraphs.ResolutionSlots := []
  /-- Each binder's bound at given binder types, where it states one. -/
  bounds : List (String × Json) → SourceTypes.Lowering (List (String × Option Json)) := fun _ => pure []

/-- What the walk records: each expression occurrence's construct kind and
computed type or reason, each statement entry's bindings, and the
environments a `break` leaves with, by label; and the generic module
functions it reads. -/
structure Walk where
  /-- Interiors under each advertised signature (expression_closures.ml:455-473). -/
  arrowClaims : List (Span × List (SourceClaims.Overlay Tree)) := []
  generics : List (String × Generic) := []
  /-- The types the `return`s of the body being walked give, and the result
  its signature expects. -/
  returns : List (Option (Ty Tree)) := []
  expected : Option (Ty Tree) := none
  /-- Each `let`'s storage contract, by its initializer's span and name:
  its declared type. -/
  contracts : List ((Span × String) × Ty Tree) := []
  /-- Evolving initializer contracts, proposed by at most four growth rounds
  (producer proposal.ml:19-47); each write is checked by the pass. -/
  assumed : List (Span × Ty Tree) := []
  evolving : List (String × (Span × Bool)) := []
  evolvedWrites : List (Span × Ty Tree) := []
  evolvedUses : List (Span × Ty Tree) := []
  following : List Stmt := []
  holders : List (String × String) := []
  /-- The type expected of a value, by the value's span: a declaration's,
  an assignment's or a return's. -/
  hints : List (Span × Ty Tree) := []
  /-- Fresh call results whose later uses require the general array contract. -/
  generalCalls : List Span := []
  /-- Whether the function literal being walked may change the heap: a write,
  an assignment of a binding it does not declare, or a call whose instance
  states another footprint than keeping both values and stores; and the
  bindings it declares. -/
  writes : Bool := false
  /-- Whether a call in it may leave a changed heap on its throw: one whose
  instance states no bound on a throw (`onThrow`). -/
  throwWrites : Bool := false
  /-- The changes it may make, by class of contents: to the old locations
  holding a value, and to those holding an array store. -/
  valueChange : Footprints.Change := .keep
  storeChange : Footprints.Change := .keep
  locals : List String := []
  exprs : Std.HashMap Span (String × Except String (Ty Tree)) := {}
  /-- The expressions whose computed type a rule the lowering shares refuses
  (`refusalMark`), by span, as last recorded. -/
  refusals : Std.HashMap Span String := {}
  /-- Each call of a generic module function, by its span: the type each
  binder takes at it, by the binder's name; and the last call's, until its
  call records it. -/
  instances : List (Span × List (String × Ty Tree)) := []
  /-- Each such call's certificate for each binder a resolution qualifies,
  by its span; and the last call's. -/
  resolutions : List (Span × List (String × ResolutionWire.Certificate)) := []
  lastResolution : List (String × ResolutionWire.Certificate) := []
  /-- The unit's own scheme row where a resolution qualifies its binders,
  with their names: what a certificate's binder names. -/
  scope : Option (PositiveGraphs.SchemeRow Tree × List String) := none
  /-- Adversarial proposals forced, for the referee's measurement
  (`TSCERT_FORCE`): `literals` states every function literal at keep/keep,
  `elements` every element read without `undefined`, `objects` every
  object literal at its expected type, `spreads` every spread with every
  key its operand's type states, `guards` every guard's and family guard's
  true answer on its false edge too, `reads` a member read's receiver
  without `null` and `undefined` at every later statement, `paths` each
  narrowed member path narrowed at every later statement, `loops` each
  path narrowed before a loop kept at its head, its body and its exit,
  `decided` every test's `false` answer unreached. -/
  force : List String := []
  /-- Where the unit's body completes: its bindings there, or none where it
  never completes. -/
  completion : Option (List (String × Ty Tree)) := none
  lastInstance : Option (List (String × Ty Tree)) := none
  entries : Std.HashMap Nat (List (String × Ty Tree)) := {}
  /-- Each statement entry's bindings and narrowed member paths by the
  statement's whole span: where statements of one start nest (a guard's
  `return c` read as `if (c) return true; else return false;`, each part at
  the start of `c`), each one's own. -/
  spanEntries : Std.HashMap Span (List (String × Ty Tree) × List (String × List (List PropKey × Ty Tree))) := {}
  /-- The bindings before each declaration of a statement declaring several,
  by the statement's start and the declared name: the entry of that
  declaration's own node. By a statement's start and `%return@p%`, the
  statement's entry in the copy of a finalizer the return at `p` passes. -/
  declarations : Std.HashMap (Nat × String) (List (String × Ty Tree)) := {}
  /-- Each statement entry's narrowed member paths, by root: what a test or
  a write found a field to hold (the entry's `current` contents). -/
  currents : Std.HashMap Nat (List (String × List (List PropKey × Ty Tree))) := {}
  /-- The member paths the walk reads at their narrowed types (a `.read` of a
  member path a test or a write narrowed there): an entry states a narrowed
  path only where this holds it or a longer path of the same root. -/
  readPaths : Std.HashSet (String × List PropKey) := {}
  breaks : List (Option String × Env) := []
  /-- The bindings a function literal walked so far assigns that it does not
  declare (captured ones, held in cells). -/
  closureAssigned : List String := []
  /-- The bindings the unit assigns that it holds in no slot: cells (a module
  binding, one a closure shares). -/
  cellAssigned : List String := []
  /-- The bindings the unit and the function literals being walked hold in
  cells (`cellLocals`: one a closure shares, every `let` of a module's
  initialization), whether or not the walk has met their assignment. -/
  heldCells : List String := []
  /-- The changes of a value location recorded so far, a cell's own
  assignment aside. -/
  valueWrites : Nat := 0
  /-- The unit's bindings held in slots (its parameters and declarations
  other than those held in cells): a completed member read narrows one. -/
  slots : Thunk (List String) := Thunk.pure []
  /-- The bindings a member read was made of, under `TSCERT_FORCE=reads`:
  held without `null` and `undefined` at every later statement. -/
  readForced : List String := []
  /-- A destructuring's collected bindings (`%v…`, `%rest`, `%items`) at
  the contracts the protocol's steps give them, by name. -/
  collected : List (String × Ty Tree) := []
  /-- The member paths narrowed so far, under `TSCERT_FORCE=paths`: held
  narrowed at every later statement. -/
  pathsForced : List ((String × List PropKey) × Ty Tree) := []
  /-- Whether a function literal is being walked. -/
  inLiteral : Bool := false
  /-- The bindings of the function literals being walked held in slots (each
  one's parameters and declarations no cell holds, `cellLocals`): a closure
  they hold sees each at the value it held when the closure was made. -/
  literalSlots : List String := []
  /-- Whether the walk reads its own record of changes as a declaration's
  footprint (`declarationEffects`): a call of an unknown callee, an
  iteration and a finalizer then change anything or bound no throw, and an
  assignment of a binding held in a cell changes the values. -/
  strict : Bool := false
  /-- Whether a handler catches what the statements being walked throw. -/
  caught : Bool := false
  /-- Whether the body being walked is an async literal's: a throw in it
  rejects the promise its call returns normally. -/
  asyncBody : Bool := false
  /-- The constants in scope: a write of a key one's record may lack grows
  its type. -/
  consts : List String := []
  /-- The constants in scope holding a condition's value, each with its
  initializer (`implicationForm`), and the unit's parameters held in no cell:
  where such a constant is `true`, what its condition narrows of those and
  of the constants (`constantImplications`). -/
  conditions : List (String × Expr) := []
  values : List String := []
  /-- Each constant holding a function literal of no type parameters and no
  rest: its literal's span and own parameters' types (the producer's
  `named_closure`, closure_offers.ml:29). -/
  closureConsts : List (String × Span × List (Ty Tree)) := []
  /-- Whether the walk is the module's initialization's. -/
  moduleInit : Bool := false
  /-- The signatures a use offers such a literal (`closure_offer`,
  closure_offers.ml:51), by the literal's span: found by a walk, read by the
  next (`walkUnit`). -/
  offered : List (Span × CallEffects.Arrow (Ty Tree)) := []
  offers : List (Span × CallEffects.Arrow (Ty Tree)) := []
  /-- The variadic signatures a use offers such a literal, as `offered` and
  `offers` hold the fixed ones. -/
  restOffered : List (Span × CallEffects.RestArrow (Ty Tree)) := []
  restOffers : List (Span × CallEffects.RestArrow (Ty Tree)) := []
  /-- Each unannotated constant holding an object literal, with its fields
  (the producer's `register_object`, closure_offers.ml:33). -/
  objectConsts : List (String × List (PropKey × Expr)) := []
  /-- Each annotated constant holding a class value whose constructor's body
  returns an allocation last: the class value's span, its constructor's
  parameters, its written instance, and its methods, each key of the
  instance's prototype chain holding a constant of `closureConsts` (the
  producer's `register_class`, closure_offers.ml:34-48). -/
  classConsts : List (String × Span × List (Ty Tree) × Ty Tree × List (PropKey × String)) := []
  /-- The construct signatures a use offers a class value (`offer_class`,
  closure_offers.ml:62-95), by its span, a variadic one with its pack:
  found by a walk, read by the next (`walkUnit`). -/
  ctorOffered : List (Span × CallEffects.MethodArrow (Ty Tree) × Option (Ty Tree)) := []
  ctorOffers : List (Span × CallEffects.MethodArrow (Ty Tree) × Option (Ty Tree)) := []
  /-- Each generic closure's scheme, by its span: the claim its annotations
  state (`writtenSchemes`), its row `Scheme.closureRows`'s. -/
  schemes : List (Span × Ty Tree) := []
  /-- The binders of the call a callback is being walked for that no actual
  has given a type yet. -/
  pending : List Tree := []
  /-- The binders of a call whose actual is being walked at its parameter,
  each standing for no type yet (the producer's `with_holes`,
  expression_support.ml:124-139). -/
  holes : List Tree := []
  /-- The constants holding a store the run allocated: each initialized by
  a call whose instance states a fresh result, or by such a constant (the
  producer's `fresh_expr`, source.ml:957-966); and whether the last call's
  instance states one. -/
  freshConsts : List String := []
  lastFresh : Bool := false
  /-- Whether the last call may have changed a value of the heap (its
  instance's footprint): the narrowed paths end there. -/
  changedValues : Bool := false
  /-- The environments a `continue` of the innermost loop leaves with. -/
  continues : List Env := []
  /-- Each `return` walked so far, last first: its statement's span, its
  value's (where a finalizer holds the return) and the environment it
  leaves with. -/
  held : List (Span × Span × Env) := []
  /-- The type the body of the last function literal walked returns (the
  union of its `return`s' values), where every one is determined. -/
  lastBody : Option (Ty Tree) := none
  /-- Whether the class value being walked is a fresh constructor (a class
  binding `C.[[class]]`): its first construct signature gives the instance
  its body allocates. -/
  freshClass : Bool := false
  /-- The allocations a fresh constructor's body returns last (its tails):
  made with their own keys exactly (`closure_offers.ml`, `tails`;
  `prepare_constructor`). -/
  exactAt : List Span := []
  /-- Each class value walked, by its constructor's span: a later class value
  whose code is that constructor (`Fragment.decodeBindings`) takes its
  construct signatures. -/
  classes : List (Span × Ty Tree) := []
  /-- The statement being walked, by its span; and each expression's
  computed type by that statement and its span: an expression of another
  statement may share a span (the parts a class's construction is lowered
  to), each point reading its own statement's. -/
  stmtAt : Span := (0, 0)
  exprsAt : Std.HashMap (Span × Span) (Except String (Ty Tree)) := {}
  /-- What the statements walked so far may end a narrowed path by: the
  loop being walked keeps across its exit the paths none of them ends. -/
  pathEnds : List PathEnd := []
  /-- The paths the loop just walked keeps: stated at its head and at each
  statement entry of its body, whose edges carry them. -/
  loopKept : List ((String × List PropKey) × Ty Tree) := []
  /-- The constants holding an allocation (an object or array literal): an
  iterator's step keeps no path of one (the producer's `allocated`). -/
  allocated : List String := []
  /-- Each expression walked, by its span: whether its walk ended a
  narrowed path (a call that may change a value of the heap, a write, an
  assignment). -/
  endsIn : Std.HashMap Span Bool := {}

abbrev W := StateT Walk Compiler

/-- The walk records what ends narrowed paths. -/
def ends (x : PathEnd) : W Unit := modify fun w => { w with pathEnds := x :: w.pathEnds }

/-- The paths of `env` none of `xs` ends. -/
def surviving (env : Env) (xs : List PathEnd) : List ((String × List PropKey) × Ty Tree) :=
  env.paths.filter fun ((root, path), _) => xs.all fun
    | .all => false
    | .field k => !path.contains k
    | .root n => n != root

/-- Sorted labels, retaining each label once in the sorted traversal. -/
def norm (A : Ty Tree) : Ty Tree := Id.run do
  let mut seen : Std.HashSet Tree := {}
  let mut out : Array Tree := #[]
  for a in A.mergeSort Labels.le do
    if !seen.contains a then
      seen := seen.insert a
      out := out.push a
  return out.toList

def graphNow : Compiler (PositiveGraphs.NormalGraph Tree) := return SourceTypes.graph (← table)

def prim (c : PositiveNormalization.Clause (Ty Tree)) : Compiler (Ty Tree) :=
  return [← lower (SourceTypes.use c)]

def boolTy : Ty Tree := norm [Labels.tru, Labels.fls]

def upd (xs : List (α × β)) (k : α) (v : β) [BEq α] : List (α × β) := (k, v) :: xs.filter (·.1 != k)

/-- The construct kind the table counts an expression under. -/
def kindOf : Expr → String
  | .var .. => "identifier"
  | .lit .. => "literal"
  | .equality .. | .singletonTest .. | .shapeTest .. | .tagMember .. | .inKeys .. | .not .. => "comparison"
  | .arith _ op _ _ => match op with
    | .lt | .le | .gt | .ge | .eq | .looseEq => "comparison"
    | _ => "arithmetic"
  | .unary .. | .update .. => "arithmetic"
  | .read .. | .index .. | .elemAt .. => "member read"
  | .call .. | .invoke .. | .construct .. | .callWithReceiver .. | .applyWithReceiver ..
  | .bindWithReceiver .. => "call"
  | .ifBody .. | .logical .. | .coalesce .. => "conditional"
  | _ => "other"

/-- A literal's type: its singleton, numbers and strings interned as the
claims' are (`SourceTypes.numberLabels`). -/
def literal : Claim.Val → Compiler (Ty Tree)
  | .vnull => pure [Labels.nul]
  | .vundef => pure [Labels.undef]
  | .vbool b => pure [if b then Labels.tru else Labels.fls]
  | .vnum b => prim (.numLit b)
  | .vstr s => lower (SourceTypes.numberLabels ⟨false, [.strLit s]⟩)
  | .vbigint i => lower (SourceTypes.numberLabels ⟨false, [.bigintLit i]⟩)

/-- A type shown to a reader of the comparison, two levels deep: records by
their fields, arrays by their elements, functions by their signatures. -/
partial def shown (T : EquationStore.State) (A : Ty Tree) (depth : Nat := 2) : String :=
  let G := SourceTypes.graph T
  let one (l : Tree) : String :=
    if depth == 0 then SourceTypes.render T [l] else
    match PositiveRules.expand G [l] with
    | [.refs fs [] vs os _ _ _] =>
      match (fs ++ vs).lookup SourceTypes.storeField with
      | some S => match PositiveRules.expand G S with
        | [.list t []] =>
          let parts := t.required.map (shown T · (depth - 1)) ++ t.optional.map (fun o => shown T o (depth - 1) ++ "?")
          let rest := (t.rest.map fun r => s!"...{shown T r (depth - 1)}").toList
          s!"[{", ".intercalate (parts ++ rest)}]"
        | _ => "array"
      | none =>
        let named := (fs ++ vs).filter (·.1 != SourceTypes.protoField) |>.map fun (k, B) =>
          s!"{match k with | .str n => n | _ => "#"}: {shown T B (depth - 1)}"
        let opt := os.map fun o => s!"{match o.key with | .str n => n | _ => "#"}?: {shown T o.type (depth - 1)}"
        "{" ++ ", ".intercalate (named ++ opt) ++ "}"
    | [.arrs L S] =>
      -- Each row with its effect, where it is not the ordinary one: its
      -- footprint by class, `T` a bounded throw, `F` a fresh result, `P` a
      -- promise, `R` a receiver's store or own locations, `+` anything else.
      let ch (c : Footprints.Change) : String := match c with
        | .keep => "keep" | .init => "init" | .scalar => "scalar" | .grow => "grow" | .any => "any"
      let eff (e : CallEffects.Effect) : String :=
        if e == CallEffects.Effect.ordinary then "" else
        let rest := { e with closed := .top, onThrow := false, fresh := false, promise := none,
                             receiverStore := false, receiverOwn := false }
        s!" !{ch e.closed.value}/{ch e.closed.store}{if e.onThrow then "T" else ""}{if e.fresh then "F" else ""}{if e.promise.isSome then "P" else ""}{if e.receiverStore || e.receiverOwn then "R" else ""}{if rest == CallEffects.Effect.ordinary then "" else "+"}"
      " & ".intercalate ((L.map fun a =>
        s!"({", ".intercalate (a.arguments.map (shown T · (depth - 1)))}) => {shown T a.result (depth - 1)}{eff a.effect}") ++
        S.map fun a =>
        s!"({", ".intercalate (a.arguments.1.map (shown T · (depth - 1)) ++ [s!"...{shown T a.arguments.2 (depth - 1)}"])}) => {shown T a.result (depth - 1)}{eff a.effect}")
    | [.ctors L S _] =>
      " & ".intercalate ((L.map fun a =>
        s!"new ({", ".intercalate (a.arguments.map (shown T · (depth - 1)))}) => {shown T a.result (depth - 1)}") ++
        S.map fun a =>
        s!"new ({", ".intercalate (a.arguments.1.map (shown T · (depth - 1)) ++ ["..."])}) => {shown T a.result (depth - 1)}")
    | _ => SourceTypes.render T [l]
  if A.isEmpty then "never" else " | ".intercalate (A.map one).eraseDups

/-- A `let`'s declared type from its initializer: each literal type widened
to its primitive (TypeScript's widening of a mutable location). -/
def widen (A : Ty Tree) : Compiler (Ty Tree) := do
  let G ← graphNow
  let mut out := []
  for l in A do
    match PositiveRules.expand G [l] with
    | [.numLit _] | [.numIn _] => out := out ++ (← prim .num)
    | [.strLit _] | [.strIn _] => out := out ++ (← prim .str)
    | [.boolLit _] => out := out ++ boolTy
    | [.bigintLit _] => out := out ++ (← prim .bigint)
    | _ => out := out ++ [l]
  return norm out

def shapeOf (G : PositiveGraphs.NormalGraph Tree) (l : Tree) : Option Tag :=
  match PositiveRules.expand G [l] with
  | [.str] | [.strLit _] | [.strIn _] => some .isStr
  | [.num] | [.numLit _] | [.numIn _] => some .isNum
  | [.bigint] | [.bigintLit _] => some .isBigint
  | [.bool] | [.boolLit _] => some .isBool
  | _ => none

def slice (A : Ty Tree) (tag : Tag) (q : Bool) (literalOperand : Bool := false) : Compiler (Ty Tree) := do
  let G ← graphNow
  -- `unknown` (a `source` label) as the kinds of value the test does not
  -- contradict, where it contradicts some (`BranchRefinement.sourceSlice`).
  let kinds : List (PositiveNormalization.Clause (Ty Tree)) := BranchRefinement.sourceKinds
  -- Equality with a literal holding: a label of its family is that
  -- singleton (the value the test compares with).
  let one : Option (Compiler (Ty Tree)) := if !q || !literalOperand then none else match tag with
    -- (`0` equals `-0` too: no one number)
    | .numEq b => if b == (0 : Float).toBits || b == (-0 : Float).toBits then none else some (prim (.numLit b))
    | .strEq v => some (literal (.vstr v))
    | .boolEq v => some (pure [if v then Labels.tru else Labels.fls])
    | .bigintEq i => some (literal (.vbigint i))
    | _ => none
  -- `Array.isArray` holding: the labels the edge's observation keeps, the
  -- built-ins' `readonly unknown[]` for the records and `unknown` it does
  -- not (`arrayRefine`, `BranchRefinement.arraySlice`).
  if tag == .isArray && q && G.builtins.isSome then
    return norm (arrayRefine G A (← builtinArrayTy))
  let mut out : Array Tree := #[]
  for a in BranchRefinement.tagSlice G A tag q do
    -- `k in x` holding: a record's optional `k` present (a field where the
    -- record states one, else a view); a dictionary not naming `k` states
    -- it as a view of its index.
    if let (.hasKey k, true) := (tag, q) then
      match PositiveRules.expand G [a] with
      | [.refs fs [] vs os ms bs st] =>
        if let some o := os.find? (·.key == k) then
          let os := os.filter (·.key != k)
          let c : PositiveNormalization.Clause (Ty Tree) :=
            if fs.isEmpty then .refs fs [] (vs ++ [(k, o.type)]) os ms bs st
            else .refs (fs ++ [(k, o.type)]) [] vs os ms bs st
          out := out ++ (← prim c).toArray
          continue
      | [.dict fs [] vs ix os ms bs cells st] =>
        if (fs.lookup k).isNone && (vs.lookup k).isNone && !os.any (·.key == k) then
          if let .str _ := k then
            if !ix.isEmpty then
              out := out ++ (← prim (.dict fs [] (vs ++ [(k, norm (ix.flatMap (·.2)))]) ix os ms bs cells st)).toArray
              continue
      | _ => pure ()
    if let some S := one then
      match PositiveRules.expand G [a], tag with
      | [.num], .numEq _ | [.str], .strEq _ | [.bool], .boolEq _ | [.bigint], .bigintEq _ =>
        out := out ++ (← S).toArray
        continue
      | _, _ => pure ()
    -- A type parameter's value (its meet with its bound) where a test naming
    -- one primitive family holds: that family, as for `unknown`; where it
    -- fails, the value stays (the producer's `typeof_slice` of a `Rigid`,
    -- refinement.ml:52-58).
    if let .meet _ := a then
      if [Tag.isNum, .isStr, .isBool, .isBigint, .isSymbol].contains tag then
        if q then
          for k in kinds.filter (fun k => tagClause tag k == some true) do out := out ++ (← prim k).toArray
        else out := out.push a
        continue
    -- Any other test: a meet row narrowed to the meets of its parts with
    -- each clause the test does not contradict, dropped where it
    -- contradicts every one (the lowering's `observedSlice`,
    -- Execution.lean:19-31; the producer's `narrow_rigid`,
    -- semantic.ml:498-508): `T ⊓ (null | number)` is `T ⊓ number` where a
    -- nullish test fails.
    if let .meet p cs also := StoreView.row (← table) a then
      -- A rigid value tested as a function keeps its parameter and meets
      -- the function kinds (refinement.ml:58, `T & Function`).
      if tag == .isFun && q then
        let functions := kinds.filter fun c => tagClause tag c == some true
        for c in PositiveNormalization.meetLists cs functions do
          out := out.push (← lower (SourceTypes.bounded p [c] also))
        continue
      let left := cs.filter fun c => tagClause tag c != some (!q)
      if left.length != cs.length then
        for c in left do out := out.push (← lower (SourceTypes.bounded p [c] also))
        continue
    if G.plain a && PositiveRules.expand G [a] == [.source] then
      let kept := kinds.filter fun k => tagClause tag k != some (!q)
      if kept.length < kinds.length then
        for k in kept do out := out ++ (← prim k).toArray
        continue
    out := out.push a
  -- A passed equality with a literal leaves the operand that value alone,
  -- where it may hold it (`Control.conditionContext`'s `single`).
  if let some S := one then
    if !out.isEmpty then return ← S
  return norm out.toList

/-- Numeric singleton exclusions, as successive false `slice`s. The common
case of a union of numeric singleton rows needs one row lookup per label
and one membership test; other rows use the general slicing rule. -/
def excludeNumbers (tags : List Tag) (A : Ty Tree) : Compiler (Ty Tree) := do
  let first :: tags := tags | return A
  -- The first slice splits a numeric set row into its interned singleton
  -- labels, with the same fallback where the graph lacks an element label.
  let A ← slice A first false
  if tags.isEmpty then return A
  let G ← graphNow
  let key (b : UInt64) := if numberEqual b (0 : Float).toBits then (0 : Float).toBits else b
  let excluded : Std.HashSet UInt64 := tags.foldl (fun acc t => match t with
    | .numEq b => if numberEqual b b then acc.insert (key b) else acc
    | _ => acc) {}
  let numbers := A.mapM fun l =>
    if G.plain l then match PositiveRules.expand G [l] with
      | [.numLit b] => some (l, b)
      | _ => none
    else none
  if let some numbers := numbers then
    return norm (numbers.filterMap fun (l, b) => if excluded.contains (key b) then none else some l)
  tags.foldlM (fun B t => slice B t false) A

/-- The union of two types, a member of `B` within `A` already stated by
`A`: one label for one meaning where the two state it twice. -/
def joinTy (A B : Ty Tree) : Compiler (Ty Tree) := do
  let T ← table
  return norm (A ++ B.filter fun b => !within T [b] A)

def nonNullish (A : Ty Tree) : Compiler (Ty Tree) := slice A .isNullish false

/-- The type a binding declared at `D` holds after an assignment of a value
of type `A`: `A` where it is within `D`; else the members of `D` some member
of `A` is within, `D` where none is (an assignment's narrowing). -/
def assigned (D A : Ty Tree) : Compiler (Ty Tree) := do
  let T ← table
  if !A.isEmpty && within T A D then return A
  let kept := D.filter fun d => A.any fun a => within T [a] [d]
  return if kept.isEmpty then D else kept

/-- The type an annotated declaration at `D` holds from an initializer of
type `A`: a primitive, nullish or callable member of `A` as `assigned`
gives it, a class value too, any other object at the members of `D` it is within (a store's contract is fixed
where it is made: it is never held at the exact type of the store it was
initialized from, which another alias may grow or write). -/
def declaredAt (D A : Ty Tree) : Compiler (Ty Tree) := do
  let G ← graphNow
  let T ← table
  let (prims, objs) := A.partition fun a =>
    (shapeOf G a).isSome || !(BranchRefinement.tagSlice G [a] .isNullish true).isEmpty ||
      !(ProgramTyping.callSigs G [a]).isEmpty ||
      (match PositiveRules.expand G [a] with | [.ctors ..] => true | _ => false)
  if objs.isEmpty then return ← assigned D A
  let kept := D.filter fun d => objs.any fun a => within T [a] [d]
  if kept.isEmpty then return ← assigned D A
  let ps ← if prims.isEmpty then pure [] else assigned D prims
  return norm (ps ++ kept)

/-- The prototype a primitive's member is read from, by its shape. -/
def protoFor (vars : List (String × Ty Tree)) (tag : Tag) : Compiler (Ty Tree) := do
  let some (_, name) := SourceTypes.primitivePrototypes.find? (·.1 == tag)
    | throw "a member of a primitive of no prototype"
  let some P := vars.lookup name | throw s!"{name} is not in scope"
  return P

/-- The labels a member read reads past its nullish guard: all but `null`
and `undefined` where the type holds both kinds (`nullishSplit`). -/
def present (G : PositiveGraphs.NormalGraph Tree) (A : Ty Tree) : Ty Tree :=
  match nullishSplit G A with
  | some (_, F) => F
  | none => A

/-- The mark of a walk failure that is the unit's refusal: a rule the
lowering shares refusing at the types the walk states, which the lowering's
own rule refuses at those types too: a read the read rule refuses
(`readCell`, a member the contract does not state; a primitive's prototype
stating none), and a call of one callable none of whose signatures admits
the actuals' count (`Plans.selectSignature`, a variadic one taking more
fixed parameters than the actuals). -/
def refusalMark : String := "refused at a "

def readRefusal (m : String) : String :=
  if m.startsWith refusalMark then m else refusalMark ++ "read: " ++ m

def callRefusal (m : String) : String :=
  if m.startsWith refusalMark then m else refusalMark ++ "call: " ++ m

/-- Union members for a read, as `ProgramTyping.members`. A record with
no repeated invariant key has no pair for `litClash` to exclude; checking
its keys first avoids expanding a large tag set merely to compare it with
itself. Other labels use `labelMembers` unchanged. -/
def readMembers (G : PositiveGraphs.NormalGraph Tree) (A : Ty Tree) : Ty Tree :=
  A.flatMap fun l =>
    match G l with
    | [c] => match ProgramTyping.recordFields c with
      | some fs =>
        let keys := fs.map (·.1)
        if keys.eraseDups.length == keys.length then [l] else ProgramTyping.labelMembers G l
      | none => ProgramTyping.labelMembers G l
    | _ => ProgramTyping.labelMembers G l

/-- `o.f` of an `o` of type `A`: each primitive member by its prototype's
field (a string's `length` a number), a function's `toString` by
`Function.prototype`'s (`Plans.primitiveArms`), an array's `length` a
number, and an object's field as the read rule reads it (`readCell`,
`HeapExpressionRules`' read, view, optional and prototype reads). A member
the read rule finds no contract stating is the unit's refusal there
(`refusalMark`). -/
def readField (vars : List (String × Ty Tree)) (A : Ty Tree) (fld : PropKey) : Compiler (Ty Tree) := do
  if A.isEmpty then return []
  let G ← graphNow
  -- A nullish receiver throws before its member is read: the read is of the
  -- others (`nullishSplit`, the lowering's read, Atoms.lean:599-618).
  -- Union elimination drops contradictory duplicate discriminants
  -- (`labelMembers`/`conflicting`; type_queries.ml:407-423).
  let A := (readMembers G (present G A)).filter fun l =>
    -- An empty intersection contributes no receiver. Drop it before
    -- partitioning dictionaries from the other object contracts.
    !(G.plain l && (PositiveRules.expand G [l]).isEmpty)
  let (prims, objs) := A.partition fun l => (shapeOf G l).isSome
  -- A function's `toString`: no function owns one, so its lookup reaches
  -- `Function.prototype`'s (`Plans.primitiveArms`, Plans.lean:631-643).
  let isFunction (l : Tree) : Bool := match PositiveRules.expand G [l] with
    | [.arrs ..] | [.callable ..] | [.ctors ..] => true
    | _ => false
  let (funs, objs) := if fld == "toString" then objs.partition isFunction else ([], objs)
  let mut out : Ty Tree := []
  for l in prims do
    let some tag := shapeOf G l | continue
    if tag == .isStr && fld == lengthKey then
      out := out ++ (← prim .num)
    else
      -- Plans.primitiveArms (Plans.lean:646-648) refuses the same missing
      -- prototype; it is a located read refusal, not an unknown construct.
      let P ← tryCatch (protoFor vars tag) fun m => throw (readRefusal m)
      let some B := fieldRow G P fld | throw (readRefusal s!"a primitive's prototype names no field '{reprStr fld}'")
      out := out ++ B
  if !funs.isEmpty then
    let some P := vars.lookup SourceTypes.functionPrototypeName
      | throw s!"{SourceTypes.functionPrototypeName} is not in scope"
    let some B := fieldRow G P fld | throw (readRefusal "Function.prototype names no field 'toString'")
    out := out ++ B
  -- An array's `length` a number, each array arm of a union apart from the
  -- others (the lowering's read of a union, each alternative as it reads).
  let (arrs, objs) := if fld == lengthKey then objs.partition fun l => arraysOnly G [l] else ([], objs)
  if !arrs.isEmpty then out := out ++ (← prim .num)
  let (dicts, objs) := objs.partition fun l => match PositiveRules.expand G [l] with
    | [.dict _ [] ..] => true
    | _ => false
  for l in dicts do
    if let [.dict fs [] vs ix os _ _ _ _] := PositiveRules.expand G [l] then
      match fs.lookup fld <|> vs.lookup fld with
      | some B => out := out ++ B
      | none =>
        match os.find? (·.key == fld) with
        | some o => out := out ++ o.type ++ [Labels.undef]
        | none =>
          let some (_, B) := (PositiveNormalization.numericFirst ix).find? (fun (K, _) => K.surely fld)
            | throw (readRefusal s!"read of a key '{fld}' no index of the object constrains")
          out := out ++ B ++ [Labels.undef]
  if !objs.isEmpty then
    if fld == lengthKey && arraysOnly G objs then out := out ++ (← prim .num)
    else
      -- A receiver typed by a bounded binder reads through the bound
      -- (`Plans.boundOf`, the lowering's `throughBound`, Expression.lean:319).
      let objs := norm (← objs.mapM fun l => boundOf [l]).flatten
      let G ← graphNow
      let plan ← tryCatch (readCell G [objs] fld (DirectProof.var [objs] 0 objs)) fun m =>
        throw (if m.startsWith "read of a field" || m.startsWith "read of a key" ||
          m == "read receiver must name a cell contract" then readRefusal m else m)
      out := out ++ plan.type
  return norm out

/-- The positions of an array's store: the type at index `k`, where the key
is that one index, with `undefined` past the required positions; any
position's with `undefined` otherwise (an index read past the end). -/
def elementAt (A : Ty Tree) (index : Option Nat) (missing : Bool := true) : Compiler (Ty Tree) := do
  if A.isEmpty then throw "an element read of a value of no type"
  let G ← graphNow
  let A ← (present G A).mapM fun l => boundOf [l]
  let A := norm A.flatten
  let G ← graphNow
  let mut out : Ty Tree := []
  for l in A do
    -- An empty intersection arm has no element to contribute.
    if G.plain l && (PositiveRules.expand G [l]).isEmpty then continue
    if shapeOf G l == some .isStr then
      out := out ++ (← prim .str) ++ (if missing then [Labels.undef] else [])
      continue
    match storeOf G [l] with
    | some S =>
      match PositiveRules.expand G S with
      | [.list t []] =>
        match index.bind t.position with
        | some B => out := out ++ B ++
            (if missing && t.required.length ≤ index.getD 0 then [Labels.undef] else [])
        | none => out := out ++ t.required.flatten ++ t.optional.flatten ++ t.rest.getD [] ++
            (if missing then [Labels.undef] else [])
      | _ => throw "an array of more than one tuple contract"
    | none =>
      match PositiveRules.expand G [l] with
      | [.dict _ _ _ ix _ _ _ _ _] =>
        out := out ++ ix.flatMap (·.2) ++ (if missing then [Labels.undef] else [])
      | _ => throw "an element read of a value that is no array"
  return norm out

/-- The one index a key's type names, where it names one. -/
def keyIndex (K : Ty Tree) : Compiler (Option Nat) := do
  let G ← graphNow
  match K.flatMap fun l => PositiveRules.expand G [l] with
  | [.numLit b] => return indexOfBits b
  | _ => return none

def keyString (K : Ty Tree) : Compiler (Option String) := do
  let G ← graphNow
  match K.flatMap fun l => PositiveRules.expand G [l] with
  | [.strLit s] => return some s
  | _ => return none

/-- A signature as a call selects it: its parameters, whether further
actuals are admitted (a rest), and its result. -/
structure Sig where
  params : List (Ty Tree)
  rest : Bool
  result : Ty Tree

/-- A position a call may omit: one whose contract admits `undefined`, also
beside a binder (`T | undefined`, which no clause expansion opens). -/
def omissible (G : PositiveGraphs.NormalGraph Tree) (A : Ty Tree) : Bool :=
  A.contains Labels.undef || admitsUndefined G A

/-- The signature a call's actuals select: the first whose parameter count
admits them (omitted positions admitting `undefined`, also before a rest)
and whose parameters each actual is within, else the first whose count
admits them (the producer's `callable`, expression_calls.ml:757-761). -/
def choose (sigs : List Sig) (args : List (Ty Tree)) : Compiler Sig := do
  let T ← table
  let G := SourceTypes.graph T
  let fits (s : Sig) : Bool :=
    (s.rest && s.params.length ≤ args.length) ||
      (args.length ≤ s.params.length && (s.params.drop args.length).all (fun D => omissible G D || within T [Labels.undef] D))
  let candidates := sigs.filter fits
  let accepts (s : Sig) : Bool := (args.zip s.params).all fun (A, D) => within T A D
  match candidates.find? accepts <|> candidates.head? with
  | some s => return s
  | none => throw s!"no signature admits {args.length} actuals (of {sigs.map fun s => (s.params.length, s.rest)})"

/-- The signatures a callable type offers, fixed and variadic. -/
def callSigsOf (F : Ty Tree) : Compiler (List Sig) := do
  let G ← graphNow
  let fixed := (ProgramTyping.callSigs G F).map fun a => ⟨a.arguments, false, a.result⟩
  let rests := (ProgramTyping.restSigs G F).map fun a => ⟨a.arguments.1, true, a.result⟩
  return fixed ++ rests

/-- The prototype a record reads an inherited key from: its prototype field
or view. -/
def protoOf (G : PositiveGraphs.NormalGraph Tree) (O : Ty Tree) : Option (Ty Tree) :=
  match PositiveRules.expand G O with
  | [.refs fs [] vs _ _ _ _] => (fs ++ vs).lookup SourceTypes.protoField
  | _ => none

def memberSigs (m : MethodMembers.Sig (Ty Tree)) : Compiler (List Sig) := do
  if m.calls.isEmpty && m.rests.isEmpty then
    throw "a generic member: its signature needs type arguments"
  return m.calls.map (fun a => ⟨a.arguments, false, a.result⟩) ++
    m.rests.map (fun a => ⟨a.arguments.1, true, a.result⟩)

/-- A member path `root.path` narrowed by `k`: its narrowed type, else the
type read along it, at `k`'s, where the path is a member of an object other
than `length` (a primitive's member is no location). -/
def narrowPath (env : Env) (root : String) (path : List PropKey) (k : Ty Tree → Compiler (Ty Tree)) :
    Compiler Env := do
  let some A := env.vars.lookup root | return env
  -- Each prefix at its narrowed type where a test narrowed it, as the read
  -- of the prefix reads it (`.read`).
  let along (p : List PropKey) : Compiler (Option (Ty Tree)) := tryCatch (do
      let mut B := A
      let mut pre : List PropKey := []
      for f in p do
        pre := pre ++ [f]
        B ← match env.paths.lookup (root, pre) with
          | some P => pure P
          | none => readField env.vars B f
      return some B) fun _ => pure none
  let P ← along path
  let G ← graphNow
  let receiver ← along path.dropLast
  let ofObject := path.getLast? != some lengthKey && receiver.any fun R => R.all fun l => (shapeOf G l).isNone
  match P with
  | some P => if ofObject then return { env with paths := upd env.paths (root, path) (← k P) } else return env
  | none => return env

/-- Disjointness against one path's contents. Clause rows and their plainness
are read once for the path. A common label with a consistent self-meet
settles overlap before the pairwise clause test; the remaining test is
`typesDisjoint`, flattened by `BranchRefinement.meetsNone_labels`. -/
structure PathDisjoint where
  clauses : List (PositiveNormalization.Clause (Ty Tree))
  shared : Std.HashSet Tree

/-- Materialize a path's clause rows before testing its receiver arms. -/
def preparePathDisjoint (G : PositiveGraphs.NormalGraph Tree) (P : Option (Ty Tree)) :
    Option PathDisjoint := do
  let P ← P
  if !G.plainTy P then none else
    let rows := P.map fun l => (l, clausesOf G [l])
    let shared : Std.HashSet Tree := rows.foldl (fun acc (l, cs) =>
      if BranchRefinement.meetsNone cs cs then acc else acc.insert l) {}
    some ⟨rows.flatMap (·.2), shared⟩

/-- Test against materialized path clauses at the current graph. -/
def pathDisjoint (P : Option PathDisjoint) (B : Ty Tree) : Compiler Bool := do
  let some P := P | return false
  if B.any P.shared.contains then return false
  let G ← graphNow
  return G.plainTy B && BranchRefinement.meetsNone (clausesOf G B) P.clauses

/-- The narrowing a test of `tag` answering `q` makes of the binding or the
member path `target` reads, and, for a test of a member `x.f`, of `x` itself:
the members of `x`'s type whose `f` can answer so (a discriminant). -/
def narrowTargetWith (env : Env) (target : Expr) (slice : Ty Tree → Compiler (Ty Tree)) : Compiler Env := do
  match memberPath target with
  | some (root, []) =>
    let some A := env.vars.lookup root | return env
    return { env with vars := upd env.vars root (← slice A) }
  | some (root, path) =>
    let some A := env.vars.lookup root | return env
    let mut env ← narrowPath env root path fun P => slice P
    -- Bind the materialized rows here: a partially applied function would
    -- rebuild them when each receiver arm runs its Compiler action.
    let prepared ← pure (preparePathDisjoint (← graphNow) (env.paths.lookup (root, path)))
    let disjoint := pathDisjoint prepared
    -- A discriminant of a member path (`o.key.kind`): the path `o.key` to
    -- its arms whose field can answer so, as the root below.
    if let some f := path.getLast? then
      if path.length > 1 then
        env ← narrowPath env root path.dropLast fun P => do
          let mut kept : Ty Tree := []
          for l in P do
            let keep ← tryCatch (do
                let B ← readField env.vars [l] f
                let B ← slice B
                return !B.isEmpty && !(← disjoint B)) fun _ => pure true
            if keep then kept := kept ++ [l]
          return kept
    -- Successive tests share the path's accumulated contents: an arm
    -- disjoint from them is impossible (`contents_meet`, refinement.ml:276).
    if let [f] := path then
      let mut kept : Ty Tree := []
      for l in A do
        let keep ← tryCatch (do
            let B ← readField env.vars [l] f
            let B ← slice B
            return !B.isEmpty && !(← disjoint B)) fun _ => pure true
        if keep then kept := kept ++ [l]
      -- (none of them: the binding holds no value there)
      env := { env with vars := upd env.vars root kept }
    return env
  | none => return env

def narrowTarget (env : Env) (target : Expr) (tag : Tag) (q : Bool) (literalOperand : Bool := false) : Compiler Env :=
  narrowTargetWith env target fun A => slice A tag q literalOperand

/-- A binding narrowed to a promised type `R`: its members within
`R`, else `R` (a type guard's true arm, an assertion's normal return). -/
def narrowTo (env : Env) (target : Expr) (R : Ty Tree) : Compiler Env := do
  let T ← table
  let at_ (A : Ty Tree) : Ty Tree :=
    let kept := A.filter fun a => within T [a] R
    if kept.isEmpty then R else kept
  match memberPath target with
  | some (root, []) =>
    let some A := env.vars.lookup root | return env
    return { env with vars := upd env.vars root (at_ A) }
  -- A guard's actual a member path (`isX(a.b)`): the path so narrowed.
  | some (root, path) => narrowPath env root path fun A => pure (at_ A)
  | _ => return env

/-- A write of key `k` at a value of type `R` on a constant of type `O` whose
records may lack it: the contract the key is added at (the optional field's
where a record states one, else the value's type, a literal's widened), and
`O` with every record owning it there (TypeScript's growth of a fresh
literal's keys, the write step's output). None where `O` is not records or
states `k` of each. -/
def growth (O : Ty Tree) (k : PropKey) (R : Ty Tree) (literal_ : Bool) : Compiler (Option (Ty Tree × Ty Tree)) := do
  let G ← graphNow
  -- A dictionary retains its index contracts when a write establishes a
  -- named key (type_queries.ml:525-564); no store is upcast.
  if !O.isEmpty && O.all (fun l => match PositiveRules.expand G [l] with | [.dict _ [] ..] => true | _ => false) then
    let rows := O.filterMap fun l => match PositiveRules.expand G [l] with
      | [.dict fs [] vs ix os ms bs cells st] => some (fs, vs, ix, os, ms, bs, cells, st)
      | _ => none
    if !(rows.any fun (fs, vs, _, _, ms, _, _, _) => (fs.lookup k).isNone && (vs.lookup k).isNone && !ms.any (·.key == k)) then return none
    if rows.any (fun (_, _, _, os, _, bs, _, _) =>
        os.any (fun o => o.key == k && o.readonly) || bs.any (fun b => !b.among && b.keys.contains k)) then return none
    let D := rows.findSome? fun (_, _, _, os, _, _, _, _) => (os.find? (·.key == k)).map (·.type)
    let C ← match D with | some D => pure D | none => if literal_ then widen R else pure R
    let grown ← rows.mapM fun (fs, vs, ix, os, ms, bs, cells, st) =>
      prim (.dict (fs.filter (·.1 != k) ++ [(k, C)]) [] (vs.filter (·.1 != k)) ix (os.filter (·.key != k)) ms bs cells st)
    return some (C, norm grown.flatten)
  let mut arms : List (List (PropKey × Ty Tree) × List (PropKey × Ty Tree) × List (OptionalField (Ty Tree)) ×
      List (MethodMembers.Sig (Ty Tree)) × List KeyBound × List PropKey) := []
  for l in O do
    let [.refs fs [] vs os ms bs st] := PositiveRules.expand G [l] | return none
    if fs.any (·.1 == SourceTypes.storeField) || fs.any (·.1 == SourceTypes.protoField) then return none
    if os.any (fun o => o.key == k && o.readonly) || bs.any (fun b => !b.among && b.keys.contains k) then return none
    arms := arms ++ [(fs, vs, os, ms, bs, st)]
  if arms.isEmpty then return none
  let lacks := arms.any fun (fs, vs, _, ms, _, _) => (fs.lookup k).isNone && (vs.lookup k).isNone && !ms.any (·.key == k)
  if !lacks then return none
  let declared := arms.findSome? fun (_, _, os, _, _, _) => (os.find? fun o => o.key == k && !o.readonly).map (·.type)
  let c ← match declared with
    | some D => pure D
    | none => if literal_ then widen R else pure R
  let mut grown : Ty Tree := []
  for (fs, vs, os, ms, bs, st) in arms do
    let bs := bs.map fun b => if b.among && !b.keys.contains k then { b with keys := b.keys ++ [k] } else b
    grown := grown ++ (← prim (.refs (fs.filter (·.1 != k) ++ [(k, c)]) [] (vs.filter (·.1 != k)) (os.filter (·.key != k)) ms bs st))
  return some (c, norm grown)

/-- Holders of a local's object, as analysis_state.ml's holders_of: aliases
are followed transitively; a cell keeps its declared contract. -/
def growHolders (env : Env) (w : Walk) (n : String) (A : Ty Tree) : Env := Id.run do
  let mut names := [n]
  for _ in w.holders do
    for (a, b) in w.holders do
      if names.contains a || names.contains b then names := (a :: b :: names).eraseDups
  return { env with vars := env.vars.map fun (m, B) =>
    (m, if names.contains m && (w.consts.contains m || w.slots.get.contains m || w.literalSlots.contains m) then A else B) }

/-- Whether evaluating an expression may call: conservatively, any form
other than a name, a literal, a read and the tests and operators over them. -/
partial def mayCall : Expr → Bool
  | .var .. | .lit .. => false
  | .read _ _ x | .not _ x | .unary _ _ x | .shapeTest _ _ _ x | .tagMember _ _ _ _ _ x | .cast _ _ x => mayCall x
  | .equality _ _ l r | .singletonTest _ _ _ _ l r | .logical _ _ l r | .coalesce _ l r | .arith _ _ l r
  | .inKeys _ l r | .elemAt _ l r | .index _ _ l r => mayCall l || mayCall r
  | _ => true

/-- Whether a statement may end a narrowed path of a binding it does not
assign: conservatively, any form but those whose expressions call nothing,
an increment or an assignment of a binding allowed (`mayCall`). -/
partial def quietStmt : Stmt → Bool
  | .ret _ e | .effect _ e | .throw _ e => quietExpr e
  | .constants _ bs | .mutables _ bs => bs.all fun b => quietExpr b.init
  | .ite _ c t e => quietExpr c && t.all quietStmt && (e.getD []).all quietStmt
  | .loop _ c b u _ => quietExpr c && b.all quietStmt && u.all quietStmt
  | .block _ _ b => b.all quietStmt
  | .brk .. | .cont .. => true
  | _ => false
where
  quietExpr : Expr → Bool
    | .update _ _ (.var ..) rhs _ => (rhs.map quietExpr).getD true
    | .assign _ _ _ rhs => quietExpr rhs
    | e => !mayCall e

/-- An environment's narrowed paths by root. -/
def currentOf (env : Env) : List (String × List (List PropKey × Ty Tree)) :=
  let roots := ((env.paths.filter (!·.2.isEmpty)).map (·.1.1)).eraseDups
  roots.map fun r => (r, (env.paths.filter (fun ((q, _), A) => q == r && !A.isEmpty)).map fun ((_, p), A) => (p, A))

/-- Whether a test leaves an arm unreached: a binding or a path it leaves no
value it held (an exhaustive test's remaining arm). The arm is still walked,
a ghost, for its entries, each binding so emptied at the empty type. -/
def emptiedBy (before after : Env) : Option Env :=
  let emptied (old : Option (Ty Tree)) (A : Ty Tree) : Bool := A.isEmpty && !(old.getD []).isEmpty
  let pathOld (p : String × List PropKey) : Option (Ty Tree) :=
    (before.paths.lookup p) <|> some [Labels.undef]
  if after.vars.any (fun (n, A) => emptied (before.vars.lookup n) A) ||
     after.paths.any (fun (p, A) => emptied (pathOld p) A) then
    some { after with ghost := true }
  else none

/-- The union of two environments where both are reached: each binding both
hold, at the union of its two types; each path both narrow, likewise. -/
def join : Option Env → Option Env → Option Env
  | none, b => b
  | a, none => a
  | some a, some b =>
    if a.ghost && !b.ghost then some b else if b.ghost && !a.ghost then some a else some {
      ghost := a.ghost
      vars := a.vars.filterMap fun (n, A) => (b.vars.lookup n).map fun B => (n, if A == B then A else norm (A ++ B))
      decl := a.decl ++ b.decl.filter fun (n, _) => (a.decl.lookup n).isNone
      paths := a.paths.filterMap fun (p, A) => (b.paths.lookup p).map fun B => (p, norm (A ++ B)) }

/-- The environment at a loop head: every binding the loop assigns at its
declared type, and no path narrowed (a loop head holds its given facts,
which state no field's contents). -/
def loopHead (env : Env) (ss : List Stmt) : Env :=
  let changed := env.vars.filter fun (n, _) => ss.any (assignsStmt n)
  { env with
    vars := env.vars.map fun (n, A) =>
      if changed.any (·.1 == n) then (n, (env.decl.lookup n).getD A) else (n, A)
    paths := [] }

/-- Each binding held in a cell at its declared type: what a cell holds is a
current-content fact, which no step keeps across a write without a
separation and no throw keeps (the producer's `forget`, environment.ml:138,
at a step that may write cells, execution_analysis.ml:243, and at a
handler's edge, proposal_flow.ml:556).
(`TSCERT_FORCE=cells` keeps them, the adversarial proposal) -/
def cellsDeclared (w : Walk) (e : Env) : Env :=
  if w.force.contains "cells" then e else
  { e with vars := e.vars.map fun (n, A) =>
      if w.cellAssigned.contains n || w.heldCells.contains n then (n, (e.decl.lookup n).getD A) else (n, A) }

/-- Whether each member of the path `root.path` is a key every arm of its
receiver states stable (the producer's `stable_path` through
`stable_member`, refinement.ml:195-251): no step writes it, so its
narrowing survives a call that may change the heap. -/
def stablePath (env : Env) (root : String) (path : List PropKey) : Compiler Bool := do
  let some A := env.vars.lookup root | return false
  if path.isEmpty then return false
  let G ← graphNow
  let mut R := A
  let mut pre : List PropKey := []
  for f in path do
    if R.isEmpty then return false
    for l in R do
      match PositiveRules.expand G [l] with
      | [.refs _ _ _ _ _ _ st] => if !st.contains f then return false
      | _ => return false
    pre := pre ++ [f]
    R ← match env.paths.lookup (root, pre) with
      | some B => pure B
      | none => tryCatch (readField env.vars R f) fun _ => pure []
  return true

/-- Whether an iterator's step keeps the path `root.path`: each member a
required field every record arm of its receiver states, none a `length`
(the producer's `separated_path`, statement_analysis.ml:785-793, the
locations the iterator is apart from). -/
def separatedPath (env : Env) (root : String) (path : List PropKey) : Compiler Bool := do
  let some A := env.vars.lookup root | return false
  let G ← graphNow
  let mut R := A
  for f in path do
    if f == lengthKey || R.isEmpty then return false
    for l in R do
      let [.refs fs _ vs _ _ _ _] := PositiveRules.expand G [l] | return false
      if (fs.lookup f).isNone && (vs.lookup f).isNone then return false
    let some B ← tryCatch (some <$> readField env.vars R f) fun _ => pure none | return false
    R := B
  return true

/-- Whether a test of a value of type `C` cannot answer `q`: its truthy
slice for `q` is empty (`BranchRefinement.tagSlice`, the edge's own
refinement of the test's value). -/
def decided (C : Option (Ty Tree)) (q : Bool) : Compiler Bool := do
  let some C := C | return false
  if C.isEmpty then return false
  return (BranchRefinement.tagSlice (← graphNow) C .truthy q).isEmpty

/-- An environment with the paths `kept` beside its own. -/
def keepPaths (kept : List ((String × List PropKey) × Ty Tree)) (env : Env) : Env :=
  { env with paths := env.paths ++ kept.filter fun (p, _) => (env.paths.lookup p).isNone }

def typeofNames : List String := ["bigint", "boolean", "function", "number", "object", "string", "symbol", "undefined"]

def need (o : Option (Ty Tree)) (what : String) : Compiler (Ty Tree) :=
  match o with
  | some A => pure A
  | none => throw s!"{what} undetermined"

/-- The result of an arithmetic or relational operator (the operator typing
of `OperatorTyping`): a Boolean for a comparison, a string for `+` with a
string operand, a bigint for bigint operands, a number otherwise. -/
def arithType (op : Arith) (L R : Ty Tree) : Compiler (Ty Tree) := do
  let G ← graphNow
  let isStr (A : Ty Tree) := A.any fun l => shapeOf G l == some .isStr
  let isBig (A : Ty Tree) := !A.isEmpty && A.all fun l => shapeOf G l == some .isBigint
  match op with
  | .lt | .le | .gt | .ge | .eq | .looseEq => return boolTy
  | .add =>
    if isStr L || isStr R then prim .str
    else if isBig L && isBig R then prim .bigint else prim .num
  | .shl | .shr | .ushr | .bitAnd | .bitOr => prim .num
  | _ => if isBig L && isBig R then prim .bigint else prim .num

/-- A label's type in claim form, read back by `Fragment.translate`. -/
def graphJson (A : Ty Tree) : Json := Json.mkObj [("top", toJson false),
  ("atoms", toJson (A.map fun l => Json.mkObj [("a", toJson "graph"), ("label", toJson l)]))]

/-- What a parameter of type `P`, which may mention the binder `b`, says `b`
is, given an actual of type `A`: `A` where `P` is `b`, `A`'s elements where
`P` is an array of `b`, `A`'s result where `P` is a function returning `b`
(the simplest matching of an actual against a parameter). -/
def isBinder (b : Tree) (P : Ty Tree) : Bool :=
  P == [b] || match P with
    | [.meet ps] => ps.toList.contains b
    | _ => false

/-- `A` with each binder `σ` names read as its type; a binder's meet with
its bound read as the type too, which an instance within the bound is: of
a meet naming several binders (a binder bounded by another, `T extends U`,
is `T ⊓ U`), the type every other's labels include, else the first's. -/
def substitute (σ : List (Tree × Ty Tree)) (A : Ty Tree) : Ty Tree :=
  norm (A.flatMap (EquationLowering.treeReplace fun u => match u with
    | .meet ps =>
      let found := ps.toList.filterMap (σ.lookup ·)
      (found.find? fun A => found.all fun B => A.all (B.contains ·)) <|> found.head?
    | u => σ.lookup u))

/-- What a call selects its signature from: a callee's binders (none for a
callee that is no scheme), its signatures, the receiver the call passes, the
binders' types written as explicit type arguments, and, for a callee that is
no instance, its own type. -/
structure Callee where
  binders : List Tree := []
  fixed : List (CallEffects.Arrow (Ty Tree)) := []
  rests : List (CallEffects.RestArrow (Ty Tree)) := []
  receiver : Ty Tree := [Labels.undef]
  seed : List (Tree × Ty Tree) := []
  own : Option (Ty Tree) := none
  /-- A class's construct signatures: its instance is a constructor's. -/
  construct : Bool := false
  /-- A generic module function's binders' names, each of `binders`; or
  its explicit type arguments, by its binders' names. -/
  names : List String := []
  explicit : List (String × Ty Tree) := []
  /-- The binders a resolution qualifies, by position in `binders`. -/
  resolution : List PositiveGraphs.ResolutionSlots := []
  /-- A generic module function's binders' bounds, where they state one. -/
  bounds : List (Tree × Ty Tree) := []
  widenBinders : List Tree := []
  /-- A union of callables: each arm's one signature (`calleeOf`). -/
  arms : List (CallEffects.Arrow (Ty Tree)) := []
  /-- A scheme's binders' declared defaults (`Draft.defaults`), each read at
  the scheme's application: proposals for binders nothing else gives. -/
  defaults : List (Tree × Ty Tree) := []

/-- The declared binder defaults of the scheme a label applies, at its
arguments, each binder its application's (`instantiateRow`'s reading). -/
def schemeDefaults (T : EquationStore.State) (l : Tree) : List (Tree × Ty Tree) :=
  match l with
  | .app h args => match T.heads[h]? with
    | some d =>
      let argF (i : Nat) : List Tree := ((args.toList[i]?).map EquationGraphs.Types.toList).getD []
      let locF (j : Nat) : List Tree := [.bound h args j]
      d.defaults.map fun (j, U) => (Tree.bound h args j, U.flatMap (EquationLowering.treeSubst argF locF))
    | none => []
  | _ => []

/-- The callee a value of type `F` is, called with receiver `O`: a scheme
by its binders and signatures, at `typeArgs` where they are written; a
union of callables, each arm of one fixed signature and no binders, by its
arms (the producer's union of callables, expression_calls.ml:1105-1118);
any other callable by its signatures. -/
def calleeOf (F O : Ty Tree) (typeArgs : List Json := []) : Compiler Callee := do
  let G ← graphNow
  if let [l] := F then
    if let some s := G.schemes l then
      let θ ← typeArgs.mapM fun t => lower (Fragment.translate t)
      if θ.length > s.binders.length then
        throw "explicit type arguments of another count than the binders"
      return { binders := s.binders, fixed := s.signatures, rests := s.variadic, receiver := O,
               seed := s.binders.zip θ, defaults := schemeDefaults (← table) l }
  if F.length > 1 && typeArgs.isEmpty && (ProgramTyping.callSigs G F).isEmpty &&
      (ProgramTyping.restSigs G F).isEmpty then
    let arms := F.map fun l => (ProgramTyping.callSigs G [l], ProgramTyping.restSigs G [l], (G.schemes l).isSome)
    if arms.all fun (L, S, s) => L.length == 1 && S.isEmpty && !s then
      return { arms := arms.flatMap (·.1), receiver := O, own := some F }
    -- An arm that is no callable (a value of no call signature, as `null`):
    -- the lowering's split refuses the call (every alternative names an
    -- arrow), and the producer's union of callables states none.
    if arms.any fun (L, S, s) => L.isEmpty && S.isEmpty && !s then
      throw (callRefusal "a call of a union an arm of which states no call signature")
  -- A bounded binder's value is called at its bound (`Plans.boundOf`, the
  -- lowering's `throughBound`).
  if (ProgramTyping.callSigs G F).isEmpty && (ProgramTyping.restSigs G F).isEmpty then
    let B ← boundOf F
    if B != F then
      let G ← graphNow
      return { fixed := ProgramTyping.callSigs G B, rests := ProgramTyping.restSigs G B, receiver := O, own := some F }
  return { fixed := ProgramTyping.callSigs G F, rests := ProgramTyping.restSigs G F, receiver := O, own := some F }

/-- A generic module function's callee: its signature at fresh binders, or
at its explicit type arguments. -/
def genericCallee (g : Generic) (typeArgs : List Json) : Compiler Callee := do
  let hidden := g.resolution.flatMap (·.associated)
  if !typeArgs.isEmpty && hidden.isEmpty then
    if typeArgs.length != g.binders.length then throw "explicit type arguments of another count than the binders"
    let inst ← lower (do Fragment.translate (← g.instantiate (g.binders.zip typeArgs)))
    let θ ← typeArgs.mapM fun t => lower (Fragment.translate t)
    let G ← graphNow
    if let [.ctors fixed rests ..] := PositiveRules.expand G inst then
      return { fixed := fixed.map (·.withReceiver [Labels.undef]),
               rests := rests.map (·.withReceiver [Labels.undef]),
               explicit := g.binders.zip θ, construct := true }
    return { fixed := ProgramTyping.callSigs G inst, rests := ProgramTyping.restSigs G inst,
             explicit := g.binders.zip θ }
  -- Written type arguments of a scheme a resolution qualifies are its
  -- binders' but the resolutions' observations and results, which the
  -- call's resolution gives.
  let shown := (List.range g.binders.length).filter (!hidden.contains ·)
  if !typeArgs.isEmpty && typeArgs.length != shown.length then
    throw "explicit type arguments of another count than the binders"
  let θ ← typeArgs.mapM fun t => lower (Fragment.translate t)
  let ps ← lower (modifyGet fun T => let (T, ps) := EquationStore.binders T g.binders; (ps, T))
  let θp := g.binders.zip (ps.map fun p => graphJson [p])
  let fresh ← lower (do Fragment.translate (← g.instantiate θp))
  let bounds ← tryCatch (do
      let bs ← lower (g.bounds θp)
      bs.filterMapM fun (n, j) => do
        let some j := j | return none
        let some p := (g.binders.zip ps).lookup n | return none
        return some (p, ← lower (Fragment.translate j))) fun _ => pure []
  let G ← graphNow
  let (fixed, rests, construct) := match PositiveRules.expand G fresh with
    | [.ctors L R ..] => (L.map (·.withReceiver [Labels.undef]), R.map (·.withReceiver [Labels.undef]), true)
    | _ => (ProgramTyping.callSigs G fresh, ProgramTyping.restSigs G fresh, false)
  return { binders := ps, fixed, rests, construct,
           names := g.binders, resolution := g.resolution, seed := (shown.filterMap (ps[·]?)).zip θ, bounds,
           widenBinders := (g.binders.zip ps).filterMap fun (n, p) => if g.widenBinders.contains n then some p else none }

/-- The callee of a generic module function of one binder typing a value and
a rest's argument lists, whose signature at a fresh binder has no argument
lists (they are an array or tuple instance's): at the tuple of the actuals
past its fixed parameters, widened, a spread of a tuple of required
positions standing for them (the producer's pack rest, a binder typing a
value too, expression_calls.ml:666-671); where its signature at that tuple
states no rest, at the actual of the first parameter that is the binder
itself. -/
def packedCallee (g : Generic) (As : List (Option (Ty Tree))) (spreads : List Nat) :
    Compiler (Option Callee) := do
  if g.binders.length != 1 || !g.resolution.isEmpty then return none
  let G ← graphNow
  let some As := As.mapM id | return none
  let mut Es : List (Ty Tree) := []
  for (A, i) in As.zipIdx do
    if spreads.contains i then
      let [l] := A | return none
      let some S := storeOf G [l] | return none
      let [.list t []] := PositiveRules.expand G S | return none
      if !t.optional.isEmpty || t.rest.isSome then return none
      for E in t.required do Es := Es ++ [← widen E]
    else Es := Es ++ [← widen A]
  let tuple (Es : List (Ty Tree)) : Compiler (Ty Tree) := lower do
    let s ← SourceTypes.use (.list ⟨Es, [], none, false, .dense⟩ [])
    let T ← get
    return [← SourceTypes.use (SourceTypes.arrayOf T s false)]
  let at_ (X : Ty Tree) : Compiler Callee := genericCallee g [graphJson X]
  let X ← tuple Es
  let c ← at_ X
  match c.rests with
  | [r] => if r.arguments.1.isEmpty then return some c else
      if spreads.any (· < r.arguments.1.length) then return none
      return some (← at_ (← tuple (Es.drop r.arguments.1.length)))
  | [] =>
    let params := c.fixed.head?.map (·.arguments) |>.getD []
    -- (the rest's argument lists a tuple's positions, read as fixed
    -- parameters: the tuple of every actual)
    if !params.contains X && params.length == Es.length then return some c
    if !spreads.isEmpty then return none
    let some (_, i) := params.zipIdx.find? (·.1 == X) | return none
    let some A := As[i]? | return none
    return some (← at_ A)
  | _ => return none

/-- The expressions an expected type naming a hole guides
(expression_typing.ml:38-40). -/
def holeGuided : Expr → Bool
  | .arrayLit .. | .call .. | .invoke .. | .lambda .. => true
  | _ => false

def arrayLiteral : Expr → Bool
  | .arrayLit .. => true
  | _ => false

/-- Whether an actual is a callback: a function literal, typed by the
parameter it is passed at where it writes no parameter's type, and stated
at that parameter's signature (`walkLambda`). -/
def callback : Expr → Bool
  | .lambda .. => true
  | _ => false

/-- A call of a union of callables (`calleeOf`'s arms) with `callbacks`
marking the actuals that are function literals and `As` the walked ones: the
call is each arm's, so every arm's count admits the actuals, else the call is
refused (the lowering splits the callee and selects each arm's signature,
`selectSignature`); each actual is made at the parameter every arm states at
its position, else at its own type (the producer's `shared_actuals`); the
value is the union of the arms' results, and the effect the arms' one effect,
else the ordinary effect bounding a throw where every arm does. Any other
callee is itself. `first` (`TSCERT_FORCE=arms`) states the first arm's
signature alone, the adversarial proposal. -/
def armsCallee (G : PositiveGraphs.NormalGraph Tree) (T : EquationStore.State) (c : Callee)
    (callbacks : List Bool) (As : List (Option (Ty Tree))) (first : Bool := false) : Except String Callee := do
  let n := callbacks.length
  let fits (a : CallEffects.Arrow (Ty Tree)) : Bool :=
    n ≤ a.arguments.length && (a.arguments.drop n).all (fun D => omissible G D || within T [Labels.undef] D)
  match c.arms with
  | [] => return c
  | a0 :: rest =>
    if first then return { c with fixed := [a0], rests := [], arms := [] }
    if !c.arms.all fits then
      throw (callRefusal s!"no signature admits {n} actuals at every arm of a union of callables")
    let params ← (callbacks.zipIdx).mapM fun (cb, i) => do
      match c.arms.map (·.arguments[i]?) with
      | some P :: Ps =>
        if Ps.all (· == some P) then return P
        match cb, As[i]?.join with
        | false, some A => return A
        | _, _ => throw "an actual where the arms of a union of callables state different parameters"
      | _ => throw "an actual past a parameter"
    let effect := if rest.all (·.effect == a0.effect) then a0.effect
      else { CallEffects.Effect.ordinary with onThrow := c.arms.all (·.effect.onThrow) }
    return { c with fixed := [⟨a0.receiver, params, norm (c.arms.flatMap (·.result)), effect⟩],
                    rests := [], arms := [] }

/-- The member `o.k` names, `o` of type `O`: its own (a host-relative
member), else its prototype's. -/
def memberFor (vars : List (String × Ty Tree)) (O : Ty Tree) (fld : PropKey) :
    Compiler (Option (MethodMembers.Sig (Ty Tree))) := do
  let G ← graphNow
  let O ← match O.filterMap (shapeOf G) |>.eraseDups with
    | [tag] => if O.all (fun l => shapeOf G l == some tag) then protoFor vars tag else pure O
    | _ => pure O
  if let some m := ProgramTyping.memberOf G O fld then return some m
  if let some P := protoOf G O then
    if let some m := ProgramTyping.memberOf G P fld then return some m
  -- A union of objects each stating the member at the same signatures,
  -- read at their receivers (a host family's node kinds, each its own
  -- receiver): the member with every clause's receivers and schemes.
  match O.mapM (fun l => match ProgramTyping.objectClauses G [l] with
      | [c] => ProgramTyping.clauseMember c fld
      | _ => none) with
  | some (m :: ms) =>
    if ms.all fun m' => m'.calls == m.calls && m'.rests == m.rests &&
        m'.schemes.isEmpty == m.schemes.isEmpty then
      return some { m with
        schemes := (m.schemes ++ ms.flatMap (·.schemes)).eraseDups
        receivers := (m.receivers ++ ms.flatMap (·.receivers)).eraseDups }
    -- Members of one signature each, of no promise, binders or rest, taking
    -- the same parameters at the same effect: one signature returning the
    -- union of their results (the producer's `bound_union`,
    -- semantic.ml:431-446; the lowering splits the host's slot,
    -- `unionVar`, and binds each host's member, `bindMember`).
    let one (m' : MethodMembers.Sig (Ty Tree)) : Option (CallEffects.MethodArrow (Ty Tree)) :=
      match m'.calls, m'.rests, m'.schemes with
      | [a], [], [] => if a.effect.promise.isNone then some a else none
      | _, _, _ => none
    match one m, ms.mapM one with
    | some a, some as =>
      if as.all fun b => b.arguments == a.arguments && b.effect == a.effect then
        return some { m with
          calls := [{ a with result := norm (a.result ++ as.flatMap (·.result)) }]
          receivers := (m.receivers ++ ms.flatMap (·.receivers)).eraseDups }
      return none
    | _, _ => return none
  | _ => return none

/-- Whether the binder `b` occurs in a label. -/
partial def occurs (b : Tree) (t : Tree) : Bool :=
  t == b || match t with
    | .app _ args | .bound _ args _ => args.toList.any fun ts => ts.toList.any (occurs b)
    | .meet ps => ps.toList.any (occurs b)
    | _ => false

/-- A callback's parameter `Ph`, read at the binders the type expected of
its call's value gives, where it is one signature naming holes in its
result alone and no binder of the call; else `Pc` (the producer's
`result_bound`, expression_calls.ml:852-868). -/
def holedCallback (G : PositiveGraphs.NormalGraph Tree) (holes binders : List Tree) (Ph Pc : Ty Tree) : Ty Tree :=
  let holed (A : Ty Tree) : Bool := holes.any fun h => A.any (occurs h)
  match Ph, ProgramTyping.callSigs G Ph with
  | [_], [s] =>
    if holed s.result && !(s.receiver :: s.arguments).any holed &&
        !binders.any (fun b => Ph.any (occurs b)) then Ph else Pc
  | _, _ => Pc

/-- The meets a tree holds, at any depth of its arguments. -/
partial def meetsIn : Tree → List Tree
  | .app _ args | .bound _ args _ => args.toList.flatMap fun ts => ts.toList.flatMap meetsIn
  | t@(.meet _) => [t]
  | _ => []

/-- What a parameter of type `P` says the binder `b` is, given an actual of
type `A`, matched structurally one level at a time (no search; the first
part mentioning `b` decides): `A` where `P` is `b`; in a union, the one
member mentioning `b` at `A` less what the others admit; in an application
of one head, its arguments at `A`'s of that head; in an array, its elements
at `A`'s; in a record, each field at `A`'s; in a callable, its result at
`A`'s. -/
partial def matchBinder (b : Tree) (P A : Ty Tree) (fuel : Nat := 6) (vars : List (String × Ty Tree) := [])
    (siblings : List Tree := []) : Compiler (Option (Ty Tree)) := do
  if isBinder b P then return some A
  if fuel == 0 || A.isEmpty then return none
  let T ← table
  let G := SourceTypes.graph T
  let (withB, others) := P.partition (occurs b)
  -- A union: the actual less what the members not mentioning `b` admit;
  -- each of its labels at the first member mentioning `b` it matches, the
  -- bare binder last (the producer's arm of a part's own kind, else the
  -- bare binder, inference.ml:425-503): a single label too, where several
  -- members mention `b` (`TResult1 | PromiseLike<TResult1>` at `string`).
  let ordered := withB.filter (!isBinder b [·]) ++ withB.filter (isBinder b [·])
  let perLabel (A : Ty Tree) (single : Bool := false) : Compiler (Option (Ty Tree)) := do
    if A.length < 2 && !single then return none
    let mut out : Ty Tree := []
    for a in A do
      let mut got : Option (Ty Tree) := none
      for m in ordered do
        if got.isNone then got ← matchBinder b [m] [a] (fuel - 1) vars
      let some B := got | return none
      out := out ++ B
    return some (norm out)
  -- (a label another binder of the call reads off a member not mentioning
  -- `b` is that member's: a union iteration's parts, each kind's binders
  -- apart, as the producer's instance reads them)
  let mut A' : Ty Tree := []
  for a in A do
    let mut theirs := within T [a] others
    for m in others do
      for b' in siblings do
        if !theirs && b' != b && occurs b' m then
          if (← matchBinder b' [m] [a] (fuel - 1) vars).isSome then theirs := true
    if !theirs then A' := A' ++ [a]
  let [l] := withB | do
    if withB.isEmpty then return none
    perLabel A' (single := true)
  if !others.isEmpty then
    if let some B ← matchBinder b [l] A' (fuel - 1) vars then return some B
    return ← perLabel A'
  -- One head applied: its arguments, each at `A`'s of the same head.
  if let .app h ps := l then
    let same := A.filterMap fun a => match a with
      | .app h' as => if h' == h then some as else none
      | _ => none
    if same.length == A.length then
      for (Pi, i) in ps.toList.zipIdx do
        if Pi.toList.any (occurs b) then
          let Ai := norm (same.flatMap fun as => ((as.toList[i]?).map (·.toList)).getD [])
          if let some B ← matchBinder b Pi.toList Ai (fuel - 1) vars then return some B
  let first (xs : List (Ty Tree × Compiler (Ty Tree))) : Compiler (Option (Ty Tree)) := do
    for (Q, read) in xs do
      if Q.any (occurs b) then
        if let some B ← tryCatch (some <$> read) (fun _ => pure none) then
          if let some C ← matchBinder b Q B (fuel - 1) vars then return some C
    return none
  if let some S := storeOf G [l] then
    if let [.list t []] := PositiveRules.expand G S then
      if !t.required.isEmpty || !t.optional.isEmpty then
        let positions := (t.required ++ t.optional).zipIdx
        if let some B ← first (positions.map fun (P, i) =>
            (P, elementAt A (some i) (missing := false))) then return some B
      else
        let E := norm (t.rest.getD [])
        if let some B ← first [(E, elementAt A none (missing := false))] then return some B
    return ← perLabel A
  let r ← match PositiveRules.expand G [l] with
  | [.ctors fixed rests ..] =>
    -- The class's own constructor is first; its result and parameters
    -- constrain the target constructor (inference.ml:287-294).
    let target := (fixed.head?.map fun a => (a.arguments, a.result)) <|>
      (rests.head?.map fun a => (a.arguments.1, a.result))
    let actual := match PositiveRules.expand G A with
      | [.ctors fixed rests ..] => (fixed.head?.map fun a => (a.arguments, a.result)) <|>
          (rests.head?.map fun a => (a.arguments.1, a.result))
      | _ => none
    match target, actual with
    | some (ps, R), some (qs, S) =>
      first ((R, pure S) :: (ps.zip qs).map fun (P, A) => (P, pure A))
    | _, _ => pure none
  | [.dict _ _ _ ix _ _ _ _ _] => first [(norm (ix.flatMap (·.2)), elementAt A none (missing := false))]
  | [.refs fs [] vs os ms _ _] =>
    first (((fs ++ vs).filter (fun (k, _) => k != SourceTypes.protoField)).map (fun (k, F) => (F, readField vars A k)) ++
      os.map (fun o => (o.type, do slice (← readField vars A o.key) .isUndef false)) ++
      -- A method: its result at `A`'s member's.
      ms.map fun m => (norm (m.calls.flatMap (·.result)), do
        let some m' ← memberFor vars A m.key | throw "no member"
        let some a := m'.calls.head? | throw "no signature"
        pure a.result))
  | _ =>
    -- (of a parameter stating a guard's plain row beside its promise row,
    -- the first signature mentioning `b`: a written guard's promised type
    -- is the binder's, the producer's `promised`, expression_calls.ml:438-445)
    let sigs := ProgramTyping.callSigs G [l]
    let some s := (sigs.find? fun s => (s.result :: s.arguments).any (·.any (occurs b))) <|> sigs.head?
      | return none
    -- A callback's result supplies the lower candidate first; only a
    -- binder absent there is read off its parameters (inference.ml:311-329).
    let rows := ProgramTyping.callSigs G A
    let row := rows.find? fun a => a.effect.promise == s.effect.promise &&
      a.arguments.length ≤ s.arguments.length
    let result ← first [(s.result, do
      let rows := (ProgramTyping.callSigs G A).map (fun a => (a.effect.promise, a.result)) ++
        (ProgramTyping.restSigs G A).map (fun a => (a.effect.promise, a.result))
      let some (_, R) := rows.find? (·.1 == s.effect.promise) | throw "no signature"
      pure R)]
    if result.isSome then pure result else
      match row with
      | some a => first ((s.arguments.zip a.arguments).map fun (P, A) => (P, pure A))
      | none => pure none
  if r.isSome then return r
  perLabel A

/-- Whether a binder supplies values in a signature. A constructor or
callback's argument pack alone does not make it a value binder
(expression_calls.ml:661-671). -/
partial def valueBinder (G : PositiveGraphs.NormalGraph Tree) (b : Tree) (A : Ty Tree)
    (fuel : Nat := 6) : Bool :=
  if fuel == 0 then A.any (occurs b) else
  match PositiveRules.expand G A with
  | [.ctors fixed rests fs more vs] =>
    (fs ++ more.flatten ++ vs).any (fun (_, A) => A.any (occurs b)) ||
    fixed.any (fun a => (a.result :: a.arguments).any (valueBinder G b · (fuel - 1))) ||
    rests.any (fun a => (a.result :: a.arguments.1).any (valueBinder G b · (fuel - 1)))
  | [.arrs fixed rests] =>
    fixed.any (fun a => (a.receiver :: a.result :: a.arguments).any (valueBinder G b · (fuel - 1))) ||
    rests.any (fun a => (a.receiver :: a.result :: a.arguments.1).any (valueBinder G b · (fuel - 1)))
  | _ => A.any (occurs b)

/-- The member `o.k` of a union `O` read arm by arm, as the read of a union
reads each alternative (`Plans.readCell`): each label's member (its own or
its prototype's, `memberFor`) at that label's receiver, else its field
(`readField`). None for a value of one label, or where an arm's member is
generic. -/
def memberArms (vars : List (String × Ty Tree)) (O : Ty Tree) (fld : PropKey) :
    Compiler (Option (Ty Tree)) := do
  if O.length < 2 then return none
  let mut out : Ty Tree := []
  for l in O do
    match ← memberFor vars [l] fld with
    | some m =>
      if !m.schemes.isEmpty || (m.calls.isEmpty && m.rests.isEmpty) then return none
      out := out ++ [← lower (SourceTypes.use (.arrs (m.calls.map (·.withReceiver [l]))
        (m.rests.map (·.withReceiver [l]))))]
    | none => out := out ++ (← readField vars [l] fld)
  return some (norm out)

/-- The member `o.k` of a union of hosts whose members differ, as a bind
reads it: each arm's (`memberArms`), where `memberFor` finds no one member;
none where an arm's member cannot be read. -/
def unionMember (vars : List (String × Ty Tree)) (O : Ty Tree) (fld : PropKey) : Compiler (Option (Ty Tree)) :=
  tryCatch (do
    let O := present (← graphNow) O
    if (← memberFor vars O fld).isSome then return none
    memberArms vars O fld) fun _ => pure none

/-- `o.k.bind(o)` of a union of hosts whose members `M` (`memberArms`)
differ: of each arm its first signature of no promise binding keeps
(`Effect.keeps`); where all take the same parameters at the same effect, the
bound function at any receiver taking them, at the effect binding keeps
(`Effect.drop`), returning the union of their results (the producer's
`Bind` of a union of hosts, `bound_union`, expression_values.ml:349-363;
the lowering splits the host's slot, `unionVar`, and binds each arm's
member, `bindMember`). `forced` states it keeping values and stores. -/
def boundUnion (M : Ty Tree) (forced : Bool) : Compiler (Option (Ty Tree)) := do
  let G ← graphNow
  if M.length < 2 then return none
  let some arms := M.mapM (fun l => (match PositiveRules.expand G [l] with
      | [.arrs L []] => L.find? fun a => a.effect.promise.isNone && a.effect.keeps 0
      | _ => none : Option (CallEffects.Arrow (Ty Tree)))) | return none
  let a :: rest := arms | return none
  if !rest.all (fun b => b.arguments == a.arguments && b.effect == a.effect) then return none
  let top ← prim .top
  let effect : CallEffects.Effect := if forced then .ofFootprint ⟨.keep, .keep⟩ else a.effect.drop 0
  return some [← lower (SourceTypes.use (.arrs
    [⟨top, a.arguments, norm (arms.flatMap (·.result)), effect⟩] []))]

/-- The callee `o.k(…)` calls, `o` of type `O`: the object's member, its
prototype's, or a field holding a callable. -/
def methodCallee (vars : List (String × Ty Tree)) (O : Ty Tree) (fld : PropKey) (callbacks : List Bool := []) (typeArgs : List Json := []) :
    Compiler Callee := do
  if let some m ← memberFor vars O fld then
    if m.calls.isEmpty && m.rests.isEmpty then
      let some S := m.schemes.head? | throw "a member of no signature"
      let first ← calleeOf S O typeArgs
      if !callbacks.any id then return first
      -- A member with several schemes (one per receiver label) called with
      -- callbacks: the scheme whose callback parameters take the most
      -- parameters, at which a walked callback admits every scheme's call.
      let G ← graphNow
      let width (c : Callee) : Nat := match c.fixed.find? (callbacks.length ≤ ·.arguments.length) with
        | some a => ((a.arguments.zip callbacks).filter (·.2)).foldl (fun (n : Nat) (P, _) =>
            n + (((ProgramTyping.callSigs G P).head?.map (·.arguments.length)).getD 0)) 0
        | none => 0
      let others ← m.schemes.tail.mapM fun S => calleeOf S O typeArgs
      return others.foldl (fun (best c : Callee) => if Nat.blt (width best) (width c) then c else best) first
    let fixed := m.calls.map (·.withReceiver O)
    let rests := m.rests.map (·.withReceiver O)
    return { fixed, rests, receiver := O, own := some [← lower (SourceTypes.use (.arrs fixed rests))] }
  -- A union whose arms' members differ: each arm's member, a union of
  -- callables (`calleeOf`).
  if typeArgs.isEmpty then
    if let some M ← tryCatch (memberArms vars O fld) (fun _ => pure none) then
      return ← calleeOf M O
  calleeOf (← readField vars O fld) O typeArgs

/-- The callee `new C(…)` calls: its construct signatures. -/
def constructCallee (F : Ty Tree) (typeArgs : List Json) : Compiler Callee := do
  let G ← graphNow
  if let [l] := F then
    if (G.schemes l).isSome then return { ← calleeOf F [Labels.undef] typeArgs with construct := true }
  match PositiveRules.expand G F with
  | [.ctors L S ..] =>
    return { fixed := L.map (·.withReceiver [Labels.undef]), rests := S.map (·.withReceiver [Labels.undef]), construct := true }
  | _ => throw "a construction of a value of no construct signature"

/-- The signature of a callable type taking the most parameters. -/
def widestOf (G : PositiveGraphs.NormalGraph Tree) (P : Ty Tree) : Option (CallEffects.Arrow (Ty Tree)) :=
  (ProgramTyping.callSigs G P).foldl (fun (best : Option (CallEffects.Arrow (Ty Tree))) a =>
    match best with
    | some b => if Nat.blt b.arguments.length a.arguments.length then some a else some b
    | none => some a) none

/-- The type expected of a key `k` of a literal where `P` is expected: the
union of the field each member of `P` states at `k`, a dictionary's index
included; none where no member states one. -/
def fieldExpected (P : Ty Tree) (k : PropKey) : Compiler (Option (Ty Tree)) := do
  let G ← graphNow
  let mut out : Ty Tree := []
  for l in P do
    -- Construction at an optional field uses its value contract, without
    -- the undefined contributed by an absent read (expression_objects.ml:34).
    let named := match PositiveRules.expand G [l] with
      | [.refs fs [] vs os _ _ _] | [.dict fs [] vs _ os _ _ _ _] =>
        fs.lookup k <|> vs.lookup k <|> (os.find? (·.key == k)).map (·.type)
      | _ => none
    let D ← match named with
      | some D => pure (some D)
      | none =>
        -- A key the member states as a method: the callable a read of it
        -- bound to that member is (the producer's `f.read` of a method
        -- field, expression_objects.ml:25-36).
        match (match ProgramTyping.objectClauses G [l] with
            | [c] => ProgramTyping.clauseMember c k
            | _ => none) with
        | some m =>
          if m.schemes.isEmpty && !(m.calls.isEmpty && m.rests.isEmpty) then
            pure (some [← lower (SourceTypes.use (.arrs (m.calls.map (CallEffects.Contract.withReceiver [l])) (m.rests.map (CallEffects.Contract.withReceiver [l]))))])
          else pure none
        | none => tryCatch (some <$> readField [] [l] k) (fun _ => pure none)
    if let some D := D then out := out ++ D
  return if out.isEmpty then none else some (norm out)

/-- A fresh object's contextual contract: the one record arm, or the one
arm its keys and literal members select (type_queries.ml:769-789,
820-830). Several compatible arms supply no allocation contract. -/
def recordContext (P : Ty Tree) (names : List PropKey) (es : List Expr) : Compiler (Option (Ty Tree)) := do
  let G ← graphNow
  let arms := P.filter fun l => (storeOf G [l]).isNone && match PositiveRules.expand G [l] with
    | [.refs _ [] ..] | [.dict _ [] ..] => true
    | _ => false
  if let [l] := arms then return some [l]
  let mut selected := []
  for l in arms do
    let required : List PropKey := match PositiveRules.expand G [l] with
      | [.refs fs [] vs _ _ _ _] | [.dict fs [] vs _ _ _ _ _ _] => (fs ++ vs).map (fun (p : PropKey × Ty Tree) => p.1)
      | _ => []
    if !required.all names.contains then continue
    let mut ok := true
    for (k, e) in names.zip es do
      let some D ← fieldExpected [l] k | ok := false; break
      if let .lit _ v := e then
        let A ← literal v
        if !within (← table) A D then ok := false; break
    if ok then selected := selected ++ [l]
  return match selected with | [l] => some [l] | _ => none

/-- Literal spread operands receive optional fields whose contextual
contracts agree across the arms that state them (expression_objects.ml:
154-181). The operand need not supply the enclosing copy's required keys. -/
def spreadContext (P : Ty Tree) : Compiler (Option (Ty Tree)) := do
  let G ← graphNow
  let fields := P.flatMap fun l => match PositiveRules.expand G [l] with
    | [.refs fs [] vs os ms _ _] | [.dict fs [] vs _ os ms _ _ _] =>
      ((fs ++ vs) ++ os.map (fun o => (o.key, o.type))).filter fun (k, _) => !ms.any (·.key == k)
    | _ => []
  let mut optional : List (OptionalField (Ty Tree)) := []
  for k in (fields.map (·.1)).eraseDups do
    if k == SourceTypes.protoField then continue
    match ((fields.filter (·.1 == k)).map (·.2)).eraseDups with
    | [A] => optional := optional ++ [⟨k, false, A⟩]
    | _ => pure ()
  if optional.isEmpty then return none
  return some (← prim (.refs [] [] [] optional [] [] []))

partial def copyLiteral : Expr → Bool
  | .alloc .. => true
  | .ifBody _ _ a b => copyLiteral a && copyLiteral b
  | _ => false

/-- The array members of an expected type. -/
def arrayArms (G : PositiveGraphs.NormalGraph Tree) (P : Ty Tree) : List Tree :=
  P.filter fun l => (storeOf G [l]).isSome

/-- What an iterable other than an array yields, where `P` is expected:
for each member of `P` stating a method of a symbol key (its
`[Symbol.iterator]`), the `value` of each result of its iterator's `next`
that is not done. -/
def iteratedElement (P : Ty Tree) : Compiler (Option (Ty Tree)) := do
  let G ← graphNow
  let mut out : Ty Tree := []
  for l in P do
    if (storeOf G [l]).isSome then continue
    let [.refs _ [] _ _ ms _ _] := PositiveRules.expand G [l] | continue
    let some m := ms.find? (fun m => match m.key with | .sym _ => true | _ => false) | continue
    let some a := m.calls.head? | continue
    let some n ← memberFor [] a.result (.str "next") | continue
    let some r := n.calls.head? | continue
    for u in r.result do
      let done ← tryCatch (some <$> readField [] [u] (.str "done")) (fun _ => pure none)
      if done == some [Labels.tru] then continue
      if let some V ← tryCatch (some <$> readField [] [u] (.str "value")) (fun _ => pure none) then
        out := out ++ V
  return if out.isEmpty then none else some (norm out)

/-- The values a protocol step `N` (a bound `next`) yields not done: its
first signature's result's arms whose `done` may be other than `true`, their
`value`s (`iteratedElement`'s). -/
def stepValue (N : Ty Tree) : Compiler (Option (Ty Tree)) := do
  let G ← graphNow
  let some r := (ProgramTyping.callSigs G N).head? | return none
  let mut out : Ty Tree := []
  for u in r.result do
    let done ← tryCatch (some <$> readField [] [u] (.str "done")) (fun _ => pure none)
    if done == some [Labels.tru] then continue
    out := out ++ (← readField [] [u] (.str "value"))
  return if out.isEmpty then none else some (norm out)

/-- The type expected of position `i` of an array literal where `P` is
expected: the union of the positions its array members state there, else
what its iterable members yield. -/
def positionExpected (P : Ty Tree) (i : Nat) : Compiler (Option (Ty Tree)) := do
  let G ← graphNow
  let mut out : Ty Tree := []
  for l in arrayArms G P do
    if let some B ← tryCatch (some <$> elementAt [l] (some i) (missing := false)) (fun _ => pure none) then
      out := out ++ B
  if out.isEmpty then return ← iteratedElement P
  return some (norm out)

/-- A call's fresh result (its signature stating `fresh`) where `H` is
expected: the first array member of `H` whose elements the result's are
within, the store the call allocates taking any contract
(`HasTyUsing.alloc`'s bound at a fresh result). -/
def freshAt (H R : Ty Tree) : Compiler (Option (Ty Tree)) := do
  let T ← table
  let G := SourceTypes.graph T
  if (storeOf G R).isNone then return none
  let E ← elementAt R none (missing := false)
  for l in arrayArms G H do
    if within T R [l] then return none
    let D ← elementAt [l] none (missing := false)
    if within T E D then return some [l]
  return none

/-- The statements of `ss` at their function's own level, nested statement
lists included but a handler's and a finalizer's (each entered as a head
is) and none of a function literal. -/
partial def ownStmts (ss : List Stmt) : List Span :=
  ss.flatMap fun s => s.pos :: match s with
    | .ite _ _ t e => ownStmts t ++ ownStmts (e.getD [])
    | .loop _ _ b u _ => ownStmts b ++ ownStmts u
    | .block _ _ b => ownStmts b
    | .forOf _ _ _ _ _ b => ownStmts b
    | .tryStmt _ b _ _ => ownStmts b
    | .closing _ _ b => ownStmts b
    | _ => []

/-- An entry's narrowed paths with `kept` beside them. -/
def withPaths (kept : List ((String × List PropKey) × Ty Tree)) (cs : List (String × List (List PropKey × Ty Tree))) :
    List (String × List (List PropKey × Ty Tree)) :=
  kept.foldl (fun cs ((r, p), A) =>
    if A.isEmpty then cs else match cs.lookup r with
    | some ps => if (ps.lookup p).isSome then cs else upd cs r (ps ++ [(p, A)])
    | none => cs ++ [(r, [(p, A)])]) cs

mutual
/-- The bindings statements declare, nested ones included. -/
partial def declaredIn (ss : List Stmt) : List String :=
  ss.flatMap fun s => s.bound ++ match s with
    | .ite _ _ t e => declaredIn t ++ declaredIn (e.getD [])
    | .loop _ _ b u _ => declaredIn b ++ declaredIn u
    | .block _ _ b => declaredIn b
    | .forOf _ n _ _ _ b => n :: declaredIn b
    | .tryStmt _ b h f => declaredIn b ++ (match h with
        | some (p, hs) => (p.map (·.1)).toList ++ declaredIn hs
        | none => []) ++ declaredIn (f.getD [])
    | .closing _ c b => declaredIn c ++ declaredIn b
    | _ => []
end

/-- The walk records a change of the heap. -/
def wrote (value store : Footprints.Change := .any) : W Unit := do
  modify fun w => { w with writes := true, valueChange := w.valueChange.max value, storeChange := w.storeChange.max store }
  if value != .keep then modify fun w => { w with valueWrites := w.valueWrites + 1 }

/-- For a declaration's footprint, a call's change of the heap at one of its
callee's signatures, graded as the producer's `effects_footprint`
(source.ml:953-956) grades it: the signature's footprint; with the values
where it changes its receiver's own locations; everything where it changes
its receiver's store and the receiver's store is not one the run allocated
(`receiverFresh`). A typed array's element write (`elementWrite`) is a
change within the footprint (`Effect.Holds`). -/
def callChange (eff : CallEffects.Effect) (receiverFresh : Bool := false) : W Unit := do
  if eff.footprint != ⟨.keep, .keep⟩ then wrote eff.footprint.value eff.footprint.store
  if eff.receiverOwn then wrote .any eff.footprint.store
  if eff.receiverStore && !receiverFresh then wrote .any .any

/-- The change of an update (`x.f += v`, `x[k]++`) or a logical assignment
(`x.f ??= v`) of a target other than a binding: for a declaration's
footprint, a field's as a field write grades it (the values; a `length`'s
the stores too) and an element's as an element write does (the values and
a store's growth), the producer's `cell_write` and `element_write`
(source.ml:924-935, 1082-1107); else everything. -/
def targetWrite (t : Expr) : W Unit := do
  if !(← get).strict then wrote else
  match t with
  | .read _ fld _ => wrote .any (if fld == lengthKey then .any else .keep)
  | .index .. => wrote .any .grow
  | _ => wrote

/-- An assignment of `n`: a change of the heap where the function literal
being walked does not declare `n`, of its values (`value`: an initializing
write's `init`). -/
def assigns (n : String) (value : Footprints.Change := .any) : W Unit := do
  modify fun w => { w with holders := w.holders.filter (fun (a, b) => a != n && b != n) }
  ends (.root n)
  let w ← get
  if !w.locals.contains n then
    wrote value .keep
    -- (the cell's own assignment: what it then holds is the value assigned)
    modify fun w => { w with valueWrites := w.valueWrites - 1 }
    if !w.cellAssigned.contains n then modify fun w => { w with cellAssigned := n :: w.cellAssigned }
    -- Inside a function literal, a captured binding.
    if w.inLiteral && !w.closureAssigned.contains n then
      modify fun w => { w with closureAssigned := n :: w.closureAssigned }

/-- An early binding's written contract (the flow graph's `.early` rule):
its annotation, else a function literal's written receiver, parameters (a
defaulted one admitting `undefined`) and result at its written effect, else
the ordinary one; none where the source states neither. -/
def earlyContract (b : Fragment.Binding) (effect : CallEffects.Effect := .ordinary) : W (Option (Ty Tree)) :=
  StateT.lift (tryCatch (some <$> match b.annot, b.init with
    | some ty, _ => lower (Fragment.translate ty)
    | none, .lambda _ receiver [] params defaults false (some result) _ stated _ _ _ => do
      let Ds ← params.zipIdx.mapM fun ((_, j), i) => do
        let D ← lower (Fragment.translate j)
        pure (if defaults.any (·.1 == i) then (D ++ [Labels.undef]).eraseDups else D)
      let R ← lower (Fragment.translate result)
      let Rt ← match receiver with
        | some (t, _) => lower (Fragment.translate t)
        | none => prim .top
      return [← lower (SourceTypes.use (.arrs [⟨Rt, Ds, R, stated.getD effect⟩] []))]
    | _, _ => throw "no written contract") fun _ => pure none)

/-- A call's actuals with its spreads read as the call reads them
(`expression_calls.ml`): a spread of a tuple of required positions as those
positions; a spread of any other array as one actual of its elements, which
only a variadic signature taking no more fixed parameters than the actuals
before the first such spread admits (its elements checked against the
rest's), the callee's signatures narrowed to those. Into a callee of no
variadic signature, no actual after the first spread runs code (the call
reads the spreads' elements after every actual). -/
def spreadCall (args : List Expr) (As : List (Option (Ty Tree))) (spreads : List Nat) (c : Callee) :
    Compiler (List Expr × List (Option (Ty Tree)) × Callee) := do
  if spreads.isEmpty then return (args, As, c)
  let G ← graphNow
  -- A callee of one signature whose rest is a packed binder's argument
  -- lists, after the fixed actuals: one spread, the last actual, of a value
  -- of that binder, at its own type (the producer's pack rest call,
  -- expression_calls.ml:607-616; the lowering's `callPacked`,
  -- Atoms.lean:220-224, checks the operand's store is one of its lists).
  if c.binders.isEmpty && c.fixed.isEmpty && spreads == [args.length - 1] then
    if let ([r], some (some A)) := (c.rests, As.getLast?) then
      if r.arguments.1.length + 1 == args.length &&
          r.arguments.2.any (fun t => G.parameterKinds t == some .packed) then
        return (args, As, { c with fixed := [⟨r.receiver, r.arguments.1 ++ [A], r.result, r.effect⟩], rests := [] })
  let first := spreads.foldl min args.length
  if !c.construct && c.rests.isEmpty && spreads != [args.length - 1] then
    for (x, i) in args.zipIdx do
      if i > first then match x with
        | .var .. | .lit .. => pure ()
        | _ => throw "a spread into fixed parameters followed by an actual that runs code"
  let mut outArgs : List Expr := []
  let mut outAs : List (Option (Ty Tree)) := []
  let mut variadicAt : Option Nat := none
  for ((x, A), i) in (args.zip As).zipIdx do
    if !spreads.contains i then
      outArgs := outArgs ++ [x]
      outAs := outAs ++ [A]
      continue
    let A ← need A "a spread's operand"
    -- (each position read through the operand's span, which no rule of the
    -- call writes)
    let placeholder := Expr.var x.span "%spread%"
    let tuple : Option (List (Ty Tree)) := match A with
      | [l] => match storeOf G [l] with
        | some S => match PositiveRules.expand G S with
          | [.list t []] => if t.optional.isEmpty && t.rest.isNone then some t.required else none
          | _ => none
        | none => none
      | _ => none
    match tuple with
    | some ps =>
      outArgs := outArgs ++ ps.map fun _ => placeholder
      outAs := outAs ++ ps.map some
    | none =>
      if !A.all fun l => (storeOf G [l]).isSome then throw "a spread of what is no array"
      if variadicAt.isNone then variadicAt := some outArgs.length
      outArgs := outArgs ++ [placeholder]
      outAs := outAs ++ [some (← elementAt A none (missing := false))]
  -- (a rest that is a binder's argument lists takes a tuple's positions
  -- alone, the producer's pack rest)
  let c := match variadicAt with
    | some k => { c with fixed := [], rests := c.rests.filter fun r => r.arguments.1.length ≤ k &&
        !(match r.arguments.2 with | [p] => c.binders.contains p | _ => false) }
    | none => c
  return (outArgs, outAs, c)

/-- An object literal's copy as a merge reads it (`object_spread.ml`,
`alternative`): its fields, each optional or not, and whether its own keys
are exactly theirs. -/
structure Copy where
  fields : List (PropKey × Bool × Ty Tree) := []
  exact : Bool := true
  /-- Target keys excluded by its contract, retained through exact sources. -/
  excluded : List PropKey := []
  numeric : Option (Ty Tree) := none
  index : Option (Ty Tree) := none
  symbols : Option (Ty Tree) := none

/-- Each required copy field must have a required source field within every
constraint on that key (object_spread.ml:56-70, field_meet). Optional
constraints do not supply required presence. -/
def checkCopyFields (cs : List (PositiveNormalization.Clause (Ty Tree))) : Compiler Unit := do
  let fields := cs.flatMap fun c => match c with
    | .refs fs [] vs _ ms _ _ | .dict fs [] vs _ _ ms _ _ _ =>
      (fs ++ vs).filter fun (k, _) => !ms.any (·.key == k)
    | .callable fs rest _ _ ms => (fs ++ rest.flatten).filter fun (k, _) => !ms.any (·.key == k)
    | _ => []
  let optional := cs.flatMap fun c => match c with
    | .refs _ [] _ os _ _ _ | .dict _ [] _ _ os _ _ _ _ => os.map fun o => (o.key, o.type)
    | _ => []
  let T ← table
  for k in (fields.map (·.1)).eraseDups do
    let candidates := (fields.filter (·.1 == k)).map (·.2)
    let constraints := candidates ++ (optional.filter (·.1 == k)).map (·.2)
    if constraints.length > 1 && !candidates.any (fun A => constraints.all (within T A)) then
      throw (refusalMark ++ s!"copy: no required field '{k}' covers every intersection constraint")

/-- The copies a value of type `A` gives as a spread's operand (or, `target`,
as `Object.assign`'s target), one per label (`object_spread.ml`,
`alternatives_of`): nothing from a primitive other than a string, its own
keys exactly; no stated key from a string or a function, and no bound; a
record's fields, but its store, its prototype link (a target's kept) and a
key it also states as a method, which may sit on the prototype, its
optional ones optional, its own keys exactly where it bounds them; a class
value's static fields, with no bound. `force` (`TSCERT_FORCE=spreads`):
every key the record states, present, and its own keys exactly. -/
def copiesOf (A : Ty Tree) (force : Bool) (target : Bool := false) : Compiler (List Copy) := do
  let A ← boundOf A
  let G ← graphNow
  let mut out : List Copy := []
  for l in A do
    -- `object_spread.ml:meet_records` excludes an intersection with two
    -- indexed operands. Inspect its parts before their indexes merge.
    if let .meet ps := l then
      -- Check each product before its fields are normalized together, as
      -- arm_products/meet_product do (object_spread.ml:93-122).
      let mut products : List (List (PositiveNormalization.Clause (Ty Tree))) := [[]]
      for p in ps.toList do
        products := products.flatMap fun row => (PositiveRules.expand G [p]).map fun c => row ++ [c]
      for row in products do checkCopyFields row
      let indexed := ps.toList.filter fun p =>
        (PositiveRules.expand G [p]).any fun c => match c with
          | .dict _ _ _ ix _ _ _ _ _ => !ix.isEmpty
          | _ => false
      if indexed.length > 1 && !(PositiveRules.expand G [l]).isEmpty then
        throw (refusalMark ++ "copy: a spread of an intersection of two operands with index signatures is outside the fragment")
    if let some S := storeOf G [l] then
      if target then throw "a copy onto an array"
      if let [.list t []] := PositiveRules.expand G S then
        out := out ++ [{ exact := false, numeric := some (norm (t.required.flatten ++ t.optional.flatten ++ (t.rest.getD []))) }]
        continue
    if l == Labels.nul || l == Labels.undef then
      out := out ++ [({} : Copy)]
      continue
    match shapeOf G l with
    | some .isStr =>
      out := out ++ [{ exact := false }]
      continue
    | some _ =>
      out := out ++ [({} : Copy)]
      continue
    | none => pure ()
    let clauses := PositiveRules.expand G [l]
    for c in clauses do checkCopyFields [c]
    match clauses with
    | [.refs fs [] vs os ms bs _] =>
      let named := ((fs ++ vs).filter fun (f, _) => f != SourceTypes.storeField &&
          (target || f != SourceTypes.protoField) && (force || !ms.any (·.key == f))).map fun (f, B) => (f, false, B)
      -- A key an intersection's operands state twice: at the field within
      -- the others (`object_spread.ml`, `field_meet`), else the first.
      let T ← table
      let named := named.foldl (fun (acc : List (PropKey × Bool × Ty Tree)) (f, o, B) =>
        match acc.find? (·.1 == f) with
        | some (_, _, A) => if within T B A then acc.map fun g => if g.1 == f then (f, o, B) else g else acc
        | none => acc ++ [(f, o, B)]) []
      let opt := (os.filter fun o => !named.any (·.1 == o.key)).map fun o => (o.key, !force, o.type)
      -- (an array's own keys are its elements' too, which no field states)
      let array := (fs ++ vs).any (·.1 == SourceTypes.storeField)
      out := out ++ [{ fields := named ++ opt, exact := force || (bs.any (·.among) && !array), excluded := if target then (bs.filter (!·.among)).flatMap (·.keys) else [] }]
    | [.dict fs [] vs ix os ms _ _ _] =>
      let fields := ((fs ++ vs).filter fun (k, _) =>
        (target || k != SourceTypes.protoField) && !ms.any (·.key == k)).map fun (k, A) => (k, false, A)
      let opt := (os.filter fun o => !fields.any (·.1 == o.key)).map fun o => (o.key, true, o.type)
      out := out ++ [{ fields := fields ++ opt, exact := false, index := if force && (ix.lookup .strings).isSome then some [Labels.tru] else ix.lookup .strings, symbols := ix.lookup .symbols }]
    | [.callable fs rest _ _ ms] =>
      -- A callable object's fields are copied just as the producer's
      -- callable Shape (object_spread.ml:156-160); every intersection
      -- operand constrains a repeated key (field_meet, lines 56-70). A
      -- copy onto a callable is not handled.
      if target then throw "a spread of a value of no record contract"
      let all := (fs ++ rest.flatten).filter fun (k, _) =>
        k != SourceTypes.protoField && !ms.any (·.key == k) &&
          (match k with | .str _ => true | _ => false)
      let T ← table
      let mut fields := []
      for k in (all.map (·.1)).eraseDups do
        let types := (all.filter (·.1 == k)).map (·.2)
        let some B := types.find? fun B => types.all (within T B)
          | throw "a callable copy's repeated field has no contract within every operand"
        fields := fields ++ [(k, false, B)]
      -- A callable can own additional keys. `spreads` forces an exact
      -- bound, whose proof the pass must refuse.
      out := out ++ [{ fields, exact := force }]
    | [.ctors _ _ statics] =>
      out := out ++ [{ fields := (statics.filter (·.1 != SourceTypes.protoField)).map fun (f, B) => (f, false, B), exact := false }]
    | [.arrs ..] => out := out ++ [{ exact := false }]
    -- (a label of no value: no copy)
    | [] => pure ()
    -- The producer rejects these operand contracts (object_spread.ml:176).
    | _ => throw (refusalMark ++ "copy: a spread of a value of no record contract")
  return out

/-- A source's copy defined over a copy's (`object_spread.ml`,
`merge_alternative`): a key the source surely has takes its type; one the
copy has keeps its own where the source never has it, or with the source's
where it may; a key only the source may have is optional where the copy's
keys are exact. A key either may hold at an unknown type is not stated. The
copy's prototype link is kept. -/
def mergeCopy (a b : Copy) : Compiler Copy := do
  let names := (a.fields.map (·.1) ++ b.fields.map (·.1)).eraseDups
  let mut out : List (PropKey × Bool × Ty Tree) := []
  for k in names do
    let af := a.fields.find? (·.1 == k)
    let bf := b.fields.find? (·.1 == k)
    if k == SourceTypes.protoField then
      if let some f := af then out := out ++ [f]
      continue
    match bf with
    | some (_, false, B) => out := out ++ [(k, false, B)]
    | _ =>
      let bMaybe := (bf.map (·.2.2)) <|> (match k with | .str _ => b.index | .sym _ => b.symbols)
      let bNever := bf.isNone && b.exact
      -- (a key the source may hold at its index)
      let indexAt (x : Copy) : Option (Ty Tree) := match k with
        | .str _ => x.index
        | _ => x.symbols
      let bMaybe := bMaybe <|> (if bf.isNone then indexAt b else none)
      match af with
      | some (_, opt, A) =>
        if bNever then out := out ++ [(k, opt, A)]
        else if let some B := bMaybe then out := out ++ [(k, opt, ← joinTy A B)]
      | none =>
        let indexed := match k with | .str _ => a.index | .sym _ => a.symbols
        if let some A := indexed then
          if let some B := bMaybe then out := out ++ [(k, true, ← joinTy A B)]
        else if a.exact then
          if let some B := bMaybe then out := out ++ [(k, true, B)]
  let resolve (left right : Option (Ty Tree)) (keys : IndexKeys) :=
    if (left.isSome || right.isSome) && (left.isSome || a.exact) && (right.isSome || b.exact) then
      some (norm (left.getD [] ++ right.getD [] ++ out.flatMap fun (k, _, A) => if keys.surely k then A else []))
    else none
  let index := resolve a.index b.index .strings
  let symbols := resolve a.symbols b.symbols .symbols
  out := out.map fun (k, o, A) => (k, o, ((match k with | .str _ => index | .sym _ => symbols).getD A))
  let numeric := if (a.numeric.isSome || b.numeric.isSome) &&
      (a.numeric.isSome || a.exact) && (b.numeric.isSome || b.exact) then
    some (norm (a.numeric.getD [] ++ b.numeric.getD [] ++ out.flatMap fun (k, _, A) =>
      if IndexKeys.numeric.surely k then A else [])) else none
  return { fields := out, exact := a.exact && b.exact, excluded := a.excluded.filter (fun k => b.exact && !b.fields.any (·.1 == k)), numeric := if index.isSome then none else numeric, index, symbols }

/-- A copy's type: its required fields, its optional ones, its own keys
exactly where its keys are exact and none is optional
(`object_spread.ml`, `alternative_type`). -/
def copyType (c : Copy) : Compiler (Ty Tree) := do
  let req := (c.fields.filter fun (_, o, _) => !o).map fun (k, _, A) => (k, A)
  let opt := (c.fields.filter fun (_, o, _) => o).map fun (k, _, A) => (⟨k, false, A⟩ : OptionalField (Ty Tree))
  let bound : List KeyBound := (if c.exact && opt.isEmpty then [⟨true, req.map (·.1)⟩] else []) ++
    (if c.excluded.isEmpty then [] else [⟨false, c.excluded⟩])
  let indexes := (c.index.map (IndexKeys.strings, ·)).toList ++
    (c.numeric.map (IndexKeys.numeric, ·)).toList ++ (c.symbols.map (IndexKeys.symbols, ·)).toList
  if indexes.isEmpty then prim (.refs req [] [] opt [] bound [])
  else prim (.dict req [] [] indexes opt [] [] indexes [])

/-- The copies after each part: a named field set in every copy, a spread
merged into each copy once per copy its operand gives. -/
def copyParts (start : List Copy) (parts : List (Option PropKey × Ty Tree)) (force : Bool) : Compiler (List Copy) := do
  let mut alts := start
  for (k, A) in parts do
    match k with
    | some k =>
      -- A written field also contributes to each applicable index of the
      -- fresh copy (object_spread.ml:merge_alternative). Every named cell
      -- covered by that writable index is allocated at its combined type.
      alts ← alts.mapM fun a =>
        if a.index.isSome || a.symbols.isSome || a.numeric.isSome then
          mergeCopy a { fields := [(k, false, A)] }
        else pure (if a.fields.any (·.1 == k) then
          { a with fields := a.fields.map fun f => if f.1 == k then (k, false, A) else f }
          else { a with fields := a.fields ++ [(k, false, A)] })
    | none =>
      let srcs ← copiesOf A force
      let mut next : List Copy := []
      for a in alts do
        for b in srcs do next := next ++ [← mergeCopy a b]
      if next.length > 64 then throw "a copy of more than 64 alternatives"
      alts := next
  return alts

/-- The property names a key of type `K` may spell, where each of its
labels is one: a string's, or the property a number's `ToString` spells
(the lowering's `keySingletons`, including fractional numeric properties). -/
def keyNames (K : Ty Tree) : Compiler (Option (List PropKey)) := do
  let G ← graphNow
  return (keySingletons G K).map fun ks => ks.map (·.2)

/-- `o[k]` of an `o` of type `O` at a key of type `K` (`type_queries.ml`,
`index_type`): an array's or a string's element, and an object's field at
each name the key may spell (an enum's reverse map, a record at a
literal-union key), else its index at a dynamic key (a dictionary's, with
`undefined`). `firstOnly` (`TSCERT_FORCE=keys`): an object's field at the
first name alone. -/
def keyedRead (vars : List (String × Ty Tree)) (O K : Ty Tree) (missing : Bool) (firstOnly : Bool := false) :
    Compiler (Ty Tree) := do
  let G ← graphNow
  if O.isEmpty then throw "an element read of a value of no type"
  let O ← (present G O).mapM fun l => boundOf [l]
  let O := norm O.flatten
  let G ← graphNow
  let index ← keyIndex K
  let names ← keyNames K
  let mut out : Ty Tree := []
  for l in O do
    let elementLike := shapeOf G l == some .isStr || (storeOf G [l]).isSome
    match elementLike, names, PositiveRules.expand G [l] with
    | true, _, _ => out := out ++ (← elementAt [l] index missing)
    | false, some ks, [.refs ..] | false, some ks, [.dict ..] =>
      for k in (if firstOnly then ks.take 1 else ks) do out := out ++ (← readField vars [l] k)
    | false, none, [.dict _ _ _ ix _ _ _ _ _] =>
      let cls := if runtimeNumberKey G K then some IndexKeys.numeric
        else if K.all (fun l => shapeOf G l == some .isStr) then some .strings
        else if (PositiveRules.expand G K).all (fun c => match c with | .symbol | .symbolLit _ => true | _ => false) then some .symbols
        else none
      let some cls := cls | throw "a dictionary key of no one key class"
      let some (_, B) := (PositiveNormalization.numericFirst ix).find? (fun (k, _) => cls.within k)
        | throw (readRefusal "a dictionary with no index over the key's class")
      out := out ++ B ++ (if missing then [Labels.undef] else [])
    | false, _, _ => out := out ++ (← elementAt [l] index missing)
  return norm out

/-- The allocations a body returns last: its last statement's `return` of
an object literal, or of each arm of its last `if`. -/
partial def tailAllocs : Expr → List Span
  | .block _ ss =>
    let rec last : List Stmt → List Span
      | [] => []
      | ss => match ss.getLast? with
        | some (.ret _ e) => match e with
          | .alloc .. | .build .. => [e.span]
          | _ => []
        | some (.ite _ _ a b) => last a ++ last (b.getD [])
        | _ => []
    last ss
  | e@(.alloc ..) | e@(.build ..) => [e.span]
  | _ => []

/-- A signature `s` binding more parameters than the literal the constant
`n` holds, whose leading parameters are within the literal's own, offered
to the literal: whether it is (the producer's `closure_offer`,
closure_offers.ml:51-59). -/
def offerSig (n : String) (s : CallEffects.Arrow (Ty Tree)) : W Bool := do
  let some (_, sp, own) := (← get).closureConsts.find? (·.1 == n) | return false
  let T ← StateT.lift table
  if s.arguments.length ≤ own.length then return false
  if !(← get).force.contains "offers" && !((s.arguments.take own.length).zip own).all fun (D, Q) => within T D Q then return false
  modify fun w => { w with offered := if w.offered.contains (sp, s) then w.offered else w.offered ++ [(sp, s)] }
  return true

/-- A constant `n` holding a function literal, read where a callable `P` of
one fixed signature binding more parameters than the literal is expected,
whose leading parameters are within the literal's own: that signature
offered to the literal (the producer's `closure_offer`,
closure_offers.ml:51-59, from expression_values.ml:58-62 and
expression_calls.ml:309-313). -/
def offerUse (n : String) (P : Ty Tree) : W Unit := do
  let some (_, sp, own) := (← get).closureConsts.find? (·.1 == n) | return
  let T ← StateT.lift table
  let G := SourceTypes.graph T
  match ProgramTyping.callSigs G P, ProgramTyping.restSigs G P with
  | [s], [] => let _ ← offerSig n s
  | [], [r] =>
    -- One variadic signature of an element rest binding at least as many
    -- fixed parameters (closure_offers.ml:54-56).
    if (PositiveRules.restElem G r.arguments.2).isNone || r.arguments.1.length < own.length then return
    if !(← get).force.contains "offers" && !((r.arguments.1.take own.length).zip own).all fun (D, Q) => within T D Q then return
    modify fun w => { w with restOffered := if w.restOffered.contains (sp, r) then w.restOffered else w.restOffered ++ [(sp, r)] }
  | _, _ => return

/-- The rows a function literal of own row `own`, binding `qs`, is stated at
beside it where the callable `ctx` is expected: each fixed signature of
`ctx` binding more parameters whose leading ones are its own, at that
signature's result where the body's is within it, and each variadic one of
an element rest binding at least as many, at the body's result, each at the
literal's effect (the producer's `from_context`,
expression_closures.ml:372-386, 400-405).
(`force`: whatever the leading ones, the adversarial proposal) -/
def contextRows (T : EquationStore.State) (ctx : Option (Ty Tree)) (own : CallEffects.Arrow (Ty Tree))
    (qs : List (Ty Tree)) (force : Bool) :
    List (CallEffects.Arrow (Ty Tree)) × List (CallEffects.RestArrow (Ty Tree)) :=
  let G := SourceTypes.graph T
  let ctxTy := (ctx.map fun P => P.filter fun l =>
    !(ProgramTyping.callSigs G [l]).isEmpty || !(ProgramTyping.restSigs G [l]).isEmpty).getD []
  -- (an expected signature's leading parameters its own, as written: the
  -- body lowers alike under each row)
  let ownLeads (Ds : List (Ty Tree)) : Bool := force || Ds.take qs.length == qs
  let atResult (R : Ty Tree) : Ty Tree := if within T own.result R then R else own.result
  (((ProgramTyping.callSigs G ctxTy).filter fun s =>
      qs.length < s.arguments.length && ownLeads (s.arguments.take qs.length)).map fun s =>
        ({ s with result := atResult s.result, effect := own.effect } : CallEffects.Arrow (Ty Tree)),
   ((ProgramTyping.restSigs G ctxTy).filter fun r =>
      qs.length ≤ r.arguments.1.length && ownLeads (r.arguments.1.take qs.length) &&
        (PositiveRules.restElem G r.arguments.2).isSome).map fun r =>
        ({ r with result := own.result, effect := own.effect } : CallEffects.RestArrow (Ty Tree)))

/-- The fields of the allocation a constructor's body returns last (the
producer's `allocated`, closure_offers.ml:11-18). -/
partial def allocatedIn (ss : List Stmt) : Option (List (PropKey × Expr)) :=
  match ss.getLast? with
  | some (.ret _ (.alloc _ names es)) => some (names.zip es)
  | some (.ret _ (.block _ ss')) => allocatedIn ss'
  | some (.ite _ _ a _) => allocatedIn a
  | _ => none

/-- An instance's methods are its prototype chain's, the nearer first
(closure_offers.ml:37-43). -/
def protoChain (objects : List (String × List (PropKey × Expr))) :
    Nat → List String → List (PropKey × Expr) → List (PropKey × Expr)
  | fuel + 1, seen, fs => match fs.lookup SourceTypes.protoField with
    | some (.var _ p) =>
      if seen.contains p then [] else
      let own := (objects.lookup p).getD []
      own.filter (·.1 != SourceTypes.protoField) ++
        (protoChain objects fuel (p :: seen) own).filter fun (k, _) => !own.any (·.1 == k)
    | _ => []
  | 0, _, _ => []

/-- A constant's object literal or class value, registered for the offers
its uses make (the producer's `named_closure`, closure_offers.ml:29-49). -/
def registerNamed (b : Binding) : W Unit := do
  match b.annot, b.init with
  | none, .alloc _ names es =>
    modify fun w => { w with objectConsts := (b.name, names.zip es) :: w.objectConsts }
  | some _, .ctor pos (.lambda _ none [] params [] false (some inst) _ _ _ _ body) _ =>
    let some fs := (match body with
      | .alloc _ names es => some (names.zip es)
      | .block _ ss => allocatedIn ss
      | _ => none) | return
    let w ← get
    let fs := if fs.any (·.1 == SourceTypes.protoField) then protoChain w.objectConsts 64 [] fs else fs
    let methods := fs.filterMap fun (k, e) => match e with
      | .var _ m => if w.closureConsts.any (·.1 == m) then some (k, m) else none
      | _ => none
    let some (ps, I) ← StateT.lift (tryCatch (do
        let I ← lower (Fragment.translate inst)
        let ps ← params.mapM fun (_, ty) => lower (Fragment.translate ty)
        pure (some (ps, I))) fun _ => pure none) | return
    modify fun w => { w with classConsts := (b.name, pos, ps, I, methods) :: w.classConsts }
  | _, _ => pure ()

/-- A constant `n` holding a class value, read where a constructor type `P`
is expected: each method the instance of a signature of `P` states at one
fixed signature binding more parameters is offered it, at the class's
instance as receiver, and the class value the construct signature giving
that instance, at that signature's parameters where it binds more than the
constructor whose leading ones are within its own, else at the
constructor's; a variadic signature of an element rest binding no more
fixed parameters, each the constructor's, is offered as it is (the
producer's `offer_class`, closure_offers.ml:62-95, from
expression_values.ml:54 and expression_calls.ml:317-318). -/
def offerClass (n : String) (P : Ty Tree) : W Unit := do
  let some (_, pos, params, inst, methods) := (← get).classConsts.find? (·.1 == n) | return
  let T ← StateT.lift table
  let G := SourceTypes.graph T
  -- (a dictionary's field is expected at its index's value, without the
  -- `undefined` an absent read gives, expression_objects.ml:36-37)
  let [.ctors L S _] := PositiveRules.expand G (P.filter (· != Labels.undef)) | return
  let force := (← get).force.contains "offers"
  let offer (c : CallEffects.MethodArrow (Ty Tree) × Option (Ty Tree)) : W Unit :=
    modify fun w => { w with ctorOffered := if w.ctorOffered.contains (pos, c) then w.ctorOffered else w.ctorOffered ++ [(pos, c)] }
  let widen (result : Ty Tree) : W Bool := do
    let mut any := false
    for (key, m) in methods do
      let some D ← StateT.lift (fieldExpected result key) | continue
      let G ← StateT.lift graphNow
      let ([o], []) := (ProgramTyping.callSigs G D, ProgramTyping.restSigs G D) | continue
      if ← offerSig m { o with receiver := inst } then any := true
    return any
  for s in L do
    let widened ← widen s.result
    let longer := params.length < s.arguments.length &&
      (force || ((s.arguments.take params.length).zip params).all fun (D, Q) => within T D Q)
    if widened || longer then
      offer (⟨(), if longer then s.arguments else params, s.result, s.effect⟩, none)
  for r in S do
    let widened ← widen r.result
    if (PositiveRules.restElem G r.arguments.2).isSome && r.arguments.1.length ≤ params.length &&
        (force || (r.arguments.1.zip params).all fun (D, Q) => within T D Q) then
      offer (⟨(), r.arguments.1, r.result, r.effect⟩, some r.arguments.2)
    else if widened then
      -- A non-variadic pack still offers its result when a method widened;
      -- the constructor keeps its own parameters (closure_offers.ml:92-95).
      offer (⟨(), params, r.result, r.effect⟩, none)

/-- Record an expression's computed type or the reason it has none. -/
partial def record (e : Expr) (r : Except String (Ty Tree)) : W (Option (Ty Tree)) := do
  -- An expression a part of which a shared rule refuses (`refusalMark`) is
  -- refused with that part: the lowering reads the part with it.
  let r ← match r with
    | .error m =>
      if m.startsWith refusalMark then pure r else do
        let w ← get
        pure (match w.refusals.toList.find? fun (sp, _) => e.span.1 ≤ sp.1 && sp.2 ≤ e.span.2 with
          | some (_, m') => .error m'
          | none => r)
    | .ok _ => pure r
  modify fun w => { w with exprs := w.exprs.insert e.span (kindOf e, r), exprsAt := w.exprsAt.insert (w.stmtAt, e.span) r,
                           refusals := match r with
                             | .error m => if m.startsWith refusalMark then w.refusals.insert e.span m else w.refusals
                             | .ok _ => w.refusals.erase e.span }
  return r.toOption

partial def recordAt (span : Span) (kind : String) (r : Except String (Ty Tree)) : W Unit :=
  modify fun w => { w with exprs := w.exprs.insert span (kind, r), exprsAt := w.exprsAt.insert (w.stmtAt, span) r,
                           refusals := match r with
                             | .error m => if m.startsWith refusalMark then w.refusals.insert span m else w.refusals
                             | .ok _ => w.refusals.erase span }

partial def attempt (e : Expr) (x : Compiler (Ty Tree)) : W (Option (Ty Tree)) := do
  let r ← StateT.lift (tryCatch (Except.ok <$> x) fun msg => pure (.error msg))
  record e r

/-- The environment after a call: its narrowed paths end where the call may
change a value of the heap, or where its callee is unknown, but those
through stable members (`stablePath`). -/
partial def afterCall (env : Env) (r : Except String (Ty Tree × Ty Tree)) : W Env := do
  let w ← get
  if w.changedValues || r.toOption.isNone then
    -- A binding a function literal assigns is held in a cell the call may
    -- change: at its declared type again (`TSCERT_FORCE=stale` keeps it).
    let reset := if w.force.contains "stale" then [] else w.closureAssigned
    ends .all
    let kept ← StateT.lift (env.paths.filterM fun ((r, p), _) => stablePath env r p)
    return { env with
      paths := kept
      vars := env.vars.map fun (n, A) => if reset.contains n then (n, (env.decl.lookup n).getD A) else (n, A) }
  return env

/-- Whether a test cannot answer `q`: its value's type has no value of that
answer (`decided`), `!e` where `e` cannot answer the other, `a || b` not
`false` where either is never falsy and not `true` where neither is ever
truthy, `a && b` dually (the edge's slice of each operand's value). -/
partial def decidedTest (c : Expr) (q : Bool) : W Bool := do
  -- (`TSCERT_FORCE=decided`: no test answers `false`)
  if !q && (← get).force.contains "decided" then return true
  match c with
  | .not _ e => decidedTest e !q
  | .logical _ andOp l r =>
    -- `&&` cannot answer `true` where either cannot, `||` cannot answer
    -- `false` where either cannot; the other answer needs both.
    if andOp == q then return (← decidedTest l q) || (← decidedTest r q)
    else return (← decidedTest l q) && (← decidedTest r q)
  | _ =>
    let C := ((← get).exprs.get? c.span).bind (·.2.toOption)
    StateT.lift (decided C q)

/-- Whether a parameter's type places a binder of `free` at a tuple position,
through at most `depth` arrays (the producer's `places`,
expression_support.ml:128-135). -/
partial def placesHoles (G : PositiveGraphs.NormalGraph Tree) (free : List Tree) (depth : Nat) (P : Ty Tree) : Bool :=
  depth > 0 && (arrayArms G P).any fun l => match storeOf G [l] with
    | some S => match PositiveRules.expand G S with
      | [.list t []] => (t.required ++ t.optional).any (fun D => free.any fun b => D.any (occurs b)) ||
          t.rest.any (placesHoles G free (depth - 1))
      | _ => false
    | none => false

/-- Fresh array literals at generic tuple positions retain those positions,
with each value widened, recursively through an array of tuples
(expression_support.ml:124-139). Existing stores keep their contracts. -/
partial def tupleActual (P : Ty Tree) (x : Expr) (A : Option (Ty Tree)) : W (Option (Ty Tree)) := do
  let .arrayLit _ es [] := x | return A
  let G ← StateT.lift graphNow
  let target ← match arrayArms G P with
    | [l] => pure ((storeOf G [l]).bind fun S => match PositiveRules.expand G S with
        | [.list t []] => some t
        | _ => none)
    | _ => do
      let E ← StateT.lift (tryCatch (iteratedElement P) fun _ => pure none)
      pure (E.map fun E => ⟨[], [], some E, true, .readable⟩)
  let some t := target | return A
  if es.length < t.required.length ||
      (t.rest.isNone && es.length > t.required.length + t.optional.length) then return A
  let mut Es : List (Ty Tree) := []
  for (e, i) in es.zipIdx do
    let some D := t.position i | return A
    let B := ((← get).exprs.get? e.span).bind (·.2.toOption)
    let some B ← tupleActual D e B | return A
    Es := Es ++ [← StateT.lift (widen B)]
  let R ← StateT.lift (lower do
    let tuple := if t.required.isEmpty && t.optional.isEmpty then
      ⟨[], [], some (norm Es.flatten), false, .readable⟩
      else ⟨Es, [], none, false, .dense⟩
    let s ← SourceTypes.use (.list tuple [])
    let T ← get
    return [← SourceTypes.use (SourceTypes.arrayOf T s false)])
  record x (.ok R)

/-- A literal where a type `P` is expected: `[]` at the arrays of `P`
(whose own type would be an array of no element); an array or object
literal at the members of `P` its type, or its elements' tuple, is within
(TypeScript's contextual typing of a literal). Any other value keeps its
type `A`. -/
partial def fit (P : Ty Tree) (x : Expr) (A : Option (Ty Tree)) : W (Option (Ty Tree)) := do
  let T ← StateT.lift table
  let G := SourceTypes.graph T
  -- An expected type naming a hole (a binder of a call whose actual is
  -- being walked at its parameter, `applyCall`): an array literal keeps the
  -- tuple positions it states, a position holding a hole its element's own
  -- type (expression_objects.ml:269-275); any other value its own type.
  if (← get).holes.any (fun h => P.any (occurs h)) then
    return ← match x with
      | .arrayLit _ (_ :: _) [] => tupleActual P x A
      | _ => pure A
  match x with
  | .ifBody _ _ t f =>
    -- Each arm where the conditional's value is expected.
    let w ← get
    let typeOf (y : Expr) : Option (Ty Tree) := (w.exprs.get? y.span).bind (·.2.toOption)
    let A' ← fit P t (typeOf t)
    let B' ← fit P f (typeOf f)
    match A', B' with
    | some A', some B' => record x (← StateT.lift (tryCatch (.ok <$> joinTy A' B') fun m => pure (.error m)))
    | _, _ => return A
  | .arrayLit _ [] _ =>
    -- A fresh empty array has its store and the standard prototype only.
    -- An array-like host value may require additional fields (NodeArray's
    -- `pos` and `end`), and a tuple may require occupied positions.
    for l in arrayArms G P do
      -- (an arm still naming a binder of the call a callback is walked for,
      -- its result read before the binder is read off it, is no type to
      -- make the array at: the literal keeps its own, the producer's
      -- `never[]`)
      if (← get).pending.any (occurs · l) then continue
      let some S := storeOf G [l] | continue
      let [.list t []] := PositiveRules.expand G S | continue
      if !t.required.isEmpty then continue
      let O ← StateT.lift (arrayObject S)
      if within (← StateT.lift table) O [l] then return ← record x (.ok [l])
    return A
  | .lambda _ _ [] _ _ false _ none _ _ _ _ =>
    -- A function literal walked with no expected type (a field of an
    -- argument's object literal), stated at its own row alone: beside it
    -- the rows the expected callable offers it (`contextRows`); the pass
    -- checks its body at each.
    let some [l] := A | return A
    let [.arrs [own] []] := PositiveRules.expand G [l] | return A
    let (fixed, rests) := contextRows T (some P) own own.arguments ((← get).force.contains "offers")
    if fixed.isEmpty && rests.isEmpty then return A
    record x (.ok [← StateT.lift (lower (SourceTypes.use (.arrs (own :: fixed.filter (· != own)) rests)))])
  | .alloc _ names es =>
    -- The literal's own record, each field at the expected record's field
    -- where the value, itself fitted there, is within it: the record the
    -- allocation makes, which the expected type then admits.
    let some A := A | return none
    if (← get).force.contains "objects" && !P.isEmpty then return ← record x (.ok P)
    let some P ← StateT.lift (recordContext P names es) | return some A
    -- A class instance, which holds its prototype, states its own keys
    -- exactly: the bound says a method is not its own
    -- (`expression_objects.ml`, `Alloc`).
    let exact := (← get).exactAt.contains x.span || names.contains SourceTypes.protoField
    for l in P do
      let w ← get
      -- A dictionary with a writable index: the literal allocated at the
      -- dictionary itself, each of its keys a field at the dictionary's
      -- field there or else at the index, the contract's optional fields it
      -- leaves out absent.
      if let [.dict first [] vs ix os [] bs cells st] := PositiveRules.expand G [l] then
        if !cells.isEmpty && first.all (fun (k, _) => names.contains k) then
          let index := norm (cells.flatMap (·.2))
          let mut ok := true
          let mut fields : List (PropKey × Ty Tree) := []
          for (k, y) in names.zip es do
            let D := (first.lookup k).getD index
            let some B ← fit D y ((w.exprs.get? y.span).bind (·.2.toOption)) | ok := false; break
            if !within (← StateT.lift table) B D then ok := false; break
            fields := fields ++ [(k, D)]
          if ok then
            let R ← StateT.lift (prim (.dict fields [] vs ix (os.filter fun o => !names.contains o.key) [] bs cells st))
            if within (← StateT.lift table) R [l] then return ← record x (.ok R)
          continue
      -- An instance's prototype key (`[[proto]]`), which the declared
      -- instance type does not name, at its walked type.
      -- (`expression_objects.ml`: a prototype link is built at what it holds)
      let Ds ← StateT.lift (tryCatch (some <$> (names.zip es).mapM fun (k, y) =>
          if k == SourceTypes.protoField then
            match (w.exprs.get? y.span).bind (·.2.toOption) with
            | some B => pure B
            | none => throw "the prototype undetermined"
          else do
            let some D ← fieldExpected [l] k | throw "no expected field"
            pure D) fun _ => pure none)
      let some Ds := Ds | continue
      let mut fields : List (PropKey × Ty Tree) := []
      let mut own : List (PropKey × Ty Tree) := []
      let mut ok := true
      for ((k, y), D) in (names.zip es).zip Ds do
        let some B ← fit D y ((w.exprs.get? y.span).bind (·.2.toOption)) | ok := false; break
        fields := fields ++ [(k, if within (← StateT.lift table) B D then D else B)]
        own := own ++ [(k, B)]
      if !ok then continue
      -- Each field at the expected one, else at the value's own type (a
      -- literal kept where the expected member states it).
      for byField in [fields, own] do
        let R? ← StateT.lift (tryCatch (do
            -- The literal's record as written, else stating its own keys
            -- exactly (`HasTyUsing.alloc`'s bound), which meets optional
            -- fields.
            -- Each key a field the allocation writes once (a field is within
            -- a view of its read type), but a stable key the expected record
            -- states as a view: a view of its value; its stable keys kept.
            let (fs, vs, st) := match PositiveRules.expand G [l] with
              | [.refs _ [] evs _ _ _ est] =>
                let isView (k : PropKey) : Bool := (evs.lookup k).isSome && est.contains k
                (byField.filter (fun (k, _) => !isView k), byField.filter (fun (k, _) => isView k),
                  est.filter names.contains)
              | _ => (byField, [], [])
            let R ← prim (.refs fs [] vs [] [] [] st)
            if !exact && within (← table) R [l] then return some (R, false)
            let R ← prim (.refs fs [] vs [] [] [⟨true, names⟩] st)
            return if within (← table) R [l] then some (R, true) else none) fun _ => pure none)
        if let some (R, _) := R? then return ← record x (.ok R)
    return some A
  | .arrayLit _ es [] =>
    -- The one array member of `P` whose positions admit the elements, each
    -- element made at its position: the store's contract (positions, rest,
    -- `readonly`, presence) is that member's.
    let some A := A | return none
    for l in arrayArms G P do
      let some S := storeOf G [l] | continue
      let [.list t []] := PositiveRules.expand G S | continue
      let n := es.length
      if !(t.required.length ≤ n && (n ≤ t.required.length + t.optional.length || t.rest.isSome)) then continue
      let w ← get
      let mut ok := true
      for (y, i) in es.zipIdx do
        let some D := t.position i | ok := false; break
        let some B ← fit D y ((w.exprs.get? y.span).bind (·.2.toOption)) | ok := false; break
        if !within (← StateT.lift table) B D then ok := false; break
      if ok then return ← record x (.ok [l])
    -- At an iterable other than an array: the readonly array of what it
    -- yields, holes read as `undefined` where that admits it.
    if let some E ← StateT.lift (iteratedElement P) then
      let w ← get
      let mut ok := true
      for y in es do
        let some B ← fit E y ((w.exprs.get? y.span).bind (·.2.toOption)) | ok := false; break
        if !within (← StateT.lift table) B E then ok := false; break
      if ok then
        let R ← StateT.lift (lower do
          let s ← SourceTypes.use (.list ⟨[], [], some E, true, .readable⟩ [])
          let T ← get
          return [← SourceTypes.use (SourceTypes.arrayOf T s true)])
        if within (← StateT.lift table) R P then return ← record x (.ok R)
    return some A
  | .arrayLit _ es spreads =>
    -- An array literal containing spreads is a fresh store. At an array
    -- contract with no fixed positions, each item or spread element must
    -- fit its rest contract; existing operands retain their store types.
    let some A := A | return none
    -- `array-spreads` proposes the expected store even for incompatible items.
    let forced := (← get).force.contains "array-spreads"
    for l in arrayArms G P do
      let some S := storeOf G [l] | continue
      let [.list t []] := PositiveRules.expand G S | continue
      if !t.required.isEmpty || !t.optional.isEmpty then continue
      let some E := t.rest | continue
      let O ← StateT.lift (arrayObject S)
      if !within (← StateT.lift table) O [l] then continue
      let w ← get
      let mut ok := true
      for (y, i) in es.zipIdx do
        let some B := (w.exprs.get? y.span).bind (·.2.toOption) | ok := false; break
        if spreads.contains i then
          let held ← StateT.lift (tryCatch (do
            let B ← boundOf B
            let G ← graphNow
            if !arraysOnly G B then return none
            let H ← elementAt B none (missing := false)
            let sparse := B.any fun l => (storeOf G [l]).any fun S =>
              match PositiveRules.expand G S with
              | [.list t []] => t.presence == .sparse
              | _ => false
            return some (norm (H ++ if sparse then [Labels.undef] else []))) fun _ => pure none)
          let T ← StateT.lift table
          if !forced && !held.any (fun H => within T H E) then ok := false; break
        else
          let some B ← fit E y (some B) | ok := false; break
          if !forced && !within (← StateT.lift table) B E then ok := false; break
      if ok then return ← record x (.ok [l])
    return some A
  | .build _ names es =>
    -- Context reaches every fresh part of a copy, including a copy nested
    -- in a call's object literal (expression_objects.ml:135-218).
    let some A := A | return none
    if (← get).force.contains "objects" && !P.isEmpty then return ← record x (.ok P)
    let spreadExp ← StateT.lift (spreadContext P)
    let mut As : List (Ty Tree) := []
    for (k, y) in names.zip es do
      let w ← get
      let B := (w.exprs.get? y.span).bind (·.2.toOption)
      let D ← match k with
        | some k => StateT.lift (fieldExpected P (.str k))
        | none => pure (if copyLiteral y then spreadExp else none)
      let B ← match D with
        | some D => fit D y B
        | none => pure B
      let some B := B | return some A
      As := As ++ [B]
    let forced := (← get).force.contains "spreads"
    let byArm ← StateT.lift (P.mapM fun l => do
      let copies ← tryCatch (do
        let mut parts : List (Option PropKey × Ty Tree) := []
        for (k, B) in names.zip As do
          match k with
          | some k =>
            let D ← match ← fieldExpected [l] (.str k) with
              | some D => pure D
              | none => widen B
            if !within (← table) B D then throw "a part not within its expected field"
            parts := parts ++ [(some (.str k), D)]
          | none => parts := parts ++ [(none, B)]
        let alts ← copyParts [{}] parts forced
        return some (← alts.mapM copyType)) fun _ => pure none
      return (l, copies))
    let some n := (byArm.findSome? (·.2)).map (·.length) | return some A
    let T ← StateT.lift table
    let mut out : Ty Tree := []
    for i in List.range n do
      let some C := byArm.findSome? fun (l, cs) => cs.bind fun cs =>
          if cs.length == n then cs[i]?.bind fun C => if within T C [l] then some C else none else none
        | return some A
      out := out ++ C
    if n == 0 then return some A
    record x (.ok (norm out))
  | _ => return A

/-- The environment where a call of a guard (or, `asserts`, an assertion
function) of the callee's recorded type holds: the actual its promise names
at the signature's guarded type, the first signature stating one whose
parameters admit the actuals' recorded types. -/
partial def promised (env : Env) (callee : Expr) (args : List Expr) (asserts : Bool)
    (site : Option Span := none) : W Env := do
  let w ← get
  -- Whether the call may have changed a value of the heap: the last call's
  -- instance, else, for a call walked earlier (a test's, refined after its
  -- condition is walked), whether its walk ended a path.
  let changed := match site with
    | some sp => (w.endsIn.get? sp).getD true
    | none => w.changedValues
  let typeOf (x : Expr) : Option (Ty Tree) := (w.exprs.get? x.span).bind (·.2.toOption)
  let some F := typeOf callee | return env
  let T ← StateT.lift table
  let G := SourceTypes.graph T
  for s in ProgramTyping.callSigs G F do
    let p? := match s.effect.promise with
      | some (.guards p) => if asserts then none else some p
      | some (.asserts p) => if asserts then some p else none
      | none => none
    let some p := p? | continue
    let admits := (args.zip s.arguments).all fun (x, D) => match typeOf x with
      | some A => within T A D
      | none => true
    if !admits || args.length < p + 1 then continue
    let some x := args[p]? | continue
    -- A member path read before a call that may change a value of the heap
    -- may hold another value after it: no path is narrowed there.
    if changed then
      if let some (_, _ :: _) := memberPath x then return env
    return ← StateT.lift (narrowTo env x s.result)
  return env

/-- A return's copy of a finalizer (or of a loop's close) walked to the
entries `walked`: its statements' entries at `positions`, read by that
copy's points (their scope holds `key`, `%return@p%`). -/
def recordCopy (positions : List Nat) (key : String) (walked : Std.HashMap Nat (List (String × Ty Tree))) : W Unit :=
  modify fun w => { w with declarations := positions.foldl (fun m k =>
    ((walked.get? k).map (m.insert (k, key) ·)).getD m) w.declarations }

/-- After a loop's close, each of the `nr` latest returns held at its
copy's completion: its held value's entry, and the return held only where
the copy completes. -/
def closeCopies (nr : Nat) (copies : List (Span × Span × Option Env)) : W Unit :=
  modify fun w =>
    let entries := copies.foldl (fun m (q, xs, g) => match g with
      | some ge => if xs.1 != q.1 then m.insert xs.1 ge.vars else m
      | none => m) w.entries
    { w with entries, held := copies.filterMap (fun (q, xs, g) => g.map (q, xs, ·)) ++ w.held.drop nr }

partial def collectBreaks (label : Option String) (saved : List (Option String × Env)) : W (Option Env) := do
  let w ← get
  let (mine, others) := w.breaks.partition (·.1 == label)
  set { w with breaks := others ++ saved }
  return mine.foldl (fun acc (_, b) => join acc (some b)) none

mutual

partial def useIn (env : Env) (n : String) (e : Expr) (P : Option (Ty Tree)) : W (List (Option (Ty Tree))) := do
  let fieldHint (P : Option (Ty Tree)) (k : PropKey) : W (Option (Ty Tree)) := do
    let G ← StateT.lift graphNow
    let ds := (P.getD []).filterMap fun l => match PositiveRules.expand G [l] with
      | [.refs fs [] vs os ..] | [.dict fs [] vs _ os ..] =>
        fs.lookup k <|> vs.lookup k <|> ((os.find? (·.key == k)).map (·.type))
      | _ => none
    return match ds.eraseDups with | [D] => some D | _ => none
  match e with
  | .var _ m => return if n == m then [P] else []
  | .call _ (.var _ g) args [] [] =>
    if g == n then return []
    let gs := (← get).generics
    let params ← StateT.lift (tryCatch (do
      let c ← match gs.lookup g with
        | some generic => genericCallee generic []
        | none => do
          let some F := env.vars.lookup g | return []
          calleeOf F [Labels.undef] []
      let [a] := c.fixed | return []
      if !c.rests.isEmpty then return []
      if c.binders.isEmpty then return a.arguments
      let some P := P | return []
      if a.arguments.length != args.length then return []
      let mut solution := c.seed
      for binder in c.binders do
        let some A ← matchBinder binder a.result P (vars := env.vars) (siblings := c.binders) | return []
        if A.isEmpty then return []
        solution := upd solution binder A
      return a.arguments.map (substitute solution)) fun _ => pure [])
    let mut uses := []
    for (a, i) in args.zipIdx do uses := uses ++ (← useIn env n a params[i]?)
    return uses
  | .alloc _ ks es =>
    let mut uses := []
    for (k, e) in ks.zip es do
      let D ← fieldHint P k
      uses := uses ++ (← useIn env n e D)
    return uses
  | .build _ ks es =>
    let mut uses := []
    for (k, e) in ks.zip es do
      let D ← match k with | some k => fieldHint P (.str k) | none => pure none
      uses := uses ++ (← useIn env n e D)
    return uses
  | .ifBody _ c t f => return (← useIn env n c none) ++ (← useIn env n t P) ++ (← useIn env n f P)
  | .arrayLit _ es spreads =>
    let mut uses := []
    for (e, i) in es.zipIdx do
      let D ← if spreads.contains i then StateT.lift (tryCatch (do
          let some P := P | return none
          let E ← elementAt P none (missing := false)
          let store ← lower (SourceTypes.use (.list ⟨[], [], some E, false, .readable⟩ []))
          some <$> lower (do return [← SourceTypes.use (SourceTypes.arrayOf (← get) store false)])) fun _ => pure none)
        else pure none
      uses := uses ++ (← useIn env n e D)
    return uses
  | .block _ ss => useNested env n ss
  | _ =>
    let children : List Expr := match e with
      | .lit .. | .var .. => []
      | .shapeTest _ _ _ e | .tagMember _ _ _ _ _ e | .not _ e | .unary _ _ e | .cast _ _ e | .read _ _ e
      | .assign _ _ _ e | .nullishAssign _ _ _ e => [e]
      | .ctor _ e fs => e :: fs.map (·.2)
      | .lambda _ _ _ _ ds _ _ _ _ _ _ body => ds.map (·.2) ++ [body]
      | .construct _ f args _ _ | .call _ f args _ _ | .invoke _ f args _ _ => f :: args
      | .logical _ _ a b | .coalesce _ a b | .equality _ _ a b | .singletonTest _ _ _ _ a b
      | .write _ _ a b | .index _ _ a b | .elemAt _ a b | .arith _ _ a b | .logicalAssign _ _ a b
      | .comma _ a b | .inKeys _ a b | .withValue _ a b _ _ | .optional _ _ a b | .withObject _ _ a b => [a, b]
      | .indexWrite _ _ a b c | .elemWrite _ a b c => [a, b, c]
      | .update _ _ a b _ => a :: b.toList
      | .arrayAssign _ targets rest rhs => rhs :: targets.flatMap (fun q => q.target :: q.default_.toList) ++ (rest.map (·.2.2.target)).toList
      | .bindWithReceiver _ f r args | .callWithReceiver _ f r args => f :: r :: args
      | .applyWithReceiver _ f r list _ => f :: r :: list.toList
      | .objectAssign _ t sources => t :: sources
      | .alloc .. | .build .. | .arrayLit .. | .ifBody .. | .block .. => []
    let mut uses := []
    for child in children do uses := uses ++ (← useIn env n child none)
    return uses

/-- Source.children of a block body, with no contextual type inherited. -/
partial def useNested (env : Env) (n : String) (ss : List Stmt) : W (List (Option (Ty Tree))) := do
  let mut uses := []
  for s in ss do
    let (es, nested) : List Expr × List Stmt := match s with
      | .constants _ bs | .mutables _ bs => (bs.map (·.init), [])
      | .ret _ e | .effect _ e | .throw _ e => ([e], [])
      | .destructure _ p d e => (e :: d.toList ++ p.defaults, [])
      | .ite _ c a b => ([c], a ++ b.getD [])
      | .loop _ c b u _ => ([c], b ++ u)
      | .block _ _ b => ([], b)
      | .forOf _ _ _ _ e b => ([e], b)
      | .tryStmt _ b h f => ([], b ++ (h.map (·.2)).getD [] ++ f.getD [])
      | .closing _ c b => ([], b ++ c)
      | .brk .. | .cont .. => ([], [])
    for e in es do uses := uses ++ (← useIn env n e none)
    uses := uses ++ (← useNested env n nested)
  return uses

end

/-- Whole-value uses in the following statements of this block, as
statement_analysis.ml:89-165. Nested control statements supply no hint. -/
partial def useHints (env : Env) (n : String) (ss : List Stmt) (typed : Bool := true) (first : Bool := false) : W (List (Ty Tree)) := do
  let mut out := []
  for s in ss do
    let uses ← match s with
      | .constants _ bs | .mutables _ bs => do
        let mut uses := []
        for b in bs do
          let P ← match b.annot with
            | some t => StateT.lift (tryCatch (some <$> lower (Fragment.translate t)) fun _ => pure none)
            | none => pure none
          uses := uses ++ (← useIn env n b.init P)
        pure uses
      | .ret _ e => useIn env n e (← get).expected
      | .effect _ e => useIn env n e none
      | _ => pure (if first && s.freeNames.contains n then [none] else [])
    let found := if typed then (uses.filterMap id).take 1 else (uses.take 1).filterMap id
    if first && !uses.isEmpty then return found
    out := out ++ found
  return out

/-- A declaration's construction hint and evolving contract registration. -/
partial def declarationHint (env : Env) (b : Binding) (mutable_ : Bool)
    (written : Option (Ty Tree)) : W (Option (Ty Tree)) := do
  modify fun w => { w with evolving := w.evolving.filter (·.1 != b.name) }
  if b.annot.isSome then return written
  let kind := match b.init with
    | .arrayLit _ [] _ => some true
    | .lit _ .vnull | .lit _ .vundef => if mutable_ then some false else none
    | _ => none
  if let some array := kind then
    modify fun w => { w with evolving := (b.name, (b.init.span, array)) :: w.evolving }
    let w ← get
    let A := if w.force.contains "evolving" then [] else (w.assumed.lookup b.init.span).getD []
    if array then
      return some (← StateT.lift (lower do
        let store ← SourceTypes.use (.list ⟨[], [], some A, false, .readable⟩ [])
        return [← SourceTypes.use (SourceTypes.arrayOf (← get) store false)]))
    let uses := (← useHints env b.name (← get).following false).eraseDups
    if let [U] := uses then modify fun w => { w with evolvedUses := upd w.evolvedUses b.init.span U }
    return written
  if !mutable_ && !(← get).force.contains "first-use" then
    let fresh := match b.init with
      | .arrayLit _ (_ :: _) _ => true
      | .invoke _ (.read _ (.str m) _) [_] [] [] => m == "map" || m == "flatMap"
      | _ => false
    if fresh then
      if let some H := (← useHints env b.name (← get).following).head? then
        let G ← StateT.lift graphNow
        if !H.isEmpty && H.all (fun l => (storeOf G [l]).isSome) then return some H
  return written

/-- Each binder in `lambdaBinders` (a callback literal's parameter) that an
earlier actual's parameter takes at a position of one of its methods, at the
callable the actual's method of that key takes there (`applyCall`'s
`from_actuals`). -/
def methodBinders (args : List Expr) (Ps : List (Ty Tree)) (As : List (Option (Ty Tree)))
    (lambdaBinders : List Tree) : Compiler (List (Tree × Ty Tree)) := do
  let mut fromActuals : List (Tree × Ty Tree) := []
  if lambdaBinders.isEmpty then return fromActuals
  let Ga := SourceTypes.graph (← table)
  -- A type's methods by key, each its signatures' parameters and effects.
  let methodsOf (X : Ty Tree) : List (PropKey × List (List (Ty Tree) × CallEffects.Effect)) :=
    match ProgramTyping.objectClauses Ga X with
    | [.refs fs _ vs _ ms _ _] =>
      ((fs ++ vs).map fun (k, t) => (k, (ProgramTyping.callSigs Ga t).map fun s => (s.arguments, s.effect))) ++
        ms.map fun m => (m.key, m.calls.map fun s => (s.arguments, s.effect))
    | _ => []
  for ((x, P), i) in (args.zip Ps).zipIdx do
    if callback x then continue
    let some A := As[i]?.join | continue
    let actual := methodsOf A
    for (k, ws) in methodsOf P do
      let [(wps, we)] := ws | continue
      let some ss := actual.lookup k | continue
      for (p, j) in wps.zipIdx do
        let [r] := p | continue
        if !lambdaBinders.contains r || (fromActuals.lookup r).isSome then continue
        let callables := ss.filterMap fun (ps, e) =>
          if ps.length != wps.length then none else match ps[j]? with
            | some t => if (ProgramTyping.callSigs Ga t).isEmpty then none else some (e, t)
            | none => none
        match (callables.filter fun (e, _) => e.covers we).reverse.head? <|> callables.head? with
        | some (_, t) => fromActuals := fromActuals ++ [(r, t)]
        | none => pure ()
  return fromActuals

/-- What a call at instance `inst` changes, recorded for the walk's footprints:
its instance's footprint, a declaration's passed functions' effects, a change
of its receiver's store or elements, its fresh result and its throws
(`applyCall`'s effects, read after the actuals are walked). -/
def callChanges (c : Callee) (inst : CallEffects.Arrow (Ty Tree)) (As : List (Option (Ty Tree)))
    (args : List Expr) (receiverFresh : Bool) : W Unit := do
  -- A call whose instance's result is the empty type never returns
  -- normally: on a normal return it changes nothing; its throw is its
  -- signature's (the producer's `no_return`, source.ml:1031-1035,
  -- expression_closures.ml:320, proposal.ml:96; the pass's footprint of a
  -- call decides the result's emptiness itself).
  -- (but under a handler or in an async body, where its throw is caught and
  -- the heap it leaves is a normal return's: source.ml:1166-1175,
  -- expression_closures.ml:344)
  if inst.result.isEmpty && !(← get).caught && !(← get).asyncBody then
    modify fun w => { w with lastFresh := false }
    if !inst.effect.onThrow then modify fun w => { w with throwWrites := true }
    return
  -- A call changing the heap, by its instance's footprint.
  if inst.effect.footprint != ⟨.keep, .keep⟩ then wrote inst.effect.footprint.value inst.effect.footprint.store
  -- For a declaration's footprint, a call passing a function may run it:
  -- the function's own effect at each of its signatures, read after the
  -- actuals are walked; one of no known type is the ordinary effect's.
  if (← get).strict then
    let Gn := SourceTypes.graph (← StateT.lift table)
    -- (a generic module function's instance is not yet read off the
    -- function passed: the ordinary effect)
    let unread := !c.names.isEmpty || !c.explicit.isEmpty
    for (A, x) in As.zip args do
      match (if unread then none else A) with
      | some A =>
        for p in ProgramTyping.callSigs Gn A do
          callChange p.effect
          if !p.effect.onThrow then modify fun w => { w with throwWrites := true }
      | none =>
        if callback x || (A.any fun A => !(ProgramTyping.callSigs Gn A).isEmpty) then
          wrote .any .any
          modify fun w => { w with throwWrites := true }
  if inst.effect.footprint.value != .keep || inst.effect.receiverOwn || inst.effect.receiverStore ||
      inst.effect.elementWrite.isSome then
    modify fun w => { w with changedValues := true }
  -- A change its receiver's store or elements state beside the footprint.
  -- (a growing receiver within its footprint; one changing its own
  -- locations at the values and its store's change; a receiver's store or
  -- elements both).
  if inst.effect.receiverOwn then wrote .any inst.effect.footprint.store
  -- (but a change of a receiver's store the run allocated, a constant
  -- holding one, which its frame bounds: the producer's `receiver_fresh`,
  -- source.ml:953-956, the checker's `Effect.within_below`)
  if (inst.effect.receiverStore && !receiverFresh) || (inst.effect.elementWrite.isSome && !(← get).strict) then
    wrote .any .any
  modify fun w => { w with lastFresh := inst.effect.fresh }
  if !inst.effect.onThrow then modify fun w => { w with throwWrites := true }
  -- For a declaration's footprint, a throw no footprint bounds that a
  -- handler catches leaves the bound.
  if (← get).strict && (← get).caught && !inst.effect.onThrow then wrote .any .any

/-- A literal of no binders, rest or guard passed where the instance's
parameter is one fixed signature binding more parameters than it, of
the ordinary effect or one a row of the literal's covers, is stated at
that parameter, where every row of the literal leads with its own
parameters: calls through it discard the further actuals, and its
body is checked at the parameter's row (the producer's `offer_to`,
expression_calls.ml:264-307, applied by `offer` at the selected
signature). -/
def offerToParameters (args : List Expr) (Ps : List (Ty Tree)) : W Unit := do
  let Go := SourceTypes.graph (← StateT.lift table)
  for (x, P) in args.zip Ps do
    let .lambda _ _ tps params _ false _ none .. := x | continue
    if !tps.isEmpty then continue
    let some (_, .ok L) := (← get).exprs.get? x.span | continue
    let rows := ProgramTyping.callSigs Go L
    let some own := rows.find? (·.arguments.length == params.length) | continue
    if !(rows.all fun r => r.arguments.take params.length == own.arguments) then continue
    let [s] := ProgramTyping.callSigs Go P | continue
    if P.length != 1 || !(ProgramTyping.restSigs Go P).isEmpty || s.arguments.length ≤ params.length then continue
    let supplies := s.effect == CallEffects.Effect.ordinary || rows.any fun r =>
      let e := { r.effect with fresh := r.effect.fresh && s.effect.fresh, onThrow := r.effect.onThrow && s.effect.onThrow }
      e == s.effect || ({ e with closed := s.effect.closed } == s.effect && e.closed.le s.effect.closed)
    if supplies then recordAt x.span (kindOf x) (.ok P)

/-- A call of a callee in the walk: a union of callables at one signature
its arms meet (`armsCallee`; `TSCERT_FORCE=arms` at the first arm's). For a
declaration's footprint, a call of a union is a call of no one instance: it
may change anything, and its throw too (the producer's `callable`,
proposal.ml:85-92, reads one callee's signatures). -/
def armsCall (c : Callee) (callbacks : List Bool) (As : List (Option (Ty Tree))) : W (Except String Callee) := do
  if c.arms.isEmpty then return .ok c
  let T ← StateT.lift table
  let w ← get
  if w.strict then
    wrote .any .any
    modify fun w => { w with throwWrites := true }
  return armsCallee (SourceTypes.graph T) T c callbacks As (w.force.contains "arms")

/-- The narrowing a condition answering `q` makes. -/
partial def refine (env : Env) (c : Expr) (q : Bool) : W Env := do
  match c with
  | .var _ name =>
    let e ← StateT.lift (narrowTarget env c .truthy q)
    -- A constant holding a condition's value, `true`: each immutable binding
    -- other than it at what the condition narrows where it holds (the
    -- lowering's `constantImplications`, Control.lean:208-224).
    let w ← get
    -- (`TSCERT_FORCE=implications`: every constant's initializer, every
    -- binding other than it)
    let forced := w.force.contains "implications"
    let some init := if q then w.conditions.lookup name else none | return e
    let narrowed ← refine e init true
    let immutable (n : String) := n != name && (forced || w.consts.contains n || w.values.contains n)
    return { e with vars := e.vars.map fun (n, A) => if immutable n then (n, (narrowed.vars.lookup n).getD A) else (n, A) }
  | .read .. => StateT.lift (narrowTarget env c .truthy q)
  | .not _ e => refine env e !q
  | .cast _ _ e => refine env e q
  -- `(a, b)` tested: `b`'s answer, after `a`'s effects.
  -- (none where the test assigns a binding: the narrowing would be of the
  -- binding's value before the assignment)
  | .comma _ _ r =>
    if env.vars.any fun (n, _) => assignsStmt n (.effect c.span c) then return env
    refine env r q
  | .logical _ andOp l r =>
    -- The right operand runs after the left's narrowing: where its walk
    -- ended a path (a call that may change a value of the heap, a write, an
    -- assignment), or where it was not walked and may call, the narrowed
    -- paths end but those through stable members, as after a call
    -- (`afterCall`; the producer's step havocs only where it may write and
    -- keeps `stable_path`, execution_analysis.ml:244-249).
    let after (e : Env) : W Env := do
      if !((← get).endsIn.get? r.span).getD (mayCall r) then return e
      return { e with paths := ← StateT.lift (e.paths.filterM fun ((root, p), _) => stablePath e root p) }
    -- The left test describes the value before the right operand runs.
    -- A binding the right assigns keeps its post-evaluation type here
    -- (execution_analysis.ml:274: separate states for a condition's exits).
    let left (answer : Bool) : W Env := do
      let e ← refine env l answer
      let written (n : String) := assignsStmt n (.effect r.span r)
      return { e with
        vars := e.vars.map fun (n, A) => (n, if written n then (env.vars.lookup n).getD A else A)
        paths := e.paths.filter fun ((n, _), _) => !written n }
    if andOp == q then refine (← after (← left q)) r q
    else
      let a ← left q
      let b ← refine (← after (← left !q)) r q
      return (join (some a) (some b)).getD a
  | .shapeTest _ tag equal e => StateT.lift (narrowTarget env e tag (equal == q))
  | .singletonTest _ tag equal testLeft l r =>
    -- A comparison of a saved field cannot refine its current contents
    -- after the other operand may write it.
    if testLeft && ((← get).endsIn.get? r.span).getD (mayCall r) then
      if let some (root, path@(_ :: _)) := memberPath l then
        if !(← StateT.lift (stablePath env root path)) then return env
    let other := if testLeft then r else l
    StateT.lift (narrowTarget env (if testLeft then l else r) tag (equal == q) (match other with | .lit .. => true | _ => false))
  -- Strict equality with an operand of one value: the test of that value on
  -- the other operand (`comparisonsExpr`'s choice, `singletonTag`).
  | .equality _ equal l r =>
    let w ← get
    let typeOf (x : Expr) : Option (Ty Tree) := (w.exprs.get? x.span).bind (·.2.toOption)
    let G ← StateT.lift graphNow
    let isLit (x : Expr) : Bool := match x with | .lit .. => true | _ => false
    match (typeOf r).bind (singletonTag G), (typeOf l).bind (singletonTag G) with
    | some tag, _ => do
      if (w.endsIn.get? r.span).getD (mayCall r) then
        if let some (root, path@(_ :: _)) := memberPath l then
          if !(← StateT.lift (stablePath env root path)) then return env
      StateT.lift (narrowTarget env l tag (equal == q) (isLit r))
    | _, some tag => StateT.lift (narrowTarget env r tag (equal == q) (isLit l))
    | _, _ =>
      -- Equal to an operand holding one of several singletons: each
      -- operand the union of its slices at each singleton the other may
      -- hold (the lowering's split, one singleton at a time, each member
      -- of the operand's type, `equalitySplit`, Control.lean:315-340).
      if equal != q then return env
      let singletons (y : Expr) : Option (List Tag) :=
        (typeOf y).bind fun B => if B.isEmpty then none else
          (ProgramTyping.members G B).mapM fun b => singletonTag G [b]
      let mut env := env
      for (x, y) in [(l, r), (r, l)] do
        if let some ts := singletons y then
          let mut out : Option Env := none
          for t in ts do out := join out (some (← StateT.lift (narrowTarget env x t true)))
          env := out.getD env
      return env
  -- A call of a type guard (`promise := guards p`): on its true arm its
  -- actual `p` at the guarded type (`PromiseCalls`' implication); a method
  -- guard (`c.isWord(v)`, `ts.isIdentifier(n)`) at its member's recorded
  -- type, as the lowering reads it (`Control.promiseNarrowing`'s `.invoke`).
  | .call _ callee args _ _ | .callWithReceiver _ callee _ args | .invoke _ callee args _ _ =>
    if !q && !(← get).force.contains "guards" then return env
    promised env callee args false (some c.span)
  | .tagMember _ _ none tags _ e =>
    let sliced (A : Ty Tree) : Compiler (Ty Tree) := do
      if q then do
        let parts ← tags.mapM fun t => slice A t true
        pure (norm parts.flatten)
      else tags.foldlM (fun B t => slice B t false) A
    match memberPath e with
    | some (root, []) =>
      let some A := env.vars.lookup root | return env
      return { env with vars := upd env.vars root (← StateT.lift (sliced A)) }
    | some (root, path) => StateT.lift (narrowPath env root path sliced)
    | _ => return env
  -- A family guard testing its operand's field (`ts.isIdentifier(n)`, the
  -- `kind` field): the binding's arms whose field can answer so, `undefined`
  -- answering no `true` and, where it throws, no `false` either
  -- (`Control.conditionContext`'s `.tagMember`, `PromiseCalls.memberFieldSlice`).
  | .tagMember _ _ (some f) tags onUndefined e =>
    let G ← StateT.lift graphNow
    -- (`TSCERT_FORCE=guards`: the true answer's arms on both edges)
    let q := q || (← get).force.contains "guards"
    let sliced (A : Ty Tree) : Ty Tree :=
      let A := if q || onUndefined == .throws then BranchRefinement.tagSlice G A .isUndef false else A
      norm (PromiseCalls.memberFieldSlice G A f tags q [])
    -- Keep the excluded field values for subsequent discriminant tests.
    let env ← if q || tags.isEmpty then pure env else
      if tags.all (fun t => match t with | .numEq _ => true | _ => false) then
        -- Numeric family exclusions commute: slice each field once through
        -- the set, then filter its receiver against the accumulated contents.
        StateT.lift (narrowTargetWith env (.read c.span f e) fun A =>
          excludeNumbers tags A)
      else tags.foldlM (fun env t =>
        StateT.lift (narrowTarget env (.read c.span f e) t false)) env
    match memberPath e with
    | some (root, []) =>
      let some A := env.vars.lookup root | return env
      return { env with vars := upd env.vars root (sliced A) }
    -- On a member path (`ts.isIdentifier(m.name)`): the path so narrowed.
    | some (root, path) => StateT.lift (narrowPath env root path fun A => pure (sliced A))
    | _ => return env
  | _ => return env

/-- The callee's type at a call: its own where it states one; a scheme's
rest at the instance; a construct signature; else every signature of the
scheme the actuals' count admits (`sigs`), at the binders `σ`. -/
def calleeAtCall (c : Callee) (σ : List (Tree × Ty Tree)) (inst : CallEffects.Arrow (Ty Tree))
    (rest : Option (CallEffects.RestArrow (Ty Tree))) (fitting : List (CallEffects.Arrow (Ty Tree))) :
    Compiler (Ty Tree) := do
  let sub (A : Ty Tree) : Ty Tree := substitute σ A
  match c.own, rest with
  | some F, _ => pure F
  | none, some r => do
    -- A scheme's rest at the instance: the argument pack of its positions
    -- read at the binders, a binder's meet row at the binder's type itself
    -- (the row the claims state, `Scheme.closureRows`' instances,
    -- Schemes.lean:627-660): a spread's store spreads into the pack whose
    -- element holds its positions' labels (`VariadicTyping.SpreadsInto`).
    let r' := r.map sub
    let G ← graphNow
    let pack ← match c.binders.isEmpty, PositiveRules.expand G r.arguments.2 with
      | false, [.pack t []] =>
        lower (do return [← SourceTypes.use (.pack
          { t with required := t.required.map sub, optional := t.optional.map sub, rest := t.rest.map sub } [])])
      | _, _ => pure r'.arguments.2
    return [← lower (SourceTypes.use (.arrs [] [{ r' with arguments := (r'.arguments.1, pack) }]))]
  | none, none =>
    if c.construct then do return [← lower (SourceTypes.use (.ctors [⟨(), inst.arguments, inst.result, inst.effect⟩]))]
    -- Every signature of the scheme the actuals' count admits, at the
    -- binders: the step chooses among them (`SinglePass.directCall`), a
    -- precondition's where the facts establish it.
    else do
      -- A scheme-typed local's instance: a bounded binder's row is a meet
      -- row, whose image is the one clause row holding the meet of its
      -- binders' types' clauses with the row's own (`SchemeInstances.meetOk`;
      -- `Scheme.closureRows`' instances, Schemes.lean:627-660, compute the
      -- producer's so).
      let sigs := fitting
      let mut images : List (Tree × Ty Tree) := []
      for l in (sigs.flatMap fun x => (x.receiver :: x.result :: x.arguments).flatten.flatMap meetsIn).eraseDups do
        let .meet ps := l | continue
        let found := ps.toList.filterMap (σ.lookup ·)
        let own := ps.toList.filter fun p => (σ.lookup p).isNone
        let G ← graphNow
        if found.isEmpty || !found.all G.plainTy || !G.plainTy own then continue
        let cs := PositiveRules.meetMany (found.map (PositiveRules.clausesOf G) ++
          (if own.isEmpty then [] else [PositiveRules.clausesOf G own]))
        if cs.isEmpty then continue
        images := images ++ [(l, [← lower (modifyGet fun T => let (T, l) := EquationStore.intern T cs; (l, T))])]
      let row (A : Ty Tree) : Ty Tree := norm (A.flatMap (EquationLowering.treeReplace fun u =>
        match images.lookup u with
        | some I => some I
        | none => match u with
          | .meet _ => some (sub [u])
          | u => σ.lookup u))
      let rows (x : CallEffects.Arrow (Ty Tree)) : CallEffects.Arrow (Ty Tree) :=
        { x.map sub with receiver := row x.receiver, arguments := x.arguments.map row, result := row x.result }
      if c.binders.isEmpty then return [← lower (SourceTypes.use (.arrs [inst] []))]
      -- (of those, the ones whose receiver admits the callee's, where
      -- some does: a member stating its signatures at several receivers, a
      -- dense and a sparse array's, is read at the walked receiver's, as the
      -- producer claims the member at the signature the call selects)
      let all := sigs.map rows
      let T ← table
      let mine := all.filter fun a => within T c.receiver a.receiver
      return [← lower (SourceTypes.use (.arrs (if mine.isEmpty then all else mine) []))]

/-- The rows a function literal at `span` of no rest binder, guard or
scheme is stated at: its own row `a` (at its own parameters `qs` where it
was walked at a signature, `walkedAtSig`), the rows its expected callable
`ctx` offers it (`contextRows`) and those the uses of the constant holding
it offer (`offerUse`); `rest` where it has a tuple rest of fixed positions. -/
def literalRows (span : Span) (a : CallEffects.Arrow (Ty Tree)) (qs : List (Ty Tree))
    (ctx : Option (Ty Tree)) (walkedAtSig rest : Bool) : W (Ty Tree) := do
  let ownRow := if walkedAtSig then { a with arguments := qs } else a
  let T ← StateT.lift table
  -- (`TSCERT_FORCE=offers`: whatever the leading ones, the adversarial
  -- proposal)
  let forceOffers := (← get).force.contains "offers"
  let leads (Ds : List (Ty Tree)) : Bool := forceOffers || (Ds.zip qs).all fun (D, Q) => within T D Q
  -- An offered row at the offered signature's result where the body's is
  -- within it, else the body's (the producer's `{s with call_effect}` and
  -- `discarded_signature`, expression_closures.ml:400-405, semantic.ml:358:
  -- the offered result, the closure's own effect and leading parameters).
  let atResult (R : Ty Tree) : Ty Tree := if within T ownRow.result R then R else ownRow.result
  let (fixedOffers, restOffers) := if rest then ([], []) else contextRows T ctx ownRow qs forceOffers
  -- and at each a use of the constant holding it offers (`offerUse`).
  let useOffers := ((← get).offers.filter (·.1 == span)).filterMap fun (_, s) =>
    if !rest && qs.length < s.arguments.length && leads (s.arguments.take qs.length) then
      let a : CallEffects.Arrow (Ty Tree) := { s with arguments := qs ++ s.arguments.drop qs.length }
      some { a with result := atResult s.result, effect := ownRow.effect }
    else none
  let useRests := ((← get).restOffers.filter (·.1 == span)).filterMap fun (_, r) =>
    if !rest && qs.length ≤ r.arguments.1.length && leads (r.arguments.1.take qs.length) then
      some ({ r with arguments := (qs ++ r.arguments.1.drop qs.length, r.arguments.2),
                     result := atResult r.result, effect := ownRow.effect } : CallEffects.RestArrow (Ty Tree))
    else none
  let restOffers := restOffers ++ useRests.filter (!restOffers.contains ·)
  let rows := ownRow :: ((fixedOffers ++ useOffers).foldl (fun acc s => if acc.contains s || s == ownRow then acc else acc ++ [s]) [])
  -- A callback's leading parameters are the ones its body was walked
  -- at, followed by the further parameters the context offers.
  let same := a.arguments.take qs.length == qs
  let (rows, restOffers) := if walkedAtSig && !same then
    -- The body was walked at its own written leading parameters; the
    -- further actuals are discarded (semantic.ml:358). This row keeps
    -- that domain when a callback's result enlarges a binder's candidate.
    ([{ a with arguments := qs ++ a.arguments.drop qs.length }], []) else (rows, restOffers)
  return [← StateT.lift (lower (SourceTypes.use (.arrs rows restOffers)))]

/-- Definite non-reading uses from Source.reads_only (source.ml:1453-1482):
an alias or a mutating member prevents a required-position result contract.
Other uses leave the existing proposal unchanged. -/
partial def generalArrayUse (name : String) : Stmt → Bool
  | .constants _ bs | .mutables _ bs => bs.any fun b => match b.init with
    | .var _ n => n == name
    | _ => false
  | .effect _ (.invoke _ (.read _ (.str m) (.var _ n)) _ _ _) =>
    n == name && !["map", "filter", "every", "some", "forEach", "join", "slice", "at", "indexOf",
      "lastIndexOf", "includes", "find", "findIndex", "flatMap", "reduce", "reduceRight", "entries", "keys", "values"].contains m
  | .effect _ (.write _ _ (.var _ n) _) | .effect _ (.indexWrite _ _ (.var _ n) _ _) => n == name
  | .ite _ _ a b => (a ++ b.getD []).any (generalArrayUse name)
  | .loop _ _ b u _ => (b ++ u).any (generalArrayUse name)
  | .block _ _ b | .forOf _ _ _ _ _ b => b.any (generalArrayUse name)
  | .tryStmt _ b h f => (b ++ (h.map (·.2)).getD [] ++ f.getD []).any (generalArrayUse name)
  | .closing _ c b => (c ++ b).any (generalArrayUse name)
  | _ => false

/-- The producer's matching overloads without required result positions,
where one exists (expression_calls.ml:1079-1087), before the fresh call. -/
def generalArrayCallee (c : Callee) (As : List (Option (Ty Tree))) : Compiler Callee := do
  if !c.binders.isEmpty then return c
  let T ← table
  let G := SourceTypes.graph T
  let required (a : CallEffects.Arrow (Ty Tree)) : Bool :=
    match (storeOf G a.result).map (PositiveRules.expand G) with
    | some [.list t []] => !t.required.isEmpty
    | _ => false
  let matching := c.fixed.filter fun a =>
    As.length ≤ a.arguments.length &&
    (a.arguments.drop As.length).all (fun D => within T [Labels.undef] D) &&
    (As.zip a.arguments).all (fun (A, P) => A.any fun A => within T A P)
  let general := matching.filter (!required ·)
  return if general.isEmpty then c else { c with fixed := general }

/-- Guard values prefer parameters stating their promise among otherwise
matching overloads (expression_calls.ml:1032-1050). -/
def promisesOfActuals (G : PositiveGraphs.NormalGraph Tree)
    (As : List (Option (Ty Tree))) (a : CallEffects.Arrow (Ty Tree)) : Bool :=
  (As.zip a.arguments).all fun (A, P) =>
    let rows := A.toList.flatMap fun A =>
      (ProgramTyping.callSigs G A).map (·.effect.promise) ++
      (ProgramTyping.restSigs G A).map (·.effect.promise)
    match rows.find? (·.isSome) with
    | some own =>
      let wanted := ProgramTyping.callSigs G P
      !wanted.isEmpty && wanted.all (·.effect.promise == own)
    | none => true

/-- Direct primitive candidates follow inference.ml:608-630: widen an
unbounded binder unless returned bare, within all actual and result bounds.
Explicit seeds, dependent bounds and callback-only candidates stay fixed. -/
def widenActualBinders (c : Callee) (a : CallEffects.Arrow (Ty Tree))
    (As : List (Option (Ty Tree))) (hidden : List Tree) (hint : Option (Ty Tree))
    (initial : List (Tree × Ty Tree))
    (scope : Option (PositiveGraphs.SchemeRow Tree × List String)) : Compiler (List (Tree × Ty Tree)) := do
  let mut σ := initial
  let G ← graphNow
  for b in c.binders do
    if !c.widenBinders.contains b || (c.seed.lookup b).isSome || (c.bounds.lookup b).any (fun B => PositiveRules.expand G B != [.source]) || hidden.contains b ||
        c.bounds.any (fun (_, B) => B.any (occurs b)) || a.result.contains b then continue
    let some B := σ.lookup b | continue
    let direct := (a.arguments.zip As).filterMap fun (P, A) =>
      if isBinder b P then A else none
    if direct.isEmpty || norm direct.flatten != norm B then continue
    let B' ← widen B
    if B' == B then continue
    let proposed := upd σ b B'
    let T ← table
    -- A stable input's observation and resolution result constrain its
    -- widening too (inference.ml:220-229,248-250,620-628). Compare the
    -- candidate's resolved result to the context before fresh allocation.
    let mut resolved := proposed
    let mut resolvedOk := true
    if hint.isSome then
      for group in c.resolution do
        if c.binders[group.input]? != some b then continue
        let trial : Except String (Option (Ty Tree) × Option (Ty Tree)) := do
          let cert ← SourceClaimJson.Scheme.resolutionCertificate T (scope.map (·.1))
            ((scope.map (·.2)).getD []) B' group.result.isSome
          SourceClaimJson.Scheme.resolutionInstance T (scope.map (·.1))
            ((scope.map (·.2)).getD []) B' cert
        match trial with
        | .error _ => resolvedOk := false
        | .ok (O, R) =>
          if let some o := c.binders[group.observation]? then
            resolved := upd resolved o (O.getD [])
          if let (some slot, some R) := (group.result, R) then
            if let some r := c.binders[slot]? then resolved := upd resolved r R
    if resolvedOk && (As.zip a.arguments).all (fun (A, P) => A.all fun A => within T A (substitute proposed P)) && hint.all (fun H => within T (substitute resolved a.result) H) then
      σ := proposed
  return σ


set_option maxHeartbeats 250000 in
mutual
/-- An expression's type, recorded at its occurrence, and the environment
after it; where a type `exp` is expected of its value (a return's, an
annotated declaration's, an assignment's, a field's, a parameter's), a
literal, a function literal or a fresh store made at it (`fit`), and each
part of it walked at the part's expected type. -/
partial def expr (env : Env) (e : Expr) (exp : Option (Ty Tree) := none) : W (Option (Ty Tree) × Env) := do
  let before := (← get).pathEnds.length
  -- An expected type naming a hole guides an array literal, a call's
  -- callback and a function literal's result alone; any other expression
  -- is at no expected type (expression_typing.ml:35-41).
  let holes := (← get).holes
  let exp := exp.filter fun P => holeGuided e || !holes.any fun h => P.any (occurs h)
  let r ← exprAt env e exp
  let w ← get
  let written := match e with
    | .assign _ n _ rhs | .nullishAssign _ n _ rhs => [(n, false, rhs)]
    | .indexWrite _ _ (.var _ n) _ rhs | .elemWrite _ (.var _ n) _ rhs => [(n, true, rhs)]
    | .invoke _ (.read _ (.str method) (.var _ n)) args [] _ =>
      if method == "push" || method == "unshift" then args.map (n, true, ·) else []
    | _ => []
  for (n, element, rhs) in written do
    if let some (key, isArray) := w.evolving.lookup n then
      if !element || isArray then
        let mut A := (w.exprs.get? rhs.span).bind (·.2.toOption)
        -- A self-reading assignment is measured for every value its cell
        -- can hold (expression_properties.ml:156-164); speculation publishes
        -- no expression or flow claim.
        if !element && rhs.freeNames.contains n then
          let saved ← get
          let reset := { env with vars := env.vars.map fun (m, B) =>
            (m, if m == n || !(w.slots.get.contains m || w.literalSlots.contains m) then (env.decl.lookup m).getD B else B), paths := [] }
          let (B, _) ← expr reset rhs
          set saved
          A := B <|> A
        if let some B := A then
          let B ← if isArray && !element then
              StateT.lift (tryCatch (elementAt B none (missing := false)) fun _ => pure [])
            else pure B
          let B ← StateT.lift (widen B)
          modify fun w => { w with evolvedWrites := upd w.evolvedWrites key (norm ((w.evolvedWrites.lookup key).getD [] ++ B)) }
  modify fun w => { w with endsIn := w.endsIn.insert e.span (w.pathEnds.length != before || (w.endsIn.get? e.span).getD false) }
  -- An unreached expression whose type the walk does not determine (each
  -- binding there at the empty type, a constructor's included): at the
  -- empty type, as the producer's `unreachable` states its bindings; the
  -- pass decides the node by its unsatisfiable context.
  if env.ghost && r.1.isNone then
    if let some (k, .error m) := (← get).exprs.get? e.span then
      if !m.startsWith refusalMark then
        modify fun w => { w with exprs := w.exprs.insert e.span (k, .ok []), exprsAt := w.exprsAt.insert (w.stmtAt, e.span) (.ok []) }
        return (some [], r.2)
  return r

/-- `expr` but the record of whether the walk ended a path. -/
partial def exprAt (env : Env) (e : Expr) (exp : Option (Ty Tree) := none) : W (Option (Ty Tree) × Env) := do
  let forceElements := (← get).force.contains "elements"
  let forceSpreads := (← get).force.contains "spreads"
  let forceKeys := (← get).force.contains "keys"
  let forceIndexes := (← get).force.contains "copy-indexes"
  match e with
  | .var _ n =>
    let r := match env.vars.lookup n with
      | some A => .ok A
      | none => .error s!"'{n}' is bound outside what the walk sees"
    if let some P := exp then
      offerUse n P
      offerClass n P
    return (← record e r, env)
  | .lit _ v => return (← attempt e (literal v), env)
  | .logical _ andOp l r =>
    let (L, e1) ← expr env l
    let (R, e2) ← expr (← refine e1 l andOp) r exp
    let A ← attempt e do
      let L ← need L "the left operand"
      let R ← need R "the right operand"
      -- `a && b`: `a`'s falsy part or `b`; `a || b`: `a`'s truthy part or `b`.
      joinTy (← slice L .truthy !andOp) R
    return (A, (join (some (← refine e1 l !andOp)) (some e2)).getD e2)
  | .coalesce _ l r =>
    let (L, e1) ← expr env l
    let expected ← match exp, L with
      | none, some L => StateT.lift (tryCatch (some <$> nonNullish L) fun _ => pure none)
      | _, _ => pure exp
    let (R, e2) ← expr e1 r expected
    -- `a ?? b`: `a` less null and undefined, or `b`.
    -- (`TSCERT_FORCE=meets`: each type parameter's value dropped there)
    let meets := (← get).force.contains "meets"
    let A ← attempt e do
      let L ← need L "the left operand"
      let G ← graphNow
      let P ← if L.any (fun l => PositiveRules.expand G [l] == [.source]) then pure L else nonNullish L
      let T ← table
      let P := if meets then P.filter fun a => !(StoreView.row T a matches .meet ..) else P
      joinTy P (← need R "the right operand")
    return (A, (join (some e1) (some e2)).getD e2)
  | .optional _ _ recv body =>
    let (O, e1) ← expr env recv
    let some O := O | do
      let _ ← expr e1 body
      return (← record e (.error "the chain's receiver undetermined"), e1)
    let present ← StateT.lift (nonNullish O)
    let inner := { e1 with vars := upd e1.vars chainName present, ghost := e1.ghost || present.isEmpty }
    let (B, e2) ← expr inner body exp
    let B ← if (← get).force.contains "chains" && !present.isEmpty then record body (.ok [Labels.tru]) else pure B
    let A ← attempt e do
      let B ← need B "the chain's body"
      let nullish := !(← slice O .isNullish true).isEmpty
      return norm (B ++ (if nullish then [Labels.undef] else []))
    let canSkip := !(← StateT.lift (slice O .isNullish true)).isEmpty
    let after := if present.isEmpty then e1 else if canSkip then (join (some e1) (some e2)).getD e1 else e2
    return (A, { after with vars := match e1.vars.lookup chainName with
      | some C => upd after.vars chainName C
      | none => after.vars.filter (·.1 != chainName) })
  | .withObject _ _ obj body =>
    let (O, e1) ← expr env obj
    let inner := match O with
      | some O => { e1 with vars := upd e1.vars objectName O }
      | none => e1
    let (B, e2) ← expr inner body
    return (← record e (match B with | some B => .ok B | none => .error "the body undetermined"),
      { e2 with vars := e2.vars.filter (·.1 != objectName) })
  | .shapeTest _ _ _ x | .tagMember _ _ _ _ _ x | .not _ x =>
    let (_, e1) ← expr env x
    return (← record e (.ok boolTy), e1)
  | .equality _ _ l r | .singletonTest _ _ _ _ l r | .inKeys _ l r =>
    let (_, e1) ← expr env l
    let (_, e2) ← expr e1 r
    return (← record e (.ok boolTy), e2)
  | .cast _ annot x =>
    -- `x as T`: the operand made at `T`.
    let target ← match annot with
      | some ty => StateT.lift (tryCatch (some <$> lower (Fragment.translate ty)) fun _ => pure none)
      | none => pure none
    let (A, e1) ← expr env x target
    let r ← attempt e do
      match annot with
      | some ty => lower (Fragment.translate ty)
      -- `e!` (or `as const`): the operand less null and undefined.
      | none => nonNullish (← need A "the operand")
    -- `f(…)!` and `xs[i]!`: the call or the read proposed at the operand
    -- less null and undefined, which its own step proves where the facts
    -- select a signature giving it (`SinglePass.directCall`'s order).
    if annot.isNone then
      match x, r with
      | .call .., some B | .invoke .., some B | .elemAt .., some B => let _ ← record x (.ok B)
      | _, _ => pure ()
    -- `[…] as const`: the readonly tuple of its elements' own types.
    let r ← match annot, x with
      | none, .arrayLit _ es [] => do
        let w ← get
        match es.mapM (fun y => (w.exprs.get? y.span).bind (·.2.toOption)) with
        | some Es => do
          let r ← attempt e (lower do
            let s ← SourceTypes.use (.list ⟨Es, [], none, true, .dense⟩ [])
            let T ← get
            return [← SourceTypes.use (SourceTypes.arrayOf T s true)])
          -- The operand is made at its const type.
          if let some C := r then let _ ← record x (.ok C)
          pure r
        | none => pure r
      -- `{…} as const`: the record of its fields' own types, made so.
      | none, .alloc _ names es => do
        let w ← get
        match es.mapM (fun y => (w.exprs.get? y.span).bind (·.2.toOption)) with
        | some Es => do
          let r ← attempt e (prim (.refs (names.zip Es) [] [] [] [] [⟨true, names⟩] []))
          if let some C := r then let _ ← record x (.ok C)
          pure r
        | none => pure r
      | _, _ => pure r
    return (r, e1)
  | .alloc _ names es =>
    -- Only a uniquely selected record gives its fields' context.
    let exp ← match exp with
      | some P => StateT.lift (recordContext P names es)
      | none => pure none
    let mut e1 := env
    let mut As : List (Option (Ty Tree)) := []
    for (k, y) in names.zip es do
      let D ← match exp with
        | some P => StateT.lift (fieldExpected P k)
        | none => pure none
      let (A, e') ← expr e1 y D
      -- An ordinary nested allocation without a field context is made at
      -- its own open record (expression_objects.ml:46-54, 83-97). Only the
      -- fresh child is retyped: an existing value's store is unchanged.
      let A ← match D, y, A with
        | none, .alloc _ ks _, some A => do
          if ks.contains SourceTypes.protoField || (← get).exactAt.contains y.span then pure (some A) else do
          let G ← StateT.lift graphNow
          match PositiveRules.expand G A with
          | [.refs fs [] vs os ms _ st] =>
            let B ← StateT.lift (prim (.refs fs [] vs os ms [] st))
            record y (.ok B)
          | _ => pure (some A)
        | _, _, _ => pure A
      As := As ++ [A]
      e1 := e'
    let r ← attempt e do
      -- A literal's type widens in a mutable field, as TypeScript's fresh
      -- literal types do; a name's or a read's type does not, nor a const
      -- assertion's (the producer's `fresh`, expression_objects.ml:49-54;
      -- a literal's cast of no annotation is its `as const`).
      let fresh (y : Expr) : Bool := match y with
        | .var .. | .read .. | .cast _ none (.alloc ..) | .cast _ none (.arrayLit ..) | .cast _ none (.lit ..) => false
        | _ => true
      let fields ← (names.zip (As.zip es)).mapM fun (n, A, y) => do
        let A ← need A "a field"
        return (n, ← if fresh y then widen A else pure A)
      -- Its own keys exactly (`HasTyUsing.alloc`'s bound).
      prim (.refs fields [] [] [] [] [⟨true, names⟩] [])
    let r ← match exp with
      | some P => fit P e r
      | none => pure r
    return (r, e1)
  | .build _ names es =>
    let spreadExp ← match exp with
      | some P => StateT.lift (spreadContext P)
      | none => pure none
    -- An object literal with spreads: each spread's record fields, then each
    -- named field, a later key replacing an earlier one; each named field
    -- walked at the field the expected type states at its key.
    let mut e1 := env
    let mut As : List (Option (Ty Tree)) := []
    for (k, y) in names.zip es do
      let D ← match exp, k with
        | some P, some k => StateT.lift (fieldExpected P (.str k))
        | some P, none => pure (if copyLiteral y then spreadExp else some P)
        | _, _ => pure none
      let (A, e') ← expr e1 y D
      As := As ++ [A]
      e1 := e'
    -- Each copy the parts give, a named field at its value's widened type
    -- (`object_spread.ml`).
    let r ← attempt e do
      let mut parts : List (Option PropKey × Ty Tree) := []
      for (k, A) in names.zip As do
        let A ← need A "a part"
        match k with
        | some k => parts := parts ++ [(some (.str k), ← widen A)]
        | none => parts := parts ++ [(none, A)]
      let alts ← copyParts [{}] parts forceSpreads
      let alts := if forceIndexes then alts.map fun c => { c with numeric := c.numeric.map fun _ => [Labels.tru] } else alts
      return norm (← alts.mapM copyType).flatten
    let r ← match exp with
      | some P => fit P e r
      | none => pure r
    return (r, e1)
  | .read _ fld x =>
    let (O, e1) ← expr env x
    -- A read off a generic module value's name (a generic class's static
    -- field) reads the value at an instance, each binder at its bound,
    -- recorded as a call's (the producer's, `Fragment.Expr.callees`); a
    -- binder of a bound is not handled here.
    let O ← match x with
      | .var _ n => match (← get).generics.lookup n with
        | some g =>
          if !g.resolution.isEmpty then pure O else do
          let r ← StateT.lift (tryCatch (do
              let U ← lower (SourceTypes.use .source)
              let θ0 := g.binders.map (·, graphJson [U])
              let B0 ← lower (g.bounds θ0)
              let θ := g.binders.map fun n => (n, ((B0.lookup n).join).getD (graphJson [U]))
              -- (a bound reading another binder: not handled)
              if (← lower (g.bounds θ)) != B0 then throw "a static read of a binder whose bound reads another"
              let inst ← lower (do Fragment.translate (← g.instantiate θ))
              let θt ← θ.mapM fun (n, j) => do return (n, ← lower (Fragment.translate j))
              return Except.ok (inst, θt)) fun m => pure (.error m))
          match r with
          | .ok (inst, θ) =>
            modify fun w => { w with instances := (e.span, θ) :: w.instances, resolutions := (e.span, []) :: w.resolutions }
            record x (.ok inst)
          | .error m => record x (.error m)
        | none => pure O
      | _ => pure O
    let narrowed := (memberPath e).bind fun p => e1.paths.lookup p
    if let (some p, some _) := (memberPath e, narrowed) then modify fun w => { w with readPaths := w.readPaths.insert p }
    let r ← attempt e do
      if let some P := narrowed then return P
      readField e1.vars (← need O "the receiver") fld
    -- A completed read narrows its receiver held in a slot: past it, not
    -- `null` or `undefined` (`readNarrowing`, Atoms.lean:93-104).
    let e1 ← match x, O, r with
      | .var _ n, some O, some _ => do
        let G ← StateT.lift graphNow
        if (← get).force.contains "reads" then
          modify fun w => { w with readForced := n :: w.readForced }
          pure { e1 with vars := upd e1.vars n (present G O) }
        else if (nullishSplit G O).isSome && !(← get).inLiteral && (env.vars.lookup n).isSome &&
            (← get).slots.get.contains n then
          pure { e1 with vars := upd e1.vars n (present G O) }
        else pure e1
      | _, _, _ => pure e1
    return (r, e1)
  | .write _ fld recv rhs =>
    wrote .any (if fld == lengthKey then .any else .keep)
    let (O, e1) ← expr env recv
    -- The reference `recv.fld`, as the read gives it.
    let mut D : Option (Ty Tree) := none
    if let .str f := fld then
      let r ← StateT.lift (tryCatch (do
          return Except.ok (← readField e1.vars (← need O "the receiver") fld)) fun m => pure (.error m))
      recordAt (recv.span.1, recv.span.2 + 1 + f.length) "member read" r
      D := r.toOption
    -- The value made at the field's type.
    let (R, e2) ← expr e1 rhs D
    -- A write ends the narrowing of every path through the field.
    ends (.field fld)
    let e2 := { e2 with paths := e2.paths.filter fun ((_, p), _) => !p.contains fld }
    -- A key a constant's records may lack: the write at the contract it adds
    -- the key at, and the constant's records owning it after.
    if let (.var _ n, some O, some R) := (recv, O, R) then
      if (← get).consts.contains n then
        let literal_ := match rhs with | .var .. | .read .. => false | _ => true
        let value := if (← get).force.contains "growth" then [Labels.tru] else exp.getD R
        if let some (c, grown) ← StateT.lift (tryCatch (growth O fld value (literal_ && exp.isNone)) fun _ => pure none) then
          return (← record e (.ok c), growHolders e2 (← get) n grown)
    -- A write of a field of an immutable binding's object that adds no key:
    -- the field then holds its contract less the nullish values the value
    -- written does not admit (the producer's `written_field`,
    -- statement_analysis.ml:168-172, 419), its path so narrowed.
    let w ← get
    let e2 ← match memberPath (.read e.span fld recv), R, D with
      | some (root, path), some R, some F =>
        let G ← StateT.lift graphNow
        -- (a field every record arm of the receiver states: a write of
        -- any other key adds it, the producer's `adds`)
        let stated := match O with
          | some O => !O.isEmpty && O.all fun l => match PositiveRules.expand G [l] with
            | [.refs fs _ _ _ _ _ _] => (fs.lookup fld).isSome
            | _ => false
          | none => false
        if stated && (w.consts.contains root || w.values.contains root) then
          let nullish (A : Ty Tree) := !(BranchRefinement.tagSlice G A .isNullish true).isEmpty
          -- (`unknown` excepted: its slice is no contract the write states)
          let open_ := F.any fun l => G.plain l && PositiveRules.expand G [l] == [.source]
          if !R.isEmpty && !open_ && nullish F then
            StateT.lift (narrowPath e2 root path fun _ => do
              let F ← if (w.force.contains "field-writes" || (BranchRefinement.tagSlice G R .isNul true).isEmpty) then slice F .isNul false else pure F
              if (w.force.contains "field-writes" || (BranchRefinement.tagSlice G R .isUndef true).isEmpty) then slice F .isUndef false else pure F)
          else pure e2
        else pure e2
      | _, _, _ => pure e2
    return (← record e (match R with | some R => .ok R | none => .error "the value undetermined"), e2)
  | .index _ field x key =>
    let (O, e1) ← expr env x
    let (K, e2) ← expr e1 key
    let r ← attempt e do
      let O ← need O "the receiver"
      let K ← need K "the key"
      match field with
      | some f => readField e2.vars O (.str f)
      | none => match ← keyString K with
        | some s => readField e2.vars O (.str s)
        | none => keyedRead e2.vars O K (missing := !forceElements) (firstOnly := forceKeys)
    return (r, e2)
  | .elemWrite p recv key rhs => expr env (.indexWrite p none recv key rhs)
  | .indexWrite _ field recv key rhs =>
    -- An element write changes values and grows stores (`writeWithinAt`).
    wrote .any .grow
    let (O, e1) ← expr env recv
    let (K, e2) ← expr e1 key
    -- The reference `recv[key]`, read where the write's target is read: the
    -- contents there, as the read gives them.
    let r ← StateT.lift (tryCatch (do
        let O ← need O "the receiver"
        let K ← need K "the key"
        let B ← match field with
          | some f => readField e2.vars O (.str f)
          | none => match ← keyString K with
            | some s => readField e2.vars O (.str s)
            | none => elementAt O (← keyIndex K)
        return Except.ok B) fun m => pure (.error m))
    recordAt (recv.span.1, key.span.2 + 1) "member read" r
    -- The value made at the contents' type.
    let D ← match r with
      | .ok B => some <$> StateT.lift (slice B .isUndef false)
      | .error _ => pure none
    let (R, e3) ← expr e2 rhs D
    -- The write ends the paths through its key: a named one's, a number's
    -- none (an element, no path's field), any other every path.
    let ended ← StateT.lift (tryCatch (do
        match field with
        | some f => return some (PathEnd.field (.str f))
        | none =>
          let K ← need K "the key"
          match ← keyString K with
          | some s => return some (.field (.str s))
          | none => return if (← slice K .isNum false).isEmpty then none else some .all) fun _ => pure (some .all))
    let e3 ← match ended with
      | some x => do
        ends x
        pure { e3 with paths := surviving e3 [x] }
      | none => pure e3
    if let (.var _ n, some O, some K, some R) := (recv, O, K, R) then
      if (← get).consts.contains n then
        let names ← StateT.lift (keyNames K)
        if let some names := names then
          let literal_ := match rhs with | .var .. | .read .. => false | _ => true
          let mut grown : Ty Tree := []
          let mut contract : Option (Ty Tree) := none
          for k in names do
            if let some (C, B) ← StateT.lift (tryCatch (growth O k R literal_) fun _ => pure none) then
              contract := some C
              grown := grown ++ B
            else grown := grown ++ O
          if let some C := contract then
            return (← record e (.ok C), growHolders e3 (← get) n (norm grown))
    return (← record e (match R with | some R => .ok R | none => .error "the value undetermined"), e3)
  | .elemAt _ x key =>
    let (O, e1) ← expr env x
    let (K, e2) ← expr e1 key
    let r ← attempt e do keyedRead e2.vars (← need O "the receiver") (← need K "the key") (missing := !forceElements) (firstOnly := forceKeys)
    return (r, e2)
  | .arrayLit _ es spreads =>
    -- Each element walked at the position the expected type states.
    let mut e1 := env
    let mut As : List (Option (Ty Tree)) := []
    for (y, i) in es.zipIdx do
      let D ← match exp with
        | some P => StateT.lift do
          let D ← positionExpected P i
          if !spreads.contains i then return D
          -- A spread's operand is expected at the readonly array of the
          -- destination's element (expression_objects.ml:276-278).
          match D with
          | none => return none
          | some E => some <$> lower do
            let store ← SourceTypes.use (.list ⟨[], [], some E, true, .readable⟩ [])
            let T ← get
            return [← SourceTypes.use (SourceTypes.arrayOf T store true)]
        | none => pure none
      let (A, e') ← expr e1 y D
      As := As ++ [A]
      e1 := e'
    let r ← attempt e do
      let mut elems : Ty Tree := []
      for (A, i) in As.zipIdx do
        let A ← need A "an element"
        let B ← if spreads.contains i then elementAt A none (missing := false) else widen A
        elems := elems ++ B
      let elems' := norm elems
      -- Made where no type is expected: holes read as `undefined` where its
      -- elements admit it (the presence a mutable array's contract states).
      lower do
        let s ← SourceTypes.use (.list ⟨[], [], some elems', false, .readable⟩ [])
        let T ← get
        return [← SourceTypes.use (SourceTypes.arrayOf T s false)]
    let r ← match exp with
      | some P => fit P e r
      | none => pure r
    return (r, e1)
  | .arrayAssign _ targets rest rhs =>
    wrote
    -- A literal assigned to a pattern is made at its targets' contracts,
    -- defaults admitting undefined and the rest supplying the remaining
    -- positions (expression_values.ml:250-269).
    let targetType (target : Expr) : Compiler (Option (Ty Tree)) := do
      match target.targetLocal, target with
      | some n, _ => return env.decl.lookup n
      | none, .read _ f (.var _ o) =>
        let some O := env.vars.lookup o | return none
        tryCatch (some <$> readField env.vars O f) fun _ => pure none
      | none, _ => return none
    let restType ← match rest with
      | some (_, _, t) => StateT.lift (targetType t.target)
      | none => pure none
    let tuple ← match rhs with
      | .arrayLit _ es [] => StateT.lift (tryCatch (do
          let mut Ds : List (Ty Tree) := []
          for t in targets do
            let some D ← targetType t.target | return none
            Ds := Ds ++ [if t.default_.isSome then norm (D ++ [Labels.undef]) else D]
          if targets.length > es.length then return none
          if rest.isNone && targets.length != es.length then return none
          for i in List.range (es.length - targets.length) do
            let some D := restType | return none
            Ds := Ds ++ [← elementAt D (some i) (missing := false)]
          some <$> lower do
            let s ← SourceTypes.use (.list ⟨Ds, [], none, false, .dense⟩ [])
            let T ← get
            return [← SourceTypes.use (SourceTypes.arrayOf T s false)]) fun _ => pure none)
      | _ => pure none
    let (R, e1) ← expr env rhs tuple
    -- The rest after the targets: as a pattern's (`restOf`), its slice's
    -- call instantiated at the value.
    if let some (rp, slice, _) := rest then
      let A ← restOf e1 R targets.length rp slice
      if !slice && A.isSome then
        if let some D := restType then
          let G ← StateT.lift graphNow
          if (storeOf G D).isSome then recordAt rp "other" (.ok D)
    let names := targets.filterMap (·.target.targetLocal) ++ (rest.bind fun r => r.2.2.target.targetLocal).toList
    -- Each name the pattern assigns at its declared type, and no path
    -- through it narrowed, from the first target's assignment on (a later
    -- default may read an earlier target).
    let reset (env : Env) : Env := { env with
      vars := env.vars.map fun (n, A) => if names.contains n then (n, (env.decl.lookup n).getD A) else (n, A)
      paths := env.paths.filter fun ((r, _), _) => !names.contains r }
    for n in names do ends (.root n)
    let mut env := reset e1
    for t in targets do
      let (_, e') ← expr env t.target
      env := e'
      if let some d := t.default_ then env := (← expr env d).2
    if let some (_, _, t) := rest then
      env := (← expr env t.target).2
    env := reset env
    return (← record e (match R with | some R => .ok R | none => .error "the value undetermined"), env)
  | .arith _ op l r =>
    let (L, e1) ← expr env l
    let (R, e2) ← expr e1 r
    let A ← attempt e do arithType op (← need L "the left operand") (← need R "the right operand")
    return (A, e2)
  | .comma _ l r =>
    let (_, e1) ← expr env l
    let (R, e2) ← expr e1 r exp
    return (← record e (match R with | some R => .ok R | none => .error "the right operand undetermined"), e2)
  | .unary _ op x =>
    let (A, e1) ← expr env x
    let r ← attempt e do
      match op with
      | .typeof => prim .str
      | .plus => prim .num
      | .neg | .bitNot =>
        let A ← need A "the operand"
        let G ← graphNow
        if !A.isEmpty && A.all (shapeOf G · == some .isBigint) then prim .bigint else prim .num
    return (r, e1)
  | .update _ op target rhs _ =>
    match target with
    | .var _ n => assigns n
    -- For a declaration's footprint, the target's grade (`targetWrite`);
    -- else source.ml:1086-1087: only a numeric literal index has the
    -- producer's compound element-write footprint.
    | t =>
      if (← get).strict then targetWrite t else
      match t with
      | .index _ _ _ (.lit _ (.vnum _)) => wrote .any .grow
      | _ => wrote
    let (L, e1) ← expr env target
    let (R, e2) ← match rhs with
      | some r => do let (R, e2) ← expr e1 r; pure (R, e2)
      | none => pure (some [], e1)
    let r ← attempt e do
      let L ← need L "the target"
      let R ← need R "the right operand"
      arithType op L (if rhs.isSome then R else L)
    let e3 ← match target, r with
      | .var _ n, some A => do
        let D := (e2.decl.lookup n).getD A
        pure { e2 with vars := upd e2.vars n (← StateT.lift (assigned D A)), paths := e2.paths.filter (·.1.1 != n) }
      -- A field's update ends the paths through the field.
      | .read _ fld _, _ => do
        ends (.field fld)
        pure { e2 with paths := surviving e2 [.field fld] }
      | _, _ => pure e2
    return (r, e3)
  | .logicalAssign _ op target rhs =>
    match target with
    | .var _ n => assigns n
    | t =>
      if (← get).strict then targetWrite t else
      match t with
      | .read _ fld recv =>
        let O := (memberPath recv).bind fun (n, path) =>
          if path.isEmpty then env.vars.lookup n else env.paths.lookup (n, path)
        let G ← StateT.lift graphNow
        wrote .any (if O.any (fun O => ExpressionEffects.sourceField G (PositiveRules.expand G O) fld) then .keep else .any)
      | _ => wrote
    let (L, e1) ← expr env target
    let D := match target with
      | .var _ n => env.decl.lookup n
      | _ => none
    let (R, e2) ← expr e1 rhs D
    let r ← attempt e do
      let L ← need L "the target"
      let R ← need R "the right operand"
      let kept ← match op with
        | .nullish => nonNullish L
        | .orElse => slice L .truthy true
        | .andAlso => slice L .truthy false
      joinTy kept R
    -- The right operand runs on one path only: the bindings after it joined
    -- with those before it.
    let e2 := (join (some e1) (some e2)).getD e2
    let e3 ← match target, r with
      | .var _ n, some A => pure { e2 with vars := upd e2.vars n A, paths := e2.paths.filter (·.1.1 != n) }
      | .read _ fld _, r => do
        ends (.field fld)
        let e3 := { e2 with paths := surviving e2 [.field fld] }
        -- The field holds the assignment's value after it: its path so
        -- narrowed.
        match memberPath target, r with
        | some (root, path), some A => StateT.lift (narrowPath e3 root path fun _ => pure A)
        | _, _ => pure e3
      | _, _ => pure e2
    return (r, e3)
  | .nullishAssign _ n namePos rhs =>
    -- `x ??= v` of a binding held in a cell whose `v` changes nothing
    -- initializes the cell: it writes it only where it holds `null` or
    -- `undefined` (the producer's `NullishAssign`, source.ml:1076-1083,
    -- Lean's initializing write); else it changes the values.
    let initializing := !(← get).locals.contains n
    assigns n (if initializing then .init else .any)
    let before := (← get).writes
    if initializing then modify fun w => { w with writes := false }
    recordAt namePos "identifier" (match env.vars.lookup n with
      | some A => .ok A
      | none => .error s!"'{n}' is bound outside what the walk sees")
    let D ← match env.decl.lookup n with
      | some D => some <$> StateT.lift (nonNullish D)
      | none => pure none
    if let some D := D then modify fun w => { w with hints := (rhs.span, D) :: w.hints }
    let (R, e1) ← expr env rhs D
    if initializing then
      let changed := (← get).writes
      modify fun w => { w with writes := before || changed }
      if changed then modify fun w => { w with valueChange := w.valueChange.max .any }
    let r ← attempt e do
      let some L := env.vars.lookup n | throw s!"'{n}' is bound outside what the walk sees"
      joinTy (← nonNullish L) (← need R "the right operand")
    -- The right operand runs on one path only.
    let e1 := (join (some env) (some e1)).getD e1
    let e2 := match r with
      | some A => { e1 with vars := upd e1.vars n A, paths := e1.paths.filter (·.1.1 != n) }
      | none => e1
    return (r, e2)
  | .assign _ n _ rhs =>
    assigns n
    if let some D := env.decl.lookup n then modify fun w => { w with hints := (rhs.span, D) :: w.hints }
    let (R, e1) ← expr env rhs (env.decl.lookup n)
    let r ← record e (match R with | some R => .ok R | none => .error "the value undetermined")
    let e2 ← match R with
      | some A => do
        let D := (e1.decl.lookup n).getD A
        -- A slot assigned an object literal holds it at its contract's
        -- members it is within (the producer's `slot_holds`,
        -- type_queries.ml:1133-1140): a store's contract is fixed where it
        -- is made, so the slot is never at the exact type of the store.
        let w ← get
        let fresh := match rhs with | .alloc .. | .build .. => true | _ => false
        let slot := fresh && (w.slots.get.contains n || w.literalSlots.contains n)
        let held ← StateT.lift (if slot then declaredAt D A else assigned D A)
        pure { e1 with vars := upd e1.vars n held, paths := e1.paths.filter (·.1.1 != n) }
      | none => pure (match e1.decl.lookup n with
        | some D => { e1 with vars := upd e1.vars n D, paths := e1.paths.filter (·.1.1 != n) }
        | none => { e1 with vars := e1.vars.filter (·.1 != n) })
    return (r, e2)
  | .withValue _ fn initial functionType bagType =>
    -- `Object.assign(fn, { … })` at its two annotations (the lowering's
    -- `withValue`, Expression.lean:797-843): the function walked at the
    -- function annotation, the literal at the record's, the value the
    -- callable object of the record's fields at the annotation's signatures
    -- (its variadic ones for a function with a rest parameter).
    let F ← StateT.lift (tryCatch (some <$> lower (Fragment.translate functionType)) fun _ => pure none)
    let P ← StateT.lift (tryCatch (some <$> lower (Fragment.translate bagType)) fun _ => pure none)
    let (_, e1) ← expr env fn F
    let (_, e2) ← expr e1 initial P
    let r ← attempt e do
      let F ← need F "the function annotation"
      let P ← need P "the record annotation"
      let G ← graphNow
      let [.arrs L S] := PositiveRules.expand G F | throw "initializer requires a free function annotation"
      let [.refs fs [] []] := PositiveRules.expand G P | throw "initializer requires an invariant record annotation"
      let rest := match fn with
        | .lambda _ _ _ _ _ rest .. => rest
        | _ => false
      if rest && !L.isEmpty then throw "initializer requires a variadic signature"
      return [← lower (SourceTypes.use (if rest then .callable fs [] [] S else .callable fs [] L []))]
    return (r, e2)
  | .objectAssign _ target sources =>
    wrote .any .keep
    let (A, e1) ← expr env target
    let (Ss, e2) ← exprs e1 sources
    let forceCopyBounds := (← get).force.contains "copy-exclusions"
    -- Each source copied over what the target and the sources before it
    -- give, as a spread is (`expression_objects.ml`, `ObjectAssign`): the
    -- object the call returns, the target grown.
    let r ← attempt e do
      let start ← copiesOf (← need A "the target") forceSpreads (target := true)
      let alts ← copyParts start (← Ss.mapM fun S => do return (none, ← need S "a source")) forceSpreads
      let alts := if forceIndexes then alts.map fun c => { c with numeric := c.numeric.map fun _ => [Labels.tru] } else alts
      -- Force absence of written own keys; the copy rule must refuse it.
      let alts := if forceCopyBounds then alts.map fun c =>
        { c with excluded := c.excluded ++ c.fields.map (·.1) } else alts
      return norm (← alts.mapM copyType).flatten
    -- It writes the target's keys: every path ends.
    ends .all
    return (r, { e2 with paths := [] })
  -- A function literal where a callable is expected, writing no parameter's
  -- type: at the expected signature taking the most parameters.
  | .lambda _ _ _ params .. =>
    let G ← StateT.lift graphNow
    let sig := if params.all (·.2 == Json.null) then exp.bind (widestOf G) else none
    return (← walkLambda env e sig (ctx := exp), env)
  | .ctor _ lam statics =>
    -- A class value: its constructor's written parameters, its instance its
    -- written result, its static fields at their initializers' widened
    -- types (the construct rule's `ctors` clause). A class whose code is
    -- its fresh constructor bound earlier (`.var`) takes that one's
    -- signatures.
    -- A fresh constructor (a class binding `C.[[class]]`) gives, first, the
    -- instance its body allocates (`expression_closures.ml`, `fresh_sig`).
    let fresh := (← get).freshClass
    modify fun w => { w with freshClass := false }
    -- A class value whose code is a constructor an earlier class value of
    -- its declaration was walked at: that one's construct signatures, with
    -- the class's static fields (`expression_closures.ml`, `Ctor (Id h)`).
    let earlier := (← get).classes.lookup lam.span
    let allocated ← match lam, earlier with
      | .lambda _ _ _ _ _ _ _ _ _ _ _ body, none => do
        let saved := (← get).exactAt
        if fresh then modify fun w => { w with exactAt := tailAllocs body ++ w.exactAt }
        let _ ← walkLambda env lam none
        modify fun w => { w with exactAt := saved }
        let body := (← get).lastBody
        pure (if fresh then body else none)
      | .lambda .., some _ => pure none
      | _, _ => do let _ ← expr env lam; pure none
    let (Ss, e1) ← exprs env (statics.map (·.2))
    -- A static the class binding's annotation states is at its type there
    -- (a data property agrees both ways), any other at its initializer's.
    let G ← StateT.lift graphNow
    let written := match (← get).hints.lookup e.span with
      | some D => match PositiveRules.expand G D with
        | [.ctors _ _ fs] => fs
        | _ => []
      | none => []
    let offers := ((← get).ctorOffers.filter (·.1 == e.span)).map (·.2)
    let r ← attempt e do
      let fields ← (statics.zip Ss).mapM fun ((k, _), S) => do
        match written.lookup k with
        | some D => return (k, D)
        | none => return (k, ← widen (← need S "a static field"))
      -- The construct signatures its uses offer it, beside its own
      -- (`offer_class`; expression_closures.ml:52-57, 66-68): the pass
      -- checks the constructor's body at each.
      let extra := offers.filterMap fun (c, pack) => if pack.isNone then some c else none
      let extraRests := offers.filterMap fun (c, pack) => pack.map fun pack =>
        (⟨(), (c.arguments, pack), c.result, c.effect⟩ : CallEffects.MethodRestArrow (Ty Tree))
      let ofClass (F : Ty Tree) : Compiler (Ty Tree) := do
        match PositiveRules.expand (← graphNow) F with
        | [.ctors L S ..] => prim (.ctors (L ++ extra.filter (!L.contains ·)) (S ++ extraRests.filter (!S.contains ·)) fields)
        | _ => throw "a class whose constructor is no class value"
      match lam, earlier with
      | _, some F => ofClass F
      | .lambda _ _ _ params _ _ (some inst) _ _ _ _ _, none =>
        let I ← lower (Fragment.translate inst)
        let ps ← params.mapM fun (_, ty) => lower (Fragment.translate ty)
        let allocates := match allocated with
          | some A => if A == I then [] else [A]
          | none => []
        let own : List (CallEffects.MethodArrow (Ty Tree)) := (allocates ++ [I]).map fun R => ⟨(), ps, R, .ordinary⟩
        prim (.ctors (own ++ extra.filter (!own.contains ·)) extraRests fields)
      | .var _ n, none =>
        let some F := env.vars.lookup n | throw s!"'{n}' is bound outside what the walk sees"
        ofClass F
      | _, _ => throw "a class of no written instance"
    if let (.lambda .., none, some C) := (lam, earlier, r) then
      modify fun w => { w with classes := (lam.span, C) :: w.classes }
    return (r, e1)
  | .block _ ss =>
    let _ ← stmts (some env) ss
    -- (but where its span is its expression's, which keeps its own)
    if (← get).exprs.contains e.span then return (none, env)
    return (← record e (.error "a function body"), env)
  | .construct .. | .call .. | .callWithReceiver .. | .applyWithReceiver .. | .bindWithReceiver ..
  | .invoke .. => exprCall env e exp
  | .ifBody _ c t f =>
    let (_, e1) ← expr env c
    let (A, e2) ← expr (← refine e1 c true) t exp
    let (B, e3) ← expr (← refine e1 c false) f exp
    let r ← attempt e do joinTy (← need A "the true arm") (← need B "the false arm")
    return (r, (join (some e2) (some e3)).getD e2)

/-- `exprAt`'s arms of a call: a construction, a call, a call at a receiver,
an `apply`, a `bind` and an invocation. -/
partial def exprCall (env : Env) (e : Expr) (exp : Option (Ty Tree)) : W (Option (Ty Tree) × Env) := do
  match e with
  | .construct _ callee args spreads typeArgs =>
    let (F, e1) ← expr env callee
    let (As, e2) ← actuals e1 args
    -- Spread actuals as the construction reads them (`spreadCall`).
    let gs := (← get).generics
    let generic := match callee with
      | .var _ n => gs.lookup n
      | _ => none
    let mut actualTypes := As
    if F.isNone && generic.isSome then
      -- A packed construction's arguments are typed before its instance;
      -- written callback parameters supply their own types here
      -- (expression_closures.ml:128-134).
      for (x, i) in args.zipIdx do
        if callback x then actualTypes := actualTypes.set i (← walkLambda e2 x none)
    let c ← StateT.lift (tryCatch (do
        let c ← match F, generic with
          | none, some g =>
            -- Ordinary constructors expose their parameters at fresh
            -- binders, as their call signatures do (expression_closures.ml:
            -- 111-143; inference.ml:287-294). A packed constructor
            -- requires the actual tuple before its signature can be read.
            tryCatch (genericCallee g typeArgs) fun m => do
              if !typeArgs.isEmpty then throw m
              let some c ← packedCallee g actualTypes spreads | throw m
              pure c
          | _, _ => constructCallee (← need F "the class") typeArgs
        let (args', As', c) ← spreadCall args actualTypes spreads c
        return Except.ok (args', As', c)) fun m => pure (.error m))
    let (args, As) := match c with
      | .ok (args', As', _) => (args', As')
      | .error _ => (args, As)
    let c := (·.2.2) <$> c
    -- A generic module class's binders, by its scheme's order.
    let c := c.map fun c => match generic with
      | some g => if g.binders.length == c.binders.length then { c with names := g.binders } else c
      | none => c
    modify fun w => { w with lastInstance := none, lastResolution := [] }
    let r ← called e2 c args As e.span exp
    -- A generic class's occurrence is read at its instance, and the call's
    -- type arguments recorded.
    if let (.ok c, .ok (inst, _)) := (c, r) then
      if !c.binders.isEmpty || !c.explicit.isEmpty then let _ ← record callee (.ok inst)
    if let some θ := (← get).lastInstance then
      modify fun w => { w with instances := (e.span, θ) :: w.instances, resolutions := (e.span, w.lastResolution) :: w.resolutions, lastInstance := none, lastResolution := [] }
    return (← record e ((·.2) <$> r), ← afterCall e2 r)
  | .call _ callee args spreads typeArgs =>
    let gs := (← get).generics
    let generic := match callee with
      | .var _ n => gs.lookup n
      | _ => none
    let (F, e1) ← expr env callee
    -- For a declaration's footprint, a call of a local binding is at its
    -- declared type's effect.
    if (← get).strict then
      if let .var _ n := callee then
        if let some D := env.decl.lookup n then
          let G ← StateT.lift graphNow
          -- (graded as the producer grades a call at its callee's
          -- signatures, `callChange`)
          for a in ProgramTyping.callSigs G D do
            callChange a.effect
            if !a.effect.onThrow then modify fun w => { w with throwWrites := true }
    let (As, e2) ← actuals e1 args
    -- Spread actuals as the call reads them (`spreadCall`).
    let c ← StateT.lift (tryCatch (do
        let c ← match generic with
          | some g => tryCatch (genericCallee g typeArgs) fun m => do
              if !typeArgs.isEmpty then throw m
              let some c ← packedCallee g As spreads | throw m
              pure c
          | none => calleeOf (← need F "the callee") [Labels.undef] typeArgs
        return Except.ok (← spreadCall args As spreads c))
      fun m => pure (.error m))
    let (args, As) := match c with
      | .ok (args', As', _) => (args', As')
      | .error _ => (args, As)
    let c := (·.2.2) <$> c
    modify fun w => { w with lastInstance := none, lastResolution := [] }
    let r ← called e2 c args As e.span exp
    -- A generic module function's occurrence, and a scheme-typed local's,
    -- is read at its instance (`Scheme.closureRows`' instances), and a
    -- generic module function's type arguments recorded.
    let schemeLocal ← match callee, F with
      | .var .., some [l] => do pure ((← StateT.lift graphNow).schemes l).isSome
      | _, _ => pure false
    if schemeLocal && generic.isNone then
      if let .ok (inst, _) := r then let _ ← record callee (.ok inst)
    if generic.isSome then
      if let .ok (inst, _) := r then let _ ← record callee (.ok inst)
      if let some θ := (← get).lastInstance then
        modify fun w => { w with instances := (e.span, θ) :: w.instances, resolutions := (e.span, w.lastResolution) :: w.resolutions, lastInstance := none, lastResolution := [] }
    return (← record e ((·.2) <$> r), ← afterCall e2 r)
  | .callWithReceiver _ callee recv args =>
    let (F, e1) ← expr env callee
    let (R, e2) ← expr e1 recv
    let (As, e3) ← actuals e2 args
    let c ← StateT.lift (tryCatch (do
        return Except.ok (← calleeOf (← need F "the callee") (R.getD [Labels.undef]))) fun m => pure (.error m))
    let r ← called e3 c args As e.span exp
    return (← record e ((·.2) <$> r), ← afterCall e3 r)
  | .applyWithReceiver _ callee recv list _ =>
    -- `f.apply(o, list)`, `Reflect.apply(f, o, list)`: the target, the
    -- receiver and the list in order, then the target called with the list's
    -- positions (the lowering's, Atoms.lean:832-918): a tuple of required
    -- positions, else, for a target of one variadic signature taking only a
    -- rest, its store's positions (holes read as `undefined`); a null or
    -- undefined list gives none. The value is the target's one signature's
    -- result (`expression_values.ml`, `Apply`), the call at its effect.
    let (F, e1) ← expr env callee
    let (_, e2) ← expr e1 recv
    let (Lt, e3) ← match list with
      | some l => do let (A, e) ← expr e2 l; pure (A.map some, e)
      | none => pure (some none, e2)
    let r ← StateT.lift (tryCatch (do
        let B ← need F "the target"
        let some Lt := Lt | throw "the list undetermined"
        let G ← graphNow
        let listed := match Lt with
          | none => some false
          | some T => if nullishList G T then some false else
            match storeOf G T with
            | some S => match PositiveRules.expand G S with
              | [.list t []] =>
                if t.optional.isEmpty && t.rest.isNone then some false
                else if t.required.isEmpty && t.optional.isEmpty then some true else none
              | _ => none
            | none => none
        let some dynamic := listed | throw ".apply needs an array list of required positions, or a null or undefined one"
        match PositiveRules.expand G B, dynamic with
        | [.arrs [a] []], false | [.callable _ _ [a] [] _], false => return Except.ok (a.effect, a.result)
        | [.arrs [] [a]], true | [.callable _ _ [] [a] _], true =>
          if !a.arguments.1.isEmpty then throw ".apply with a list of unknown length needs a target taking only a rest parameter"
          return Except.ok (a.effect, a.result)
        | _, _ => throw ".apply requires a single arrow") fun m => pure (.error m))
    modify fun w => { w with changedValues := false }
    let r ← match r with
      | .ok (eff, R) => do
        -- The call changes the heap by its signature's footprint, as a call's
        -- instance does (`applyCall`).
        if eff.footprint != ⟨.keep, .keep⟩ then wrote eff.footprint.value eff.footprint.store
        if eff.footprint.value != .keep || eff.receiverOwn || eff.receiverStore || eff.elementWrite.isSome then
          modify fun w => { w with changedValues := true }
        if eff.receiverOwn then wrote .any eff.footprint.store
        if eff.receiverStore || (eff.elementWrite.isSome && !(← get).strict) then wrote .any .any
        if !eff.onThrow then modify fun w => { w with throwWrites := true }
        if (← get).strict && (← get).caught && !eff.onThrow then wrote .any .any
        -- For a declaration's footprint, a list holding a function may pass it.
        if (← get).strict then
          if let some (some T) := Lt then
            let G ← StateT.lift graphNow
            let E ← StateT.lift (tryCatch (elementAt T none (missing := false)) fun _ => pure [])
            if E.any fun l => !(ProgramTyping.callSigs G [l]).isEmpty then
              wrote .any .any
              modify fun w => { w with throwWrites := true }
        pure (Except.ok R)
      | .error m => do
        if (← get).strict then
          wrote .any .any
          modify fun w => { w with throwWrites := true }
        pure (Except.error m)
    let v ← record e r
    return (v, ← afterCall e3 ((fun R => (R, R)) <$> r))
  | .bindWithReceiver _ callee recv args =>
    -- `o.m.bind(o)`: the method's signatures, its receiver the object
    -- (`bindMember`); with no further actual bound.
    match callee with
    | .read _ fld o =>
      let (O, e1) ← expr env o
      let (_, e2) ← expr e1 recv
      let (_, e3) ← exprs e2 args
      let r ← StateT.lift (tryCatch (do
          if !args.isEmpty then throw "a bound function with bound actuals"
          let O ← need O "the receiver"
          -- (a union of hosts whose members differ: each arm's, `memberArms`)
          if let some M ← unionMember e1.vars O fld then return Except.ok M
          let c ← methodCallee e1.vars O fld
          match c.own with
          | some M => return Except.ok M
          | none => throw "a bound generic method") fun m => pure (.error m))
      let _ ← record callee r
      -- The bound member at any receiver, at the effect binding keeps: of
      -- several signatures (`next(...[value]: [] | [TNext])`) its first of
      -- no promise binding keeps (`Effect.keeps`), with each further one of
      -- its parameters promising
      -- (`expression_values.ml`, `Bind`), which the lowering selects among
      -- the member's (`bindMember`); as the general form below.
      -- `TSCERT_FORCE=binds` states it keeping values and stores, the
      -- adversarial proposal.
      let forced := (← get).force.contains "binds"
      let r ← match r with
        | .ok M => StateT.lift (do
            if let some B ← boundUnion M forced then return Except.ok B
            let G ← graphNow
            let top ← prim .top
            let bound (e : CallEffects.Effect) : CallEffects.Effect :=
              if forced then .ofFootprint ⟨.keep, .keep⟩ else e.drop 0
            match PositiveRules.expand G M with
            | [.arrs L R] =>
              match L.find? (fun a => a.effect.promise.isNone && a.effect.keeps 0), R with
              | some a, _ =>
                let further := L.filterMap fun s =>
                  if s.receiver == a.receiver && s.arguments == a.arguments && s.effect.promise.isSome &&
                      s.effect.keeps 0 then
                    some (⟨top, s.arguments, s.result, bound s.effect⟩ : CallEffects.Arrow (Ty Tree)) else none
                return Except.ok [← lower (SourceTypes.use (.arrs
                  (⟨top, a.arguments, a.result, bound a.effect⟩ :: further) []))]
              | none, [a] => if !a.effect.keeps 0 then return r else return Except.ok [← lower (SourceTypes.use (.arrs []
                  [⟨top, a.arguments, a.result, bound a.effect⟩]))]
              | _, _ => return r
            | _ => return r)
        | .error _ => pure r
      return (← record e r, e3)
    | _ =>
      -- `f.bind(o, a…)` of any other target: the target, the receiver and
      -- the prefix in order; the target's first signature of no promise
      -- taking the prefix (`expression_values.ml`, `Bind`), the prefix at
      -- its first positions; the bound function at any receiver takes the
      -- positions left, at the effect binding keeps (`Effect.drop`), with
      -- each further signature of the same parameters promising about a
      -- position past the prefix (`Effect.keeps`), as the lowering builds
      -- it (Expression.lean:518-573); a variadic one keeps its rest.
      let (F, e1) ← expr env callee
      let (R, e2) ← expr e1 recv
      let (Ps, e3) ← exprs e2 args
      let n := args.length
      let r ← StateT.lift (tryCatch (do
          let B ← need F "the target"
          let _ ← need R "the receiver"
          let Ps ← Ps.mapM (need · "a bound actual")
          let T ← table
          let G := SourceTypes.graph T
          let top ← prim .top
          match PositiveRules.expand G B with
          | [.arrs L@(_ :: _) _] | [.callable _ _ L@(_ :: _) _ _] =>
            let some a := L.find? fun a => a.effect.promise.isNone && a.effect.keeps n && n ≤ a.arguments.length
              | throw "bind requires a signature taking the prefix"
            if !(Ps.zip a.arguments).all (fun (P, D) => within T P D) then
              throw "a bound actual outside its parameter"
            let further := L.filterMap fun s =>
              if s.receiver == a.receiver && s.arguments == a.arguments && s.effect.promise.isSome &&
                  s.effect.keeps n then
                some (⟨top, s.arguments.drop n, s.result, s.effect.drop n⟩ : CallEffects.Arrow (Ty Tree))
              else none
            return Except.ok [← lower (SourceTypes.use (.arrs
              (⟨top, a.arguments.drop n, a.result, a.effect.drop n⟩ :: further) []))]
          | [.arrs [] [a]] | [.callable _ _ [] [a] _] =>
            if a.effect.promise.isSome || !a.effect.keeps n then throw "bind requires a signature of no promise"
            let some El := PositiveRules.restElem G a.arguments.2
              | throw "a variadic bound function needs an element rest"
            let Ds := a.arguments.1 ++ List.replicate (n - a.arguments.1.length) El
            if !(Ps.zip Ds).all (fun (P, D) => within T P D) then
              throw "a bound actual outside its parameter"
            return Except.ok [← lower (SourceTypes.use (.arrs []
              [⟨top, (a.arguments.1.drop n, a.arguments.2), a.result, a.effect.drop n⟩]))]
          | _ => throw "bind requires a single callable contract") fun m => pure (.error m))
      return (← record e r, e3)
  | .invoke _ callee args spreads typeArgs =>
    -- The method's object, then its read (the member, recorded apart), then
    -- the actuals.
    let (obj, fld, keyE) := match callee with
      | .read _ f o => (some o, some f, none)
      | .index _ (some f) o k => (some o, some (PropKey.str f), some k)
      | .index _ none o k => (some o, none, some k)
      | _ => (none, none, none)
    let some o := obj | do
      let (_, e1) ← expr env callee
      let (_, e2) ← exprs e1 args
      if (← get).strict then
        wrote .any .any
        modify fun w => { w with throwWrites := true }
      return (← record e (.error "a method call of an unknown form"), e2)
    let (O, e1) ← expr env o
    let (K, e1) ← match keyE with
      | some k => expr e1 k
      | none => pure (none, e1)
    -- The method is read before its actuals. A path's current contents
    -- supply that read as for any other member read (expression_calls.ml:85,
    -- expression_properties.ml:32-35). The existing path invalidation in
    -- `expr`/`afterCall` decides which contents reach this point.
    let narrowed := (memberPath callee).bind fun p => e1.paths.lookup p
    -- The adversarial proposal changes the saved member's callable row.
    let narrowed := if (← get).force.contains "path-callees" then narrowed.map fun _ => [Labels.tru] else narrowed
    if let (some p, some _) := (memberPath callee, narrowed) then
      modify fun w => { w with readPaths := w.readPaths.insert p }
    let (As, e2) ← actuals e1 args
    -- Spread actuals as the call reads them (`spreadCall`).
    let c ← StateT.lift (tryCatch (do
        if let some F := narrowed then
          let R := present (← graphNow) (← need O "the receiver")
          return Except.ok (← spreadCall args As spreads (← calleeOf F R typeArgs))
        -- A computed key of one string literal names its member, as a
        -- literal key does (the lowering's `keySingletons`, Atoms.lean:1079).
        let fld ← match fld, K with
          | some f, _ => pure (some f)
          | none, some K => pure ((← keyString K).map PropKey.str)
          | none, none => pure none
        let some fld := fld | do
          -- An array's element at an index key, called at the array (the
          -- lowering's `keySingletons` reads a numeric key as its property,
          -- Atoms.lean:1079; the element read is `keyedRead`'s).
          let some i ← (match K with | some K => keyIndex K | none => pure none)
            | throw "a method of a computed key"
          let R := present (← graphNow) (← need O "the receiver")
          if (storeOf (← graphNow) R).isNone then throw "a method of a computed key"
          let F ← elementAt R (some i)
          return Except.ok (← spreadCall args As spreads (← calleeOf F R typeArgs))
        -- A nullish receiver throws before its method is read (the
        -- lowering's saved receiver, Atoms.lean:1176-1184).
        return Except.ok (← spreadCall args As spreads (← methodCallee e1.vars (present (← graphNow) (← need O "the receiver")) fld (args.map callback) typeArgs)))
      fun m => pure (.error m))
    let (args, As) := match c with
      | .ok (args', As', _) => (args', As')
      | .error _ => (args, As)
    let c := (·.2.2) <$> c
    -- (`TSCERT_FORCE=fresh`: every named receiver, the adversarial
    -- proposal)
    let fcs := (← get).freshConsts
    let anyFresh := (← get).force.contains "fresh"
    let receiverFresh := match o with
      | .var _ n => anyFresh || fcs.contains n
      | _ => false
    let r ← called e2 c args As e.span exp receiverFresh
    -- A function's `toString` call is lowered as a test of its receiver: a
    -- function calls `Function.prototype`'s, any other value its own
    -- (`Plans.primitiveArms`' `.isFun` arm, Plans.lean:631-643), a callee
    -- the walk does not know; a declaration's footprint reads that call as a
    -- call of an unknown callee.
    if (← get).strict && fld == some (PropKey.str "toString") then
      if let some O := O then
        let G ← StateT.lift graphNow
        let isFunction (l : Tree) : Bool := match PositiveRules.expand G [l] with
          | [.arrs ..] | [.callable ..] | [.ctors ..] => true
          | _ => false
        if O.any isFunction then
          wrote .any .any
          modify fun w => { w with throwWrites := true }
    let e2 ← afterCall e2 r
    let _ ← record callee ((·.1) <$> r)
    let r ← record e ((·.2) <$> r)
    return (r, e2)
  | _ => return (none, env)

partial def exprs (env : Env) (es : List Expr) : W (List (Option (Ty Tree)) × Env) := do
  let mut env := env
  let mut out := []
  for x in es do
    let (A, e') ← expr env x
    out := out ++ [A]
    env := e'
  return (out, env)

/-- A call's actuals in order, a callback left for the signature's pass
(`applyCall`), none in its place. -/
partial def actuals (env : Env) (args : List Expr) : W (List (Option (Ty Tree)) × Env) := do
  let mut env := env
  let mut out := []
  for x in args do
    if callback x then out := out ++ [none]
    else
      let (A, e') ← expr env x
      out := out ++ [A]
      env := e'
  return (out, env)

/-- `applyCall` where the callee is known; the callbacks walked unexpected
where it is not. -/
partial def called (env : Env) (c : Except String Callee) (args : List Expr) (As : List (Option (Ty Tree)))
    (at_ : Span) (exp : Option (Ty Tree) := none) (receiverFresh : Bool := false) :
    W (Except String (Ty Tree × Ty Tree)) := do
  modify fun w => { w with changedValues := false }
  match c with
  | .ok c =>
    let c ← if (← get).generalCalls.contains at_ then StateT.lift (generalArrayCallee c As) else pure c
    applyCall env c args As (exp <|> (← get).hints.lookup at_) receiverFresh
  | .error m =>
    for x in args do if callback x then let _ ← walkLambda env x none
    -- A call of an unknown callee may change anything, and its throw too.
    if (← get).strict then
      wrote .any .any
      modify fun w => { w with throwWrites := true }
    return .error m

/-- The actuals of a call with those at a parameter placing the call's
unbounded binders at tuple positions made at the parameter with those
binders as holes: an array literal a tuple there, and a call's callback's
result (`new Map(xs.map((x) => [x.k, x]))`); of a construction's
signatures, at the first placing them so (the producer's
`contextual_actual`, expression_support.ml:105-137, expression_calls.ml:927,
expression_closures.ml:121-133). `skip`: the positions made at their
binders' bounds. -/
partial def holedActuals (env : Env) (c : Callee) (candidates : List (List (Ty Tree))) (args : List Expr)
    (As : List (Option (Ty Tree))) (skip : List Nat) : W (List (Option (Ty Tree))) := do
  let G ← StateT.lift graphNow
  -- (a bound of `unknown` constrains nothing)
  let free := c.binders.filter fun b => (c.seed.lookup b).isNone &&
    (c.bounds.lookup b).all fun B => PositiveRules.expand G B == [.source]
  if free.isEmpty || !(candidates.length == 1 || c.construct) then return As
  let mut As := As
  for (x, i) in args.zipIdx do
    if skip.contains i || callback x || !holeGuided x then continue
    let some P := (candidates.filterMap (·[i]?)).find? (placesHoles G free 4) | continue
    if arrayLiteral x then
      if candidates.length != 1 then As := As.set i (← tupleActual P x (As[i]?.join))
    else
      let before := (← get).holes
      modify fun w => { w with holes := free ++ before }
      let (A, _) ← expr env x (some P)
      modify fun w => { w with holes := before }
      if A.isSome then As := As.set i A
  return As

/-- A call's instance, in a fixed order (TypeScript's contextual typing of
arguments, one pass): the signature the actuals' count and the walked
actuals' types select; each binder from the receiver and the walked
actuals (`matchBinder`); then each callback walked with its parameters at
the selected signature's, under those binders, its result binding what
remains; each literal actual at the parameter's shape (`fit`). The callee's
type at the call and the call's result. -/
partial def applyCall (env : Env) (c : Callee) (args : List Expr) (As : List (Option (Ty Tree)))
    (hint : Option (Ty Tree) := none) (receiverFresh : Bool := false) : W (Except String (Ty Tree × Ty Tree)) := do
  let T ← StateT.lift table
  let G := SourceTypes.graph T
  let n := args.length
  -- An expected type naming a hole guides a callback's result alone; the
  -- call's instance is read off its actuals (expression_calls.ml:42-46).
  let outer := (← get).holes
  let contextual := hint.filter fun H => outer.any fun h => H.any (occurs h)
  let hint := if contextual.isSome then none else hint
  let fits (a : CallEffects.Arrow (Ty Tree)) : Bool :=
    n ≤ a.arguments.length && (a.arguments.drop n).all (fun D => omissible G D || within T [Labels.undef] D)
  -- A union of callables (`armsCall`): one signature its arms meet.
  let c ← match ← armsCall c (args.map callback) As with
    | .ok c => pure c
    | .error m => do
      for x in args do if callback x then let _ ← walkLambda env x none
      return .error m
  -- A variadic signature: its fixed parameters, then each further actual at
  -- the element its rest's argument list states; a call omitting fixed
  -- parameters that each admit `undefined` passes no rest (the producer's
  -- `callable`, expression_calls.ml:757-761).
  let variadic := c.rests.filterMap fun r =>
    if r.arguments.1.length ≤ n then
      match PositiveRules.expand G r.arguments.2 with
      | [.pack t []] => match t.rest with
        | some E => some ((⟨r.receiver, r.arguments.1 ++ (List.replicate (n - r.arguments.1.length) E),
            r.result, r.effect⟩ : CallEffects.Arrow (Ty Tree)), some r)
        -- (an argument pack of required positions, a tuple instance's
        -- argument lists: exactly its positions)
        | none => if t.optional.isEmpty && n == r.arguments.1.length + t.required.length then
            some (⟨r.receiver, r.arguments.1 ++ t.required, r.result, r.effect⟩, some r) else none
      | _ => none
    else if (r.arguments.1.drop n).all (fun D => omissible G D || within T [Labels.undef] D) then
      some (⟨r.receiver, r.arguments.1, r.result, r.effect⟩, some r)
    else none
  -- A rest that is a binder's argument lists (`...args: T`): the actuals
  -- past the fixed ones, widened, are its instance, an argument pack where
  -- only the rest uses the binder, else the tuple of them; the other
  -- binders are read off the fixed actuals (the producer's pack rest,
  -- expression_calls.ml:638-689).
  let mut packs : List (Tree × Ty Tree) := []
  let mut packed : List (CallEffects.Arrow (Ty Tree) × Option (CallEffects.RestArrow (Ty Tree))) := []
  for r in c.rests do
    let [p] := r.arguments.2 | continue
    if !c.binders.contains p || (c.seed.lookup p).isSome || n < r.arguments.1.length then continue
    let some extras := (As.drop r.arguments.1.length).mapM id | continue
    let Es ← extras.mapM fun A => StateT.lift (widen A)
    let typesValue := (r.receiver :: r.result :: r.arguments.1).any (valueBinder G p)
    let P ← StateT.lift (lower (do
      if !typesValue then
        return [← SourceTypes.use (.pack ⟨Es, [], none, false, .dense⟩ [])]
      let s ← SourceTypes.use (.list ⟨Es, [], none, false, .dense⟩ [])
      let T ← get
      return [← SourceTypes.use (SourceTypes.arrayOf T s false)]))
    packs := packs ++ [(p, P)]
    packed := packed ++ [(⟨r.receiver, r.arguments.1 ++ Es, r.result, r.effect⟩, some r)]
  let c := { c with seed := c.seed ++ packs }
  let variadic := if packed.isEmpty then variadic else packed
  let candidates := (c.fixed.filter fits).map (·, none) ++ variadic
  -- Of one signature, a fresh literal at a parameter that is a bounded
  -- binder is made at the bound where the bound names a dictionary (an
  -- object literal) or a tuple (an array literal), as TypeScript types it
  -- by the constraint (the producer's `dictionary_bound` and `tuple_bound`,
  -- expression_calls.ml:806-822, 866-875, 900-916).
  let mut As := As
  -- A fresh array literal at a parameter whose binders are bounded by
  -- literal types is made at the parameter read at those bounds, where
  -- that leaves it no binder (the producer's `literal_bounds`,
  -- expression_calls.ml:827-844, 900-902).
  let literalLabel (l : Tree) : Bool := l == Labels.nul || l == Labels.undef ||
    match PositiveRules.expand G [l] with
    | [.numLit _] | [.numIn _] | [.strLit _] | [.strIn _] | [.boolLit _] | [.bigintLit _] => true
    | _ => false
  let literalBounds := c.bounds.filter fun (_, B) => !B.isEmpty && B.all literalLabel
  let mut atBounds : List Nat := []
  if let ([(a, _)], false) := (candidates, literalBounds.isEmpty) then
    for ((x, P), i) in (args.zip a.arguments).zipIdx do
      let .arrayLit .. := x | continue
      let P' := substitute literalBounds P
      if P' == P || c.binders.any (fun b => P'.any (occurs b)) then continue
      if let some A' ← fit P' x (As[i]?.join) then
        As := As.set i (some A')
        atBounds := i :: atBounds
  if let ([(a, _)], false) := (candidates, c.binders.isEmpty) then
    for ((x, P), i) in (args.zip a.arguments).zipIdx do
      if c.binders.any (fun b => P.any (occurs b)) && !atBounds.contains i then
        As := As.set i (← tupleActual P x (As[i]?.join))
  -- (`holedActuals`: the producer's `contextual_actual`)
  As ← holedActuals env c (candidates.map (·.1.arguments)) args As atBounds
  if let ([(a, _)], false) := (candidates, c.binders.isEmpty) then
    for ((x, P), i) in (args.zip a.arguments).zipIdx do
      let some A := As[i]?.join | continue
      if !c.binders.any (isBinder · P) then continue
      let B ← match P with
        | [b] => match c.bounds.lookup b with
          | some B => pure B
          | none => StateT.lift (boundOf P)
        | _ => StateT.lift (boundOf P)
      if B == P then continue
      let arms := PositiveRules.expand G B
      let guided := match x with
        | .alloc .. => arms.any fun | .dict .. => true | _ => false
        | .arrayLit _ _ [] => B.any fun l => match storeOf G [l] with
          | some S => match PositiveRules.expand G S with
            | [.list t []] => t.rest.isNone
            | _ => false
          | none => false
        | _ => false
      if !guided then continue
      if let some A' ← fit B x (some A) then
        if within (← StateT.lift table) A' B then As := As.set i (some A')
  -- A resolution's observation and result are the resolution's, never an
  -- actual's.
  let hidden := (c.resolution.flatMap (·.associated)).filterMap (c.binders[·]?)
  -- A binder the signature reads only at its callbacks' parameters (each
  -- parameter mentioning it a callable whose results do not): its
  -- candidates are upper bounds, of which the one within every other is
  -- taken (the producer's upper-only candidates' meet, inference.ml:557-569).
  let uppersOf (a : CallEffects.Arrow (Ty Tree)) : List Tree := c.binders.filter fun b =>
    (a.receiver :: a.arguments).any (·.any (occurs b)) &&
    (a.receiver :: a.arguments).all fun P => !P.any (occurs b) ||
      (let sigs := ProgramTyping.callSigs G P
       !sigs.isEmpty && sigs.all fun s => !s.result.any (occurs b))
  let bindFrom (σ : List (Tree × Ty Tree)) (pairs : List (Ty Tree × Ty Tree)) (receiverFirst : Bool := true)
      (uppers : List Tree := []) : W (List (Tree × Ty Tree)) := do
    let mut σ := σ
    -- Each binder at what the first pair (the receiver, where the caller
    -- passes it first) gives it, else at the join of what the others give
    -- it (the producer's join of its lower bounds, inference.ml:557-569),
    -- a primitive's members read off its prototype.
    for b in c.binders do
      if hidden.contains b || (c.seed.lookup b).isSome ||
          ((σ.lookup b).isSome && (receiverFirst || c.fixed.any (fun a => a.receiver.any (occurs b)))) then continue
      let mut got : Option (Ty Tree) := none
      for ((P, A), i) in pairs.zipIdx do
        if let some B ← StateT.lift (tryCatch (matchBinder b P A (vars := env.vars) (siblings := c.binders)) fun _ => pure none) then
          let T ← StateT.lift table
          got := match got with
            | some A => if !uppers.contains b then some (norm (A ++ B))
              else if within T B A then some B else some A
            | none => some (norm B)
        if i == 0 && got.isSome && receiverFirst then break
      if let some B := got then
        -- Callback results join the actuals' lower bounds (inference.ml:
        -- 327-329, 557-569); a primitive absorbs its literal candidate.
        let B ← match σ.lookup b with
          | none => pure B
          | some A => StateT.lift (do
            let T ← table
            if uppers.contains b then pure (if within T B A then B else A)
            else if within T A B then pure B else if within T B A then pure A else joinTy A B)
        σ := upd σ b B
    -- A lower candidate for U also constrains T where U extends T.
    -- These edges copy finite candidate sets; at most one pass per binder
    -- propagates every path (inference.ml:540-556, saturation of bounds).
    for _ in List.range c.binders.length do
      let before := σ
      for (u, bound) in c.bounds do
        let [t] := bound | continue
        if !c.binders.contains t || (c.seed.lookup t).isSome then continue
        let some U := σ.lookup u | continue
        let B ← match σ.lookup t with
          | none => pure U
          | some B => StateT.lift (joinTy B U)
        σ := upd σ t B
      if σ == before then break
    return σ
  -- The first signature, in order, each walked actual is within (a
  -- scheme's at the binders its walked actuals give); else the first the
  -- count admits.
  -- The signature taking the most parameters of a callback parameter.
  let widest (P : Ty Tree) : Option (CallEffects.Arrow (Ty Tree)) :=
    (ProgramTyping.callSigs G P).foldl (fun (best : Option (CallEffects.Arrow (Ty Tree))) a =>
      match best with
      | some b => if Nat.blt b.arguments.length a.arguments.length then some a else some b
      | none => some a) none
  -- The binders a signature mentions.
  let mentioned (a : CallEffects.Arrow (Ty Tree)) (b : Tree) : Bool :=
    (a.receiver :: a.result :: a.arguments).any (·.any (occurs b))
  -- Of several signatures, each callback walked first at the first one's
  -- parameter, under the binders its receiver and other actuals give, at
  -- its own effect: the signature chosen is the first whose parameter its
  -- type is within (the checker's subtyping of arrows, its effect within
  -- the parameter's), in the store after its walk (the producer's
  -- `matches_actuals`, expression_calls.ml:980-1000).
  -- A member stating its signatures at several receivers (a dense and a
  -- sparse array's): those whose receiver, at the binders it gives, admits
  -- the callee's, where some does (the producer reads the member at the
  -- walked receiver).
  let mut candidates := candidates
  if ((candidates.map (·.1.receiver)).eraseDups).length > 1 then
    let mut mine := []
    for (a, r) in candidates do
      let σr ← if c.binders.isEmpty then pure c.seed else bindFrom c.seed [(a.receiver, c.receiver)]
      if within (← StateT.lift table) c.receiver (substitute σr a.receiver) then mine := mine ++ [(a, r)]
    if !mine.isEmpty then candidates := mine
  -- As for a written guard literal, a guard passed by name prefers the
  -- signature whose callback states that promise. Each instance must still
  -- pass the actuals check below.
  let preferred := candidates.filter fun (a, _) => promisesOfActuals G As a
  candidates := preferred ++ candidates.filter fun (a, _) => !promisesOfActuals G As a
  let mut walked : List (Nat × Ty Tree) := []
  if candidates.length > 1 then
    if let some (a0, _) := candidates.head? then
      let σ0 ← if c.binders.isEmpty then pure c.seed else
        bindFrom c.seed ((a0.receiver, c.receiver) :: (a0.arguments.zip As).filterMap fun (P, A) => A.map (P, ·))
      for ((x, P), i) in (args.zip a0.arguments).zipIdx do
        if callback x then
          let w0 ← get
          modify fun w => { w with pending := c.binders.filter fun b => (σ0.lookup b).isNone }
          let L ← walkLambda env x (widest (substitute σ0 P)) (ctx := some (substitute σ0 P))
          set w0
          if let some L := L then walked := walked ++ [(i, L)]
  -- An object or array literal at a parameter the candidates state
  -- differently is made at the first candidate's parameter it fits, as
  -- TypeScript reads a literal against each overload in turn (the
  -- producer's `shared_actuals`, expression_calls.ml:353-380).
  if candidates.length > 1 && c.binders.isEmpty then
    for (x, i) in args.zipIdx do
      let literal := match x with
        | .alloc .. | .arrayLit _ _ [] => true
        | _ => false
      let Ds := (candidates.filterMap fun (a, _) => a.arguments[i]?).eraseDups
      let some A := As[i]?.join | continue
      if !literal || Ds.length < 2 then continue
      for D in Ds do
        let w0 ← get
        if let some A' ← fit D x (some A) then
          if A' != A && within (← StateT.lift table) A' D then
            As := As.set i (some A')
            break
        modify fun w => { w with exprs := w0.exprs }
  let Tw ← StateT.lift table
  let mut chosen : Option (CallEffects.Arrow (Ty Tree) × Option (CallEffects.RestArrow (Ty Tree))) := none
  let mut fallback : Option (CallEffects.Arrow (Ty Tree) × Option (CallEffects.RestArrow (Ty Tree))) := none
  let mut promised : Option (CallEffects.Arrow (Ty Tree) × Option (CallEffects.RestArrow (Ty Tree))) := none
  -- (`TSCERT_FORCE=callbacks`: the first, whatever its parameter, the
  -- adversarial proposal)
  let forceCallbacks := (← get).force.contains "callbacks"
  for (a, r) in candidates do
    if chosen.isSome || forceCallbacks then break
    let σa ← if c.binders.isEmpty then pure c.seed else
      bindFrom c.seed ((a.receiver, c.receiver) :: (a.arguments.zip As).filterMap fun (P, A) => A.map (P, ·))
    if c.bounds.all (fun (b, B) => (σa.lookup b).all fun A => within Tw A (substitute σa B)) &&
        (As.zip a.arguments).all (fun (A, D) => A.all fun A => within Tw A (substitute σa D)) then
      if fallback.isNone then fallback := some (a, r)
      -- (where none admits a callback, the first stating each callback's
      -- promise: the rows stating a guard's written promise first, the
      -- producer's `states_written`, expression_calls.ml:1032-1047)
      if promised.isNone && walked.all (fun (i, L) => match a.arguments[i]? with
          | some D =>
            let Gw := SourceTypes.graph Tw
            let ps (X : Ty Tree) := (ProgramTyping.callSigs Gw X).map (·.effect.promise)
            (ps L).any (·.isSome) == (ps D).any (·.isSome) && (ps D).all ((ps L).contains ·)
          | none => false) then promised := some (a, r)
      let σa ← if c.binders.isEmpty then pure σa else
        bindFrom σa (walked.filterMap fun (i, L) => (a.arguments[i]?).map (·, L)) (receiverFirst := false)
          (uppers := uppersOf a)
      -- With every binder it mentions the actuals and callbacks give bound.
      let bound := walked.isEmpty || c.binders.all fun b =>
        hidden.contains b || !mentioned a b || (σa.lookup b).isSome
      if bound && walked.all fun (i, L) => match a.arguments[i]? with
          | some D => within Tw L (substitute σa D)
          | none => false then chosen := some (a, r)
  chosen := chosen <|> promised <|> fallback
  let some (a, rest) := chosen <|> candidates.head?
    | do
      for x in args do if callback x then let _ ← walkLambda env x none
      -- One callable of no binders none of whose signatures the count
      -- admits, omitted positions admitting `undefined`, a variadic one's
      -- fixed ones too: the lowering's selection refuses it too
      -- (`refusalMark`). (A binder's admission is its instance's.)
      -- A class's construction of no binders likewise (a constructor none
      -- of whose signatures takes the count, `new Error()` at a message).
      let one := match c.own with
        | some [_] => c.binders.isEmpty
        | _ => c.construct && c.binders.isEmpty
      -- (`undefined` within an omitted position's type, `unknown` too.)
      let admits (D : Ty Tree) : Bool := admitsUndefined G D || within T [Labels.undef] D
      let short (ps : List (Ty Tree)) : Bool := n ≤ ps.length && (ps.drop n).all admits
      -- (a rest whose argument lists are the empty type admits no list,
      -- an empty one included: `(...args: never) => R`)
      let none_ (P : Ty Tree) : Bool := P.isEmpty
      let m := s!"no signature admits {n} actuals"
      -- (a value of no call signature, `Function` or `(...args: never) =>
      -- R`, is none: the producer states no call of it)
      return .error (if one && c.fixed.all (!short ·.arguments) &&
        c.rests.all (fun r => none_ r.arguments.2 || (n < r.arguments.1.length && !short r.arguments.1))
        then callRefusal m else m)
  let mut σ : List (Tree × Ty Tree) := c.seed
  -- Each binder from the receiver and the walked actuals first; then those
  -- still unbound from the type expected of the call's value, where the
  -- instance admits every walked actual (a callback is then walked at it).
  let admitsAt (σ : List (Tree × Ty Tree)) : Bool :=
    (As.zip a.arguments).all (fun (A, P) => A.all fun A => within T A (substitute σ P))
  σ ← bindFrom σ ((a.receiver, c.receiver) :: (a.arguments.zip As).filterMap fun (P, A) => A.map (P, ·))
  let mut hinted : List (Tree × Ty Tree) := []
  if let some H := hint then
    let H' := match a.result with
      | [.app h _] =>
        let same := H.filter fun | .app h' _ => h' == h | _ => false
        if same.length == 1 then same else H
      | _ => H
    let σh ← bindFrom σ [(a.result, H')]
    hinted := σh
    if admitsAt σh then σ := σh
    -- Where the two conflict (the instance the actuals give has a result
    -- the expected type does not admit), the expected type's instance, where
    -- it binds every binder and admits the actuals (TypeScript's widening of
    -- an inferred literal at its context).
    -- (`TSCERT_FORCE=instances` keeps the actuals' instance: its result is
    -- then stated at a type that does not admit it.)
    if !(← get).force.contains "instances" &&
        c.binders.all (fun b => hidden.contains b || (σ.lookup b).isSome) &&
        !within T (substitute σ a.result) H then
      let σe ← bindFrom c.seed [(a.result, H')]
      if c.binders.all (fun b => hidden.contains b || (σe.lookup b).isSome) && admitsAt σe then σ := σe
  -- A binder that is a callback literal's parameter, which an earlier
  -- actual's parameter takes at a position of one of its methods: the
  -- literal is walked at the callable the actual's method of that key takes
  -- there, of its signatures of that arity taking a callable the last whose
  -- effect covers the parameter's method's, else the first (a string's
  -- `replace` dispatching to a native regex's `[Symbol.replace]`, whose
  -- replacer rows differ by the footprint they keep; the producer's
  -- `from_actuals`, expression_calls.ml:446-485). The binder is then read
  -- off the walked literal, as any callback's.
  let lambdaBinders := (args.zip a.arguments).filterMap fun (x, P) => match x, P with
    | .lambda .., [r] => if c.binders.contains r && (σ.lookup r).isNone then some r else none
    | _, _ => none
  let fromActuals ← StateT.lift (methodBinders args a.arguments As lambdaBinders)
  for ((x, P), i) in (args.zip a.arguments).zipIdx do
    let sub (A : Ty Tree) : Ty Tree := substitute σ A
    if callback x then
      -- The callback's parameter's signature taking the most parameters:
      -- the callback walked there is within each of them.
      let Pc := match P with
        | [r] => if (σ.lookup r).isNone then ((fromActuals.lookup r).getD (sub P)) else sub P
        | _ => sub P
      -- Where the type expected of the call's value names a hole, the
      -- callback is walked at its parameter read at the binders the result
      -- gives there, where that is one signature naming holes in its result
      -- alone and no binder of this call (the producer's `result_bound`,
      -- expression_calls.ml:852-868).
      let Pc ← match contextual with
        | none => pure Pc
        | some H => do
          let σh ← bindFrom σ [(a.result, H)]
          let G ← StateT.lift graphNow
          pure (holedCallback G outer c.binders (substitute σh P) Pc)
      let before := (← get).pending
      modify fun w => { w with pending := c.binders.filter fun b => (σ.lookup b).isNone }
      let L ← walkLambda env x (widest Pc) (ctx := some Pc)
      modify fun w => { w with pending := before }
      As := As.set i L
      if let some L := L then σ ← bindFrom σ [(P, L)] (receiverFirst := false) (uppers := uppersOf a)
    else if let some A := As[i]? then
      if let .var _ n := x then
        offerUse n (sub P)
        offerClass n (sub P)
      As := As.set i (← fit (sub P) x A)
  -- A finite record supplies no index candidate to a dictionary parameter
  -- (inference.ml:301-308). With no other candidate or declared bound,
  -- that binder defaults to unknown (inference.ml:631-632): its unnamed
  -- own values are unconstrained, not the union of its named fields.
  for b in c.binders do
    if (σ.lookup b).isSome || (c.bounds.lookup b).isSome || hidden.contains b then continue
    let G ← StateT.lift graphNow
    let missingIndex := (a.arguments.zip As).any fun (P, A) =>
      match PositiveRules.expand G P, A with
      | [.dict [] [] [] ix [] [] _ _ _], some A =>
        ix.any (fun (_, E) => isBinder b E) && !A.isEmpty && A.all fun l =>
          (storeOf G [l]).isNone && match PositiveRules.expand G [l] with
            | [.refs _ [] ..] => true
            | _ => false
      | _, _ => false
    if missingIndex then σ := upd σ b (← StateT.lift (prim .source))
  σ ← StateT.lift (widenActualBinders c a As hidden hint σ (← get).scope)
  -- A binder a resolution qualifies: its observation and result the
  -- resolution of its input's type by the certificate its form gives
  -- (`resolutionCertificate`), checked (`resolutionInstance`).
  let mut certificates : List (String × ResolutionWire.Certificate) := []
  for group in c.resolution do
    let (some b, some o) := (c.binders[group.input]?, c.binders[group.observation]?) | continue
    let some A := σ.lookup b | continue
    let T ← StateT.lift table
    let scope := (← get).scope
    let r : Except String (ResolutionWire.Certificate × Option (Ty Tree) × Option (Ty Tree)) := do
      let row := scope.map (·.1)
      let names := (scope.map (·.2)).getD []
      let cert ← SourceClaimJson.Scheme.resolutionCertificate T row names A group.result.isSome
      let (O, R) ← SourceClaimJson.Scheme.resolutionInstance T row names A cert
      return (cert, O, R)
    match r with
    | .error m =>
      return .error s!"the resolution of a binder's type: {m}"
    | .ok (cert, O, R) =>
      if let some n := c.names[group.input]? then certificates := certificates ++ [(n, cert)]
      -- An observation no source type names is placed at the empty type:
      -- the instance's check admits it only where the signature does not
      -- read it (`moduleInstances`).
      σ := σ.filter (·.1 != o) ++ [(o, O.getD [])]
      if let (some slot, some R) := (group.result, R) then
        if let some rb := c.binders[slot]? then σ := σ.filter (·.1 != rb) ++ [(rb, R)]
  -- A binder the signature does not mention, at the empty type.
  σ := σ ++ (c.binders.filter fun b => !mentioned a b && (σ.lookup b).isNone).map (·, [])
  -- A binder no actual gives: at what the type expected of the call's value
  -- gives it, whether or not that instance admits the actuals (the call's
  -- step decides); else at its bound, read at the binders so far; else at
  -- `unknown` (the producer's candidates, inference.ml:584-636: the lower
  -- bounds' join, else the upper bounds', the expected result among them,
  -- else `top`). A binder the expected type does not give either takes its
  -- declared default, read at the binders so far, before its bound (the
  -- producer's `default`, inference.ml:637-647): a proposal, the instance
  -- checked against the scheme at the call.
  for b in c.binders do
    if (σ.lookup b).isSome then continue
    let B ← match hinted.lookup b, c.defaults.lookup b, c.bounds.lookup b with
      | some B, _, _ => pure B
      | none, some D, _ =>
        let D := substitute σ D
        if c.binders.any (fun b' => D.any (occurs b')) then continue
        pure D
      | none, none, some B =>
        let B := substitute σ B
        if c.binders.any (fun b' => B.any (occurs b')) then continue
        pure B
      | none, none, none => StateT.lift (prim .source)
    σ := σ ++ [(b, B)]
  let sub (A : Ty Tree) : Ty Tree := substitute σ A
  if let some b := c.binders.find? (fun b => (σ.lookup b).isNone) then
    let _ := b
    return .error "a type argument is not an actual's type"
  let inst := a.map sub
  offerToParameters args inst.arguments
  -- A generic module function's instance: each binder's type, by name.
  if !c.names.isEmpty || !c.explicit.isEmpty then
    modify fun w => { w with lastInstance := some (c.explicit ++
      c.names.zip (c.binders.map fun b => (σ.lookup b).getD [])), lastResolution := certificates }
  callChanges c inst As args receiverFresh
  -- A fresh result where a type is expected: made at the expected array.
  let mut result := inst.result
  if let some H := hint then
    if inst.effect.fresh then
      if let some R ← StateT.lift (tryCatch (freshAt H inst.result) fun _ => pure none) then result := R
  let own ← StateT.lift (calleeAtCall c σ inst rest (c.fixed.filter fits))
  return .ok (own, result)

/-- A function literal's walk: its parameters at their written types, or
else at `expected` (a callback's, from the parameter it is passed at),
each captured cell at its contract and each captured slot at its current
type (environment.ml:138-142); its result its written one,
or else what its body gives (its returns' union, `undefined` where it
completes). Recorded at the literal as a signature where every part is
determined. -/
partial def walkLambda (env : Env) (e : Expr) (sig : Option (CallEffects.Arrow (Ty Tree)))
    (ctx : Option (Ty Tree) := none) (rowInterior : Bool := false) :
    W (Option (Ty Tree)) := do
  let G ← StateT.lift graphNow
  let expected := (sig <|> ctx.bind (widestOf G)).map (·.arguments)
  let expectedResult := sig.map (·.result)
  let .lambda _ receiver tps params defaults rest result guard stated async requires body := e
    | return none
  -- For a declaration's footprint, a generic function literal is walked
  -- with no scheme of its own: the declaration is at the ordinary effect.
  if !tps.isEmpty && (← get).strict then
    wrote .any .any
    modify fun w => { w with throwWrites := true }
  -- A captured binding held in a cell at its declared type (a cell holds
  -- whatever its contract admits when the body runs); one held in a slot at
  -- its type here: no write of it follows the closure's creation
  -- (`cellLocals`; the producer's `forget`, environment.ml:138-142, keeps
  -- every binding but a cell's).
  -- (`TSCERT_FORCE=captures`: every captured binding at its type here, a
  -- cell's included, the adversarial proposal)
  let w0 ← get
  let captured := env.vars.map fun (n, A) =>
    if w0.force.contains "captures" || w0.slots.get.contains n || w0.literalSlots.contains n then (n, A)
    else (n, (env.decl.lookup n).getD A)
  let mut vars := captured
  let mut ps : List (Option (Ty Tree)) := []
  -- Each parameter's type in the body, for its default's expected type.
  let mut bound : List (Option (Ty Tree)) := []
  -- A rest parameter, the last: in the body at its written array type, a
  -- fresh argument pack with no holes; offered at the pack of its element
  -- (`ClosureSetup`'s array rest). None where it has no array element.
  let mut restPack : Option (Option (Ty Tree)) := none
  for ((n, ty), i) in params.zipIdx do
    let A ← if rowInterior || ty == Json.null then pure ((expected.bind (·[i]?)))
      else StateT.lift (tryCatch (some <$> lower (Fragment.translate ty)) fun _ => pure none)
    bound := bound ++ [A]
    if rest && i + 1 == params.length then
      restPack := some (← StateT.lift (tryCatch (do
        let some el := Fragment.arrayElement ty (readonly := true) | throw "a rest of no array element"
        let E ← lower (Fragment.callableType el)
        pure (some [← lower (SourceTypes.use (.pack ⟨[], [], some E, false, .dense⟩ []))])) fun _ => pure none))
      -- A rest of a tuple of required positions: one fixed parameter per
      -- position (the lowering's tuple rest, the producer's source.ml:644-646).
      if restPack == some none then
        let G ← StateT.lift graphNow
        if let some [l] := A then
          if let some S := storeOf G [l] then
            if let [.list t []] := PositiveRules.expand G S then
              if t.optional.isEmpty && t.rest.isNone then
                restPack := none
                ps := ps ++ t.required.map some
    else
      -- A defaulted one is offered with `undefined`: a call may omit it.
      ps := ps ++ [if defaults.any (·.1 == i) then A.map (fun A => norm (A ++ [Labels.undef])) else A]
    match A with
    | some A => vars := upd vars n A
    | none => vars := vars.filter (·.1 != n)
  let mut thisTy : Option (Ty Tree) := none
  if let some (ty, _) := receiver then
    match ← StateT.lift (tryCatch (some <$> lower (Fragment.translate ty)) fun _ => pure none) with
    | some A => vars := upd vars "this" A; thisTy := some A
    | none => pure ()
  let written ← match result with
    | some ty => StateT.lift (tryCatch (some <$> lower (Fragment.translate ty)) fun _ => pure none)
    | none => pure none
  let mut inner : Env := { vars, decl := vars, paths := [] }
  let saved ← get
  let declared := params.map (·.1) ++ (match body with
    | .block _ ss => declaredIn ss
    | _ => [])
  let bodyStmts := match body with
    | .block _ ss => ss
    | x => [.effect x.span x]
  let cells := (cellLocals (params.map (·.1)) bodyStmts).map (·.1)
  modify fun w => { w with writes := false, throwWrites := false, valueChange := .keep, storeChange := .keep, locals := declared, inLiteral := true,
                           literalSlots := declared.filter (!cells.contains ·) ++ w.literalSlots, heldCells := cells ++ w.heldCells }
  -- The contextual result guides async resolution calls as well as ordinary
  -- returns (expression_closures.ml:263-268), before their stores are made.
  modify fun w => { w with returns := [], expected := (if rowInterior then expectedResult else written <|> expectedResult), asyncBody := async }
  -- An expression body's entry is its prologue's, at the body's start.
  modify fun w => { w with entries := w.entries.insert body.span.1 inner.vars }
  -- Each default runs at a call omitting its argument, before the body: its
  -- effect is the literal's, its value made at the parameter's type.
  -- (`TSCERT_FORCE=defaults`: their changes left out of the literal's
  -- effect, the adversarial proposal)
  let beforeDefaults ← get
  -- The body binds a defaulted parameter after replacing `undefined`
  -- (expression_closures.ml:187-201).
  -- A parameter of `unknown` is bound at `unknown`, which holds the default's
  -- value too: its parts other than `undefined` are no type the prologue's
  -- join states (the producer states `(value: unknown = seed)` at
  -- `boolean | unknown` in the body, default-parameters.ts).
  let G0 ← StateT.lift graphNow
  for (i, d) in defaults do
    let B := bound[i]?.join
    let (D, _) ← withDefault inner B (some d)
    let open_ := B.any fun B => B.any fun l => G0.plain l && PositiveRules.expand G0 [l] == [.source]
    if let (some (n, _), some D) := (params[i]?, if open_ then B else D) then
      inner := { inner with vars := upd inner.vars n D, decl := upd inner.decl n D }
  if (← get).force.contains "defaults" then
    modify fun w => { w with writes := beforeDefaults.writes, throwWrites := beforeDefaults.throwWrites }
    modify fun w => { w with valueChange := beforeDefaults.valueChange, storeChange := beforeDefaults.storeChange }
  let R ← match body with
    | .block _ ss => do
      let done ← stmts (some inner) ss
      -- A body has no type, but where its span is its expression's (an
      -- expression body the parser writes as statements, `booleanReturn`),
      -- which keeps its own.
      if !(← get).exprs.contains body.span then let _ ← record body (.error "a function body")
      let rs := (← get).returns ++ (if done.any (!·.ghost) then [some [Labels.undef]] else [])
      pure (if rs.all (·.isSome) then some (norm (rs.filterMap id).flatten) else none)
    | x => do
      modify fun w => { w with lastFresh := false }
      let (A, _) ← expr inner x (← get).expected
      pure A
  -- A body that changes nothing keeps both values and stores: the
  -- footprint its calls are checked at (the producer's inferred effect).
  let pure_ := !(← get).writes
  -- One that also calls nothing leaving a changed heap on its throw keeps
  -- them on a throw too (`onThrow`).
  -- An expression body calling a function whose instance states a fresh
  -- result returns a fresh store (the producer's `fresh_result`,
  -- source.ml:1230).
  let freshResult := (match body with | .call .. | .invoke .. => true | _ => false) && (← get).lastFresh
  let kept : CallEffects.Effect :=
    { CallEffects.Effect.ofFootprint ⟨.keep, .keep⟩ with onThrow := !(← get).throwWrites, fresh := freshResult }
  -- One that changes the heap at the classes of contents its writes and
  -- calls change.
  let changed : CallEffects.Effect :=
    { CallEffects.Effect.ofFootprint ⟨(← get).valueChange, (← get).storeChange⟩ with
      onThrow := !(← get).throwWrites, fresh := freshResult }
  modify fun w => { w with breaks := saved.breaks, returns := saved.returns, held := saved.held, expected := saved.expected, literalSlots := saved.literalSlots, heldCells := saved.heldCells, evolving := saved.evolving, holders := saved.holders }
  modify fun w => { w with writes := saved.writes, throwWrites := saved.throwWrites, locals := saved.locals, inLiteral := saved.inLiteral }
  modify fun w => { w with valueChange := saved.valueChange, storeChange := saved.storeChange, lastBody := R, asyncBody := saved.asyncBody }
  -- Async returns are already the fragment's resolution calls, including
  -- returns in a block (expression_closures.ml:263-291). Their walked
  -- result is a proposal checked at each body return.
  let R := written <|> R
  let forced := (← get).force.contains "literals"
  -- A written effect (`Modifies<…>`) is the one it states.
  let kept := { stated.getD kept with pre := requires }
  let changed := { stated.getD changed with pre := requires }
  -- A generic closure: at the scheme its annotations state, its body walked
  -- with each binder a rigid row (`Scheme.closureRows`), where that scheme's
  -- effect covers its body's.
  -- (Where no scheme names it, a walk before the scheme rows are made: at
  -- its own parameters, as any other literal.)
  if let (false, some S) := (tps.isEmpty, (← get).schemes.lookup e.span) then
    let G ← StateT.lift graphNow
    let some s := (match S with | [l] => G.schemes l | _ => none)
      | return ← record e (.error "a generic closure's claim is no scheme")
    let mine := if pure_ then kept else changed
    if !forced && !(← get).force.contains "schemes" && !(s.signatures.all (mine.covers ·.effect) && s.variadic.all (mine.covers ·.effect)) then
      return ← record e (.error "a generic closure whose body changes the heap beyond its scheme's effect")
    return ← record e (.ok S)
  match ps.mapM id, R, restPack with
  | some _, some _, some none => record e (.error "a function value: a rest of no array element")
  | some qs, some R, some (some pack) =>
    -- A rest literal at its rest arrow, at its written effect else the
    -- ordinary one (`ClosureSetup`'s own signature of an array rest).
    let recv ← match thisTy, sig with
      | some A, _ => pure A
      | none, some a => pure a.receiver
      | none, none => StateT.lift (prim .source)
    let r : CallEffects.RestArrow (Ty Tree) := ⟨recv, (qs, pack), R, stated.getD .ordinary⟩
    record e (.ok [← StateT.lift (lower (SourceTypes.use (.arrs [] [r])))])
  | some qs, some R, none =>
    -- A callback is checked at the signature it is passed at, its result its
    -- body's; any other literal at its own parameters.
    let a : CallEffects.Arrow (Ty Tree) ← match sig with
      | some a =>
        -- (`TSCERT_FORCE=callbacks`: at the parameter's effect, the
        -- adversarial proposal)
        if (← get).force.contains "callbacks" then pure { a with result := R }
        else if pure_ then pure { a with result := R, effect := kept }
        else if forced then pure { a with result := R, effect := .ofFootprint ⟨.keep, .keep⟩ }
        -- A callback that changes the heap at its own effect, never the
        -- parameter's: the call's signature is chosen by it (`applyCall`;
        -- the producer's footprint at every row it claims,
        -- expression_closures.ml:348-351, 400-406), without its bound on a
        -- throw where the parameter states none.
        else pure { a with result := R, effect := if a.effect.onThrow then changed else { changed with onThrow := false } }
      -- Any other literal at its own parameters and written receiver (a
      -- method's `this`), else a receiver admitting every value.
      | none => do pure ⟨← match thisTy with
            | some A => pure A
            | none => StateT.lift (prim .top), qs, R,
          if pure_ then kept else if forced then .ofFootprint ⟨.keep, .keep⟩ else changed⟩
    -- A written type guard or assertion: its promise, the result its
    -- promised type (`ClosureSetup`'s written promise).
    let a ← match guard with
      | some g => do
        let promised ← StateT.lift (lower (Fragment.translate g.type))
        let promise : CallEffects.TypePromise := if g.asserts then .asserts g.param else .guards g.param
        pure { a with result := promised, effect := { a.effect with promise := some promise } }
      | none => pure a
    -- A guard is also offered at its own parameters, where its promise is
    -- checked (`ClosureSetup`'s written promise).
    if guard.isSome then
      -- The promise is beside the plain row, whose result is the body's
      -- Boolean (or assertion's undefined), not the promised type
      -- (expression_closures.ml:433-450; Types.lean:820-843).
      let plain := { a with arguments := qs, result := R, effect := { a.effect with promise := none } }
      let offered := if a.arguments.length != qs.length then
        [plain, a, { a with arguments := a.arguments.take qs.length }] else [plain, a]
      -- A named guard offers its written promise at the requested longer
      -- row (expression_closures.ml:396-399,433-450). Each interior is
      -- walked under that row's leading parameters, with a Boolean body.
      let extra := ((← get).offers.filter (·.1 == e.span)).filterMap fun (_, r) =>
        if r.effect.promise == a.effect.promise then
          some { r with result := a.result, effect := a.effect }
        else none
      let offered := offered ++ extra.filter (!offered.contains ·)
      if !rowInterior && !extra.isEmpty && !rest && defaults.isEmpty then
        let outside ← get
        let mut interiors : List (SourceClaims.Overlay Tree) := []
        for r in offered do
          set { outside with exprs := {}, entries := {}, currents := {}, contracts := [],
                             spanEntries := {}, declarations := {}, exprsAt := {} }
          let _ ← walkLambda env e (some { r with result := R }) none true
          let inside ← get
          interiors := interiors ++ [{
            exprs := inside.exprs.toList.map (fun (sp, _, A) => (sp, A))
            envs := inside.entries.toList.map (fun (p, vs) => (p, vs.map fun (n, A) => (n, .ok A)))
            entryCurrent := inside.currents.toList
            contracts := inside.contracts.map (fun (key, A) => (key, .ok A)) }]
        set { outside with arrowClaims := upd outside.arrowClaims e.span interiors }
      return ← record e (.ok [← StateT.lift (lower (SourceTypes.use (.arrs offered [])))])
    -- Any other at its own parameters' row and, beside it, at each signature
    -- the expected callable `ctx` states taking more parameters whose leading
    -- ones are within its own (or, variadic, at least as many), at its own
    -- result and effect: calls through it discard the actuals past its
    -- parameters, and its body is checked at each row (`ClosureSetup`;
    -- the producer's `from_context`, expression_closures.ml:372-386).
    -- One body obligation for each implemented signature, at that row's
    -- parameters; captured cells retain the contracts above. The producer
    -- states these interiors in expression_closures.ml:455-473.
    let rows := ctx.toList.flatMap (ProgramTyping.callSigs G)
    if !rowInterior && tps.isEmpty && !rest && defaults.isEmpty && rows.length > 1 &&
        rows.all (fun r => r.arguments.length == params.length) then
      let outside ← get
      let mut interiors : List (SourceClaims.Overlay Tree) := []
      for r in rows do
        set { outside with exprs := {}, entries := {}, currents := {}, contracts := [],
                           spanEntries := {}, declarations := {}, exprsAt := {} }
        let _ ← walkLambda env e (some r) none true
        let inside ← get
        interiors := interiors ++ [{
          exprs := inside.exprs.toList.map (fun (sp, _, A) => (sp, A))
          envs := inside.entries.toList.map (fun (p, vs) => (p, vs.map fun (n, A) => (n, .ok A)))
          entryCurrent := inside.currents.toList
          contracts := inside.contracts.map (fun (key, A) => (key, .ok A)) }]
      set { outside with arrowClaims := upd outside.arrowClaims e.span interiors }
      return ← record e (.ok (ctx.getD []))
    record e (.ok (← literalRows e.span a qs ctx sig.isSome rest))
  | _, _, _ => record e (.error "a function value: a parameter or its result undetermined")

/-- Bind a pattern's names to the parts of a value of type `A` (none where
`A` is undetermined). -/
partial def bindPattern (env : Env) (p : Pattern Expr) (A : Option (Ty Tree))
    (origin : Option (String × List PropKey) := none) : W Env := do
  match p with
  | .name n namePos =>
    -- A name at its value's own span (a defaulted parameter's binding)
    -- keeps the value's record there.
    if !(← get).exprs.contains namePos then
      recordAt namePos "identifier" (match A with
        | some A => .ok A
        | none => .error "the bound value undetermined")
    match A with
    | some A => return { env with vars := upd env.vars n A, decl := upd env.decl n A }
    | none => return { env with vars := env.vars.filter (·.1 != n) }
  | .object pos props rest =>
    -- A nested pattern's value at its span (a parameter's pattern's is its
    -- parameter's read there).
    if !(← get).exprs.contains pos then
      recordAt pos "other" (match A with | some A => .ok A | none => .error "the bound value undetermined")
    let mut env := env
    for (key, q, d) in props do
      let path := origin.map fun (root, pre) => (root, pre ++ [.str key])
      let B ← match path.bind (env.paths.lookup ·), A with
        | some B, _ => pure (some B)
        | none, A => match A with
          | some A => StateT.lift (tryCatch (some <$> readField env.vars A (.str key)) fun _ => pure none)
          | none => pure none
      -- A defaulted part's read keeps the original field type at its span;
      -- its binding receives the value after the default (binding_analysis.ml:61).
      if let (some _, some B) := (d, B) then
        let sp := match q with | .name _ sp | .object sp .. | .array sp .. => sp
        if !(← get).exprs.contains sp then recordAt sp "other" (.ok B)
      let (B, e') ← withDefault env B d
      env ← bindPattern e' q B (if d.isNone then path else none)
    if let some (rp, q) := rest then
      -- The rest: a fresh object of the value's own fields but the named
      -- keys, at their types (`Object.assign`'s copy of one record).
      -- (`TSCERT_FORCE=spreads`: the copies with every key stated)
      let forced := (← get).force.contains "spreads"
      let R ← match A with
        | some A => StateT.lift (tryCatch (do
            let A ← boundOf A
            let G ← graphNow
            match PositiveRules.expand G A with
            | [.callable fs _ _ _ _] =>
              let named := props.map fun (k, _, _) => PropKey.str k
              Except.ok <$> prim (.refs (fs.filter fun (k, _) => !named.contains k) [] [])
            | [.refs fs [] vs [] ms _ _] =>
              if (fs ++ vs).any (·.1 == SourceTypes.storeField) then
                let cs ← copiesOf A forced
                let Rs ← cs.mapM copyType
                return .ok (norm Rs.flatten)
              let named := props.map fun (k, _, _) => PropKey.str k
              let fields := (fs ++ vs).filter fun (f, _) => f != SourceTypes.protoField &&
                f != SourceTypes.storeField && !ms.any (·.key == f) && !named.contains f
              Except.ok <$> prim (.refs fields [] [] [] [] [])
            | _ =>
              -- Any other value: the copies it gives as a spread's operand
              -- (`copiesOf`: each record arm's, a class value's static
              -- fields, a function's none), but the named keys.
              let named := props.map fun (k, _, _) => PropKey.str k
              let cs ← copiesOf A forced
              if cs.isEmpty then return .error "a rest of a value of no record contract"
              let Rs ← cs.mapM fun c => copyType { c with fields := c.fields.filter fun (k, _, _) => !named.contains k }
              return .ok (norm Rs.flatten)) fun m => pure (.error m))
        | none => pure (.error "the bound value undetermined")
      recordAt rp "other" R
      env ← bindPattern env q R.toOption
    return env
  | .array pos elems rest =>
    if !(← get).exprs.contains pos then
      recordAt pos "other" (match A with | some A => .ok A | none => .error "the bound value undetermined")
    let mut env := env
    for (i, q, d) in elems do
      let B ← match A with
        | some A => StateT.lift (tryCatch (some <$> elementAt A (some i)) fun _ => pure none)
        | none => pure none
      if let (some _, .name _ np, some B) := (d, q, B) then
        if !(← get).exprs.contains np then recordAt np "identifier" (.ok B)
      let (B, e') ← withDefault env B d
      env ← bindPattern e' q B
    if let some (k, rp, slice, q) := rest then
      let R ← restOf env A k rp slice
      env ← bindPattern env q R
    return env

/-- An array pattern's rest after `k` positions of a value of type `A`,
recorded at its span `rp`: a slice rest the call of `%RestFrom:k%` at `A`
(its intrinsic read at the `...`); any other the fresh array of the
positions of `A`'s tuple from `k` on. -/
partial def restOf (env : Env) (A : Option (Ty Tree)) (k : Nat) (rp : Span) (slice : Bool) : W (Option (Ty Tree)) := do
  let some A := A | return none
  if slice then
    let some g := (← get).generics.lookup (restFromName k) | return none
    let .ok c ← StateT.lift (tryCatch (Except.ok <$> genericCallee g []) fun m => pure (Except.error m)) | return none
    -- Its binder the union of the value's elements from position `k` on,
    -- its rest's included, an optional one's with `undefined` (the
    -- producer's `slice_element`, type_queries.ml:626-638).
    let E ← StateT.lift (tryCatch (do
        let G ← graphNow
        let mut Es : List (Ty Tree) := []
        for l in A do
          let some S := storeOf G [l] | return none
          let [.list t []] := PositiveRules.expand G S | return none
          Es := Es ++ t.required.drop k ++ (t.optional.drop (k - t.required.length)).map (· ++ [Labels.undef]) ++ t.rest.toList
        pure (some (norm Es.flatten))) fun _ => pure none)
    let c := match c.binders, E with
      | [b], some E => { c with seed := c.seed ++ [(b, E)] }
      | _, _ => c
    modify fun w => { w with lastInstance := none, lastResolution := [] }
    let r ← applyCall env c [.var rp "%rest%"] [some A]
    recordAt (rp.1, rp.1 + "...".length) "identifier" ((·.1) <$> r)
    recordAt rp "call" ((·.2) <$> r)
    if let some θ := (← get).lastInstance then
      modify fun w => { w with instances := (rp, θ) :: w.instances, resolutions := (rp, w.lastResolution) :: w.resolutions, lastInstance := none, lastResolution := [] }
    return ((·.2) <$> r).toOption
  let r ← StateT.lift (tryCatch (do
      let G ← graphNow
      let some S := storeOf G A | throw "a rest of a value that is no array"
      let [.list t []] := PositiveRules.expand G S | throw "an array of more than one tuple contract"
      let Es := t.required.drop k
      let Os := t.optional.drop (k - t.required.length)
      Except.ok <$> lower do
        let s ← SourceTypes.use (.list ⟨Es, Os, t.rest, false, .dense⟩ [])
        let T ← get
        return [← SourceTypes.use (SourceTypes.arrayOf T s false)]) fun m => pure (.error m))
  recordAt rp "other" r
  return r.toOption

/-- A part with a default: the part less `undefined`, or the default's. -/
partial def withDefault (env : Env) (B : Option (Ty Tree)) (d : Option Expr) : W (Option (Ty Tree) × Env) := do
  match d with
  | none => return (B, env)
  | some d =>
    -- The default made at the part's type less `undefined` (a parameter's
    -- at its annotation's).
    let X ← match B with
      | some B => do
        let X ← StateT.lift (slice B .isUndef false)
        pure (if X.isEmpty then none else some X)
      | none => pure none
    let (D, e1) ← expr env d X
    match B, D with
    -- The default only where the part may be `undefined`.
    | some B, some D =>
      if (← StateT.lift (slice B .isUndef true)).isEmpty then return (some B, (join (some env) (some e1)).getD e1)
      let Bd ← StateT.lift (slice B .isUndef false)
      -- (a function the default makes within the part's type is held at
      -- that type, an upcast of a function value, whichever value the part
      -- took: a parameter's type is what the body reads, the default
      -- replacing `undefined`, the producer's source.ml:643-646)
      let T ← StateT.lift table
      let G := SourceTypes.graph T
      if !D.isEmpty && within T D Bd && D.all (fun l => !(ProgramTyping.callSigs G [l]).isEmpty) &&
          Bd.all (fun l => !(ProgramTyping.callSigs G [l]).isEmpty) then
        return (some Bd, (join (some env) (some e1)).getD e1)
      -- An object literal default at the part's members it is within: a
      -- store's contract is fixed where it is made (`declaredAt`; the
      -- producer binds a defaulted parameter at its annotation).
      let D ← match d with
        | .alloc .. | .build .. => if Bd.isEmpty then pure D else StateT.lift (declaredAt Bd D)
        | _ => pure D
      return (some (norm (Bd ++ D)), (join (some env) (some e1)).getD e1)
    | _, _ => return (none, e1)

/-- Walk statements from `env` (none: unreached), recording each statement
entry; the environment where the list completes, none where it does not. -/
partial def stmts (env : Option Env) (ss : List Stmt) : W (Option Env) := do
  let mut env := env
  -- The list's early bindings, each allocated at the list's entry (the flow
  -- graph's `.early` node): from there on at its written contract, which
  -- is its storage contract.
  if let some e0 := env then
    let mut e := e0
    for s in ss do
      let bs := match s with
        | .constants _ bs | .mutables _ bs => bs
        | _ => []
      for b in bs.filter (·.early) do
        if let some D ← earlyContract b then
          modify fun w => { w with contracts := w.contracts ++ [((b.init.span, b.name), D)] }
          e := { e with vars := upd e.vars b.name D, decl := upd e.decl b.name D }
    env := some e
  let mut prev : Option Stmt := none
  for (s, i) in ss.zipIdx do
    let some e := env | return none
    -- (`TSCERT_FORCE=reads`: a read's receiver kept present whatever ends it)
    let forced := (← get).readForced
    let e ← if forced.isEmpty then pure e else do
      let G ← StateT.lift graphNow
      pure { e with vars := e.vars.map fun (n, A) => if forced.contains n then (n, present G A) else (n, A) }
    -- (`TSCERT_FORCE=paths`: each path narrowed so far kept narrowed)
    let w ← get
    let e := if !w.force.contains "paths" then e else
      { e with paths := e.paths ++ (w.pathsForced.filter fun (p, _) => (e.paths.lookup p).isNone) }
    if w.force.contains "paths" then
      modify fun w => { w with pathsForced := w.pathsForced ++ e.paths.filter fun (p, _) => (w.pathsForced.lookup p).isNone }
    -- A `for`'s loop, right after its declarations, has its head's entry at
    -- the `for`'s start, the declarations' position: there the bindings
    -- the loop's entry holds, then the declarations' entry's.
    let at_ := match prev, s with
      | some (.mutables p _), .loop q .. | some (.constants p _), .loop q .. => if p.2 == q.1 then p.1 else s.pos.1
      | _, _ => s.pos.1
    -- A loop's entry is its head's: each binding the loop assigns at its
    -- declared type (`loopHead`).
    let vars := match s with
      | .loop _ c body update _ => (loopHead e (.effect c.span c :: body ++ update)).vars
      | _ => e.vars
    modify fun w =>
      let earlier := if at_ == s.pos.1 then [] else
        ((w.entries.get? at_).getD []).filter fun (n, _) => (vars.lookup n).isNone
      let current := match s with
        | .loop .. | .forOf .. => []
        | _ => currentOf e
      { w with entries := (w.entries.insert s.pos.1 vars).insert at_ (vars ++ earlier),
               spanEntries := w.spanEntries.insert s.pos (vars, current) }
    -- The narrowed paths of an entry no loop's head is (a `for`'s head
    -- shares its declarations' entry).
    match s with
    | .loop .. | .forOf .. => modify fun w => { w with currents := w.currents.erase at_ }
    | _ => if !e.paths.isEmpty then modify fun w => { w with currents := w.currents.insert s.pos.1 (currentOf e) }
    -- An array pattern's element bindings (`let %v0 = undefined, …`,
    -- `protocolPattern`, tools/fragment-statements.mts) before the
    -- protocol's `%next`: each an evolving `let` holding what a step not done
    -- yields (statement_analysis.ml:222-240), at `undefined` or that, the
    -- step's type read off the next statement, walked ahead.
    if let .mutables _ bs := s then
      if !bs.isEmpty && bs.all (fun b => b.name.startsWith "%v" && b.annot.isNone &&
          (match b.init with | .lit _ .vundef => true | _ => false)) then
        let tag := (((bs.head?.map (·.name)).getD "").splitOn "@").getLast!
        let rest := ss.dropWhile (·.pos != s.pos)
        if let some next@(Stmt.constants _ _) := rest[1]? then
          let saved ← get
          let ahead ← match ← stmt e s with
            | some e' => stmt e' next
            | none => pure none
          set saved
          if let some N := ahead.bind (·.vars.lookup s!"%next@{tag}") then
            if let some E ← StateT.lift (tryCatch (stepValue N) fun _ => pure none) then
              modify fun w => { w with collected := bs.map (·.name, norm (E ++ [Labels.undef])) ++ w.collected }
    let outer := (← get).stmtAt
    modify fun w => { w with stmtAt := s.pos }
    let before := (← get).valueWrites
    let following := (← get).following
    modify fun w => { w with following := ss.drop (i + 1) }
    env ← stmt e s
    modify fun w => { w with following }
    -- A cell's narrowed contents end at a change of a value location: a
    -- current-content fact no separation keeps (the producer's entries
    -- after a write; PROGRAM-TYPING, "No general frame rule").
    -- (`TSCERT_FORCE=cells` keeps them)
    let w ← get
    if w.valueWrites != before then
      env := env.map (cellsDeclared w)
    -- A loop's kept paths, at its head's entry and its body's.
    if let some (body, update) := (match s with
        | .loop _ _ body update _ => some (body, update)
        | .forOf _ _ _ _ _ body => some (body, [])
        | _ => none) then
      let kept := (← get).loopKept
      if !kept.isEmpty then
        let ps := s.pos :: ownStmts (body ++ update)
        modify fun w => { w with
          loopKept := []
          currents := (at_ :: ps.map (·.1)).eraseDups.foldl (fun m k => m.insert k (withPaths kept ((m.get? k).getD []))) w.currents
          spanEntries := ps.foldl (fun m sp => match m.get? sp with
            | some (vs, cs) => m.insert sp (vs, withPaths kept cs)
            | none => m) w.spanEntries }
    if (← get).force.contains "paths" then
      if let some e' := env then
        modify fun w => { w with pathsForced := w.pathsForced ++ e'.paths.filter fun (p, _) => (w.pathsForced.lookup p).isNone }
    modify fun w => { w with stmtAt := outer }
    prev := some s
  return env

/-- A function literal a constant holds that reads the constant (its self
entry, SOURCE-ELABORATION.md, "Recursive constants"): walked with the
constant at its written type, else at its written signature changing
nothing and bounding its throws, raised to the type the walk gives it until
the two agree (the producer's `raise_selves`), at most four rounds: the
footprint of each class of contents only rises and `onThrow` only falls. -/
partial def recursiveConstant (env : Env) (b : Fragment.Binding) (written : Bool) :
    W (Option (Ty Tree) × Env) := do
  -- An early self is read through its cell at the early contract
  -- (statement_analysis.ml:289-293), rather than a self-entry proposal.
  let some S0 ← earlyContract b (if b.early then .ordinary else
      { CallEffects.Effect.ofFootprint ⟨.keep, .keep⟩ with onThrow := true })
    | expr env b.init
  -- An annotation supplies the signature, not the self-effect seed:
  -- statement_analysis.ml:294-317 seeds every non-early self at keep/keep.
  let S0 ← if b.early || b.annot.isNone then pure S0 else StateT.lift do
    let G ← graphNow
    match PositiveRules.expand G S0 with
    | [.arrs L S] =>
      let seed (e : CallEffects.Effect) : CallEffects.Effect :=
        { e with closed := ⟨.keep, .keep⟩, onThrow := true }
      lower (do return [← SourceTypes.use (.arrs
        (L.map fun a => { a with effect := seed a.effect })
        (S.map fun a => { a with effect := seed a.effect }))])
    | _ => pure S0
  -- Its self reads are uses of the constant as any other read is: each
  -- offers the literal a longer signature it is expected at
  -- (`offerUse`), and where the walk states offered rows at the literal,
  -- the self entry holds the literal's whole type, those rows included.
  if let .lambda _ _ [] _ _ false _ _ _ _ _ _ := b.init then
    let G := SourceTypes.graph (← StateT.lift table)
    if let ([own], []) := (ProgramTyping.callSigs G S0, ProgramTyping.restSigs G S0) then
      modify fun w => { w with closureConsts := (b.name, b.init.span, own.arguments) :: w.closureConsts }
  let offered := (← get).offers.any (·.1 == b.init.span) || (← get).restOffers.any (·.1 == b.init.span)
  let w0 ← get
  let mut S := S0
  for _ in [0:4] do
    set w0
    let (A, e1) ← expr { env with vars := upd env.vars b.name S, decl := upd env.decl b.name S } b.init (if b.annot.isSome then some S else none)
    let some L := A | return (A, e1)
    if (written && b.annot.isNone && !offered) || b.early || sameMeaning (← StateT.lift table) L S then return (A, e1)
    S := L
  set w0
  return (← record b.init (.error "not handled: a recursive closure's effect undetermined"), env)

partial def stmt (env : Env) (s : Stmt) : W (Option Env) := do
  match s with
  | .ret p x =>
    -- The value's entry, where a finalizer holds the return (the flow
    -- graph's `.returnHeld`): the statement's bindings.
    modify fun w => { w with entries := w.entries.insert x.span.1 env.vars }
    if let some P := (← get).expected then modify fun w => { w with hints := (x.span, P) :: w.hints }
    let before := (← get).valueWrites
    let (A, _) ← expr env x (← get).expected
    -- The finalizers it passes run after its value: each cell at its
    -- declared type where evaluating the value changes a value location.
    let w ← get
    let held := if w.valueWrites != before then cellsDeclared w env else env
    modify fun w => { w with held := (p, x.span, held) :: w.held }
    if !env.ghost then modify fun w => { w with returns := w.returns ++ [A] }
    return none
  | .throw _ x =>
    let before ← get
    let _ ← expr env x
    -- With no enclosing handler and outside async completion, neither
    -- the throw nor its operand has a normal exit (source.ml:1140-1144).
    -- Keep its throw effect, and every expression claim, for the checker.
    if !before.caught && !before.asyncBody then
      modify fun w => { w with writes := before.writes, valueChange := before.valueChange, storeChange := before.storeChange }
    return none
  | .effect _ x =>
    let added := match x with
      | .write _ k (.var _ n) _ => some (n, k)
      | .indexWrite _ _ (.var _ n) (.lit _ (.vstr k)) _ => some (n, PropKey.str k)
      | _ => none
    let hint ← match added with
      | some (n, k) => do
        let uses ← useHints env n (← get).following false true
        match uses.head? with
        | some P => StateT.lift (fieldExpected P k)
        | none => pure none
      | none => pure none
    let (A, e1) ← expr env x hint
    let w ← get
    let e1 := match x, A with
      | .objectAssign _ (.var _ n) _, some A =>
        if w.consts.contains n then { e1 with vars := upd e1.vars n A } else e1
      | _, _ => e1
    -- A value of no type (a call of a function returning `never`): the
    -- statement does not complete; what follows is walked for its entries,
    -- unreached, each binding at the empty type (the producer's
    -- `unreachable`, environment.ml:91, proposal_flow.ml:347).
    -- (`TSCERT_FORCE=never`: every call's statement so, whatever it returns)
    let forced := (← get).force.contains "never" && match x with
      | .call .. | .callWithReceiver .. | .invoke .. => true
      | _ => false
    if A == some [] || forced then return some { e1 with ghost := true, vars := e1.vars.map fun (n, _) => (n, []) }
    -- An assertion function's normal return: its promise holds.
    match x with
    | .call _ callee args _ _ | .callWithReceiver _ callee _ args | .invoke _ callee args _ _ =>
      return some (← promised e1 callee args true)
    | _ => return some e1
  | .constants p bs =>
    -- A spread's or an array pattern's collected array (`collect`,
    -- `protocolPattern`, tools/fragment-statements.mts: `const %items = [],
    -- %iterator = …, %next = …`, the values pushed onto it): an unannotated
    -- `[]` whose elements the protocol's steps write, made at the array of
    -- the values a step not done yields, the evolving array's type
    -- (statement_analysis.ml:222-230), the step's type read off the
    -- statement's other bindings, walked ahead.
    let collected ← match bs with
      | b0 :: rest@(_ :: _) =>
        match b0.init with
        | .arrayLit _ [] [] =>
          if b0.annot.isSome || !(b0.name.startsWith "%items@" || b0.name.startsWith "%rest@") then pure none else do
          let saved ← get
          let ahead ← stmt env (.constants p rest)
          set saved
          let tag := (b0.name.splitOn "@").getLast!
          let some N := ahead.bind (·.vars.lookup s!"%next@{tag}") | pure none
          StateT.lift (tryCatch (do
            let some E ← stepValue N | return none
            return some (← lower do
              let s ← SourceTypes.use (.list ⟨[], [], some E, false, .readable⟩ [])
              let T ← get
              return [← SourceTypes.use (SourceTypes.arrayOf T s false)])) fun _ => pure none)
        | _ => pure none
      | _ => pure none
    let mut env := env
    modify fun w => { w with
      consts := bs.map (·.name) ++ w.consts
      conditions := (bs.filter (fun b => implicationForm b.init || w.force.contains "implications")).map (fun b => (b.name, b.init)) ++
        w.conditions.filter fun (n, _) => !bs.any (·.name == n)
      allocated := (bs.filter fun b => match b.init with | .alloc .. | .arrayLit .. => true | _ => false).map (·.name) ++ w.allocated }
    -- An early binding's declaration writes its cell (a declaration's
    -- footprint).
    if (← get).strict && bs.any (·.early) then wrote .any .keep
    for b in bs do
      modify fun w => { w with holders := w.holders.filter (fun (a, c) => a != b.name && c != b.name) }
      if let .var _ n := b.init then
        modify fun w => { w with holders := (b.name, n) :: w.holders }
      modify fun w => { w with declarations := w.declarations.insert (p.1, b.name) env.vars }
      let written ← match b.annot with
        | some ty => StateT.lift (tryCatch (some <$> lower (Fragment.translate ty)) fun _ => pure none)
        | none => pure (if b.name.startsWith "%items@" || b.name.startsWith "%rest@" then collected else none)
      if b.annot.isNone && (← get).following.any (generalArrayUse b.name) then
        modify fun w => { w with generalCalls := b.init.span :: w.generalCalls }
      let written ← declarationHint env b false written
      if let some D := written then modify fun w => { w with hints := (b.init.span, D) :: w.hints }
      if b.name.endsWith ".[[class]]" then modify fun w => { w with freshClass := true }
      -- The initializer made at the annotation's type.
      modify fun w => { w with lastFresh := false }
      let (A, e1) ← match b.init with
        | .lambda _ _ _ _ _ _ _ _ stated _ _ _ =>
          if b.init.freeNames.contains b.name then recursiveConstant env b (b.annot.isSome || stated.isSome)
          else expr env b.init written
        | _ => expr env b.init written
      -- A module constant, unannotated, holding a literal of no type
      -- parameters, rest, defaults or guard whose result is written: also
      -- at its signature extended by a rest of `unknown`, its code
      -- discarding the further actuals, as a module function's slot is (the
      -- producer's, proposal.ml:320-327, module_contract.ml:34-38).
      let mut A₀ := A
      if let (.lambda _ _ [] _ [] false (some _) none _ _ _ _, some L, none, true, false) :=
          (b.init, A, b.annot, (← get).moduleInit, (← get).inLiteral) then
        let G := SourceTypes.graph (← StateT.lift table)
        if let ([own], []) := (ProgramTyping.callSigs G L, ProgramTyping.restSigs G L) then
          let U ← StateT.lift (prim .source)
          let L' ← StateT.lift (lower do
            let pack ← SourceTypes.use (.pack ⟨[], [], some U, false, .dense⟩ [])
            let r : CallEffects.RestArrow (Ty Tree) := ⟨own.receiver, (own.arguments, [pack]), own.result, own.effect⟩
            return [← SourceTypes.use (.arrs [own] [r])])
          let _ ← record b.init (.ok L')
          A₀ := some L'
      let A := A₀
      modify fun w => { w with freshClass := false }
      -- A constant holding a store the run allocated.
      let w ← get
      let fresh := match b.init with
        | .var _ m => w.freshConsts.contains m
        | .call .. | .invoke .. => w.lastFresh
        | _ => false
      let fcs := if fresh then b.name :: w.freshConsts else w.freshConsts.filter (· != b.name)
      modify fun w => { w with lastFresh := false, freshConsts := fcs }
      env := e1
      -- A literal of no type parameters and no rest, unannotated or
      -- annotated at one signature, whose uses may offer it more rows.
      if let (.lambda _ _ [] _ _ false _ _ _ _ _ _, some L) := (b.init, A) then
        let G := SourceTypes.graph (← StateT.lift table)
        let single := match written with
          | some D => (ProgramTyping.callSigs G D).length == 1 && (ProgramTyping.restSigs G D).isEmpty
          | none => true
        if single then
          if let some own := (ProgramTyping.callSigs G L).head? then
            modify fun w => { w with closureConsts := (b.name, b.init.span, own.arguments) :: w.closureConsts }
      registerNamed b
      let D := if b.annot.isSome || written.isSome then written else A
      match D, A with
      | some D, some A =>
        -- (an early binding, read through its cell from the list's entry
        -- on, stays at its written contract: its declaration writes the
        -- cell, whose contents every later read checks against it, the
        -- producer's early declaration, proposal_flow.ml:317-327)
        -- (`TSCERT_FORCE=early`: at its initializer's type, the adversarial
        -- proposal)
        match (if b.early && !(← get).force.contains "early" then env.decl.lookup b.name else none) with
        | some C => env := { env with vars := upd env.vars b.name C }
        | none =>
          let held ← StateT.lift (if b.annot.isSome then declaredAt D A else assigned D A)
          env := { env with vars := upd env.vars b.name held, decl := upd env.decl b.name D }
      | some D, none => env := { env with vars := upd env.vars b.name D, decl := upd env.decl b.name D }
      | none, _ => env := { env with vars := env.vars.filter (·.1 != b.name) }
    return some env
  | .mutables p bs =>
    let mut env := env
    modify fun w => { w with
      consts := w.consts.filter (fun n => !bs.any (·.name == n))
      conditions := w.conditions.filter fun (n, _) => !bs.any (·.name == n) }
    modify fun w => { w with freshConsts := w.freshConsts.filter fun n => !bs.any (·.name == n) }
    if (← get).strict && bs.any (·.early) then wrote .any .keep
    for b in bs do
      modify fun w => { w with holders := w.holders.filter (fun (a, c) => a != b.name && c != b.name) }
      modify fun w => { w with declarations := w.declarations.insert (p.1, b.name) env.vars }
      let written ← match b.annot with
        | some ty => StateT.lift (tryCatch (some <$> lower (Fragment.translate ty)) fun _ => pure none)
        | none => pure none
      -- (a pattern's collected binding at the contract its steps give it)
      let written := written <|> (← get).collected.lookup b.name
      let written ← declarationHint env b true written
      if let some D := written then modify fun w => { w with hints := (b.init.span, D) :: w.hints }
      -- The initializer made at the annotation's type.
      let (A, e1) ← expr env b.init written
      env := e1
      let D ← match written, A with
        | some _, _ => pure written
        | none, some A => do
          let A ← StateT.lift (widen A)
          let w ← get
          let evolved := match w.evolving.lookup b.name with
            | some (key, false) => if w.force.contains "evolving" then [] else (w.assumed.lookup key).getD []
            | _ => []
          pure (some (norm (A ++ evolved)))
        | none, none => pure none
      if let some D := D then
        modify fun w => { w with contracts := ((b.init.span, b.name), D) :: w.contracts }
      match D, A with
      | some D, some A =>
        -- Initializing an early cell keeps its entry contract; later reads
        -- run through that cell (proposal_flow.ml:317-327).
        let held ← if b.early && !(← get).force.contains "early-contracts" then pure D
          else StateT.lift (if b.annot.isSome then declaredAt D A else assigned D A)
        env := { env with vars := upd env.vars b.name held, decl := upd env.decl b.name D }
      | some D, none => env := { env with vars := upd env.vars b.name D, decl := upd env.decl b.name D }
      | none, _ => env := { env with vars := env.vars.filter (·.1 != b.name) }
    return some env
  | .destructure _ target d init =>
    let (A, e1) ← expr env init
    let (A, e2) ← withDefault e1 A d
    return some (← bindPattern e2 target A (if d.isNone then memberPath init else none))
  | .ite _ c thn els =>
    let (_, e1) ← expr env c
    let arm (q : Bool) (ss : List Stmt) : W (Option Env) := do
      let r ← refine e1 c q
      -- An answer the test's value cannot give (`if (true)`'s `false`): the
      -- arm unreached, walked for its entries.
      if ← decidedTest c q then return ← stmts (some { r with ghost := true }) ss
      match emptiedBy e1 r with
      | some walked => stmts (some walked) ss
      | none => stmts (some r) ss
    let t ← arm true thn
    let f ← arm false (els.getD [])
    return join t f
  | .brk _ label =>
    modify fun w => { w with breaks := (label, env) :: w.breaks }
    return none
  | .cont _ =>
    modify fun w => { w with continues := env :: w.continues }
    return none
  | .loop _ c body update _ =>
    -- The paths narrowed before the loop that nothing in it can end, held
    -- from its head on: the root no binding the loop declares or assigns,
    -- and either nothing in the loop calling or writing, or each member of
    -- the path stable (`stablePath`), as after a call. The pass checks them
    -- at the head's entry, from each edge into it.
    let all := .effect c.span c :: body ++ update
    let declared := declaredIn (body ++ update)
    let quiet := all.all quietStmt
    let early ← if (← get).force.contains "loops" then pure [] else
      StateT.lift (env.paths.filterM fun ((r, p), _) => do
        if declared.contains r || all.any (assignsStmt r) then return false
        if quiet then return true
        stablePath env r p)
    let head := keepPaths early (loopHead env all)
    let savedEnds := (← get).pathEnds
    modify fun w => { w with pathEnds := [] }
    let (_, e1) ← expr head c
    let saved := (← get).breaks
    let savedContinues := (← get).continues
    modify fun w => { w with breaks := [], continues := [] }
    let b ← stmts (some (← refine e1 c true)) body
    -- The update runs after the body's end and after each `continue`.
    let continued := (← get).continues.foldl (fun acc c => join acc (some c)) b
    modify fun w => { w with continues := savedContinues }
    let _ ← stmts (some (continued.getD head)) update
    let out ← collectBreaks none saved
    -- A test that cannot answer `false` (`while (true)`): left by its breaks
    -- alone.
    let noExit ← decidedTest c false
    -- Past the loop, the paths narrowed before it that nothing in its test,
    -- body and update ends.
    let evs := (← get).pathEnds
    -- (`TSCERT_FORCE=loops`: every path kept, whatever ends it)
    let evs := if (← get).force.contains "loops" then [] else evs
    let kept := early ++ ((surviving env evs).filter fun ((r, p), _) => !declared.contains r && (early.lookup (r, p)).isNone)
    modify fun w => { w with pathEnds := evs ++ savedEnds, loopKept := kept }
    let keep := keepPaths kept
    if noExit then return out.map keep
    return join (some (keep (← refine e1 c false))) (out.map keep)
  | .block _ label body =>
    match label with
    | none => stmts (some env) body
    | some l =>
      let saved := (← get).breaks
      modify fun w => { w with breaks := [] }
      let r ← stmts (some env) body
      -- Unlabeled breaks inside go to an enclosing loop.
      let out ← collectBreaks (some l) saved
      return join r out
  | .forOf p name namePos it iterable body =>
    let (I, e1) ← expr env iterable
    -- A generic iteration intrinsic's instance: its call at the iterable,
    -- the stepper it gives held at the loop's head (`%next@…%`) and its
    -- one binder kept as a fallback where no stepper is available.
    let mut stepper : Option (Ty Tree) := none
    let mut bound : Option (Ty Tree) := none
    -- An iteration's throw is bounded by no footprint here.
    if (← get).strict then
      modify fun w => { w with throwWrites := true }
    if let some g := (← get).generics.lookup it then
      let c? : Except String Callee ← StateT.lift (tryCatch (Except.ok <$> genericCallee g []) fun m => pure (Except.error m))
      if let .ok c := c? then
        modify fun w => { w with lastInstance := none, lastResolution := [] }
        let r ← applyCall e1 c [iterable] [I]
        -- The call at the loop's span, its intrinsic read at the `for`
        -- keyword (`Stmt.callees`).
        recordAt (p.1, p.1 + "for".length) "identifier" ((·.1) <$> r)
        recordAt p "call" ((·.2) <$> r)
        stepper := ((·.2) <$> r).toOption
        if let some θ := (← get).lastInstance then
          if let [(_, A)] := θ then bound := some A
          modify fun w => { w with instances := (p, θ) :: w.instances, resolutions := (p, w.lastResolution) :: w.resolutions, lastInstance := none, lastResolution := [] }
    -- An intrinsic of no binders (a string's, `%Iterate:string%`): its call
    -- at the iterable likewise, the stepper it gives at the loop's head.
    else if let some F := e1.vars.lookup it then
      let c? : Except String Callee ← StateT.lift (tryCatch (Except.ok <$> calleeOf F [Labels.undef]) fun m => pure (Except.error m))
      if let .ok c := c? then
        if c.binders.isEmpty then
          let r ← applyCall e1 c [iterable] [I]
          recordAt (p.1, p.1 + "for".length) "identifier" (.ok F)
          recordAt p "call" ((·.2) <$> r)
          stepper := ((·.2) <$> r).toOption
    -- For a declaration's footprint, the iteration changes what its
    -- intrinsic's call states (`applyCall`) and what each step of the
    -- stepper it gives does: the values where a step changes its receiver's
    -- own locations, the iterator the call made, else its footprint (the
    -- producer's `iteration_footprint`, source.ml:939-950); an iteration
    -- whose stepper the walk does not determine may change anything.
    if (← get).strict then
      match stepper with
      | some N =>
        let G ← StateT.lift graphNow
        let steps := (ProgramTyping.callSigs G N).map (·.effect) ++ (ProgramTyping.restSigs G N).map (·.effect)
        if steps.isEmpty then wrote .any .any
        for eff in steps do
          if eff.receiverOwn then wrote .any eff.footprint.store
          else if eff.footprint != ⟨.keep, .keep⟩ then wrote eff.footprint.value eff.footprint.store
      | none => wrote .any .any
    let exit := loopHead e1 body
    let head := match stepper with
      | some N => { exit with vars := upd exit.vars s!"%next@{p.1}%" N, decl := upd exit.decl s!"%next@{p.1}%" N }
      | none => exit
    modify fun w => { w with entries := w.entries.insert p.1 head.vars }
    -- The yielded value is the step result's field, not necessarily the
    -- intrinsic's binder: ForIn yields a key/value pair
    -- (statement_analysis.ml:765-779).
    let elem ← match stepper, bound, I with
      | some N, _, _ => StateT.lift (tryCatch (do
          let some s := (← callSigsOf N).head? | throw "no step"
          some <$> readField [] (← nonNullish s.result) (PropKey.str "value")) fun _ => pure none)
      | none, some A, _ => pure (some A)
      | none, none, some I => StateT.lift (tryCatch (some <$> elementAt I none (missing := false)) fun _ => pure none)
      | none, none, none => pure none
    -- An adversarial yield narrower than the iterator's value contract.
    let elem ← if (← get).force.contains "iteration-values" then
        pure (some (← StateT.lift (prim (.numLit 0)))) else pure elem
    recordAt namePos "identifier" (match elem with | some A => .ok A | none => .error "the element undetermined")
    let inner := match elem with
      | some A => { head with vars := upd head.vars name A, decl := upd head.decl name A }
      | none => { head with vars := head.vars.filter (·.1 != name) }
    let saved := (← get).breaks
    modify fun w => { w with breaks := [] }
    let savedEnds := (← get).pathEnds
    modify fun w => { w with pathEnds := [] }
    let _ ← stmts (some inner) body
    let out ← collectBreaks none saved
    -- Past the loop, over an array (whose native iterator's steps change
    -- only the iterator), the paths narrowed before it that nothing in its
    -- body, nor the element's assignment, ends.
    let evs := (← get).pathEnds
    modify fun w => { w with pathEnds := evs ++ savedEnds }
    let G ← StateT.lift graphNow
    let overArray := match I with
      | some I => !I.isEmpty && (arrayArms G I).length == I.length
      | none => false
    let declared := declaredIn body
    let forced := (← get).force.contains "loops"
    let allocated := (← get).allocated
    let kept ← if overArray || forced then
        (surviving e1 (if forced then [] else .root name :: evs)).filterM fun ((r, p), _) => do
          if declared.contains r then return false
          if forced then return true
          return !allocated.contains r && (← StateT.lift (separatedPath e1 r p))
      else pure []
    modify fun w => { w with loopKept := kept }
    let keep := keepPaths kept
    return join (some (keep exit)) (out.map fun o => keep { o with vars := o.vars.filter (·.1 != s!"%next@{p.1}%") })
  | .tryStmt p body handler finalizer =>
    if finalizer.isSome && (← get).strict then modify fun w => { w with throwWrites := true }
    let outer := (← get).caught
    if handler.isSome || finalizer.isSome then modify fun w => { w with caught := true }
    -- The jumps and returns the statement's body and handler leave by (each
    -- through the finalizer: a copy of it per route, `SourceFlow.sequence`).
    let w0 ← get
    let b ← stmts (some env) body
    modify fun w => { w with caught := outer || finalizer.isSome }
    -- A handler's entry: each binding the body assigns at its declared
    -- type, and each cell (a throw keeps no current-content fact).
    let reset := cellsDeclared (← get) (loopHead env body)
    let h ← match handler with
      | some (param, hs) =>
        let unknown ← StateT.lift (prim .source)
        let hEnv := match param with
          | some (n, _) => { reset with vars := upd reset.vars n unknown, decl := upd reset.decl n unknown }
          | none => reset
        stmts (some hEnv) hs
      | none => pure none
    modify fun w => { w with caught := outer }
    let joined := if handler.isSome then join b h else b
    match finalizer with
    | some fs =>
      let w1 ← get
      let nb := w1.breaks.length - w0.breaks.length
      let nc := w1.continues.length - w0.continues.length
      let nr := w1.held.length - w0.held.length
      -- The finalizer's entry, which every copy but a return's shares: the
      -- statement's normal completion, a throw of its body or handler (each
      -- binding they assign at its declared type), and each jump passing it.
      let thrown := cellsDeclared (← get) (loopHead env (body ++ (handler.map (·.2)).getD []))
      let routes := (w1.breaks.take nb).map (·.2) ++ w1.continues.take nc
      -- (`TSCERT_FORCE=finally`: the statement's normal completion alone)
      let entry := if (← get).force.contains "finally" then some (joined.getD thrown) else
        routes.foldl (fun acc e => join acc (some e)) (join joined (some thrown))
      let f ← stmts entry fs
      -- Each return's own copy (its scope holds the return, `%return@p%`),
      -- walked from the return's bindings: its statements' entries, read
      -- by that copy's points, and its bindings where it completes.
      let positions := ((ownStmts fs).map (·.1)).eraseDups
      let mut copies : List (Span × Span × Option Env) := []
      for (q, xs, e) in w1.held.take nr do
        let saved ← get
        let fq ← stmts (some e) fs
        let walked := (← get).entries
        set saved
        recordCopy positions s!"%return@{q.1}%" walked
        copies := copies ++ [(q, xs, fq.map fun fe => { fe with ghost := fe.ghost || e.ghost })]
      -- After the finalizer: at the statement's start (its rethrow, and the
      -- dead end of a body that never completes, `SourceFlow.sequence`), at
      -- each return's held value, and each jump leaving with it; where a
      -- copy never completes, what follows it is not reached.
      modify fun w =>
        let atEnd := fun (e : Env) => match f with
          | some fe => some { fe with ghost := fe.ghost || e.ghost }
          | none => none
        let after := fun (g : Option Env) (vs : List (String × Ty Tree)) => match g with
          | some ge => ge.vars
          | none => vs.map fun (n, _) => (n, [])
        let cur := fun (g : Option Env) => match g with
          | some ge => currentOf ge
          | none => []
        -- The jumps and returns the finalizer itself makes come first.
        let kb := w.breaks.length - w1.breaks.length
        let kc := w.continues.length - w1.continues.length
        let kr := w.held.length - w1.held.length
        let (ob, pb, rb) := (w.breaks.take kb, (w.breaks.drop kb).take nb, w.breaks.drop (kb + nb))
        let (oc, pc, rc) := (w.continues.take kc, (w.continues.drop kc).take nc, w.continues.drop (kc + nc))
        let (or_, rr) := (w.held.take kr, w.held.drop (kr + nr))
        let entries := w.entries.insert p.1 (after f ((w.entries.get? p.1).getD []))
        let currents := match cur f with
          | [] => w.currents.erase p.1
          | cs => w.currents.insert p.1 cs
        -- A held value at its statement's start (a guard's Boolean return the
        -- parser writes as statements) by its own span (`shared`).
        let (entries, spanEntries, currents) := copies.foldl (fun (m, sm, cm) (q, xs, g) =>
          let vs := after g ((m.get? xs.1).getD [])
          if xs.1 != q.1 then
            (m.insert xs.1 vs, sm, match cur g with | [] => cm.erase xs.1 | cs => cm.insert xs.1 cs)
          else if xs != q then (m, sm.insert xs (vs, cur g), cm) else (m, sm, cm)) (entries, w.spanEntries, currents)
        { w with
          breaks := ob ++ pb.filterMap (fun (l, e) => (atEnd e).map (l, ·)) ++ rb
          continues := oc ++ pc.filterMap atEnd ++ rc
          held := or_ ++ copies.filterMap (fun (q, xs, g) => g.map (q, xs, ·)) ++ rr
          entries, spanEntries, currents }
      return if joined.isNone then none else f
    | none => return joined
  | .closing _ close body =>
    let w0 ← get
    let b ← stmts (some env) body
    let nr := (← get).held.length - w0.held.length
    let _ ← stmts (some (b.getD env)) close
    -- Each return's own copy of the close (a finalizer of the loop, its
    -- scope holding the return, `%return@p%`), walked from the return's
    -- bindings: its statements' entries, read by that copy's points, and
    -- the bindings at the return's held value where it completes.
    let positions := ((ownStmts close).map (·.1)).eraseDups
    let mut copies : List (Span × Span × Option Env) := []
    for (q, xs, e) in (← get).held.take nr do
      let saved ← get
      let fq ← stmts (some e) close
      let walked := (← get).entries
      set saved
      recordCopy positions s!"%return@{q.1}%" walked
      copies := copies ++ [(q, xs, fq.map fun fe => { fe with ghost := fe.ghost || e.ghost })]
    closeCopies nr copies
    return b
end

/-- How a computed type stands to the claimed one. -/
def classify (T : EquationStore.State) (A C : Ty Tree) : String :=
  if within T A C && within T C A then "identical"
  else if within T C A then "wider"
  else if within T A C then "narrower"
  else "unrelated"

/-- The comparison of a walk with a function's claims: per construct kind
and class, the count; and each occurrence that is not identical, with its
span, kind, class and both types rendered, or the reason. -/
def compareWalk (T : EquationStore.State) (fc : SourceClaims.Function Tree) (w : Walk) :
    Std.HashMap (String × String) Nat × Array Json := Id.run do
  let mut counts : Std.HashMap (String × String) Nat := {}
  let mut samples : Array Json := #[]
  let mut seen : Std.HashSet Span := {}
  let bump (m : Std.HashMap (String × String) Nat) (k : String × String) := m.insert k ((m.getD k 0) + 1)
  let raw (A : Ty Tree) : String := reprStr (A.map fun l => (l, PositiveRules.expand (SourceTypes.graph T) [l]))
  for (span, cand) in fc.exprs do
    if seen.contains span then continue
    seen := seen.insert span
    let some C := (SourceClaims.resolve T cand).toOption | continue
    let (kind, r) := (w.exprs.get? span).getD ("unvisited", .error "not reached by the walk")
    let cls := match r with
      | .ok A => classify T A C
      | .error _ => "undetermined"
    counts := bump counts (kind, cls)
    -- Same meaning under other labels: what a syntactic reading of the type
    -- (a clause's form) may still tell apart.
    let other := match r with
      | .ok A => cls == "identical" && norm A != norm C
      | .error _ => false
    if other then
      samples := samples.push (Json.mkObj [("span", toJson span), ("kind", toJson kind), ("class", toJson "same meaning, other labels"),
        ("computed", toJson (match r with | .ok A => reprStr (A.map fun l => PositiveRules.expand (SourceTypes.graph T) [l]) | .error m => m)),
        ("claimed", toJson (reprStr (C.map fun l => PositiveRules.expand (SourceTypes.graph T) [l])))])
    if cls != "identical" then
      samples := samples.push (Json.mkObj [("span", toJson span), ("kind", toJson kind), ("class", toJson cls),
        ("computed", toJson (match r with | .ok A => shown T A | .error m => s!"({m})")),
        ("claimed", toJson (shown T C)), ("computedRaw", toJson (match r with | .ok A => raw A | .error _ => "")),
        ("claimedRaw", toJson (raw C))])
  for (pos, vars) in fc.envs do
    let computed := w.entries.get? pos
    for (n, cand) in vars do
      let some C := (SourceClaims.resolve T cand).toOption | continue
      let r : Except String (Ty Tree) := match computed with
        | none => .error "statement not reached by the walk"
        | some vs => match vs.lookup n with
          | some A => .ok A
          | none => .error s!"binding not held by the walk (held: {vs.map (·.1)})"
      let cls := match r with
        | .ok A => classify T A C
        | .error _ => "undetermined"
      counts := bump counts ("entry", cls)
      if cls != "identical" then
        samples := samples.push (Json.mkObj [("pos", toJson pos), ("name", toJson n), ("kind", toJson "entry"),
          ("class", toJson cls),
          ("computed", toJson (match r with | .ok A => shown T A | .error m => s!"({m})")),
          ("claimed", toJson (shown T C)), ("computedRaw", toJson (match r with | .ok A => raw A | .error _ => "")),
          ("claimedRaw", toJson (raw C))])
  return (counts, samples)

/-- A unit's walk over the store `T`, from its parameters' written types
and the module values `module` it reads: what it records, and the grown
store. -/
def walkUnit (T : EquationStore.State) (f : Fragment.Fn)
    (module : List (String × Compiler (Ty Tree))) (generics : List (String × Generic) := [])
    (force : List String := []) (scope : Option (PositiveGraphs.SchemeRow Tree × List String) := none)
    (strict : Bool := false) (schemes : List (Span × Ty Tree) := []) :
    Except String (Walk × EquationStore.State) := do
  let action : Compiler (Walk × EquationStore.State) := do
    let mut vars : List (String × Ty Tree) := []
    for (n, ty) in module do
      match ← tryCatch (some <$> ty) fun _ => pure none with
      | some A => vars := upd vars n A
      | none => pure ()
    for p in f.params do
      match ← tryCatch (some <$> lower (Fragment.translate p.ty)) fun _ => pure none with
      | some A => vars := upd vars p.name A
      | none => pure ()
    let env : Env := { vars, decl := vars }
    let expected ← tryCatch (some <$> lower (Fragment.translate f.ret)) fun _ => pure none
    -- Its own parameters and declarations are its locals: assigning one
    -- changes no heap location.
    -- (but one held in a cell, which a closure shares, for a declaration's
    -- footprint)
    let cells := if strict then (cellLocals (f.params.map (·.name)) f.body).map (·.1) else []
    let locals := (f.params.map (·.name) ++ declaredIn f.body).filter (!cells.contains ·)
    -- (computed where a read first narrows one)
    let slots := Thunk.mk fun _ => (f.params.map (·.name) ++ declaredIn f.body).filter fun n =>
      !(cellLocals (f.params.map (·.name)) f.body f.name.isEmpty).any (·.1 == n)
    let values := (f.params.map (·.name)).filter fun n =>
      !(cellLocals (f.params.map (·.name)) f.body f.name.isEmpty).any (·.1 == n)
    let heldCells := (cellLocals (f.params.map (·.name)) f.body f.name.isEmpty).map (·.1)
    let start : Walk := { generics, expected, force, scope, locals, strict, slots, schemes, values, heldCells, moduleInit := f.name.isEmpty, entries := (({} : Std.HashMap Nat _).insert 0 vars).insert f.namePos.1 vars }
    let settle (start : Walk) (initial : List (Span × Ty Tree)) :
        Compiler ((Option Env × Walk) × List (Span × Ty Tree)) := do
      let mut assumed := initial
      let mut result ← (stmts (some env) f.body).run { start with assumed }
      -- Four growth rounds and one unique-use fallback, exactly the bound of
      -- proposal.ml:23-47. The final pass checks all writes at these contracts.
      for round in List.range 5 do
        let w := result.2
        let grown := w.evolvedWrites.filter fun (key, A) => norm ((assumed.lookup key).getD [] ++ A) != (assumed.lookup key).getD []
        if grown.isEmpty then break
        if round == 4 then
          if !grown.all (fun (key, _) => (w.evolvedUses.lookup key).isSome) then
            throw "not handled: an evolving binding's contract does not settle"
          for (key, _) in grown do assumed := upd assumed key ((w.evolvedUses.lookup key).getD [])
        else
          for (key, A) in grown do assumed := upd assumed key (norm ((assumed.lookup key).getD [] ++ A))
        result ← (stmts (some env) f.body).run { start with assumed }
      return (result, assumed)
    let (result, assumed) ← settle start []
    let (done, w) := result
    -- Where a use offers a constant's literal more rows, walked again with
    -- them (the producer's second round, proposal.ml:47-52), once.
    let (done, w) ← if w.offered.isEmpty && w.ctorOffered.isEmpty && w.restOffered.isEmpty then pure (done, w)
      else do
        let (result, _) ← settle { start with offers := w.offered, ctorOffers := w.ctorOffered, restOffers := w.restOffered } assumed
        pure result
    let w := { w with completion := done.bind fun d => if d.ghost then none else some d.vars }
    return (w, ← table)
  let ((w, T'), _) ← runCompiler T [] action
  return (w, T')

/-- A unit's walk compared with its claims. -/
def compareUnit (T : EquationStore.State) (f : Fragment.Fn) (fc : SourceClaims.Function Tree)
    (module : List (String × Compiler (Ty Tree))) (generics : List (String × Generic) := []) :
    Except String Json := do
  let (w, T') ← walkUnit T f module generics
  let (counts, samples) := compareWalk T' fc w
  return Json.mkObj [
    ("counts", Json.arr (counts.toArray.map fun ((k, c), n) =>
      Json.mkObj [("kind", toJson k), ("class", toJson c), ("n", toJson n)])),
    ("samples", Json.arr samples)]

/-- The lowering's reading of an expression the walk gives no type: the
unit's refusal where a rule the lowering shares refuses it (`refusalMark`), else a type
the pass does not handle. -/
def undetermined (m : String) : String :=
  if m.startsWith refusalMark then m else s!"not handled: {m} (type undetermined)"

/-- A unit's claims with what the walk computes in place of what a producer
infers: every expression's type, every statement entry's bindings and every
`let`'s storage contract, at each execution point alike; no asserted field
contents, entry facts or per-closure overlays. The signature, footprints and
the execution points' names are the unit's own (`fc`). The first undetermined
type the lowering would read is the unit's refusal there. Beside them, where
the unit's body completes (`Walk.completion`). -/
def retypeUnitWith (T : EquationStore.State) (f : Fragment.Fn) (fc : SourceClaims.Function Tree)
    (module : List (String × Compiler (Ty Tree))) (generics : List (String × Generic) := [])
    (parts : String := "xec") (force : List String := [])
    (scope : Option (PositiveGraphs.SchemeRow Tree × List String) := none) :
    Except String (EquationStore.State × SourceClaims.Function Tree × Option (List (String × Ty Tree)) ×
      Std.HashMap (Nat × String) (List (String × Ty Tree)) ×
      Std.HashMap Span (List (String × Ty Tree) × List (String × List (List PropKey × Ty Tree))) ×
      Std.HashMap (Span × Span) (SourceClaims.Candidate Tree)) := do
  -- A generic closure at the scheme its claim names.
  let schemes := fc.exprs.filterMap fun (sp, c) => c.toOption.map (sp, ·)
  let (w, T') ← walkUnit T f module generics force scope (schemes := schemes)
  let exprs : List (Span × SourceClaims.Candidate Tree) := w.exprs.toList.map fun (span, (_, r)) =>
    (span, r.mapError undetermined)
  let envs : List (Nat × List (String × SourceClaims.Candidate Tree)) :=
    w.entries.toList.map fun (pos, vars) => (pos, vars.map fun (n, A) => (n, .ok A))
  let contracts : SourceClaims.Contracts Tree := w.contracts.map fun (k, D) => (k, .ok D)
  -- Debugging: which parts are replaced (`x` expressions, `e` entries, `c`
  -- contracts), the claims' kept for the others.
  let claimed := fc.exprs.foldl (fun (acc : List (Span × SourceClaims.Candidate Tree)) (sp, c) =>
    if (acc.lookup sp).isSome then acc else (sp, c) :: acc) []
  let lo := ((parts.splitOn ":")[1]?.bind String.toNat?).getD 0
  let hi := ((parts.splitOn ":")[2]?.bind String.toNat?).getD 0
  let exprs := if parts.contains 'x' then
      (if hi > 0 then claimed.filter (fun (sp, _) => lo ≤ sp.1 && sp.1 < hi) ++
        exprs.filter (fun (sp, _) => !(lo ≤ sp.1 && sp.1 < hi)) else exprs)
    else claimed
  let envs := if parts.contains 'e' then envs else fc.envs
  let contracts := if parts.contains 'c' then contracts else fc.contracts
  -- The entry facts are the given ones (class (d) of the single pass's
  -- draft, section 8): the unit's own, kept per point.
  -- Debugging: `k` keeps the claims' asserted field contents (`current`).
  let keep := parts.contains 'k'
  -- Each entry's narrowed paths that some read of the walk reads narrowed,
  -- or of which it reads a longer path of the same root so.
  let readPaths := w.readPaths.toList
  let read (root : String) (p : List PropKey) : Bool :=
    readPaths.any fun (r, q) => r == root && p.isPrefixOf q
  let currents := w.currents.toList.map fun (at_, cs) =>
    (at_, (cs.map fun (root, ps) => (root, ps.filter fun (p, _) => read root p)).filter (!·.2.isEmpty))
  return (T', ({ fc with
    exprs, envs, contracts
    entryCurrent := if keep then fc.entryCurrent else currents
    exprCurrent := if keep then fc.exprCurrent else []
    arrowClaims := w.arrowClaims
    points := fc.points.map fun (id, row) =>
      (id, { row with exprs := exprs, envs := envs,
                      entryCurrent := if keep then row.entryCurrent else currents,
                      exprCurrent := if keep then row.exprCurrent else [] }) } : SourceClaims.Function Tree), w.completion,
    w.declarations, w.spanEntries, w.exprsAt.fold (fun m k r => m.insert k (r.mapError undetermined)) {})

/-- `retypeUnitWith`'s grown store and claims. -/
def retypeUnit (T : EquationStore.State) (f : Fragment.Fn) (fc : SourceClaims.Function Tree)
    (module : List (String × Compiler (Ty Tree))) (generics : List (String × Generic) := [])
    (parts : String := "xec") (force : List String := [])
    (scope : Option (PositiveGraphs.SchemeRow Tree × List String) := none) :
    Except String (EquationStore.State × SourceClaims.Function Tree) := do
  let (T, fc, _, _, _, _) ← retypeUnitWith T f fc module generics parts force scope
  return (T, fc)

end Verification.SourceExtraction.Synthesis
