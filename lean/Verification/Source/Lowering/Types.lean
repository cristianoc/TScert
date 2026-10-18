import Verification.Source.Lowering.State
import Verification.Source.FragmentTypes

/-! Resolves source claims and type-directed expression operations. -/
namespace Verification.SourceExtraction
open CallEffects (Arrow RestArrow Contract Effect)
open Lean ProgramTyping PositiveRules ControlFlow CertificateProducer RequestJson
open Fragment LabelStore
open EquationGraphs (Tree)

section
variable {ι : Type} [Labels ι]

/-- The type of the `i`-th actual past a variadic signature's fixed ones: its
position in the rest's one tuple contract. -/
@[nospecialize] def restPosition (G : PositiveGraphs.NormalGraph ι) (P : List ι) (i : Nat) :
    Option (List ι) :=
  match PositiveRules.expand G P with
  | [.pack T []] => ProgramTyping.positionTy T i
  | _ => none

/-- Inclusion for source contracts through the common subtype operation,
retaining the execution outcome. -/
@[nospecialize] def withinResult (T : EquationStore.State) (C A : List Tree) :
    PositiveCertificates.ComparisonResult Unit :=
  (CertificateProducer.comparisonUsing (SourceTypes.graph T) (StoreView.images T) C A).map fun _ => ()

/-- Optional inference probes use only established inclusion. -/
@[nospecialize] def within (T : EquationStore.State) (C A : List Tree) : Bool :=
  (withinResult T C A).accepted

@[nospecialize] def sameMeaning (T : EquationStore.State) (A B : List Tree) : Bool :=
  within T A B && within T B A

/-- A located subtype judgment under the displayed equations. Both occurrences
of its source span come from `pos`, so transport cannot move the judgment away
from its location. -/
@[nospecialize] def subtypeFailure (T : EquationStore.State) (pos : Span)
    (role : DirectObligation.SourceRole) (A B : Ty Tree) (outcome : DiagnosticOutcome)
    (reason : String) : String :=
  let p := StoreView.projection T (A ++ B).eraseDups
  RequestJson.withDiagnostic s!"source direct obligation at [{pos.1},{pos.2}): {reason}"
    ([("kind",toJson "direct-obligation"),("phase",toJson "request-validation"),
      ("outcome",toJson outcome),("id",toJson s!"subtype:{pos.1}:{role.wire}"),
      ("sourceMap",toJson (SourceMapEntry.mk pos role.wire none [])),
      ("judgment",(DirectObligation.Judgment.subtyping pos (p.shown A) (p.shown B)).toJson),
      ("fuel",toJson 0)] ++ p.fields)

/-- A required source comparison retains exhaustion and its judgment. -/
@[nospecialize] private def requireComparison (T : EquationStore.State) (pos : Span)
    (role : DirectObligation.SourceRole) (A B : Ty Tree)
    (result : PositiveCertificates.ComparisonResult Unit) (reason : String) : Except String Unit :=
  match result with
  | .established _ => .ok ()
  | .notEstablished => .error (subtypeFailure T pos role A B .notEstablished reason)
  | .exhausted rounds visited => .error (subtypeFailure T pos role A B
      (.exhausted T.subtypeBudget.rounds rounds visited)
      s!"subtype search exhausted while checking {role.wire}: {SourceTypes.render T A} ≤ {SourceTypes.render T B}")

@[nospecialize] def requireWithin (T : EquationStore.State) (pos : Span)
    (role : DirectObligation.SourceRole) (A B : Ty Tree) (reason : String) : Except String Unit :=
  requireComparison T pos role A B (withinResult T A B) reason

@[nospecialize] def requireSameMeaning (T : EquationStore.State) (pos : Span)
    (role : DirectObligation.SourceRole) (A B : Ty Tree) (reason : String) : Except String Unit := do
  requireWithin T pos role A B reason
  requireWithin T pos role B A reason

@[nospecialize] private def envCore (T : EquationStore.State) (fc : SourceClaims.Function Tree) (pos : Nat) (scope : List (ScopeBinding Tree)) :
    Except String (List (Ty Tree)) := do
  let vars ← match fc.envs.lookup pos with
    | some vars => pure vars
    | none => throw s!"missing statement environment at {pos}"
  if !distinct (vars.map Prod.fst) then throw s!"duplicate environment binding at {pos}"
  scope.mapM fun b => do
    -- The slot holds the cell's identity. What the producer says `x` is now
    -- describes the contents, and is an observation, not this slot's type.
    let name := b.source.name
    if let some A := b.fixed then return A
    let some t := vars.lookup name | throw s!"missing claimed binding '{name}' at {pos}"
    let A ← (SourceClaims.resolve T t).mapError fun msg =>
      if msg == "type claim unavailable from producer" then
        s!"unavailable claimed binding '{name}' at {pos}"
      else msg
    match b.storage with
    | .value | .slot _ => return A
    | .cell _ reference => return reference

@[nospecialize] def env (fc : SourceClaims.Function Tree) (pos : Nat) (scope : List (ScopeBinding Tree)) :
    Compiler (List (Ty Tree)) := do
  (envCore (← table) fc pos scope).mapError fun msg =>
    s!"source environment obligation at {pos}: {msg}"

/-- A pattern reads fields, never a method: a method is a member of its object,
called with it as receiver (`MethodMembers`); read off it, it is no function
value. -/
@[nospecialize] def noMethodRead (G : PositiveGraphs.NormalGraph ι) (A : Ty ι) (fld : String) :
    Except String Unit :=
  if (PositiveRules.expand G A).any fun c => match c with
      | .refs _ _ _ _ ms _ => ms.any (·.key == fld) | _ => false then
    throw s!"a method '{fld}' read off its object is not a function value: it takes the object as its receiver"
  else pure ()

/-- Why an array rest is refused over an array whose contract does not fix its
length: its rest is a slice of a length known only at run time, which no
fixed list of reads is, and the calculus has no slice. -/
def restOfUnknownLength : String :=
  "an array rest needs one tuple contract of required positions: the rest of an array of unknown length is a slice"

/-- The type claimed at a site: a source expression, or an array pattern's
rest. -/
@[nospecialize] def claimAt (fc : SourceClaims.Function Tree) (span : Span) : Compiler (Ty Tree) := do
  match fc.exprs.lookup span with
  | some t => (SourceClaims.resolve (← table) t).mapError fun msg =>
      s!"source expression obligation at [{span.1},{span.2}): {msg}"
  | none => throw s!"no claimed type for the expression at {spanStr span}"

@[nospecialize] def exprType (fc : SourceClaims.Function Tree) (e : Fragment.Expr) : Compiler (Ty Tree) := do
  if let .var _ name := e then
    if let some T := (← executionType name) then return T
  claimAt fc e.span

/-- The store type of an array claim: the type of its store field, held
invariantly or as a view. -/
@[nospecialize] def storeOf (G : PositiveGraphs.NormalGraph ι) (A : Ty ι) : Option (Ty ι) :=
  match PositiveRules.expand G A with
  | [.refs fs [] vs _ _ _] => fs.lookup SourceTypes.storeField <|> vs.lookup SourceTypes.storeField
  | _ => none

/-- A union of arrays: every clause of the type holds a store. -/
@[nospecialize] def arraysOnly (G : PositiveGraphs.NormalGraph ι) (A : Ty ι) : Bool :=
  let cs := PositiveRules.expand G A
  !cs.isEmpty && cs.all fun c => match c with
    | .refs fs [] vs _ _ _ => (fs.lookup SourceTypes.storeField <|> vs.lookup SourceTypes.storeField).isSome
    | _ => false

/-- A source numeric key must denote one valid array index. The two runtime
zeros name the same property although their numeric values remain distinct. -/
@[nospecialize] private def arrayIndex (G : PositiveGraphs.NormalGraph ι) (K : Ty ι) : Except String Nat := do
  let cs := PositiveRules.expand G K
  let .numLit b :: _ := cs
    | throw "a numeric array key needs a proved array-index singleton; ordinary numeric properties are not modeled"
  let some k := indexOfBits b
    | throw "numeric property keys outside the array-index range are outside the fragment"
  if !cs.all (fun c => match c with | .numLit b => indexOfBits b == some k | _ => false) then
    throw "a numeric array key needs one array index"
  return k

def arrayPrototypeName : String := SourceTypes.arrayPrototypeName

/-- A fresh array object's type: its store and prototype as fields, and its own
keys bounded to them, the type `alloc` gives before it is read as an array. -/
@[nospecialize] def arrayObject (S : Ty Tree) : Compiler (Ty Tree) := do
  let label ← lower (SourceTypes.use (.refs [(SourceTypes.storeField, S),
    (SourceTypes.protoField, [StoreView.arrayProto (← table)])] [] [] [] []
    [⟨true, [SourceTypes.storeField, SourceTypes.protoField]⟩]))
  recordHints [label]
  return [label]

/-- The slot holding `Array.prototype` in a scope. -/
@[nospecialize] def prototypeSlot (scope : List (ScopeBinding ι)) : Except String Nat :=
  match resolve scope arrayPrototypeName with
  | some (i, .value) => pure i
  | _ => throw "an array needs Array.prototype, which this unit does not see"

/-- Allocate the array object holding the store in slot 0, with the prototype
from slot `proto`. -/
def arrayTerm (proto : Nat) : Tm :=
  .makeAt .absent [SourceTypes.storeField, SourceTypes.protoField] [.var 0, .var proto]

/-- The literal index of one position, interned like any other number the
program mentions. -/
@[nospecialize] def indexTerm (j : Nat) : Compiler Tm := do
  let b := bitsOfNat j
  let label ← lower (SourceTypes.use (.numLit b))
  recordHints [label]
  return .num b

@[nospecialize] def arrayKeyTerm (K : Ty Tree) : Compiler Tm := do
  let k ← arrayIndex (SourceTypes.graph (← table)) K
  let b := bitsOfNat k
  let label ← lower (SourceTypes.use (.numLit b))
  recordHints [label]
  return .num b

/-- The type a binary operator's value is claimed at before it meets the
expression's claim: both Booleans for a comparison, strings for `+` with a
string operand, a number for an operator stated on numbers alone, else the
numeric family of its operands. -/
@[nospecialize] def operatorResult (op : Arith) (A B : Ty Tree) : Compiler (Ty Tree) := do
  if op.relational || op == .eq || op == .looseEq then return [Labels.tru, Labels.fls]
  if op.numberOnly then return [← lower (SourceTypes.use .num)]
  let G := SourceTypes.graph (← table)
  let strings := fun (T : Ty Tree) =>
    let cs := PositiveRules.expand G T
    !cs.isEmpty && cs.all ProgramTyping.stringClause
  if op == .add && (strings A || strings B) then return [← lower (SourceTypes.use .str)]
  let cs := PositiveRules.expand G A
  if !cs.isEmpty && cs.all ProgramTyping.bigintClause then return [← lower (SourceTypes.use .bigint)]
  return [← lower (SourceTypes.use .num)]

/-- A unary operator as the binary one it is on its operand's numeric family,
with a constant right operand: `-x` is `x * -1`, `+x` is `x * 1` and `~x` is
`x ^ -1`, exactly, on numbers and on bigints alike. The family is the
operand's claimed one, which its own obligation establishes. `+` on a bigint
throws a `TypeError`, and an operand of both families has no one constant, so
each is refused. The constant's singleton is interned and offered to search. -/
@[nospecialize] def unaryOperation (p : Span) (op : Fragment.UnaryOp) (B : Ty Tree) :
    Compiler (Arith × Tm × Ty Tree × ProgramCertificates.Rule Tree) := do
  let cs := PositiveRules.expand (SourceTypes.graph (← table)) B
  let located := s!"unsupported source expression at [{p.1},{p.2}): "
  let bigint ← if !cs.isEmpty && cs.all ProgramTyping.numberClause then pure false
    else if !cs.isEmpty && cs.all ProgramTyping.bigintClause then pure true
    else throw (located ++ "a unary numeric operator needs an operand of one numeric family, number or bigint")
  let (arith, factor) ← match op with
    | .neg => pure (Arith.mul, -1) | .plus => pure (.mul, 1) | .bitNot => pure (.xor, -1)
    | .typeof => throw "internal extraction error: typeof is not a numeric operator"
  if bigint then
    if op == .plus then throw (located ++ "unary + on a bigint throws a TypeError")
    let label ← lower (SourceTypes.use (.bigintLit factor))
    recordHints [label]
    return (arith, .bigint factor, [label], .bigintLit)
  let b := (if factor < 0 then -1.0 else 1.0 : Float).toBits
  let label ← lower (SourceTypes.use (.numLit b))
  recordHints [label]
  return (arith, .num b, [label], .numLit)

/-- The operand of `key in o`, whose test (`Tag.hasKey`) asks whether the
object owns the key. JavaScript throws on a primitive, where the test would
answer `false`, so the operand must be of object clauses. A class value is
refused: its static members are bound apart (`static C.x`), so it lacks keys
JavaScript's has. On the other objects of the fragment own keys are
JavaScript's, and the key names nothing a prototype holds
(`Fragment.inKeyRefusal`). -/
@[nospecialize] def inOperand (p : Span) (tag : Tag) (B : Ty Tree) : Compiler Unit := do
  let .hasKey _ := tag | return
  let G := SourceTypes.graph (← table)
  let cs := PositiveRules.expand G B
  let located := s!"unsupported source expression at [{p.1},{p.2}): "
  if cs.any (fun | .ctors .. => true | _ => false) then
    throw (located ++ "`in` on a class value: its static members are bound apart from it")
  unless G.plainTy B && !cs.isEmpty && cs.all (fun
      | .refs .. | .dict .. | .arrs .. | .callable .. => true
      | _ => false) do
    throw (located ++ "`in` needs an object operand: it throws on a primitive")

/-- The keys `key in o` may test, from the key's claim: a union of string
singletons, each a key `in` answers as JavaScript does (`inKeyRefusal`). -/
@[nospecialize] def inKeyList (p : Span) (K : Ty Tree) : Compiler (List String) := do
  let G := SourceTypes.graph (← table)
  let located := s!"unsupported source expression at [{p.1},{p.2}): "
  let keys := (PositiveRules.expand G K).filterMap fun
    | .strLit s => some s
    | _ => none
  unless G.plainTy K && !keys.isEmpty && keys.length == (PositiveRules.expand G K).length do
    throw (located ++ "`in` with a key that is not a union of string literals")
  let keys := keys.eraseDups
  for k in keys do
    if let some reason := Fragment.inKeyRefusal k then
      throw (located ++ s!"`in` with the key '{k}': {reason}")
  return keys

/-- `key in o` with the key in `keySlot` and the object in `slot`: the key's
singletons, tested in turn, each selecting its own key's test; the last
needs no test, since the key is one of them. -/
def inKeysTerm (keys : List String) (keySlot slot : Nat) : Tm :=
  match keys.reverse with
  | [] => .fls
  | last :: earlier => earlier.reverse.foldr (fun k rest =>
      .ite (.test (.strEq k) (.var keySlot)) (has k) rest) (has last)
where has (k : String) : Tm := .ite (.test (.hasKey (.str k)) (.var slot)) .tru .fls

/-- `o[k]` with the key in `keySlot` a union of singletons: each singleton,
tested in turn, selects the read of its own key (`reads`); the last needs no
test, since the key is one of them. -/
def keyedReadTerm (arms : List (Tag × Tm)) (keySlot : Nat) : Tm :=
  match arms.reverse with
  | [] => .undef
  | (_, last) :: earlier => earlier.reverse.foldr (fun (tag, read) rest =>
      .ite (.test tag (.var keySlot)) read rest) last

/-- `typeof v`, in the order the lowering tests it: each tag holds of exactly
the values `typeof` names by its string, and a value none of them holds of is
an object with call code, which `typeof` names `"function"`. -/
def typeofAnswers : List (Tag × String) :=
  [(.isUndef, "undefined"), (.typeofObject, "object"), (.isBool, "boolean"), (.isNum, "number"),
   (.isStr, "string"), (.isBigint, "bigint"), (.isSymbol, "symbol")]

/-- `typeof` of the value in `slot`: one tag test per answer, in order. -/
def typeofTerm (slot : Nat) : Tm :=
  typeofAnswers.foldr (fun (tag, s) rest => .ite (.test tag (.var slot)) (.str s) rest) (.str "function")

/-- What a computed key names, by its claimed type: a field for a string
singleton, a dictionary lookup for a broad string, or an element of the
array's store for a number. On a receiver that is only records and
dictionaries, a number singleton names the field its `ToString` spells
(`ToPropertyKey`), as `o[0]` reads `o["0"]`, both zeros spelling `0`; and a
broad number or symbol is a dictionary lookup, through an index over its keys.
The key stays in
the program, evaluated after the receiver and before any right side, and its
expression obligation must establish that claim. -/
inductive KeyKind where
  | field (name : String)
  | dynamic
  | element

/-- Whether an expression is claimed only at records and dictionaries: no
array store, no primitive, nothing else. Such an object's property named by a
number is the field its `ToString` spells; an array's is its store's
element. -/
@[nospecialize] def recordReceiver (fc : SourceClaims.Function Tree) (e : Fragment.Expr) : Compiler Bool := do
  let G := SourceTypes.graph (← table)
  let R ← exprType fc e
  let cs := PositiveRules.expand G R
  return !cs.isEmpty && (storeOf G R).isNone && cs.all fun
    | .refs .. | .dict .. => true | _ => false

/-- Whether an expression is claimed only at dictionaries, whose indexes a
broad key reads through. -/
@[nospecialize] def dictReceiver (fc : SourceClaims.Function Tree) (e : Fragment.Expr) : Compiler Bool := do
  let cs := PositiveRules.expand (SourceTypes.graph (← table)) (← exprType fc e)
  return !cs.isEmpty && cs.all fun | .dict .. => true | _ => false

/-- The singletons of a key's claim, each with the tag that tests a value for
it and the property key it converts to (`ToPropertyKey`: a number's is the
key its `ToString` spells). `none` unless every clause is a string or number
singleton; NaN, which no equality test finds, is not one. -/
@[nospecialize] def keySingletons (G : PositiveGraphs.NormalGraph ι) (K : Ty ι) : Option (List (Tag × PropKey)) :=
  let cs := PositiveRules.expand G K
  if !G.plainTy K || cs.isEmpty then none else
  cs.mapM fun c => match c with
    | .strLit v => some (.strEq v, .str v)
    | .numLit b => if numberEqual b b then some (.numEq b, .str (numberToString b)) else none
    | _ => none

@[nospecialize] def keyField (fc : SourceClaims.Function Tree) (key : Fragment.Expr)
    (string : Bool := false) (record : Bool := false) (dict : Bool := false) : Compiler KeyKind := do
  let K ← exprType fc key
  let G := SourceTypes.graph (← table)
  let spelled := fun (s : String) =>
    if SourceTypes.reservedKey s then throw s!"'{s}' is internal to the model, not a source property"
    else pure (KeyKind.field s)
  -- Several singletons on an object: each reads the member its key names
  -- (`keyedReadTerm`).
  if record || dict then
    if let some keys := keySingletons G K then
      if (keys.map (·.2)).eraseDups.length > 1 then
        for (_, k) in keys do
          if let .str s := k then
            if SourceTypes.reservedKey s then throw s!"'{s}' is internal to the model, not a source property"
        return .dynamic
  match PositiveRules.expand G K with
  | [.strLit s] => spelled s
  | [.str] => pure .dynamic
  | [.num] | [.symbol] => if dict then pure .dynamic else
    if string && decide (Answers G K .isNum true) then return .element else do
      let _ ← arrayIndex G K
      pure .element
  | .numLit b :: cs =>
    if record && cs.all (fun c => match c with
        | .numLit b' => numberToString b' == numberToString b | _ => false) then
      spelled (numberToString b)
    else
      if string && decide (Answers G K .isNum true) then return .element
      let _ ← arrayIndex G K
      pure .element
  | _ =>
    -- A string's index properties are its code units: any number names one
    -- or none (`elemStr`); an array's needs one proved index.
    if string && decide (Answers G K .isNum true) then return .element
    let _ ← arrayIndex G K
    pure .element

/-- Whether a key's claim is of keys known only at run time: every clause a
string, a number or a symbol, singletons or families, and not one key the
source spells (one string or number singleton, which `growingWrite` reads as
a named write). -/
@[nospecialize] def computedKeyClaim (G : PositiveGraphs.NormalGraph ι) (K : Ty ι) : Bool :=
  let cs := PositiveRules.expand G K
  G.plainTy K && !cs.isEmpty &&
  cs.all (fun c => match c with
    | .strLit _ | .str | .num | .symbolLit _ | .symbol => true
    | .numLit b => numberEqual b b
    | _ => false) &&
  match keySingletons G K with
  | some ks => (ks.map (·.2)).eraseDups.length > 1
  | none => true

/-- The tag testing equality with the one value every member of `A` is:
null, undefined, a number (both zeros are one), a string, a Boolean or a
bigint. -/
@[nospecialize] def singletonTag (G : PositiveGraphs.NormalGraph ι) (A : Ty ι) : Option Tag :=
  if A == [Labels.nul] then some Tag.isNul else if A == [Labels.undef] then some Tag.isUndef else
    match PositiveRules.expand G A with
    | .numLit bits :: cs =>
      if cs.all (fun c => match c with | .numLit b => numberEqual bits b | _ => false)
      then some (.numEq bits) else none
    | [.strLit s] => some (.strEq s)
    | [.boolLit b] => some (.boolEq b)
    | [.bigintLit i] => some (.bigintEq i)
    | _ => none

mutual
/-- A claimed singleton operand (null, undefined, a number, a string, a Boolean
or a bigint) selects a tag-test implementation, never an assumption: both
operands remain in the program, in source order, and their expression
obligations must establish the singleton used by this translation. Without
one, the comparison is the strict-equality operator (`Arith.eq`), which the
operator rule admits where either operand is a primitive; `!==` is its
negation. -/
@[nospecialize] partial def comparisonsExpr (fc : SourceClaims.Function Tree) (e : Fragment.Expr) :
    Compiler Fragment.Expr := do
  match e with
  | .var .. | .lit .. => pure e
  | .equality p eq l r =>
    let l ← comparisonsExpr fc l
    let r ← comparisonsExpr fc r
    let L ← exprType fc l
    let R ← exprType fc r
    let G := SourceTypes.graph (← table)
    let select := singletonTag G
    match select R, select L with
    | some tag, _ => pure (.singletonTest p tag eq true l r)
    | _, some tag => pure (.singletonTest p tag eq false l r)
    | _, _ =>
      -- The typing rule decides strict equality when either operand's
      -- clauses contain only JavaScript values.
      let identified := ProgramTyping.decidingClause (α := Ty Tree) .eq
      if (PositiveRules.expand G L).any (fun c => !identified c) &&
          (PositiveRules.expand G R).any (fun c => !identified c) then
        throw s!"unsupported source expression at [{p.1},{p.2}): strict equality of two operands that may both be values of no known kind, neither a primitive nor an object"
      let same := Fragment.Expr.arith p .eq l r
      pure (if eq then same else .not p same)
  | .logical p a l r => return .logical p a (← comparisonsExpr fc l) (← comparisonsExpr fc r)
  | .coalesce p l r => return .coalesce p (← comparisonsExpr fc l) (← comparisonsExpr fc r)
  | .optional p m r b => return .optional p m (← comparisonsExpr fc r) (← comparisonsExpr fc b)
  | .nullishAssign p n np r => return .nullishAssign p n np (← comparisonsExpr fc r)
  | .assign p n np r => return .assign p n np (← comparisonsExpr fc r)
  | .shapeTest p t eq e => return .shapeTest p t eq (← comparisonsExpr fc e)
  | .singletonTest p t eq tl l r => return .singletonTest p t eq tl (← comparisonsExpr fc l) (← comparisonsExpr fc r)
  | .not p e => return .not p (← comparisonsExpr fc e)
  | .unary p op e => return .unary p op (← comparisonsExpr fc e)
  | .cast p annot e => return .cast p annot (← comparisonsExpr fc e)
  | .ctor p lam fs => return .ctor p (← comparisonsExpr fc lam) (← fs.mapM fun (k, e) => do
      pure (k, ← comparisonsExpr fc e))
  | .construct p f args spreads ts => return .construct p (← comparisonsExpr fc f) (← args.mapM (comparisonsExpr fc)) spreads ts
  | .alloc p ns es => return .alloc p ns (← es.mapM (comparisonsExpr fc))
  | .build p ns es => return .build p ns (← es.mapM (comparisonsExpr fc))
  | .read p f e => return .read p f (← comparisonsExpr fc e)
  | .write p f l r => return .write p f (← comparisonsExpr fc l) (← comparisonsExpr fc r)
  | .index p _ e key =>
    let key ← comparisonsExpr fc key
    let e ← comparisonsExpr fc e
    let string := decide (Answers (SourceTypes.graph (← table)) (← exprType fc e) .isStr true)
    -- A read at a key the object may lack finds, in JavaScript, what
    -- `Object.prototype` holds under it, where the model finds nothing: no
    -- rule reads such a key as possibly absent (`inheritedKey`, and
    -- `indexDict` at no key of every string). A key known only at run time
    -- to be some string is refused here, at its site.
    let anyString := (PositiveRules.expand (SourceTypes.graph (← table)) (← exprType fc key)).any
      fun c => match c with
        | .str => true
        | _ => false
    match ← keyField fc key string (← recordReceiver fc e) (← dictReceiver fc e) with
    | .field s => return .index p (some s) e key
    | .dynamic =>
      if anyString then
        throw (locatedRefusal (← table) p .expressionClaim
          "a read at a key that may name a member every object inherits from `Object.prototype` (`toString`, `constructor`, `valueOf`, ...): the model's objects hold no prototype there, so a key the object may lack is read only where no member of it is under the key")
      return .index p none e key
    | .element => return .elemAt p e key
  | .arrayLit p es spreads => return .arrayLit p (← es.mapM (comparisonsExpr fc)) spreads
  | .arrayAssign p targets rest rhs =>
    let targets ← targets.mapM fun q => do
      return { q with default_ := ← q.default_.mapM (comparisonsExpr fc) }
    return .arrayAssign p targets rest (← comparisonsExpr fc rhs)
  | .elemAt p e key => return .elemAt p (← comparisonsExpr fc e) (← comparisonsExpr fc key)
  | .elemWrite p r key rhs =>
    return .elemWrite p (← comparisonsExpr fc r) (← comparisonsExpr fc key) (← comparisonsExpr fc rhs)
  | .arith p op l r => return .arith p op (← comparisonsExpr fc l) (← comparisonsExpr fc r)
  | .comma p l r => return .comma p (← comparisonsExpr fc l) (← comparisonsExpr fc r)
  | .inKeys p k o => return .inKeys p (← comparisonsExpr fc k) (← comparisonsExpr fc o)
  | .logicalAssign p op target rhs =>
    return .logicalAssign p op (← comparisonsExpr fc target) (← comparisonsExpr fc rhs)
  | .update p op target rhs post =>
    return .update p op (← comparisonsExpr fc target) (← rhs.mapM (comparisonsExpr fc)) post
  | .indexWrite p _ r key rhs =>
    let key ← comparisonsExpr fc key
    let r ← comparisonsExpr fc r
    let rhs ← comparisonsExpr fc rhs
    -- A key-adding write at a key known only at run time on a local's own
    -- object, which the statement's lowering copies (`computedGrowth`).
    if (← ownedWrite) == some p then
      if computedKeyClaim (SourceTypes.graph (← table)) (← exprType fc key) then
        return .indexWrite p none r key rhs
    match ← keyField fc key (record := ← recordReceiver fc r) (dict := ← dictReceiver fc r) with
    | .field s => return .indexWrite p (some s) r key rhs
    | .dynamic =>
      -- A write at a key known only at run time may add the key: on an
      -- object another reference may hold it is refused as a named write
      -- adding a key is, and through a parameter on principle.
      -- The receiver as the source spells it, where the operands are saved.
      let origins ← executionOrigins
      let receiver := match r with
        | .var _ n => (origins.lookup n).getD r
        | _ => r
      if let .var _ n := receiver then
        if fc.params.any (·.1 == n) then
          throw (locatedRefusal (← table) p .expressionClaim
            (parameterGrowth "a write at a key known only at run time" n))
      throw (locatedRefusal (← table) p .expressionClaim
        "a write at a key known only at run time may add the key to an object another reference holds, which would see the object's keys change: a key-adding write is typed only on a local's own fresh object that nothing else has reached")
    | .element => return .elemWrite p r key rhs
  | .withValue p f i ft bt => return .withValue p (← comparisonsExpr fc f) (← comparisonsExpr fc i) ft bt
  | .objectAssign p t ss => return .objectAssign p (← comparisonsExpr fc t) (← ss.mapM (comparisonsExpr fc))
  | .lambda .. => pure e
  | .bindWithReceiver p c r args => return .bindWithReceiver p (← comparisonsExpr fc c) (← comparisonsExpr fc r) (← args.mapM (comparisonsExpr fc))
  | .callWithReceiver p c r args => return .callWithReceiver p (← comparisonsExpr fc c) (← comparisonsExpr fc r) (← args.mapM (comparisonsExpr fc))
  | .applyWithReceiver p c r list => return .applyWithReceiver p (← comparisonsExpr fc c) (← comparisonsExpr fc r) (← list.mapM (comparisonsExpr fc))
  | .call p c args spread ts =>
    return .call p (← comparisonsExpr fc c) (← args.mapM (comparisonsExpr fc)) spread ts
  | .invoke p c args spreads typeArgs =>
    -- A field, by name or by a string key, or an array element by a numeric
    -- key: `comparisonsExpr` resolves the key from its claim.
    return .invoke p (← comparisonsExpr fc c) (← args.mapM (comparisonsExpr fc)) spreads typeArgs
  | .ifBody p c t e => return .ifBody p (← comparisonsExpr fc c) (← comparisonsExpr fc t) (← comparisonsExpr fc e)
  | .block .. => pure e


end

/-- A module function's value as its callers see it: an ordinary function at
its annotated parameters and result. A leading `this: T` parameter
is its receiver, which every call passes (a plain call `undefined`), and no
position; without one the receiver is irrelevant. A rest parameter
contributes its tuple's positions or its array's element. A function without
a rest parameter is code that discards the actuals past its parameters, so it
also meets its signature extended by a rest of `unknown` elements: the
further actuals a caller writes may be any values. -/
def moduleArrow (g : Fragment.Fn) (footprint : Footprints.Closed := .top) (onThrow : Bool := false) :
    Except String Json := do
  let top := Json.mkObj [("top", toJson true), ("atoms", toJson ([] : List Json))]
  let (receiver, params) := match g.params with
    | p :: ps => if p.name == "this" then (p.ty, ps) else (top, g.params)
    | [] => (top, [])
  let fixed := if params.getLast?.any (·.rest) then params.dropLast else params
  let (positions, rest) ← match params.getLast? with
    | some p =>
      if !p.rest then pure (fixed.map (·.ty), [])
      else match Fragment.arrayElement p.ty (readonly := true) with
        | some e => pure (fixed.map (·.ty), [("rest", e)])
        | none => pure (fixed.map (·.ty) ++ (← Fragment.tupleRequired p.ty), [])
    | none => pure ([], [])
  let signature (rest : List (String × Json)) (result : Json) (effect : List (String × Json)) :=
    [("a", toJson "function"), ("this", receiver), ("params", toJson positions)] ++ rest ++
      [("result", result), ("construct", toJson "unknown"), ("array", toJson "unknown")] ++ effect
  -- A guard's promise is a signature of its own, beside the plain one, its
  -- result the promise's type.
  let promised : List (Json × List (String × Json)) := match g.guard with
    | some guard => [(guard.type, [("effect", toJson (CallEffects.Effect.mk footprint
        (some (if guard.asserts then .asserts guard.param else .guards guard.param)) false false onThrow))])]
    | none => []
  -- The plain signature states the footprint the declaration's claim
  -- proposes, which the declaration's own unit certifies; its extension
  -- discarding further actuals runs the same code, so it states the same.
  let plain : List (String × Json) :=
    if footprint = .top ∧ onThrow = false then [] else
      [("effect", toJson ({ CallEffects.Effect.ofFootprint footprint with onThrow } : CallEffects.Effect))]
  let extra := promised.map (fun (result, effect) => Json.mkObj (signature rest result effect)) ++
    if params.any (·.rest) then []
    else ((g.ret, plain) :: promised).map fun (result, effect) => Json.mkObj (signature [("rest", top)] result effect)
  let conjuncts := if extra.isEmpty then [] else [("and", toJson extra)]
  return Json.mkObj [("top", toJson false), ("atoms", toJson [Json.mkObj (signature rest g.ret plain ++ conjuncts)])]

/-- The same values with each label that is a union row, a declaration such as
`type Maybe = number | undefined`, replaced by one label per clause: a tag
slice tells the values apart clause by clause, never inside one label. -/
@[nospecialize] def byClause (R : Ty Tree) : Compiler (Ty Tree) := do
  let G := SourceTypes.graph (← table)
  let parts ← R.mapM fun a =>
    let cs := PositiveRules.expand G [a]
    if !G.plain a || cs.length ≤ 1 then pure [a] else cs.mapM fun c => lower (SourceTypes.use c)
  pure parts.flatten.eraseDups

/-- The type claimed at an expression a closure plan is built for. -/
@[nospecialize] def closureType (fc : SourceClaims.Function Tree) (e : Fragment.Expr) : Compiler (Ty Tree) :=
  exprType fc e

end
end Verification.SourceExtraction
