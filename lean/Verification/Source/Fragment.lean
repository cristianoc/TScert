-- ResolutionWire.lean reads resolution slots on the wire; without it the fragment cannot represent a resolution-qualified binder.
import Verification.Source.ResolutionWire
import Verification.Types.Claim

/-! # The fragment language

The subset of TypeScript this pipeline accepts, as an abstract syntax tree:
functions, statements, expressions and type parameters. The tree is declared on
the producer side in `tools/fragment.mts` and written by `tools/fragment-parse.mts`;
the decoders here read that JSON, so the two files describe one language.

Raw claims travel alongside the tree. Types remain JSON until consumed, so
unsupported unused claims do not become invented types; `FragmentTypes`
translates the ones consumed. -/
namespace Verification.Fragment
open Lean

/-- Whether a source key is one the model's representation of keys moves
(`escapedSpelling`): an array's store, an object's prototype and a class's
prototype object's own key (`classKeyOf`) live under keys no source property
may name, the store's `[]` and every name in double brackets, and a key
beginning with the escape `[!` is where the representation puts a key so
spelled. A source key is refused where its representation (`escapeKey`) is
not itself, so that a key the source spells and the same key computed at run
time (`propertyKey`) are one. -/
def reservedSourceKey (s : String) : Bool := escapedSpelling s.toList

/-- The key class `C`'s prototype object owns and no other object does:
`x instanceof C` looks for it along `x`'s prototype chain. -/
def classKeyOf (cls : String) : String := "[[" ++ cls ++ ".prototype]]"

/-- The module binding holding class `C`'s prototype object. -/
def prototypeBindingOf (cls : String) : String := cls ++ ".[[prototype]]"

/-- Class `C`'s own binding of its name, which its instance members read: the
class value, a module value of the initialization unit at the class's
construct signature (`SourceClaimJson`, the module values). -/
def selfBindingOf (cls : String) : String := cls ++ ".[[self]]"

#guard reservedSourceKey (classKeyOf "C") && reservedSourceKey "[[proto]]" && reservedSourceKey "[]" &&
  reservedSourceKey "[!x" && !reservedSourceKey "[x" && !reservedSourceKey "a"

/-- A key the source spells: any but a reserved one. -/
def protoKeyName : String := "[[proto]]"

#guard PropKey.str protoKeyName == CallArguments.protoField

def sourceKey (s : String) : Except String String :=
  if reservedSourceKey s then throw s!"'{s}' is internal to the model, not a source property"
  else pure s

/-- `key in o` looks the key up along `o`'s prototype chain; the model's test
(`Tag.hasKey`) asks whether the object owns it. The two agree for a key none
of the built-in prototypes an object of the fragment inherits from holds, and
that no own key of the built-in making the model leaves out names: an array's
`length` and indices, a function's `length`, `name` and `prototype`. The
names are node's (`Object.getOwnPropertyNames` of `Object.prototype`,
`Array.prototype` and `Function.prototype`), a trusted list: a builtins whose
prototypes hold another string key would answer `true` where the model
answers `false`. A key the model reserves for itself is refused too. -/
def inKeyRefusal (key : String) : Option String :=
  let objectKeys := objectProtoKeys
  let arrayKeys := ["length", "at", "concat", "copyWithin", "fill", "find", "findIndex", "findLast",
    "findLastIndex", "lastIndexOf", "pop", "push", "reverse", "shift", "unshift", "slice", "sort",
    "splice", "includes", "indexOf", "join", "keys", "entries", "values", "forEach", "filter", "flat",
    "flatMap", "map", "every", "some", "reduce", "reduceRight", "toReversed", "toSorted",
    "toSpliced", "with"]
  let functionKeys := ["name", "prototype", "apply", "bind", "call", "arguments", "caller"]
  -- A regular expression owns `lastIndex` and inherits the rest from
  -- `RegExp.prototype`; the model's regex states methods and no property.
  let regexpKeys := ["lastIndex", "source", "flags", "global", "ignoreCase", "multiline", "sticky",
    "unicode", "unicodeSets", "dotAll", "hasIndices", "exec", "test", "compile"]
  if reservedSourceKey key then some "the model reserves this key"
  else if regexpKeys.contains key then
    some "a regular expression owns it or inherits it from RegExp.prototype"
  else if objectKeys.contains key then some "every object inherits it from Object.prototype"
  else if arrayKeys.contains key then some "an array owns it or inherits it from Array.prototype"
  else if functionKeys.contains key then some "a function owns it or inherits it from Function.prototype"
  else if !key.isEmpty && key.all Char.isDigit && (key == "0" || key.front != '0') then
    some "an array index names an element, which the model keeps in the array's store"
  else none

/-- A unary numeric operator: `-e`, `+e` and `~e`; and `typeof e`, the string
naming the operand's shape. -/
inductive UnaryOp where
  | neg | plus | bitNot | typeof
  deriving Repr, DecidableEq

/-- The test a logical assignment makes on the target's current value. -/
inductive LogicalOp where
  | nullish | orElse | andAlso
  deriving Repr, DecidableEq

/-- One element of an array assignment: position `index` is written to
`target`, a mutable local (`var`) or a field (`read`, `index`), with a
default when the read is undefined. -/
structure ArrayElem (Expr : Type) where
  index : Nat
  target : Expr
  default_ : Option Expr

/-- What a pattern binds at one place: a name, or a nested pattern over the
value found there. An object pattern reads its fields in order; an array
pattern reads its positions in order, a hole being a position no element
names, and its rest, at the position after its elements, collects the
positions from there on into a fresh array: by reads where it is not a
`slice`, and by a call of `%RestFrom:k%` (`restFromName`) where it is one.
An element's default replaces a read that is `undefined`. -/
inductive Pattern (Expr : Type) where
  | name (name : String) (namePos : Span)
  /-- An object pattern: its properties, then, with `rest`, the fresh object
  holding the source's other own enumerable properties, bound where its span
  is claimed. -/
  | object (pos : Span) (props : List (String × Pattern Expr × Option Expr))
      (rest : Option (Span × Pattern Expr))
  | array (pos : Span) (elems : List (Nat × Pattern Expr × Option Expr))
      (rest : Option (Nat × Span × Bool × Pattern Expr))

/-- The names a pattern binds, in the order it binds them. -/
partial def Pattern.names {Expr : Type} : Pattern Expr → List String
  | .name n _ => [n]
  | .object _ props rest => props.flatMap (fun (_, t, _) => t.names) ++
      ((rest.map fun (_, t) => t.names).getD [])
  | .array _ elems rest => elems.flatMap (fun (_, t, _) => t.names) ++
      ((rest.map fun (_, _, _, t) => t.names).getD [])

/-- Where a pattern stands in the source: a name's span, or the whole pattern's. -/
def Pattern.span {Expr : Type} : Pattern Expr → Span
  | .name _ p | .object p _ _ | .array p _ _ => p

/-- A pattern's defaults, in evaluation order. -/
partial def Pattern.defaults {Expr : Type} : Pattern Expr → List Expr
  | .name .. => []
  | .object _ props rest => props.flatMap (fun (_, t, d) => d.toList ++ t.defaults) ++
      ((rest.map fun (_, t) => t.defaults).getD [])
  | .array _ elems rest => elems.flatMap (fun (_, t, d) => d.toList ++ t.defaults) ++
      ((rest.map fun (_, _, _, t) => t.defaults).getD [])

/-- The intrinsic a slice rest after `k` positions calls (`intrinsics.mts`):
`<T>(xs: readonly [unknown?, …, ...T[]]) => T[]`, `k` optional positions, a
fresh array of `xs`'s elements from `k` to its current length, trusted. -/
def restFromName (k : Nat) : String := s!"%RestFrom:{k}%"

/-- A pattern's slice rests, each a call of its `%RestFrom:k%`: the rest's
span, which is the call's, and `k`. -/
partial def Pattern.slices {Expr : Type} : Pattern Expr → List (Span × Nat)
  | .name .. => []
  | .object _ props rest => props.flatMap (fun (_, t, _) => t.slices) ++
      ((rest.map fun (_, t) => t.slices).getD [])
  | .array _ elems rest => elems.flatMap (fun (_, t, _) => t.slices) ++
      ((rest.map fun (k, p, slice, t) => (if slice then [(p, k)] else []) ++ t.slices).getD [])

/-- The calls of the intrinsics slice rests make, as `Expr.callees` lists a
call: the call at the rest's span, the intrinsic read at its `...`. -/
def sliceCallees (slices : List (Span × Nat)) : List (Span × Span × String × List Json) :=
  slices.map fun (p, k) => (p, (p.1, p.1 + "...".length), restFromName k, [])

/-- A lexically scoped rigid binder. Bounds may mention outer or preceding
binders; the source decoder that consumes the expression checks that scope. -/
structure TypeParam where
  name : String
  bound : Option Json
  resolution : Option ResolutionWire.Slots

def decodeTypeParam (j : Json) : Except String TypeParam := do
  fieldsExactly j ["name", "bound", "resolution"]
  let name ← jStr (← jField j "name")
  if name.isEmpty then throw "empty type-parameter name"
  let b ← jField j "bound"
  let r ← jField j "resolution"
  let resolution ← if r == .null then pure none else some <$> fromJson? r
  ResolutionWire.validateOwnership [(name, resolution)]
  return ⟨name, if b == Json.null then none else some b, resolution⟩

def decodeTypeParams (raw : List Json) : Except String (List TypeParam) := do
  let parameters ← raw.mapM decodeTypeParam
  ResolutionWire.validateOwnership (parameters.map fun p => (p.name, p.resolution))
  return parameters

/-- A user-defined guard's promise (`x is T`, `asserts x is T`), written in
its result annotation: the actual it is about, by position among a call's
actuals, whether it is an assertion function's, and `T`'s annotation. -/
structure Guard where
  param : Nat
  asserts : Bool
  type : Json

mutual
inductive Expr where
  | var (pos : Span) (name : String)
  | lit (pos : Span) (v : Claim.Val)
  | logical (pos : Span) (andOp : Bool) (left right : Expr)
  | coalesce (pos : Span) (left right : Expr)
  /-- An optional chain, `r?.b`, `r?.[k]`, `r?.(a)` and what follows them in
  the chain: the receiver once; `undefined` when it is null or undefined,
  else `body`, in which the variable `chainName` (spelled at `mark`, the
  `?.` token) is the receiver's value. -/
  | optional (pos mark : Span) (receiver body : Expr)
  | shapeTest (pos : Span) (tag : Tag) (equal : Bool) (e : Expr)
  /-- Strict equality awaiting a checked singleton operand from source claims. -/
  | equality (pos : Span) (equal : Bool) (left right : Expr)
  | singletonTest (pos : Span) (tag : Tag) (equal testLeft : Bool) (left right : Expr)
  | not (pos : Span) (e : Expr)
  /-- `e as T`, `e satisfies T`, `e!` or `e as const`: the operand's value. An
  annotation is an obligation the operand must meet, never a fact about it. -/
  | cast (pos : Span) (annot : Option Json) (e : Expr)
  /-- An object literal: one named field per initializer, in source order. A
  key is a string, or the symbol a `unique symbol` constant names
  (`[Symbol.iterator]`). -/
  | alloc (pos : Span) (names : List PropKey) (es : List Expr)
  /-- An object literal with spreads of values, in source order: a named
  field (`some k`) or a spread (`none`), each part evaluated where written and
  a spread's operand copied as soon as it is evaluated (DESIGN.md, "Object
  literals"). -/
  | build (pos : Span) (names : List (Option String)) (es : List Expr)
  /-- A named read: a string key, or, for `e[k]` with `k` a `unique symbol`
  constant, that symbol's key. -/
  | read (pos : Span) (field : PropKey) (e : Expr)
  /-- A named write, keyed as a named read is. -/
  | write (pos : Span) (field : PropKey) (receiver rhs : Expr)
  /-- `e[key]`: the receiver, then the key, then the read of the field the
  key's claimed type names. The decoder leaves the field unresolved; the
  extractor fills it from the key's claim, a string singleton, and the key's
  expression obligation must establish it. -/
  | index (pos : Span) (field : Option String) (e key : Expr)
  | indexWrite (pos : Span) (field : Option String) (receiver key rhs : Expr)
  /-- An array literal: one element per initializer, in source order.
  `spreads` are the positions of the elements written with `...`, in
  order: each stands for the elements of its operand's store, read where it
  is written. -/
  | arrayLit (pos : Span) (elems : List Expr) (spreads : List Nat)
  /-- `[a, b = d, ...r] = rhs`: the right side once, then, for each target
  in turn, its reference (a field's receiver, then its key), then its
  position of the store, or its default when that read is undefined, written
  to the reference; the rest's target takes the fresh array of the positions
  after them, claimed at the rest's span; the value is the right side. -/
  | arrayAssign (pos : Span) (targets : List (ArrayElem Expr)) (rest : Option (Span × Bool × ArrayElem Expr))
      (rhs : Expr)
  /-- `e[key]` with a numeric key: an element read of the array's store, and
  its assignment; resolved from `index` and `indexWrite` by the key's claim. -/
  | elemAt (pos : Span) (e key : Expr)
  | elemWrite (pos : Span) (receiver key rhs : Expr)
  /-- A binary operator on primitive operands, left operand first:
  arithmetic, `**`, a relational comparison, or `+` concatenating strings. A
  template literal is the concatenation of its parts, in order, starting from
  its first string. -/
  | arith (pos : Span) (op : Arith) (l r : Expr)
  /-- `key in e` with a key that is not a string literal: the key, then the
  operand, then the test of the key the key's claim names, one of a union of
  string singletons (`hasKey`). A string literal key is a `shapeTest`. -/
  | inKeys (pos : Span) (key e : Expr)
  /-- `left, right`: the left operand for its effects, its value discarded,
  then the right operand's value. `void e` is `e, undefined`. -/
  | comma (pos : Span) (left right : Expr)
  /-- A unary numeric operator on its operand's value. -/
  | unary (pos : Span) (op : UnaryOp) (e : Expr)
  /-- `target op= rhs`, or an increment when `rhs` is absent: the target's
  parts once, its value read, the right side, the operation, the write back.
  `post` makes the old value the expression's value. -/
  | update (pos : Span) (op : Arith) (target : Expr) (rhs : Option Expr) (post : Bool)
  /-- `target ??= rhs`, `||=` or `&&=`: the target's parts once, its value
  read, the test on it, and the right side written only on the writing arm.
  The Boolean forms need a Boolean target: truthiness is only that. -/
  | logicalAssign (pos : Span) (op : LogicalOp) (target rhs : Expr)
  /-- Read a local once; assign and return the RHS only when nullish. -/
  | nullishAssign (pos : Span) (name : String) (namePos : Span) (rhs : Expr)
  /-- Assignment to a mutable local, which is an expression: it yields the
  value written, where the calculus's write yields null. -/
  | assign (pos : Span) (name : String) (namePos : Span) (rhs : Expr)
  | withValue (pos : Span) (fn initial : Expr) (functionType bagType : Json)
  /-- `Object.assign(target, ...sources)` other than the callable form: the
  target, then each source, copied onto the target when it is evaluated; the
  value is the target. -/
  | objectAssign (pos : Span) (target : Expr) (sources : List Expr)
  /-- `params` are what the body reads. `defaults` names the positions a call
  may omit and the expression that replaces the `undefined` bound there; the
  advertised domain at such a position is the parameter's type with
  `undefined`. `receiver` is none for an arrow, whose `this` is a capture; an
  ordinary function binds the receiver of each call as `this`, at the
  annotation given here, by its code's kind: `sloppy` for sloppy code that
  reads `this`, whose call converts a receiver that is not an object, and
  `call` for any other (`Invoke`). -/
  | lambda (pos : Span) (receiver : Option (Json × Invoke)) (typeParams : List TypeParam)
      (params : List (String × Json)) (defaults : List (Nat × Expr)) (rest : Bool)
      (result : Option Json) (guard : Option Guard) (body : Expr)
  /-- A class value: its constructor `lambda` as construct-only code, and its
  static fields, each the binding its initializer bound, in member order. -/
  | ctor (pos : Span) (lam : Expr) (statics : List (PropKey × Expr))
  /-- `new callee(args)`: the callee, then the actuals, then its construct code.
  `spreads` marks tuple operands expanded at their required positions.
  `typeArgs` are the explicit type arguments written on it, empty where none
  are: the call's claimed instance must agree with them. -/
  | construct (pos : Span) (callee : Expr) (args : List Expr) (spreads : List Nat) (typeArgs : List Json)
  | bindWithReceiver (pos : Span) (callee receiver : Expr) (args : List Expr)
  | callWithReceiver (pos : Span) (callee receiver : Expr) (args : List Expr)
  /-- `f.apply(r, list)`: the target, the receiver and the list are saved,
  then the list's length and each index are read in order, before the call. No
  list, or a null or undefined one, gives no actuals. -/
  | applyWithReceiver (pos : Span) (callee receiver : Expr) (list : Option Expr)
  /-- `spreads` are the positions of the arguments written with `...`, in
  increasing order: each stands for the elements of its operand, read where it
  is written. `typeArgs` are the explicit type arguments written on the call,
  empty where none are: the call's claimed instance must agree with them. -/
  | call (pos : Span) (callee : Expr) (args : List Expr) (spreads : List Nat)
      (typeArgs : List Json)
  /-- A call through a property reference, `o.m(a)`: `callee` is the `read`
  (or `index`) of the method; its object is the receiver. The object is saved,
  the method read and saved, the actuals evaluated, then the saved method is
  invoked with the saved object. `typeArgs` are the explicit type arguments
  written on the call, empty where none are: they instantiate the method's
  leading binders, and the call's claimed instance must agree with them. -/
  | invoke (pos : Span) (callee : Expr) (args : List Expr) (spreads : List Nat)
      (typeArgs : List Json)
  /-- A source ternary, `cond ? thn : els`: its own expression claim supplies
  its result. -/
  | ifBody (pos : Span) (cond thn els : Expr)
  /-- A closure body written as statements, the body of a function: its
  parameters written as patterns or with defaults are destructured by its
  first statements, and a body that can complete returns `undefined` at its
  closing brace. Only a lambda's body is one. -/
  | block (pos : Span) (body : List Stmt)

/-- One declarator of a `const` or `let`. -/
structure Binding where
  name : String
  namePos : Span
  annot : Option Json
  init : Expr

inductive Stmt where
  | ret (pos : Span) (e : Expr)
  /-- Immutable bindings, left to right, each initializer seeing the earlier
  ones. The statement is the entry; no cut separates its declarators. -/
  | constants (pos : Span) (bindings : List Binding)
  /-- Mutable locals, one private cell each. A binding's annotation is the
  storage contract every assignment is checked against; absent, the producer
  supplies one. What the initializer happens to produce is not what the
  binding may later hold. -/
  | mutables (pos : Span) (bindings : List Binding)
  /-- A pattern on a `const`, `const target = init`: the initializer once,
  then the target binds it, its default (a parameter's) replacing it where it
  is `undefined`. The parser also writes a parameter pattern or default as
  one, over the parameter's hidden name. -/
  | destructure (pos : Span) (target : Pattern Expr) (default_ : Option Expr) (init : Expr)
  | ite (pos : Span) (cond : Expr) (thn : List Stmt) (els : Option (List Stmt))
  /-- `break`: to the end of the nearest enclosing loop, or with a label, of
  the enclosing block of that label. -/
  | brk (pos : Span) (label : Option String)
  | cont (pos : Span)
  /-- `while (cond) body`, and the loop of `for (…; cond; update) body`: the
  end of the body and every `continue` targeting the loop run `update`, then
  return to the head. A `while` has none. -/
  | loop (pos : Span) (cond : Expr) (body : List Stmt) (update : List Stmt)
  /-- `{ body }`: its statements in a lexical scope of their own, and no entry
  of their own: the first statement's is the block's. A labeled block is where
  a `break` of its label goes: a lowered `switch` is made of them. -/
  | block (pos : Span) (label : Option String) (body : List Stmt)
  /-- `for (const name of iterable) body`: the iterable once, then the
  iteration intrinsic `iterate` (one of `iterateNames`, which the parser picks
  by the iterable's type) steps its iterator, binding each element to `name`
  for one run of the body. -/
  | forOf (pos : Span) (name : String) (namePos : Span) (iterate : String) (iterable : Expr)
      (body : List Stmt)
  | effect (pos : Span) (e : Expr)
  /-- `throw e`: `e`, then a throw of its value, which leaves the function
  unless an enclosing `try` catches it. -/
  | throw (pos : Span) (e : Expr)
  /-- `try { body } catch (param) { handler } finally { finalizer }`. A throw
  in the body goes to the handler, which binds the thrown value to `param`
  (`unknown`), when there is one; the finalizer runs on every way out of the
  body and the handler, a normal completion, a `return` or a throw, and then
  that way out resumes, unless the finalizer itself leaves. -/
  | tryStmt (pos : Span) (body : List Stmt)
      (handler : Option (Option (String × Span) × List Stmt)) (finalizer : Option (List Stmt))
  /-- The body of a `for...of` loop over an iterable the program defines, the
  last statement of its loop (the parser's lowering of the iterator
  protocol): `close`, IteratorClose, runs where `body` is left otherwise than
  by completing or by a `continue` of the loop: before a `break` of the loop
  leaves it, before a `return` returns, and, its own throws discarded, before
  a throw out of `body` resumes. -/
  | closing (pos : Span) (close : List Stmt) (body : List Stmt)
end

/-- The intrinsic a `for...of` over an array steps (`intrinsics.mts`):
`<T>(xs: readonly T[]) => () => { readonly value: T } | null`, trusted. -/
def iterateName : String := "%Iterate%"

/-- The iteration intrinsics, one per kind of host iterable (`intrinsics.mts`):
an array's, a string's (by code point), a `Set`'s, a `Map`'s, a host
collection iterator's, a native regex's match iterator, and the entries a
`for...in` over a dictionary visits.
Each is `() => { readonly value: E } | null` of the iterable at its
signature; none has a `return`, so an early exit calls nothing. A loop names
one of them and no other value. -/
def iterateNames : List String :=
  [iterateName, "%Iterate:string%", "%Iterate:Set%", "%Iterate:Map%", "%Iterate:Iterator%",
    "%Iterate:RegExpString%", "%Iterate:ForIn%"]

/-- The name an optional chain's body reads its saved receiver by: no source
identifier is spelled so. -/
def chainName : String := "?."

mutual
/-- Lexical dependencies, including deferred bodies. Exhaustive so a new
executable source form cannot bypass parameter-initialization checks. -/
partial def Expr.freeNames : Expr → List String
  | .var _ n => [n]
  | .lit .. => []
  | .lambda _ receiver _ ps ds _ _ _ b =>
    -- An ordinary function binds its own `this`; an arrow captures it.
    ((ds.flatMap fun d => d.2.freeNames) ++ b.freeNames).filter
      (fun n => !(ps.map Prod.fst).contains n && (receiver.isNone || n != "this"))
  | .shapeTest _ _ _ e | .not _ e | .unary _ _ e | .cast _ _ e | .read _ _ e => e.freeNames
  | .ctor _ e fs => e.freeNames ++ fs.flatMap (·.2.freeNames)
  | .construct _ f args _ _ => f.freeNames ++ args.flatMap Expr.freeNames
  | .alloc _ _ es | .build _ _ es | .arrayLit _ es _ => es.flatMap Expr.freeNames
  | .logical _ _ a b | .coalesce _ a b | .equality _ _ a b
  | .singletonTest _ _ _ _ a b | .write _ _ a b | .index _ _ a b
  | .elemAt _ a b | .arith _ _ a b | .logicalAssign _ _ a b | .comma _ a b | .inKeys _ a b
  | .withValue _ a b _ _ => a.freeNames ++ b.freeNames
  | .indexWrite _ _ a b c | .elemWrite _ a b c | .ifBody _ a b c =>
    a.freeNames ++ b.freeNames ++ c.freeNames
  | .update _ _ a b _ => a.freeNames ++ (b.map Expr.freeNames).getD []
  | .assign _ n _ e | .nullishAssign _ n _ e => n :: e.freeNames
  | .arrayAssign _ targets rest rhs => rhs.freeNames ++ targets.flatMap
      (fun q => q.target.freeNames ++ (q.default_.map Expr.freeNames).getD []) ++
      ((rest.map (·.2.2.target.freeNames)).getD []) ++
      -- A slice rest reads its `%RestFrom:k%`.
      (rest.filter (·.2.1)).toList.map (fun (_, _, q) => restFromName q.index)
  | .bindWithReceiver _ f r args | .callWithReceiver _ f r args =>
    f.freeNames ++ r.freeNames ++ args.flatMap Expr.freeNames
  | .applyWithReceiver _ f r list => f.freeNames ++ r.freeNames ++ (list.map Expr.freeNames).getD []
  | .call _ f args _ _ | .invoke _ f args _ _ => f.freeNames ++ args.flatMap Expr.freeNames
  | .objectAssign _ t ss => t.freeNames ++ ss.flatMap Expr.freeNames
  | .optional _ _ r b => r.freeNames ++ b.freeNames.filter (· != chainName)
  | .block _ ss => stmtsFreeNames ss

/-- Every direct call of a named function: the call's span, the callee read's
span, the name, as `freeNames` binds names, and the explicit type arguments
written on the call. -/
partial def Expr.callees : Expr → List (Span × Span × String × List Json)
  | .var .. | .lit .. => []
  | .lambda _ _ _ ps ds _ _ _ b =>
    ((ds.flatMap fun d => d.2.callees) ++ b.callees).filter
      (fun c => !(ps.map Prod.fst).contains c.2.2.1)
  -- A read off a name instantiates it, as a call does, where it is a
  -- generic class value whose static field it reads.
  | .read p _ (.var q n) => [(p, q, n, [])]
  | .shapeTest _ _ _ e | .not _ e | .unary _ _ e | .cast _ _ e | .read _ _ e => e.callees
  | .ctor _ e fs => e.callees ++ fs.flatMap (·.2.callees)
  | .construct p f args _ ts =>
    (match f with | .var q n => [(p, q, n, ts)] | _ => []) ++ f.callees ++ args.flatMap Expr.callees
  | .alloc _ _ es | .build _ _ es | .arrayLit _ es _ => es.flatMap Expr.callees
  | .logical _ _ a b | .coalesce _ a b | .equality _ _ a b
  | .singletonTest _ _ _ _ a b | .write _ _ a b | .index _ _ a b
  | .elemAt _ a b | .arith _ _ a b | .logicalAssign _ _ a b | .comma _ a b | .inKeys _ a b
  | .withValue _ a b _ _ => a.callees ++ b.callees
  | .indexWrite _ _ a b c | .elemWrite _ a b c | .ifBody _ a b c =>
    a.callees ++ b.callees ++ c.callees
  | .update _ _ a b _ => a.callees ++ (b.map Expr.callees).getD []
  | .assign _ _ _ e | .nullishAssign _ _ _ e => e.callees
  | .arrayAssign _ targets rest rhs => rhs.callees ++ targets.flatMap
      (fun q => q.target.callees ++ (q.default_.map Expr.callees).getD []) ++
      ((rest.map (·.2.2.target.callees)).getD []) ++
      sliceCallees ((rest.filter (·.2.1)).toList.map fun (p, _, q) => (p, q.index))
  | .bindWithReceiver _ f r args | .callWithReceiver _ f r args =>
    f.callees ++ r.callees ++ args.flatMap Expr.callees
  | .applyWithReceiver _ f r list => f.callees ++ r.callees ++ (list.map Expr.callees).getD []
  | .call p f args _ ts =>
    (match f with | .var q n => [(p, q, n, ts)] | _ => []) ++ f.callees ++ args.flatMap Expr.callees
  | .invoke _ f args _ _ => f.callees ++ args.flatMap Expr.callees
  | .objectAssign _ t ss => t.callees ++ ss.flatMap Expr.callees
  | .optional _ _ r b => r.callees ++ b.callees.filter (·.2.2.1 != chainName)
  | .block _ ss => stmtsCallees ss

/-- The names a statement binds for the statements after it. -/
partial def Stmt.bound : Stmt → List String
  | .constants _ bs | .mutables _ bs => bs.map (·.name)
  | .destructure _ t _ _ => t.names
  | _ => []

/-- A statement list's lexical dependencies: each statement's, less the names
the statements before it bind. -/
partial def stmtsFreeNames : List Stmt → List String
  | [] => []
  | s :: rest => s.freeNames ++ (stmtsFreeNames rest).filter (!s.bound.contains ·)

partial def Stmt.freeNames : Stmt → List String
  | .ret _ e | .effect _ e | .throw _ e => e.freeNames
  | .constants _ bs | .mutables _ bs =>
    -- Each initializer sees the earlier declarators.
    (bs.zipIdx.flatMap fun (b, i) =>
      b.init.freeNames.filter fun n => !((bs.take i).map (·.name)).contains n)
  | .destructure _ t d init => init.freeNames ++ (d.toList ++ t.defaults).flatMap Expr.freeNames ++
    t.slices.map (restFromName ·.2)
  | .ite _ c t e => c.freeNames ++ stmtsFreeNames t ++ stmtsFreeNames (e.getD [])
  | .loop _ c b u => c.freeNames ++ stmtsFreeNames b ++ stmtsFreeNames u
  | .block _ _ b => stmtsFreeNames b
  -- The loop reads its iteration intrinsic, which no expression names.
  | .forOf _ name _ it i b => it :: i.freeNames ++ (stmtsFreeNames b).filter (· != name)
  | .tryStmt _ b h f => stmtsFreeNames b ++
    (match h with
     | some (some (name, _), hs) => (stmtsFreeNames hs).filter (· != name)
     | some (none, hs) => stmtsFreeNames hs
     | none => []) ++ stmtsFreeNames (f.getD [])
  | .closing _ c b => stmtsFreeNames b ++ stmtsFreeNames c
  | .brk .. | .cont .. => []

/-- A statement list's direct calls of named functions, less those of names
the statements before them bind. -/
partial def stmtsCallees : List Stmt → List (Span × Span × String × List Json)
  | [] => []
  | s :: rest => s.callees ++ (stmtsCallees rest).filter (!s.bound.contains ·.2.2.1)

/-- Every direct call of a named function in a statement. -/
partial def Stmt.callees : Stmt → List (Span × Span × String × List Json)
  | .ret _ e | .effect _ e | .throw _ e => e.callees
  | .tryStmt _ b h f => b.flatMap Stmt.callees ++ ((h.map (·.2)).getD []).flatMap Stmt.callees ++
    (f.getD []).flatMap Stmt.callees
  | .constants _ bs | .mutables _ bs => bs.flatMap fun b => b.init.callees
  | .destructure _ target d init => init.callees ++
    (d.toList ++ target.defaults).flatMap Expr.callees ++ sliceCallees target.slices
  | .ite _ c t e => c.callees ++ t.flatMap Stmt.callees ++ (e.getD []).flatMap Stmt.callees
  | .loop _ c b u => c.callees ++ b.flatMap Stmt.callees ++ u.flatMap Stmt.callees
  | .block _ _ b => b.flatMap Stmt.callees
  -- The loop calls its iteration intrinsic at its own span, reading it at
  -- the `for` keyword, which is no expression and has no claim.
  | .forOf p name _ it i b => (p, (p.1, p.1 + "for".length), it, []) :: i.callees ++
    (b.flatMap Stmt.callees).filter (·.2.2.1 != name)
  | .closing _ c b => b.flatMap Stmt.callees ++ c.flatMap Stmt.callees
  | .brk .. | .cont .. => []
end

/-- Closure conversion for acyclic forward captures. Only a literal closure's
allocation can move; every potentially effectful initializer keeps source order.
No pending binding may be read or exposed by another executing initializer.
A deferred closure is allocated exactly once, after its captures exist. Source
parameters are immutable in this fragment, and mutable outer captures retain
cell identity. Thus delaying this unobservable allocation preserves captures,
aliasing and effects (up to fresh-location renaming). Cyclic/escaping pending
closures require an explicit initialization frame and are refused here. -/
def parameterOrder (ps : List (String × Json)) (defaults : List (Nat × Expr)) :
    Except String (List Nat) := do
  let names := ps.map Prod.fst
  let dependencies (i : Nat) := ((defaults.lookup i).map Expr.freeNames).getD []
    |>.filter names.contains
  let ready (done : List Nat) (i : Nat) :=
    (dependencies i).all fun n => done.any fun j => names[j]? == some n
  let mut done := []
  let mut pending := []
  for i in List.range ps.length do
    if ready done i then done := done ++ [i]
    else
      match defaults.lookup i with
      | some (.lambda ..) => pending := pending ++ [i]
      | _ => throw "parameter default may only read initialized earlier parameters and captures; a pending closure cannot be invoked or exposed"
    -- At most one new dependency is discharged per iteration; the bounded
    -- fixpoint also handles chains of literal closures capturing one another.
    for _ in List.range ps.length do
      if let some j := pending.find? (ready done) then
        done := done ++ [j]
        pending := pending.filter (· != j)
  if !pending.isEmpty then throw "cyclic parameter-default captures require an initialization frame"
  return done

/-- Why sloppy code that reads `this` is refused at a receiver type that may
hold a value other than an object. -/
def sloppyReceiverReason : String :=
  "sloppy code that reads `this` needs a receiver type of objects only: a sloppy call replaces an undefined or primitive receiver by the global object or a wrapper object, which the model does not have"

def Expr.span : Expr → Span
  | .ifBody p _ _ _ | .equality p _ _ _ | .singletonTest p _ _ _ _ _ | .coalesce p _ _ | .logical p _ _ _ => p
  | .index p _ _ _ | .indexWrite p _ _ _ _ | .arith p _ _ _ | .update p _ _ _ _ | .logicalAssign p _ _ _ => p
  | .comma p _ _ | .inKeys p _ _ | .optional p _ _ _ | .block p _ => p
  | .arrayLit p _ _ | .elemAt p _ _ | .elemWrite p _ _ _ | .arrayAssign p _ _ _ => p
  | .var p _ | .lit p _ | .shapeTest p _ _ _ | .not p _ | .unary p _ _ | .cast p _ _ | .alloc p _ _ | .build p _ _ | .read p _ _ | .write p _ _ _ | .assign p _ _ _ | .nullishAssign p _ _ _ | .withValue p _ _ _ _ | .objectAssign p _ _ | .lambda p _ _ _ _ _ _ _ _ | .call p _ _ _ _ | .invoke p _ _ _ _ | .callWithReceiver p _ _ _ | .bindWithReceiver p _ _ _ | .applyWithReceiver p _ _ _ | .ctor p _ _ | .construct p _ _ _ _ => p

/-- What evaluating an assignment target's reference evaluates: a field's
receiver, then its key; nothing for a local. -/
def Expr.referenceParts : Expr → List Expr
  | .read _ _ receiver => [receiver]
  | .index _ _ receiver key | .elemAt _ receiver key => [receiver, key]
  | _ => []

/-- The local an assignment target writes, if it is one. -/
def Expr.targetLocal : Expr → Option String
  | .var _ name => some name
  | _ => none

/-- One element of an array pattern, decoded with the given expression
decoder, since the structure is shared by statements and expressions. -/
def decodeArrayElem (decodeExpr : Json → Except String Expr) (q : Json) :
    Except String (ArrayElem Expr) := do
  fieldsExactly q ["index","target","default_"]
  let d ← jField q "default_"
  let dflt ← if d == .null then pure none else some <$> decodeExpr d
  return ⟨← (← jField q "index").getNat?, ← decodeExpr (← jField q "target"), dflt⟩

/-- A statement's own span. -/
def Stmt.pos : Stmt → Span
  | .ret p _ | .constants p _ | .mutables p _ | .destructure p _ _ _
  | .ite p _ _ _ | .loop p _ _ _ | .forOf p _ _ _ _ _ | .brk p _ | .cont p | .effect p _
  | .block p _ _ | .throw p _ | .tryStmt p _ _ _ | .closing p _ _ => p

structure Param where
  name : String
  ty : Json
  /-- A rest parameter stands for the required positions of its tuple
  contract, and binds the array its arguments are collected into. -/
  rest : Bool := false
structure Fn where
  name : String
  namePos : Span
  params : List Param
  ret : Json
  body : List Stmt
  /-- Whether a call of the function converts a receiver that is not an
  object, as a call of sloppy code does; a leading `this` parameter is the
  receiver. -/
  convertsReceiver : Bool
  /-- The promise its result annotation states, beside its plain result `ret`. -/
  guard : Option Guard := none

private def decodeArith (j : Json) : Except String Arith := do
  match ← jStr j with
  | "add" => pure .add
  | "sub" => pure .sub
  | "mul" => pure .mul
  | "div" => pure .div
  | "pow" => pure .pow
  | "rem" => pure .rem
  | "xor" => pure .xor
  | "bitAnd" => pure .bitAnd
  | "bitOr" => pure .bitOr
  | "shl" => pure .shl
  | "shr" => pure .shr
  | "ushr" => pure .ushr
  | "lt" => pure .lt
  | "le" => pure .le
  | "gt" => pure .gt
  | "ge" => pure .ge
  | op => throw s!"unknown binary operator '{op}'"

/-- A pattern: a name, or a nonempty object or array pattern whose positions
increase, holes between them, and whose rest comes after them. -/
partial def decodePattern (decodeExpr : Json → Except String Expr) (j : Json) :
    Except String (Pattern Expr) := do
  let target (q : Json) : Except String (Pattern Expr × Option Expr) := do
    let d ← jField q "default_"
    let dflt ← if d == .null then pure none else some <$> decodeExpr d
    return (← decodePattern decodeExpr (← jField q "target"), dflt)
  match ← jStr (← jField j "k") with
  | "name" =>
    fieldsExactly j ["k","name","pos"]
    return .name (← jStr (← jField j "name")) (← jSpan j "pos")
  | "object" =>
    fieldsExactly j ["k","pos","props","rest"]
    let props ← (← jArr j "props").mapM fun q => do
      fieldsExactly q ["field","target","default_"]
      let (t, d) ← target q
      return (← sourceKey (← jStr (← jField q "field")), t, d)
    let rest ← match ← jField j "rest" with
      | .null => pure none
      | r => do
        fieldsExactly r ["pos","target"]
        pure (some (← jSpan r "pos", ← decodePattern decodeExpr (← jField r "target")))
    if props.isEmpty && rest.isNone then throw "an empty pattern binds nothing"
    return .object (← jSpan j "pos") props rest
  | "array" =>
    fieldsExactly j ["k","pos","elems","rest"]
    let elems ← (← jArr j "elems").mapM fun q => do
      fieldsExactly q ["index","target","default_"]
      let (t, d) ← target q
      return (← (← jField q "index").getNat?, t, d)
    let rest ← match ← jField j "rest" with
      | .null => pure none
      | r => do
        fieldsExactly r ["index","pos","target","slice"]
        pure (some (← (← jField r "index").getNat?, ← jSpan r "pos", ← (← jField r "slice").getBool?,
          ← decodePattern decodeExpr (← jField r "target")))
    let indices := elems.map (·.1) ++ (rest.map (·.1)).toList
    if indices.isEmpty then throw "an empty pattern binds nothing"
    if !(indices.zip (indices.drop 1)).all (fun (a, b) => a < b) then
      throw "array pattern positions must increase"
    return .array (← jSpan j "pos") elems rest
  | k => throw s!"unknown pattern kind {k}"

/-- Explicit type arguments, written only where the source has them. -/
private def decodeTypeArgs (j : Json) : Except String (List Json) := do
  match (j.getObjVal? "typeArgs").toOption with
  | none => pure []
  | some written =>
    let ts := (← written.getArr?).toList
    if ts.isEmpty then throw "an empty type argument list is written by omitting it"
    pure ts

private def typeArgsField (typeArgs : List Json) : List String :=
  if typeArgs.isEmpty then [] else ["typeArgs"]

/-- A call's or an array literal's spread positions, and its exact fields:
`fields`, then `spreads` when written, then the optional ones. -/
private def decodeSpreads (j : Json) (arity : Nat) (optional : List String)
    (fields : List String := ["k","pos","callee","args"]) :
    Except String (List Nat) := do
  match (j.getObjVal? "spreads").toOption with
  | none => do
    fieldsExactly j (fields ++ optional)
    pure []
  | some marked => do
    fieldsExactly j (fields ++ "spreads" :: optional)
    let spreads ← (← marked.getArr?).toList.mapM fun i => do
      let i ← i.getNat?
      if i ≥ arity then throw "a spread position names no argument"
      pure i
    if spreads.isEmpty then throw "an empty spread list is written by omitting it"
    if !(spreads.zip spreads.tail).all (fun (a,b) => a < b) then
      throw "spread positions are listed once each, in order"
    pure spreads

/-- A jump's or block's label: a string, or null for none. -/
def decodeLabel (j : Json) : Except String (Option String) := do
  match ← jField j "label" with
  | .null => pure none
  | l => some <$> jStr l

/-- A guard's promise as the Fragment states it, or none. -/
def decodeGuard : Json → Except String (Option Guard)
  | .null => pure none
  | g => do
    fieldsExactly g ["param", "asserts", "type", "span"]
    let some param := (← jField g "param").getNat?.toOption | throw "a guard's parameter is a position"
    return some ⟨param, ← (← jField g "asserts").getBool?, ← jField g "type"⟩

mutual
partial def decodeExpr (j : Json) : Except String Expr := do
  let p ← jSpan j "pos"
  match ← jStr (← jField j "k") with
  | "id" => return .var p (← jStr (← jField j "name"))
  -- No declaration can bind the name `this`, so it names the receiver slot.
  | "this" =>
    fieldsExactly j ["k","pos"]
    return .var p "this"
  | "lit" => return .lit p (← decodeVal (← jField j "lit"))
  | "bin" =>
    let op ← jStr (← jField j "op")
    if op == "&&" || op == "||" then
      return .logical p (op == "&&") (← decodeExpr (← jField j "l")) (← decodeExpr (← jField j "r"))
    let left ← decodeExpr (← jField j "l")
    let right ← decodeExpr (← jField j "r")
    -- `x == null` and `x == undefined` hold exactly when `x` is either.
    if op == "==" || op == "!=" then
      match left, right with
      | _, .lit _ .vnull | _, .lit _ .vundef => return .singletonTest p .isNullish (op == "==") true left right
      | .lit _ .vnull, _ | .lit _ .vundef, _ => return .singletonTest p .isNullish (op == "==") false left right
      | _, _ =>
        let same := Expr.arith p .looseEq left right
        return if op == "==" then same else .not p same
    if op != "===" && op != "!==" then
      throw s!"unsupported source expression at [{p.1},{p.2}): binary operator outside the fragment ({op})"
    match left, right with
    | _, .lit _ .vnull => return .singletonTest p .isNul (op == "===") true left right
    | .lit _ .vnull, _ => return .singletonTest p .isNul (op == "===") false left right
    | _, .lit _ .vundef => return .singletonTest p .isUndef (op == "===") true left right
    | .lit _ .vundef, _ => return .singletonTest p .isUndef (op == "===") false left right
    | _, _ => return .equality p (op == "===") left right
  | "typeofTest" => do
    fieldsExactly j ["k","pos","shape","equal","e"]
    -- Each `typeof` result names one value shape.
    let tag ← match ← jStr (← jField j "shape") with
      | "number" => pure Tag.isNum | "string" => pure .isStr | "boolean" => pure .isBool
      | "undefined" => pure .isUndef | "function" => pure .isFun
      | "bigint" => pure .isBigint | "symbol" => pure .isSymbol
      | "object" => pure .typeofObject
      | other => throw s!"unsupported typeof test '{other}'"
    return .shapeTest p tag (← (← jField j "equal").getBool?) (← decodeExpr (← jField j "e"))
  | "inTest" => do
    fieldsExactly j ["k","pos","key","e"]
    match ← decodeExpr (← jField j "key") with
    | .lit _ (.vstr key) =>
      if let some reason := inKeyRefusal key then
        throw s!"unsupported source expression at [{p.1},{p.2}): `in` with the key '{key}': {reason}"
      return .shapeTest p (.hasKey (.str key)) true (← decodeExpr (← jField j "e"))
    | key => return .inKeys p key (← decodeExpr (← jField j "e"))
  | "instanceTest" => do
    -- `e instanceof C`, `C` a class the file declares at its top level, as
    -- TypeScript binds it: the operand, then a read of the class's
    -- prototype object, then the test of the key only that object owns
    -- (`Tag.hasKey`, which walks the operand's prototype chain). In the
    -- class's own instance members the read is of the class value, its
    -- own binding (`selfBindingOf`): the test is the key's either way.
    fieldsExactly j ["k","pos","e","proto","key"]
    let key ← jStr (← jField j "key")
    let proto ← decodeExpr (← jField j "proto")
    let .var _ binding := proto | throw "`instanceof` reads its class's prototype object"
    unless ((binding.dropEnd ".[[prototype]]".length).toString |> fun cls =>
        prototypeBindingOf cls == binding && classKeyOf cls == key) ||
        ((binding.dropEnd ".[[self]]".length).toString |> fun cls =>
          selfBindingOf cls == binding && classKeyOf cls == key) do
      throw s!"`instanceof` tests '{key}', not the key of the prototype '{binding}'"
    return .singletonTest p (.hasKey (.str key)) true true (← decodeExpr (← jField j "e")) proto
  | "arrayTest" => do
    -- `Array.isArray(e)`, which the parser writes only for the standard
    -- library's `Array` through its reviewed overlay entry.
    fieldsExactly j ["k","pos","e"]
    return .shapeTest p .isArray true (← decodeExpr (← jField j "e"))
  | "coalesce" => return .coalesce p (← decodeExpr (← jField j "left")) (← decodeExpr (← jField j "right"))
  | "optional" => do
    fieldsExactly j ["k","pos","at","receiver","body"]
    return .optional p (← jSpan j "at") (← decodeExpr (← jField j "receiver")) (← decodeExpr (← jField j "body"))
  | "comma" => do
    fieldsExactly j ["k","pos","left","right"]
    return .comma p (← decodeExpr (← jField j "left")) (← decodeExpr (← jField j "right"))
  | "not" => return .not p (← decodeExpr (← jField j "e"))
  | "unary" => do
    fieldsExactly j ["k","pos","op","e"]
    let op ← match ← jStr (← jField j "op") with
      | "neg" => pure UnaryOp.neg | "plus" => pure .plus | "bitNot" => pure .bitNot
      | "typeof" => pure .typeof
      | other => throw s!"unknown unary operator '{other}'"
    return .unary p op (← decodeExpr (← jField j "e"))
  | "cast" =>
    fieldsExactly j ["k","pos","cast","annot","e"]
    let kind ← jStr (← jField j "cast")
    if kind != "as" && kind != "satisfies" && kind != "nonNull" && kind != "const" then
      throw "unknown cast kind"
    let a ← jField j "annot"
    -- `e!` and `e as const` assert no type: their claim follows from the operand's.
    if (kind == "nonNull" || kind == "const") != (a == .null) then
      throw "a cast's annotation does not match its kind"
    return .cast p (if a == .null then none else some a) (← decodeExpr (← jField j "e"))
  | "alloc" =>
    let fields ← jArr j "fields"
    -- A name the source spells, or a class's private name, which the
    -- declaration document lists as a symbol of its own.
    let parts ← fields.mapM fun f => do
      let key ← PropKey.decode (← jField f "name")
      if let .str s := key then discard <| sourceKey s
      return (key, ← decodeExpr (← jField f "e"))
    -- A class instance holds its class's prototype object under the key no
    -- source property spells: the parser's lowering of a class states it
    -- apart from the fields, never as a key.
    -- A class's prototype object that `instanceof` tests owns the class's
    -- key, at `undefined`, after its own prototype.
    let brand ← match (j.getObjVal? "brand").toOption with
      | some b => do
        fieldsExactly b ["key", "pos"]
        let key ← jStr (← jField b "key")
        unless key.startsWith "[[" && key.endsWith ".prototype]]" do
          throw s!"'{key}' is not a class's prototype key"
        pure [(PropKey.str key, Expr.lit (← jSpan b "pos") .vundef)]
      | none => pure []
    let parts := brand ++ parts
    match (j.getObjVal? "proto").toOption with
    | some e =>
      return .alloc p (.str protoKeyName :: parts.map Prod.fst) ((← decodeExpr e) :: parts.map Prod.snd)
    | none => return .alloc p (parts.map Prod.fst) (parts.map Prod.snd)
  | "build" =>
    let fields ← jArr j "parts"
    let parts ← fields.mapM fun f => do
      match (f.getObjVal? "spread").toOption with
      | some e => do
        fieldsExactly f ["spread"]
        return ((none : Option String), ← decodeExpr e)
      | none => do
        fieldsExactly f ["name", "e"]
        return (some (← sourceKey (← jStr (← jField f "name"))), ← decodeExpr (← jField f "e"))
    if !parts.any (·.1.isNone) then throw "an object literal with no spread is an allocation"
    -- A derived class's instance holds its prototype, as a class instance's
    -- allocation does, first.
    let parts ← match (j.getObjVal? "proto").toOption with
      | some e => pure ((some protoKeyName, ← decodeExpr e) :: parts)
      | none => pure parts
    return .build p (parts.map Prod.fst) (parts.map Prod.snd)
  | "read" => do
    let field ← PropKey.decode (← jField j "field")
    if let .str s := field then discard <| sourceKey s
    return .read p field (← decodeExpr (← jField j "e"))
  | "arith" => do
    fieldsExactly j ["k","pos","op","l","r"]
    return .arith p (← decodeArith (← jField j "op")) (← decodeExpr (← jField j "l")) (← decodeExpr (← jField j "r"))
  | "update" => do
    fieldsExactly j ["k","pos","op","target","rhs","post"]
    let rhs ← jField j "rhs"
    let rhs ← if rhs == .null then pure none else do pure (some (← decodeExpr rhs))
    let op ← decodeArith (← jField j "op")
    if op.relational then throw "a compound assignment computes; it does not compare"
    return .update p op (← decodeExpr (← jField j "target"))
      rhs (← (← jField j "post").getBool?)
  | "arrayLit" => do
    let elems ← (← jArr j "elems").mapM decodeExpr
    return .arrayLit p elems (← decodeSpreads j elems.length [] ["k","pos","elems"])
  | "arrayAssign" => do
    fieldsExactly j ["k","pos","targets","rest","rhs"]
    let targets ← (← jArr j "targets").mapM (decodeArrayElem decodeExpr)
    let rest ← match ← jField j "rest" with
      | .null => pure none
      | r => do
        fieldsExactly r ["index","pos","target","slice"]
        pure (some (← jSpan r "pos", ← (← jField r "slice").getBool?,
          (⟨← (← jField r "index").getNat?, ← decodeExpr (← jField r "target"), none⟩ : ArrayElem Expr)))
    let reference : ArrayElem Expr → Bool := fun q => match q.target with
      | .var .. | .read .. | .index .. => true
      | _ => false
    if !(targets.all reference && rest.all (reference ·.2.2)) then
      throw "an array assignment pattern writes a local or a field"
    let indices := targets.map (·.index) ++ (rest.map (·.2.2.index)).toList
    if indices.isEmpty then throw "an empty pattern binds nothing"
    if !(indices.zip (indices.drop 1)).all (fun (a, b) => a < b) then
      throw "array pattern positions must increase"
    return .arrayAssign p targets rest (← decodeExpr (← jField j "rhs"))
  | "index" => do
    fieldsExactly j ["k","pos","e","key"]
    return .index p none (← decodeExpr (← jField j "e")) (← decodeExpr (← jField j "key"))
  | "indexWrite" => do
    fieldsExactly j ["k","pos","receiver","key","rhs"]
    return .indexWrite p none (← decodeExpr (← jField j "receiver")) (← decodeExpr (← jField j "key"))
      (← decodeExpr (← jField j "rhs"))
  | "bindWithReceiver" => do
    fieldsExactly j ["k","pos","callee","receiver","args"]
    return .bindWithReceiver p (← decodeExpr (← jField j "callee"))
      (← decodeExpr (← jField j "receiver")) (← (← jArr j "args").mapM decodeExpr)
  | "callWithReceiver" => do
    fieldsExactly j ["k","pos","callee","receiver","args"]
    return .callWithReceiver p (← decodeExpr (← jField j "callee"))
      (← decodeExpr (← jField j "receiver")) (← (← jArr j "args").mapM decodeExpr)
  | "applyWithReceiver" => do
    fieldsExactly j ["k","pos","callee","receiver","list"]
    let list ← match ← jField j "list" with
      | .null => pure none
      | l => some <$> decodeExpr l
    return .applyWithReceiver p (← decodeExpr (← jField j "callee"))
      (← decodeExpr (← jField j "receiver")) list
  | "withValue" => do
    fieldsExactly j ["k","pos","fn","initial","functionType","bagType"]
    return .withValue p (← decodeExpr (← jField j "fn")) (← decodeExpr (← jField j "initial"))
      (← jField j "functionType") (← jField j "bagType")
  | "objectAssign" => do
    fieldsExactly j ["k","pos","target","sources"]
    return .objectAssign p (← decodeExpr (← jField j "target")) (← (← jArr j "sources").mapM decodeExpr)
  | "ctor" => do
    -- A generic class's binders are the declaring unit's (`typeParams`);
    -- they are read where the unit's binders are, not here.
    fieldsExactly j (["k","pos","lambda"] ++
      (if (j.getObjVal? "typeParams").isOk then ["typeParams"] else []) ++
      (if (j.getObjVal? "statics").isOk then ["statics"] else []))
    -- Or the name of a class value bound earlier in the same declaration,
    -- whose constructor this one's code is (`decodeBindings`).
    let lam ← decodeExpr (← jField j "lambda")
    match lam with
    | .lambda _ none [] _ [] false _ _ _ | .var .. => pure ()
    | _ => throw "a class value is a constructor lambda with plain parameters"
    -- Its static fields, each read from the binding its initializer bound,
    -- under a name a source property spells; the list is left out when
    -- empty, its one spelling of none.
    let statics ← match (j.getObjVal? "statics").toOption with
      | none => pure []
      | some (.arr fs) => do
        if fs.isEmpty then throw "a class value's empty static field list is left out"
        fs.toList.mapM fun f => do
          fieldsExactly f ["name","e"]
          let key ← PropKey.decode (← jField f "name")
          if let .str name := key then discard <| sourceKey name
          let e ← decodeExpr (← jField f "e")
          let .var _ _ := e | throw "a class value's static field is the binding its initializer bound"
          pure (key, e)
      | some _ => throw "a class value's statics are a list"
    return .ctor p lam statics
  | "new" => do
    let typeArgs ← decodeTypeArgs j
    let args ← (← jArr j "args").mapM decodeExpr
    let spreads ← decodeSpreads j args.length (typeArgsField typeArgs)
    return .construct p (← decodeExpr (← jField j "callee")) args spreads typeArgs
  | "lambda" => do
    -- Two proof fixtures embed parser snapshots from before quantified lambdas.
    -- Live producers always write `typeParams`; absence in those snapshots is
    -- the unique encoding of the former, necessarily empty list.
    let (typeParams, receiver) ← match (j.getObjVal? "typeParams").toOption with
      | some raw => do
        fieldsExactly j ["k","pos","typeParams","receiver","params","result","guard","body"]
        -- An ordinary function records its receiver annotation and whether
        -- its code is strict, which decides its code's kind below.
        let receiver ← match ← jField j "receiver" with
          | .null => pure none
          | r => do
            fieldsExactly r ["type","strict"]
            pure (some (← jField r "type", ← (← jField r "strict").getBool?))
        pure ((← decodeTypeParams (← raw.getArr?).toList), receiver)
      | none => do
        fieldsExactly j ["k","pos","params","result","body"]
        pure ([], none)
    let raw ← jArr j "params"
    let restAt := raw.zipIdx.filterMap fun (param,i) =>
      if (param.getObjVal? "rest").toOption.isSome then some i else none
    if restAt.any (· != raw.length - 1) then
      throw "a rest parameter must be the last one"
    let params ← raw.mapM fun param => do
      let fields := ["name","type"] ++
        (if (param.getObjVal? "default").toOption.isSome then ["default"] else []) ++
        (if (param.getObjVal? "rest").toOption.isSome then ["rest"] else [])
      fieldsExactly param fields
      match (param.getObjVal? "rest").toOption with
      | none => pure ()
      | some marked =>
        if !(← marked.getBool?) then throw "a rest parameter is marked by `true`"
        if (param.getObjVal? "default").toOption.isSome then
          throw "a rest parameter cannot have a default"
      return (← jStr (← jField param "name"), ← jField param "type")
    let defaults ← raw.zipIdx.filterMapM fun (param,i) => do
      match (param.getObjVal? "default").toOption with
      | none => return none
      | some d => return some (i, ← decodeExpr d)
    let body ← decodeExpr (← jField j "body")
    -- Sloppy code that reads `this` observes the receiver conversion of a
    -- sloppy call: its code is `sloppy`, which binds objects only. A body
    -- that does not read `this` cannot tell the kinds apart.
    let readsThis := (body :: defaults.map Prod.snd).any (·.freeNames.contains "this")
    let receiver := receiver.map fun (annot, strict) =>
      (annot, if !strict && readsThis then Invoke.sloppy else Invoke.call)
    -- A result the source does not annotate is null: the producer's claim
    -- at the closure proposes it, and every claimed arrow's body is checked.
    let result ← jField j "result"
    let guard ← match (j.getObjVal? "guard").toOption with
      | some g => decodeGuard g
      | none => pure none
    return .lambda p receiver typeParams params defaults (!restAt.isEmpty)
      (if result == .null then none else some result) guard body
  | "conditional" =>
    return .ifBody p (← decodeExpr (← jField j "cond"))
      (← decodeExpr (← jField j "then")) (← decodeExpr (← jField j "else_"))
  | "blockBody" => do
    fieldsExactly j ["k","pos","body"]
    return .block p (← (← jArr j "body").mapM decodeStmt)
  | "apply" => do
    let args ← (← jArr j "args").mapM decodeExpr
    let typeArgs ← decodeTypeArgs j
    let spreads ← decodeSpreads j args.length (typeArgsField typeArgs)
    return .call p (← decodeExpr (← jField j "callee")) args spreads typeArgs
  | "invoke" => do
    let args ← (← jArr j "args").mapM decodeExpr
    let typeArgs ← decodeTypeArgs j
    let spreads ← decodeSpreads j args.length (typeArgsField typeArgs)
    let callee ← decodeExpr (← jField j "callee")
    match callee with
    | .read .. | .index .. => pure ()
    | _ => throw "a method call's target is a property reference"
    return .invoke p callee args spreads typeArgs
  | "write" => do
    let field ← PropKey.decode (← jField j "field")
    if let .str s := field then discard <| sourceKey s
    return .write p field (← decodeExpr (← jField j "receiver")) (← decodeExpr (← jField j "rhs"))
  | "logicalAssign" => do
    fieldsExactly j ["k","pos","op","target","rhs"]
    let op ← match ← jStr (← jField j "op") with
      | "nullish" => pure LogicalOp.nullish
      | "or" => pure .orElse
      | "and" => pure .andAlso
      | op => throw s!"unknown logical assignment '{op}'"
    return .logicalAssign p op (← decodeExpr (← jField j "target")) (← decodeExpr (← jField j "rhs"))
  | "nullishAssign" => do
    fieldsExactly j ["k","pos","name","namePos","rhs"]
    return .nullishAssign p (← jStr (← jField j "name")) (← jSpan j "namePos")
      (← decodeExpr (← jField j "rhs"))
  | "assign" => do
    fieldsExactly j ["k","pos","name","namePos","rhs"]
    return .assign p (← jStr (← jField j "name")) (← jSpan j "namePos")
      (← decodeExpr (← jField j "rhs"))
  | _ => throw s!"unsupported source expression at [{p.1},{p.2}): expression outside the stateful fragment"

/-- The declarators of a `const` or `let`: at least one, in source order. -/
partial def decodeBindings (j : Json) : Except String (List Binding) := do
  fieldsExactly j ["k","pos","bindings"]
  let bindings ← (← jArr j "bindings").mapM fun b => do
    fieldsExactly b ["name","namePos","annot","init"]
    let a ← jField b "annot"
    return (⟨← jStr (← jField b "name"), ← jSpan b "namePos",
      if a == .null then none else some a, ← decodeExpr (← jField b "init")⟩ : Binding)
  if bindings.isEmpty then throw "a declaration needs a binding"
  -- A class value whose code is that of a class value bound earlier in the
  -- declaration, by name: its static initializers construct the class
  -- through that one before it exists. It is that constructor, allocated
  -- again with the class's static fields; its body is written once.
  bindings.mapM fun b => match b.init with
    | .ctor p (.var _ h) fs =>
      match bindings.find? (·.name == h) with
      | some ⟨_, _, _, .ctor _ lam@(.lambda ..) []⟩ => pure { b with init := .ctor p lam fs }
      | _ => throw s!"a class value's code names no class value '{h}' of its declaration"
    | _ => pure b

partial def decodeStmt (j : Json) : Except String Stmt := do
  let p ← jSpan j "pos"
  match ← jStr (← jField j "k") with
  | "return" => return .ret p (← decodeExpr (← jField j "e"))
  | "effect" => return .effect p (← decodeExpr (← jField j "e"))
  | "const" => return .constants p (← decodeBindings j)
  | "let" => return .mutables p (← decodeBindings j)
  | "destructure" =>
    fieldsExactly j ["k","pos","target","default_","init"]
    let d ← jField j "default_"
    let dflt ← if d == .null then pure none else some <$> decodeExpr d
    return .destructure p (← decodePattern decodeExpr (← jField j "target")) dflt
      (← decodeExpr (← jField j "init"))
  | "break" =>
    fieldsExactly j ["k","pos","label"]
    return .brk p (← decodeLabel j)
  | "continue" => return .cont p
  | "throw" =>
    fieldsExactly j ["k","pos","e"]
    return .throw p (← decodeExpr (← jField j "e"))
  | "try" =>
    fieldsExactly j ["k","pos","body","handler","finalizer"]
    let handler ← match ← jField j "handler" with
      | .null => pure none
      | h => do
        fieldsExactly h ["param","body"]
        let param ← match ← jField h "param" with
          | .null => pure none
          | q => do
            fieldsExactly q ["name","namePos"]
            pure (some (← jStr (← jField q "name"), ← jSpan q "namePos"))
        pure (some (param, ← (← jArr h "body").mapM decodeStmt))
    let finalizer ← match ← jField j "finalizer" with
      | .null => pure none
      | .arr a => pure (some (← a.toList.mapM decodeStmt))
      | _ => throw "malformed finalizer"
    if handler.isNone && finalizer.isNone then throw "a try needs a catch or a finally"
    return .tryStmt p (← (← jArr j "body").mapM decodeStmt) handler finalizer
  | "while" =>
    fieldsExactly j ["k","pos","cond","body","update"]
    return .loop p (← decodeExpr (← jField j "cond")) (← (← jArr j "body").mapM decodeStmt)
      (← (← jArr j "update").mapM decodeStmt)
  | "block" =>
    fieldsExactly j ["k","pos","label","body"]
    return .block p (← decodeLabel j) (← (← jArr j "body").mapM decodeStmt)
  | "closing" =>
    fieldsExactly j ["k","pos","close","body"]
    return .closing p (← (← jArr j "close").mapM decodeStmt) (← (← jArr j "body").mapM decodeStmt)
  | "forOf" =>
    fieldsExactly j ["k","pos","name","namePos","iterate","iterable","body"]
    let iterate ← jStr (← jField j "iterate")
    if !iterateNames.contains iterate then
      throw s!"a for...of loop steps an iteration intrinsic, not {iterate}"
    return .forOf p (← jStr (← jField j "name")) (← jSpan j "namePos") iterate
      (← decodeExpr (← jField j "iterable")) (← (← jArr j "body").mapM decodeStmt)
  | "if" =>
    let thn ← (← jArr j "then").mapM decodeStmt
    let els ← match ← jField j "else_" with
      | .null => pure none
      | .arr a => pure (some (← a.toList.mapM decodeStmt))
      | _ => throw "malformed else branch"
    return .ite p (← decodeExpr (← jField j "cond")) thn els
  | _ => throw "statement outside the stateful fragment"
end


def decodeFn (j : Json) : Except String (Fn × List TypeParam) := do
  fieldsExactly j ["name", "namePos", "typeParams", "params", "retType", "guard", "body", "strict"]
  let typeParams ← decodeTypeParams (← jArr j "typeParams")
  let fn : Fn := ⟨← jStr (← jField j "name"), ← jSpan j "namePos",
    ← (← jArr j "params").mapM (fun p => do
      let rest ← match (p.getObjVal? "rest").toOption with
        | none => pure false
        | some b => do
          if !(← b.getBool?) then throw "a rest parameter is marked by `true`"
          pure true
      return ⟨← jStr (← jField p "name"), ← jField p "type", rest⟩),
    ← jField j "retType", ← (← jArr j "body").mapM decodeStmt, !(← (← jField j "strict").getBool?),
    ← decodeGuard (← jField j "guard")⟩
  return (fn, typeParams)

def decodeAstWithParams (j : Json) : Except String (List (Fn × List TypeParam)) := do
  fieldsExactly j ["file", "sourceSha256", "declarations", "init", "functions"]
  let document ← jField j "declarations"
  fieldsExactly document ["roots", "definitions", "values", "symbols", "applications"]
  if !(← jArr document "roots").isEmpty || !(← jArr document "definitions").isEmpty ||
      !(← jArr document "values").isEmpty || !(← jArr document "symbols").isEmpty ||
      !(← jArr document "applications").isEmpty then
    throw "type declarations have no certified graph interpretation"
  (← jArr j "functions").mapM decodeFn

/-- The module's top-level code, in source order. -/
def decodeInit (j : Json) : Except String (List Stmt) := do
  (← jArr j "init").mapM decodeStmt

end Verification.Fragment
