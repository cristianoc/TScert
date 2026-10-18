import Lean.Data.Json

/-!
# The object language

The operational foundation of the stateful type development. It is compiled
and tested, and is the current verifier's language.

An untyped call-by-value calculus with a mutable heap: code objects, calls,
explicit binding, primitive values, and object allocation/read/write. Values are terms, so worlds, heaps and the
operational semantics all speak about the same objects.

An object is a finite map from field names to heap locations, fixed at
allocation. Each location still holds one value under one contract, so worlds,
heap satisfaction and the write rule are unchanged; what a field name buys is
that one object can own several of them, and that two contracts naming
different fields of the same object constrain different locations.

Substitution is written for *closed* arguments. `Bindings.lean` proves its
closing-substitution laws; `ProgramTyping.lean` ensures typed positive values
are closed. The untyped step relation itself imposes no scope check.

The step relation is small-step and total in the sense that matters: a term
that is not a value, does not throw (`Raises`) and cannot step is **stuck**,
and the safety predicate in `Safety.lean` rules that out. A throw is an
outcome, as a value is: JavaScript's exceptions are part of its meaning, and a
well-typed program may throw, never reach a wrong value.
-/
namespace Verification

/-- A property key. JavaScript keys an object's properties by strings and by
symbols, and the two spaces are disjoint: no string names a symbol-keyed
property, so a string-keyed access, and a type that constrains every string
key, never reaches one. A symbol key is the identity of a symbol value. -/
inductive PropKey where
  | str (name : String)
  | sym (id : Nat)
  deriving Repr, DecidableEq

/-- Field names written in the model are string keys. -/
instance : Coe String PropKey := ⟨PropKey.str⟩

/-- For messages only: a symbol key is shown by its identity. -/
instance : ToString PropKey where
  toString
    | .str name => name
    | .sym id => s!"[symbol {id}]"

/-- An order for sorting field maps: string keys by name, then symbol keys by
identity. -/
def PropKey.before : PropKey → PropKey → Bool
  | .str a, .str b => a < b
  | .str _, .sym _ => true
  | .sym _, .str _ => false
  | .sym a, .sym b => a < b

/-- The field every single-cell object of the earlier development carries. A
one-field object named this way is what `Tm.obj`, `Tm.read` and `Tm.write`
abbreviate, so every rule and proof written before field names keeps its
meaning. -/
def valueField : PropKey := "value"

/-- The key an array object holds its store under (`CallArguments.arrayStoreField`).
No source property names it, so an object owns it exactly when it is an array:
that is what `Array.isArray` tests (`Tag.isArray`). -/
def arrayStoreKey : PropKey := "[]"

/-- The key a host object owns (COMPILER-API.md, "The host classification"):
the package's instances and node lists, which the model reads as records and
readonly arrays. No source property names it (a double-bracketed key is the
model's, `RequestJson.reservedKey`), so no allocation of the program makes
one, and the field map is fixed at allocation: an object's classification
never changes. The steps that copy an object's own keys are stuck on one. -/
def hostKey : PropKey := "[[host]]"


/-- The string keys `Object.prototype` holds (node's
`Object.getOwnPropertyNames(Object.prototype)`): every ordinary object
inherits a member under each, which the model's objects do not hold. -/
def objectProtoKeys : List String := ["constructor", "__defineGetter__", "__defineSetter__", "hasOwnProperty",
  "__lookupGetter__", "__lookupSetter__", "isPrototypeOf", "propertyIsEnumerable", "toString",
  "valueOf", "__proto__", "toLocaleString"]

/-- **A key every ordinary object inherits a member under**: where the object
does not own it, JavaScript's read finds `Object.prototype`'s member and the
model's finds `undefined`, so no rule reads it as possibly absent. -/
def inheritedKey : PropKey → Bool
  | .str s => objectProtoKeys.contains s
  | .sym _ => false

/-- The shapes a value can have, and so the tests a program can make of one.
Nullishness groups null and undefined for source coalescing; the other tests
distinguish individual runtime shapes. `truthy` is JavaScript's `ToBoolean`:
false exactly for `false`, the two zeros, NaN, `""`, `0n`, `null` and
`undefined`. -/
inductive Tag where
  | isNul | isBool | isRef | isFun | isUndef | isNullish | isNum | isStr
  | numEq (bits : UInt64)
  | strEq (value : String)
  | isBigint | isSymbol
  | truthy
  /-- `Array.isArray`: a plain object owning the store key, which only an
  array does. Keys are fixed at allocation, so the answer never changes. -/
  | isArray
  /-- One Boolean, and one bigint: equality with a singleton of the last two
  primitive kinds that carry a value. -/
  | boolEq (value : Bool)
  | bigintEq (value : Int)
  /-- `typeof v === "object"`: `null`, or an object without call code. An
  object with call code, a class included, is `"function"` (`isFun`). -/
  | typeofObject
  /-- `key in v`: an object owning the key, or one its prototype chain
  reaches (`tagHoldsIn`). Keys are fixed at allocation and no source writes a
  prototype, so the answer never changes; which source keys this answers as
  JavaScript does is the lowering's business (`inKeyRefusal`). -/
  | hasKey (key : PropKey)
  deriving Repr, DecidableEq

/-- The binary operators on primitive operands, JavaScript's own (`binop`
gives their meaning). Arithmetic combines two numbers as the IEEE-754 double
operation, or two bigints as the integer one: `pow` is `**`, `xor` is `^`,
which `~x` is written with (`x ^ -1`). `bitAnd`, `bitOr`, `shl`, `shr` and
`ushr` are `&`, `|`, `<<`, `>>` and `>>>` on two numbers, through `ToInt32`
and `ToUint32`; on bigints they are stuck (`numberOnly`), and the typing
admits them on numbers alone. The relational operators compare two
numeric operands, number and bigint alike, or two strings, and answer a
Boolean. Strict equality answers a Boolean where one operand is a
primitive. A combination JavaScript throws on, or converts through anything
else, is stuck. `rem` is `%`: on doubles the exact remainder of truncating
division, with the dividend's sign; on bigints the truncating remainder. -/
inductive Arith where
  | add | sub | mul | div
  | pow | xor | rem
  | bitAnd | bitOr | shl | shr | ushr
  | lt | le | gt | ge
  /-- Strict equality, `===`: a Boolean, where one operand is a primitive
  (`strictEquals`). -/
  | eq
  /-- Abstract equality on primitives, nullish values and identified objects. -/
  | looseEq
  deriving Repr, DecidableEq, BEq

/-- The bitwise operators the model states on numbers only: `&`, `|`, `<<`,
`>>` and `>>>`. -/
def Arith.numberOnly : Arith → Bool
  | .bitAnd | .bitOr | .shl | .shr | .ushr => true
  | _ => false

/-- Whether an operator compares rather than computes. -/
def Arith.relational : Arith → Bool
  | .lt | .le | .gt | .ge => true
  | _ => false

/-- Which of JavaScript's internal methods a function's code provides: `call`
code runs when the function is called (`[[Call]]`), and `construct` code only
under `new` (`[[Construct]]`), as a class constructor's does, whose plain call
throws. An arrow's or a method's code is `call`: `new` on it throws.
`sloppy` code also runs when the function is called: it is the code of a
sloppy (non-strict) function that reads its receiver, whose call binds
`this` by `OrdinaryCallBindThis` with `[[ThisMode]]` global: an object
receiver unchanged, `undefined` or `null` replaced by the global object and
a primitive by a wrapper object. The model has the first case only
(`Invoke.binds`). -/
inductive Invoke where
  | call | construct | sloppy
  deriving Repr, DecidableEq

namespace ControlFlow
/-- A control-flow destination: a node's label, and the slot map applied on
the way (`PointClaims.mapEnv`; none keeps every slot). Executable program data,
shared by the graph machine, graph code and the checker. -/
structure Target where
  label : Nat
  mapping : Option (List Nat) := none
  deriving DecidableEq, Repr

instance (n : Nat) : OfNat Target n := ⟨⟨n, none⟩⟩

/-- What a graph node does with its expression's value (`ControlFlow`). -/
inductive Continuation where
  | ret
  | bind (next : Target)
  | effect (next : Target)
  | branch (yes no : Target)
  /-- Dispatch and bind the tested Boolean before applying the destination map. -/
  | branchBind (yes no : Target)
  /-- Test the returned value itself, bind it, then apply the destination map. -/
  | tagBind (test : Tag) (yes no : Target)
  deriving DecidableEq, Repr
end ControlFlow

mutual
/-- Terms. Values are terms too, so worlds and the operational semantics speak
about the same objects. -/
inductive Tm where
  | var (i : Nat)
  /-- Invoke the callee `f` with the receiver `r` and the actuals `args`: the
  callee first, then the receiver, then the actuals left to right. A receiver
  is not an actual: it changes no arity, optional position or rest. -/
  | invoke (f r : Tm) (args : List Tm)
  /-- `new f(args)`: evaluate `f`, then the actuals left to right, then run
  `f`'s `construct` code with them. There is no receiver: the code allocates
  and returns the instance itself. -/
  | construct (f : Tm) (args : List Tm)
  /-- Evaluate `a`, then substitute its value into `b`. Binding allocates no object. -/
  | letE (a b : Tm)
  | nul
  /-- The value a body produces by completing rather than returning. -/
  | undef
  | tru
  | fls
  /-- A number, carried as the bit pattern of the double it denotes, which is
  the identity `numBits` below assigns a numeric literal. Equality tests
  inspect these bits and `arith` combines them as doubles; otherwise a number
  is opaque: it is bound, passed, stored and shape-tested. Two patterns
  that denote the same double are equal, so singletons cannot be confused; two
  that denote it differently would be distinct singletons, which costs
  completeness and never soundness. -/
  | num (bits : UInt64)
  /-- A string, carried as itself: bound, passed, stored, shape-tested,
  compared, and concatenated by `+` (`binop`). -/
  | str (value : String)
  /-- A bigint, carried as the integer it is: its identity, as a number's bits
  are. `arith` computes with it; equal integers are the same bigint. -/
  | bigint (value : Int)
  /-- A symbol, carried as an identity. Nothing here computes with it: it is
  bound, passed, stored and shape-tested. -/
  | sym (id : Nat)
  /-- An object identity: the locations its named fields stand for, fixed at
  allocation, with an optional immutable invocation descriptor. -/
  | objAt (fields : List (PropKey × Nat)) (call : CallCode) (identity : Nat)
  /-- Allocate one object with immutable call code, one fresh location per
  named field, holding the values of `inits` in order. Only the initializers
  are evaluated; code binds its declared parameter count. -/
  | makeAt (call : CallCode) (names : List PropKey) (inits : List Tm)
  | readAt (field : PropKey) (a : Tm)
  /-- Evaluate the receiver, then a string key, then read the named property. -/
  | indexAt (a key : Tm)
  | writeAt (field : PropKey) (a b : Tm)
  | test (k : Tag) (a : Tm)
  | ite (c t e : Tm)
  /-- A binary operator on the values of `a` and `b`, in that order: defined
  where `binop` answers, stuck elsewhere. -/
  | arith (op : Arith) (a b : Tm)
  /-- An array's store: the location of each element, in order, or none at a
  hole. The array object holds this value in its store field and replaces it
  when the array grows, so identity, aliasing and holes all live in locations. -/
  | arr (elems : List (Option Nat))
  /-- Allocate one location per initializer, in order, as a store. -/
  | arrLit (inits : List Tm)
  /-- The element a numeric index names in a store: `undefined` at a hole or
  past the end, as property lookup answers. In a string it is the code unit
  there, as the string's own index property answers. -/
  | elemAt (a i : Tm)
  /-- Store a value at a numeric index: into the element's location, or, at a
  hole or past the end, into a fresh location the returned store records. -/
  | setElem (a i v : Tm)
  /-- A store's length, or a string's own `length`: its UTF-16 code units. -/
  | lenOf (a : Tm)
  /-- An actual that stands for the elements of the store `a` evaluates to,
  read in order when every earlier actual is a value. Only an argument list
  gives it meaning: anywhere else it is stuck. -/
  | spread (a : Tm)
  /-- `throw a`: evaluate `a`, then throw its value. A thrown value is not a
  value: it propagates outward through every evaluation context (`Raises`)
  until a handler catches it or it leaves the program. -/
  | throw (a : Tm)
  /-- An allocation from parts: evaluate `a`, then `b`, then allocate one
  fresh plain object holding `a`'s own fields (its prototype included, its
  store not) and, over them, the own enumerable data properties `b` has now,
  but the keys in `drop` (`mergeParts`). An object literal with spreads is a
  chain of these from a fresh accumulator: `{ ...x, k: e }` copies `x` into
  `{}`, then `{ k: e }` into that (DESIGN.md, "Object literals"). -/
  | merge (drop : List PropKey) (a b : Tm)
  /-- An allocation at a key known only at run time: evaluate the key, then
  the initializer, then allocate one fresh plain object owning one property,
  at the key `ToPropertyKey` gives the key's value (`propertyKey`), holding
  the initializer's value, as `makeAt` allocates at a key the source spells. -/
  | makeKey (key init : Tm)
  /-- A run of graph code (`CallCode.graph`) at a node, before it is entered:
  the code's node expressions and continuations, the label, and the
  environment, its slots in order and the value every slot past them holds.
  A runtime form only: no source term has one. -/
  | goto (exprs : List Tm) (conts : List (ControlFlow.Continuation × Option ControlFlow.Target))
      (label : Nat) (env : List Tm) (dflt : Tm)
  /-- A run of graph code evaluating a node's instantiated expression `t`, then
  continuing by `k`; a throw out of `t` goes to `handler`, when it has one, and
  otherwise leaves the run as a throw of the same value. A runtime form only. -/
  | frame (exprs : List Tm) (conts : List (ControlFlow.Continuation × Option ControlFlow.Target))
      (t : Tm) (env : List Tm) (dflt : Tm) (k : ControlFlow.Continuation)
      (handler : Option ControlFlow.Target)
  deriving Repr

/-- Invocation code is not a runtime value. A plain object has no call code. -/
inductive CallCode where
  | absent
  /-- A forwarding descriptor: what `.bind` creates. It keeps the target, the
  receiver and the argument prefix it was given, each a value by the time the
  object is allocated. Invoking it ignores the receiver of that call and
  invokes the target with the saved receiver, the prefix, then the new actuals.
  No field holds this state, so no write can reach it, and a second `.bind`
  cannot replace the first receiver. -/
  | bound (target receiver : Tm) (pre : List Tm)
  /-- Code whose body is a control-flow graph, as a function body is
  (`ControlFlow`): the node expressions, each node's continuation and
  handler, the entry label, the values the code captured where it was
  created, which internal method the code provides (`kind`: `[[Call]]`, or
  `[[Construct]]` for a class constructor), and whether it collects a rest
  (`rest`). Invocation starts the
  graph at `start` in the environment
  `[this, parameter_0, …, parameter_{arity-1}] ++ captures`; `new` on
  construct code passes `undefined` for `this`. Code with a rest first
  collects the actuals past its `arity` fixed parameters into one fresh store,
  which the run finds in slot 0, before the receiver
  (`CallArguments.graphEntry`). The node expressions are scoped by that
  environment alone: substitution reaches the captures, never the nodes. -/
  | graph (arity : Nat) (exprs : List Tm)
      (conts : List (ControlFlow.Continuation × Option ControlFlow.Target))
      (start : Nat) (caps : List Tm) (kind : Invoke := .call) (rest : Bool := false)
  deriving Repr
end

/-- Whether code has `[[Call]]`: all code but a class constructor's. A plain
object has none. -/
def CallCode.callable : CallCode → Bool
  | .absent => false
  | .graph _ _ _ _ _ .construct _ => false
  | _ => true

/-- Whether a call of code of this kind binds the receiver `r` as `this`:
`call` code binds every receiver unchanged; `sloppy` code an object, which
`OrdinaryCallBindThis` leaves unchanged, and no other receiver, whose
conversion (the global object, a wrapper) the model has no term for, so such
a call has no step; construct code is not called. -/
def Invoke.binds : Invoke → Tm → Bool
  | .call, _ => true
  | .sloppy, .objAt .. => true
  | _, _ => false

/-- A call without a receiver supplies `undefined` for it: an abbreviation of
`invoke`, not a second form of call. -/
@[match_pattern] abbrev Tm.call (f : Tm) (args : List Tm) : Tm := .invoke f .undef args

/-- Canonical bits for a source numeric literal type. Equal decimal spellings
share a singleton; source type zero expands to both runtime bit patterns in
`SourceTypes`. Runtime literals use `literalBits` and retain their sign. -/
def numBits (lexeme : String) : Except String UInt64 :=
  match Lean.Json.parse lexeme with
  | .ok (.num n) =>
      let f := n.toFloat
      .ok (if f == 0.0 then (0.0 : Float).toBits else f.toBits)
  | _ => .error s!"not a decimal numeric literal: {lexeme}"

/-- Runtime literals retain their sign. Source type zero
is lowered to both bit singletons, while an expression keeps its exact bits. -/
def literalBits (lexeme : String) : Except String UInt64 := do
  let bits ← numBits lexeme
  return if Float.ofBits bits == 0.0 && lexeme.startsWith "-"
    then (9223372036854775808 : UInt64) else bits

/-- JavaScript's `Number::exponentiate`, which is IEEE `pow` except that a NaN
exponent always gives NaN and a base of magnitude one to an infinite power is
NaN, where C's `pow` answers 1 for both. -/
def jsPow (a b : Float) : Float :=
  if b.isNaN then 0.0 / 0.0
  else if (a == 1.0 || a == -1.0) && b.isInf then 0.0 / 0.0
  else a ^ b

/-- `ToInt32` on the bits of a double, exactly: NaN and the infinities are 0;
otherwise the value truncated toward zero, modulo 2^32, read as signed. -/
def toInt32 (x : UInt64) : Int :=
  let e := ((x >>> 52) &&& 0x7ff).toNat
  let m := (x &&& 0xfffffffffffff).toNat
  if e == 0x7ff then 0 else
  let mant := if e == 0 then m else m + 2 ^ 52
  let shift : Int := (if e == 0 then 1 else (e : Int)) - 1075
  -- Past 2^32 the low 32 bits of an integer multiple of 2^32 are zero.
  let mag : Nat := if 32 ≤ shift then 0
    else if 0 ≤ shift then mant * 2 ^ shift.toNat else mant / 2 ^ (-shift).toNat
  let k : Nat := mag % 2 ^ 32
  let u : Nat := if x >>> 63 == 1 then (2 ^ 32 - k) % 2 ^ 32 else k
  if 2 ^ 31 ≤ u then (u : Int) - 2 ^ 32 else u

/-- Two's-complement exclusive or of two integers: a negative integer is the
complement of a natural, and complementing one operand complements the result. -/
def intXor : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a ^^^ b)
  | .ofNat a, .negSucc b => .negSucc (a ^^^ b)
  | .negSucc a, .ofNat b => .negSucc (a ^^^ b)
  | .negSucc a, .negSucc b => .ofNat (a ^^^ b)

/-- Two's-complement conjunction of two integers: `~a & ~b` is `~(a | b)`,
and `a & ~b` clears `b`'s bits of `a`. -/
def intAnd : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a &&& b)
  | .ofNat a, .negSucc b => .ofNat (a ^^^ (a &&& b))
  | .negSucc a, .ofNat b => .ofNat (b ^^^ (a &&& b))
  | .negSucc a, .negSucc b => .negSucc (a ||| b)

/-- Two's-complement disjunction of two integers: `a | ~b` is
`~(b & ~a)`, and `~a | ~b` is `~(a & b)`. -/
def intOr : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a ||| b)
  | .ofNat a, .negSucc b => .negSucc (b ^^^ (a &&& b))
  | .negSucc a, .ofNat b => .negSucc (a ^^^ (a &&& b))
  | .negSucc a, .negSucc b => .negSucc (a &&& b)

/-- `ToUint32` on the bits of a double: `ToInt32`'s value modulo 2^32. -/
def toUint32 (x : UInt64) : Nat :=
  let i := toInt32 x
  if i < 0 then (i + 2 ^ 32).toNat else i.toNat

/-- An integer modulo 2^32, read as signed: the 32-bit result of a shift. -/
def wrapInt32 (i : Int) : Int :=
  let u := i % 2 ^ 32
  if 2 ^ 31 ≤ u then u - 2 ^ 32 else u

/-- The double an integer in the 32-bit range denotes, exactly. -/
def int32Bits (i : Int) : UInt64 :=
  (if i < 0 then -((-i).toNat.toFloat) else i.toNat.toFloat).toBits

/-- The bits of the double `mant * 2^(b - 1075)`, positive, where the value is
a double: normalized to 53 significant bits, or subnormal when its exponent
is below the least normal one. -/
def encodeBits (mant b : Nat) : UInt64 :=
  if mant == 0 then 0 else
  let len := Nat.log2 mant + 1
  if len ≤ 53 then
    let up := 53 - len
    if up < b then
      UInt64.ofNat (((b - up) <<< 52) ||| (mant <<< up - 2 ^ 52))
    else UInt64.ofNat (mant <<< (b - 1))
  else
    let down := len - 53
    UInt64.ofNat (((b + down) <<< 52) ||| (mant >>> down - 2 ^ 52))

/-- JavaScript's `Number::remainder`, exactly (the result is always a double,
so no rounding occurs): NaN when the dividend is NaN or infinite or the
divisor is NaN or a zero; the dividend when the divisor is infinite or the
dividend a zero; otherwise `n - d * q` for `q` the quotient truncated toward
zero, computed on the integers both operands are multiples of, with the
dividend's sign (so `-4 % 2` is `-0`). -/
def remBits (x y : UInt64) : UInt64 :=
  let ex := ((x >>> 52) &&& 0x7ff).toNat
  let mx := (x &&& 0xfffffffffffff).toNat
  let ey := ((y >>> 52) &&& 0x7ff).toNat
  let my := (y &&& 0xfffffffffffff).toNat
  if ex == 0x7ff || (ey == 0x7ff && my != 0) || (ey == 0 && my == 0) then (0.0 / 0.0 : Float).toBits
  else if ey == 0x7ff || (ex == 0 && mx == 0) then x
  else
    let bx := if ex == 0 then 1 else ex
    let by_ := if ey == 0 then 1 else ey
    let nx := if ex == 0 then mx else mx + 2 ^ 52
    let ny := if ey == 0 then my else my + 2 ^ 52
    let b := min bx by_
    let r := (nx * 2 ^ (bx - b)) % (ny * 2 ^ (by_ - b))
    (x &&& 0x8000000000000000) ||| encodeBits r b

/-- The bits of an arithmetic result on two numbers: the double operation on
the operands' doubles. Signed zero is preserved: division observes its sign
even though strict equality equates the two zeros. A relational operator
yields a Boolean, not a number (`binop`); it has no bits here. -/
def arithBits (op : Arith) (x y : UInt64) : UInt64 :=
  let a := Float.ofBits x
  let b := Float.ofBits y
  match op with
    | .add => (a + b).toBits
    | .sub => (a - b).toBits
    | .mul => (a * b).toBits
    | .div => (a / b).toBits
    | .pow => (jsPow a b).toBits
    | .xor => int32Bits (intXor (toInt32 x) (toInt32 y))
    | .bitAnd => int32Bits (intAnd (toInt32 x) (toInt32 y))
    | .bitOr => int32Bits (intOr (toInt32 x) (toInt32 y))
    -- The shift count is the right operand's `ToUint32`, modulo 32.
    | .shl => int32Bits (wrapInt32 (toInt32 x * 2 ^ (toUint32 y % 32)))
    | .shr => int32Bits (toInt32 x / 2 ^ (toUint32 y % 32))
    | .ushr => int32Bits (toUint32 x / 2 ^ (toUint32 y % 32))
    | .rem => remBits x y
    | .lt | .le | .gt | .ge | .eq | .looseEq => (0.0 / 0.0 : Float).toBits

/-- Arithmetic on two bigints: JavaScript's integer operations. Division
truncates toward zero, and the remainder is the one it leaves, with the
dividend's sign; dividing by zero, a remainder by zero and a negative exponent
throw a `RangeError` (`binopThrows`), so they have no result. -/
def bigintArith : Arith → Int → Int → Option Int
  | .add, x, y => some (x + y)
  | .sub, x, y => some (x - y)
  | .mul, x, y => some (x * y)
  | .div, x, y => if y = 0 then none else some (x.tdiv y)
  | .pow, x, y => if y < 0 then none else some (x ^ y.toNat)
  | .xor, x, y => some (intXor x y)
  | .rem, x, y => if y = 0 then none else some (x.tmod y)
  | .bitAnd, _, _ | .bitOr, _, _ | .shl, _, _ | .shr, _, _ | .ushr, _, _ => none
  | .lt, _, _ | .le, _, _ | .gt, _, _ | .ge, _, _ | .eq, _, _ | .looseEq, _, _ => none

/-- The order of two doubles: none when either is NaN, and the two zeros
equal, as IEEE comparison has them. -/
def doubleOrder (x y : UInt64) : Option Ordering :=
  let a := Float.ofBits x
  let b := Float.ofBits y
  if a < b then some .lt else if a == b then some .eq else if b < a then some .gt else none

/-- The order of a double and an integer, exactly: none when the double is
NaN; an infinity is beyond every integer; a finite double is compared as the
rational it denotes, `mantissa * 2^shift`. -/
def doubleIntOrder (x : UInt64) (n : Int) : Option Ordering :=
  let e := ((x >>> 52) &&& 0x7ff).toNat
  let m := (x &&& 0xfffffffffffff).toNat
  let negative := x >>> 63 == 1
  if e == 0x7ff then
    if m != 0 then none else some (if negative then .lt else .gt)
  else
    let mant : Int := if e == 0 then m else m + 2 ^ 52
    let signed := if negative then -mant else mant
    let shift : Int := (if e == 0 then 1 else (e : Int)) - 1075
    if 0 ≤ shift then some (compare (signed * 2 ^ shift.toNat) n)
    else some (compare signed (n * 2 ^ (-shift).toNat))

/-- A string as JavaScript sees it: its UTF-16 code units, in order. -/
def utf16Units (s : String) : List Nat :=
  s.toList.flatMap fun c =>
    let v := c.val.toNat
    if v < 0x10000 then [v]
    else [0xD800 + (v - 0x10000) / 0x400, 0xDC00 + (v - 0x10000) % 0x400]

/-- Lexicographic order of code-unit sequences: a proper prefix is less. -/
def unitsOrder : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => if a < b then .lt else if b < a then .gt else unitsOrder as bs

/-- A relational operator's answer from the order of its operands, where
`none` is JavaScript's undefined comparison (a NaN operand): every relational
operator is then false. -/
def relationHolds : Arith → Option Ordering → Bool
  | .lt, some .lt => true
  | .le, some .lt | .le, some .eq => true
  | .gt, some .gt => true
  | .ge, some .gt | .ge, some .eq => true
  | _, _ => false

def boolVal (b : Bool) : Tm := if b then .tru else .fls

/-- `a * 2^e / 10^d` as a fraction of naturals, exactly. -/
private def scaledFraction (a : Nat) (e d : Int) : Nat × Nat :=
  (a * 2 ^ e.toNat * 10 ^ (-d).toNat, 2 ^ (-e).toNat * 10 ^ d.toNat)

/-- The shortest decimal digits of a positive finite double `mant * 2^exp`,
as `Number::toString` chooses them: the integer `s` and exponent `d` with
`s * 10^d` rounding to the double, `s` of as few digits as possible, and among
those the one closest to the double, the even one on a tie (the choice the
specification's note recommends and engines make). Rounding to nearest even
rounds exactly the reals strictly between the midpoints to the neighbouring
doubles, and the midpoints too when `mant` is even; the midpoint below is
nearer where `mant` is the first of a binade above the smallest. Measured in
quarters of the double's unit, the double is `4 mant` and the midpoints
`4 mant + 2` and `4 mant - 2` (or `- 1`). The largest `d` for which an integer
fits between them gives the fewest digits; `fuel` counts the exponents
tried, from above every finite double's. -/
def shortestDigits (mant : Nat) (exp : Int) (lower : Bool) : Nat × Int :=
  let e := exp - 2
  let x := 4 * mant
  let lo := if lower then x - 1 else x - 2
  let hi := x + 2
  let closed := mant % 2 == 0
  let rec go : Nat → Int → Nat × Int
    | 0, d => (mant, d)
    | fuel + 1, d =>
      let (ln, ld) := scaledFraction lo e d
      let (hn, hd) := scaledFraction hi e d
      -- The least integer at or above (above, when open) the lower midpoint,
      -- and the greatest at or below (below) the upper one.
      let least := if closed then (ln + ld - 1) / ld else ln / ld + 1
      let most := if closed then hn / hd else (hn + hd - 1) / hd - 1
      if least ≤ most then
        let (xn, xd) := scaledFraction x e d
        let below := xn / xd
        let twice := 2 * (xn % xd)
        let nearest := if twice < xd then below else if xd < twice then below + 1
          else if below % 2 == 0 then below else below + 1
        (min most (max least nearest), d)
      else go fuel (d - 1)
  go 700 309

/-- The digits `digits` of a finite nonzero magnitude, with the decimal point
`d` places after its last digit, spelled as `Number::toString` does: plain up
to 21 integer digits, `0.` and up to six leading zeros below one, else
exponent form `d.ddde±x`. -/
def decimalBody (digits : String) (d : Int) : String :=
  let k : Int := digits.length
  let n : Int := k + d
  let zeros := fun (i : Int) => String.ofList (List.replicate i.toNat '0')
  if k ≤ n && n ≤ 21 then digits ++ zeros (n - k)
  else if 0 < n && n ≤ 21 then
    String.ofList (digits.toList.take n.toNat) ++ "." ++ String.ofList (digits.toList.drop n.toNat)
  else if -6 < n && n ≤ 0 then "0." ++ zeros (-n) ++ digits
  else
    let x := n - 1
    let exponent := "e" ++ (if 0 ≤ x then "+" else "-") ++ toString x.natAbs
    match digits.toList with
    | [c] => String.singleton c ++ exponent
    | c :: rest => String.singleton c ++ "." ++ String.ofList rest ++ exponent
    | [] => exponent

/-- `Number::toString` in radix 10, exactly: `NaN`, the infinities, `0` for
both zeros, and otherwise the shortest digits `s` with `n` the position of
the decimal point: plain up to 21 integer digits, `0.` and up to six leading
zeros below one, else exponent form `d.ddde±x`. -/
def numberToString (x : UInt64) : String :=
  let e := ((x >>> 52) &&& 0x7ff).toNat
  let m := (x &&& 0xfffffffffffff).toNat
  let sign := if x >>> 63 == 1 then "-" else ""
  if e == 0x7ff then (if m != 0 then "NaN" else sign ++ "Infinity")
  else if e == 0 && m == 0 then "0"
  else
    let mant := if e == 0 then m else m + 2 ^ 52
    let exp : Int := (if e == 0 then 1 else (e : Int)) - 1075
    let (s, d) := shortestDigits mant exp (m == 0 && 1 < e)
    sign ++ decimalBody (toString s) d

/-- `ToString` of a primitive other than a symbol, as JavaScript defines it:
no user code runs. A symbol throws a `TypeError`, and an object's conversion
calls its own methods, so neither has one here. -/
def primString : Tm → Option String
  | .str s => some s
  | .num x => some (numberToString x)
  | .bigint i => some (toString i)
  | .tru => some "true"
  | .fls => some "false"
  | .nul => some "null"
  | .undef => some "undefined"
  | _ => none

def isVal : Tm → Bool
  | .nul | .undef | .tru | .fls | .num _ | .str _ | .bigint _ | .sym _ | .objAt .. | .arr _ => true
  | _ => false

/-- Values exposed to JavaScript. Element stores are internal machine values. -/
def isSourceVal : Tm → Bool
  | .nul | .undef | .tru | .fls | .num _ | .str _ | .bigint _ | .sym _ | .objAt .. => true
  | _ => false

theorem sourceVal_isVal {v : Tm} (h : isSourceVal v = true) : isVal v = true := by
  cases v <;> simp_all [isSourceVal, isVal]

/-- A spelling the model keeps for itself: the array store's `[]` and every
name in double brackets (the prototype, a function's code, a class's
prototype object's key). -/
def reservedSpelling : List Char → Bool
  | ['[', ']'] => true
  | '[' :: '[' :: rest => rest.reverse.take 2 == [']', ']']
  | _ => false

/-- A spelling the model's representation of keys moves: a reserved one, and
every one beginning with the escape `[!`. -/
def escapedSpelling (cs : List Char) : Bool :=
  reservedSpelling cs || cs.take 2 == ['[', '!']

/-- How the model spells JavaScript's string property key `s`: as itself, but
a spelling the model keeps for itself, or one beginning with the escape `[!`,
with `[!` before it. The map spells no key the model keeps for itself
(`reservedSpelling_escapeKey`): every string key JavaScript has is represented
apart from the model's own keys, by construction. A source key is a spelling it does not move
(`Fragment.reservedSourceKey`), so it is its own representation. -/
def escapeKey (s : String) : String :=
  if escapedSpelling s.toList then String.ofList ('[' :: '!' :: s.toList) else s

theorem reservedSpelling_escapeKey (s : String) : reservedSpelling (escapeKey s).toList = false := by
  unfold escapeKey
  split
  · simp [reservedSpelling]
  · rename_i h
    simp only [escapedSpelling, Bool.or_eq_true, not_or, Bool.not_eq_true] at h
    exact h.1

/-- `ToPropertyKey` on the primitives whose conversion runs no code and that
a computed key reaches: a string is its own key, spelled as the model
represents it (`escapeKey`), a symbol its identity, and a number the key its
`ToString` spells (`numberToString`), so `o[1]` reads `o["1"]` and `o[0.5]`
reads `o["0.5"]`. Any other value has no key here. -/
def propertyKey : Tm → Option PropKey
  | .str s => some (.str (escapeKey s))
  | .sym i => some (.sym i)
  | .num b => some (.str (numberToString b))
  | _ => none

/-- A key is a value. -/
theorem propertyKey_val {t : Tm} {p : PropKey} (h : propertyKey t = some p) : isVal t = true := by
  cases t <;> simp_all [propertyKey, isVal]

/-- ECMAScript Number::equal on IEEE-754 bits: NaN never equals, and the
sign of zero is ignored. All other equal Numbers have the same encoding. -/
def numberEqual (a b : UInt64) : Bool :=
  let nan := fun (x : UInt64) =>
    (x &&& 0x7ff0000000000000) == 0x7ff0000000000000 &&
      (x &&& 0x000fffffffffffff) != 0
  !nan a && !nan b &&
    (a == b || ((a &&& 0x7fffffffffffffff) == 0 && (b &&& 0x7fffffffffffffff) == 0))

def isSym : Tm → Bool
  | .sym _ => true
  | _ => false

/-- ECMAScript WhiteSpace and LineTerminator code points used by numeric strings. -/
def numericSpace (c : Char) : Bool :=
  let n := c.toNat
  n == 0x9 || n == 0xA || n == 0xB || n == 0xC || n == 0xD || n == 0x20 ||
  n == 0xA0 || n == 0x1680 || (0x2000 ≤ n && n ≤ 0x200A) || n == 0x2028 ||
  n == 0x2029 || n == 0x202F || n == 0x205F || n == 0x3000 || n == 0xFEFF

def trimNumeric (s : String) : List Char :=
  ((s.toList.dropWhile numericSpace).reverse.dropWhile numericSpace).reverse

/-- A nonempty sequence of digits in the specified radix. Separators are invalid. -/
def radixDigits (radix : Nat) (cs : List Char) : Option Nat := do
  if cs.isEmpty then none else
  cs.foldlM (fun n c => do
    let d := if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
      else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
      else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10 else radix
    if d < radix then some (n * radix + d) else none) 0

def prefixedInteger : List Char → Option Nat
  | '0' :: 'x' :: cs | '0' :: 'X' :: cs => radixDigits 16 cs
  | '0' :: 'o' :: cs | '0' :: 'O' :: cs => radixDigits 8 cs
  | '0' :: 'b' :: cs | '0' :: 'B' :: cs => radixDigits 2 cs
  | _ => none

/-- `StringToBigInt`: an invalid integer string has no value, rather than throwing. -/
def stringBigInt (s : String) : Option Int :=
  match trimNumeric s with
  | [] => some 0
  | '+' :: cs => (radixDigits 10 cs).map Int.ofNat
  | '-' :: cs => (radixDigits 10 cs).map (fun n => -(Int.ofNat n))
  | cs => (prefixedInteger cs <|> radixDigits 10 cs).map Int.ofNat

/-- Normalize StringNumericLiteral's decimal grammar to a JSON number.
Decimal order bounds overflow and underflow before expanding an exponent. -/
def decimalNumeric (cs : List Char) : Option String := do
  let (sign, cs) := match cs with
    | '+' :: rest => ("", rest)
    | '-' :: rest => ("-", rest)
    | _ => ("", cs)
  let whole := cs.takeWhile Char.isDigit
  let rest := cs.drop whole.length
  let (fraction, rest) := match rest with
    | '.' :: rest => let ds := rest.takeWhile Char.isDigit; (ds, rest.drop ds.length)
    | _ => ([], rest)
  if whole.isEmpty && fraction.isEmpty then none else do
    let exponent : Int ← match rest with
      | [] => some 0
      | 'e' :: rest | 'E' :: rest => do
        let (negative, digits) := match rest with
          | '+' :: ds => (false, ds)
          | '-' :: ds => (true, ds)
          | _ => (false, rest)
        let n ← radixDigits 10 digits
        some (if negative then -(Int.ofNat n) else Int.ofNat n)
      | _ => none
    let digits := (whole ++ fraction).dropWhile (· == '0')
    if digits.isEmpty then return sign ++ "0"
    let exponent := exponent - Int.ofNat fraction.length
    let order := Int.ofNat digits.length - 1 + exponent
    if order ≥ 309 then return sign ++ "1e309"
    if order ≤ -325 then return sign ++ "0"
    return sign ++ String.ofList digits ++ "e" ++ toString exponent

/-- `ToNumber` for strings, including whitespace, radices, Infinity and invalid text. -/
def stringNumber (s : String) : UInt64 :=
  let cs := trimNumeric s
  let nan := (0.0 / 0.0 : Float).toBits
  if cs.isEmpty then 0 else
  if cs == "Infinity".toList || cs == "+Infinity".toList then (1.0 / 0.0 : Float).toBits else
  if cs == "-Infinity".toList then (-1.0 / 0.0 : Float).toBits else
  match prefixedInteger cs with
  | some n => n.toFloat.toBits
  | none => match decimalNumeric cs with
    | some n => (literalBits n).toOption.getD nan
    | none => nan

/-- A primitive value: one no conversion runs code on. -/
def isPrim : Tm → Bool
  | .nul | .undef | .tru | .fls | .num _ | .str _ | .bigint _ | .sym _ => true
  | _ => false

/-- `IsStrictlyEqual` where one operand is a primitive: operands of different
types differ; two numbers are equal by `Number::equal` (NaN differs from
itself, the zeros are equal); strings, bigints, Booleans and symbols by their
content; `null` and `undefined` each only to itself. -/
def sameValue : Tm → Tm → Bool
  | .nul, .nul | .undef, .undef | .tru, .tru | .fls, .fls => true
  | .num x, .num y => numberEqual x y
  | .str s, .str t => s == t
  | .bigint i, .bigint j => i == j
  | .sym i, .sym j => i == j
  | _, _ => false

def isNullish : Tm → Bool
  | .nul | .undef => true
  | _ => false

/-- Abstract equality of primitive values. Boolean conversion precedes numeric comparison. -/
def primitiveEquals (a b : Tm) : Bool :=
  let numberBool : Tm → Tm
    | .tru => .num (1.0 : Float).toBits
    | .fls => .num 0
    | v => v
  let a := numberBool a
  let b := numberBool b
  if isNullish a && isNullish b then true else
  match a, b with
  | .num n, .str s | .str s, .num n => numberEqual n (stringNumber s)
  | .bigint n, .str s | .str s, .bigint n => stringBigInt s == some n
  | .num n, .bigint i | .bigint i, .num n => doubleIntOrder n i == some .eq
  | _, _ => sameValue a b

/-- Strict equality compares primitives by JavaScript value equality and
objects by allocated identity. Two internal element stores have no answer. -/
def strictEquals (a b : Tm) : Option Bool :=
  if !(isVal a && isVal b) then none
  else if isPrim a || isPrim b then some (sameValue a b)
  else match a, b with
    | .objAt _ _ i, .objAt _ _ j => some (i == j)
    | .objAt .., .arr _ | .arr _, .objAt .. => some false
    | _, _ => none

/-- Loose equality runs no client code on primitive pairs, nullish comparisons,
or object identity comparisons. Object-to-primitive conversion has no rule here. -/
def looseEquals (a b : Tm) : Option Bool :=
  if !(isVal a && isVal b) then none
  else if isPrim a && isPrim b then some (primitiveEquals a b)
  else if isNullish a || isNullish b then some false
  else match a, b with
    | .objAt .., .objAt .. => strictEquals a b
    | _, _ => none

/-- `ToNumeric` of a primitive whose conversion runs no code and is a
number or a bigint: a number and a bigint are themselves, `undefined` is NaN,
`null` and `false` are `+0`, `true` is `1`. A string (`StringToNumber`), a
symbol (a `TypeError`) and an object (its `valueOf` or `toString`) have none. -/
def relNumeric : Tm → Option Tm
  | .num x => some (.num x)
  | .bigint i => some (.bigint i)
  | .undef => some (.num (0.0 / 0.0 : Float).toBits)
  | .nul | .fls => some (.num 0)
  | .tru => some (.num (1.0 : Float).toBits)
  | _ => none

/-- A relational operator on two numeric values of either kind, exactly:
`IsLessThan`'s numeric arm, undefined (false) where a number is NaN. -/
def numericRelation (op : Arith) : Tm → Tm → Option Tm
  | .num x, .num y => some (boolVal (relationHolds op (doubleOrder x y)))
  | .bigint x, .bigint y => some (boolVal (relationHolds op (some (compare x y))))
  | .num x, .bigint y => some (boolVal (relationHolds op (doubleIntOrder x y)))
  | .bigint x, .num y => some (boolVal (relationHolds op ((doubleIntOrder y x).map Ordering.swap)))
  | _, _ => none

/-- `IsLessThan` on two primitives: two strings by their UTF-16 code units;
otherwise both operands convert by `ToNumeric` (`relNumeric`) and compare as
numbers or bigints. -/
def relationalValue (op : Arith) (a b : Tm) : Option Tm :=
  match a, b with
  | .str s, .str t => some (boolVal (relationHolds op (some (unitsOrder (utf16Units s) (utf16Units t)))))
  | _, _ => (relNumeric a).bind fun x => (relNumeric b).bind fun y => numericRelation op x y

/-- **What a binary operator does on two values**, as JavaScript's does on
them, where that is a value. Arithmetic combines two numbers or two bigints,
never one of each (JavaScript throws a `TypeError`: `binopThrows`), and not a
bigint division or remainder by zero or a negative bigint exponent (a
`RangeError`). A relational operator compares two strings by their UTF-16
code units, or two operands among numbers, bigints, Booleans, `null` and
`undefined` after `ToNumeric` (`relationalValue`), exactly. `+` with a string
operand concatenates: the other operand, a primitive other than a symbol,
converts by `ToString` (`primString`), which runs no code. Strict equality
compares where one operand is a primitive (`strictEquals`). Every other pair
converts its operands through code or coercions not modelled here, and has
no answer: the term is stuck. -/
def binop (op : Arith) (a b : Tm) : Option Tm :=
  if op = .eq then (strictEquals a b).map boolVal else
  if op = .looseEq then (looseEquals a b).map boolVal else
  if op.relational then relationalValue op a b else
  match a, b with
  | .num x, .num y => some (.num (arithBits op x y))
  | .bigint x, .bigint y => (bigintArith op x y).map .bigint
  | .str s, .str t => if op == .add then some (.str (s ++ t)) else none
  | .str s, b => if op == .add then (primString b).map fun t => .str (s ++ t) else none
  | a, .str t => if op == .add then (primString a).map fun s => .str (s ++ t) else none
  | _, _ => none

/-- **Where a binary operator throws** on two values, as JavaScript's does,
with no code of the program's run first: a bigint division or remainder by
zero and a negative bigint exponent (`RangeError`); arithmetic combining a number and a
bigint (`TypeError`); and any operator with a symbol operand and a primitive
other one, which converts the symbol by `ToString` or `ToNumeric`
(`TypeError`). Strict equality converts nothing and never throws. An object
operand converts through its own code first, which is not modelled: that
combination stays stuck. Disjoint from `binop`
(`binop_not_throws`). -/
def binopThrows : Arith → Tm → Tm → Bool
  | .eq, _, _ | .looseEq, _, _ => false
  | op, .bigint _, .bigint y => match op with
    | .div | .rem => y == 0
    | .pow => decide (y < 0)
    | _ => false
  | op, .num _, .bigint _ | op, .bigint _, .num _ => !op.relational
  | _, a, b => isSym a && isPrim b || isPrim a && isSym b

/-- The object a primitive operation throws: an object with no field, which
takes no location, as `{}` allocates. It stands for the `TypeError` or
`RangeError` instance JavaScript allocates; a handler binds it at `unknown`,
and nothing typed reads more of it. -/
def thrownError (oid : Nat) : Tm := .objAt [] .absent oid

/-- The array index a number denotes, when it is one: a finite integer in the
index range, the property name it would spell. Any other number names an
ordinary property this fragment does not model. -/
def indexOfBits (b : UInt64) : Option Nat :=
  let f := Float.ofBits b
  if f.isFinite && decide (0.0 ≤ f) && f == f.floor && decide (f < 4294967295.0)
  then some f.toUInt64.toNat else none

def bitsOfNat (n : Nat) : UInt64 := n.toFloat.toBits

/-- A one-code-unit string. A model string is a sequence of Unicode scalar
values, so half of a surrogate pair has no string of its own: it reads as
U+FFFD, the one place the model's strings differ from JavaScript's
(SEMANTICS.md, "Strings"). -/
def unitString (u : Nat) : String :=
  if 0xD800 ≤ u ∧ u ≤ 0xDFFF then "\uFFFD" else String.singleton (Char.ofNat u)

/-- What a string's index property holds at a numeric key: the code unit at an
array index below its length, else nothing (a JavaScript string owns no other
numeric key, and its prototype none). -/
def codeUnitAt (s : String) (b : UInt64) : Tm :=
  match (indexOfBits b).bind fun k => (utf16Units s)[k]? with
  | some u => .str (unitString u)
  | none => .undef

/-- The location an index names in a store: none at a hole or past the end. -/
def elemLoc (ls : List (Option Nat)) (b : UInt64) : Option Nat :=
  (indexOfBits b).bind fun k => (ls[k]?).bind id

/-- The elements a store holds, in order: `undefined` at a hole, as iterating
an array answers. None when a location is missing from the heap. -/
def readElems (h : List Tm) : List (Option Nat) → Option (List Tm)
  | [] => some []
  | none :: ls => (readElems h ls).map (.undef :: ·)
  | some l :: ls => h[l]?.bind fun v => (readElems h ls).map (v :: ·)

/-- One fresh location per element, in order, as a literal allocates them. -/
def elemSlots (base n : Nat) : List (Option Nat) := (List.range n).map fun i => some (base + i)

/-- The store with location `l` at index `k`, holes filling any gap before it. -/
def placeAt (ls : List (Option Nat)) (k l : Nat) : List (Option Nat) :=
  (ls ++ List.replicate (k + 1 - ls.length) none).set k (some l)

/-! Executable structural equality, kept explicit because Lean's deriving
handler does not support nested mutual types such as list-valued applications.
Each recursive comparison visits a strict subterm; no classical decision is used. -/
mutual
def tmDecEq (a b : Tm) : Decidable (a = b) := by
  cases a <;> cases b <;> try (solve | apply isFalse; intro h; cases h)
  case var.var a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp only [Tm.var.injEq])
  case invoke.invoke a0 a1 a2 b0 b1 b2 =>
    haveI : Decidable (a0 = b0) := tmDecEq a0 b0
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    haveI : Decidable (a2 = b2) := argsDecEq a2 b2
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp only [Tm.invoke.injEq])
  case construct.construct a0 a1 b0 b1 =>
    haveI : Decidable (a0 = b0) := tmDecEq a0 b0
    haveI : Decidable (a1 = b1) := argsDecEq a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Tm.construct.injEq])
  case letE.letE a0 a1 b0 b1 =>
    haveI : Decidable (a0 = b0) := tmDecEq a0 b0
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Tm.letE.injEq])
  case nul.nul =>
    exact isTrue rfl
  case undef.undef =>
    exact isTrue rfl
  case tru.tru =>
    exact isTrue rfl
  case fls.fls =>
    exact isTrue rfl
  case num.num a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp only [Tm.num.injEq])
  case str.str a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp only [Tm.str.injEq])
  case bigint.bigint a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp only [Tm.bigint.injEq])
  case sym.sym a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp only [Tm.sym.injEq])
  case objAt.objAt a0 a1 a2 b0 b1 b2 =>
    haveI : Decidable (a1 = b1) := callCodeDecEq a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp only [Tm.objAt.injEq])
  case makeAt.makeAt a0 a1 a2 b0 b1 b2 =>
    haveI : Decidable (a0 = b0) := callCodeDecEq a0 b0
    haveI : Decidable (a2 = b2) := argsDecEq a2 b2
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp only [Tm.makeAt.injEq])
  case readAt.readAt a0 a1 b0 b1 =>
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Tm.readAt.injEq])
  case indexAt.indexAt a0 a1 b0 b1 =>
    haveI : Decidable (a0 = b0) := tmDecEq a0 b0
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Tm.indexAt.injEq])
  case writeAt.writeAt a0 a1 a2 b0 b1 b2 =>
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    haveI : Decidable (a2 = b2) := tmDecEq a2 b2
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp only [Tm.writeAt.injEq])
  case test.test a0 a1 b0 b1 =>
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Tm.test.injEq])
  case ite.ite a0 a1 a2 b0 b1 b2 =>
    haveI : Decidable (a0 = b0) := tmDecEq a0 b0
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    haveI : Decidable (a2 = b2) := tmDecEq a2 b2
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp only [Tm.ite.injEq])
  case arith.arith a0 a1 a2 b0 b1 b2 =>
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    haveI : Decidable (a2 = b2) := tmDecEq a2 b2
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp only [Tm.arith.injEq])
  case arr.arr a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp only [Tm.arr.injEq])
  case arrLit.arrLit a0 b0 =>
    haveI : Decidable (a0 = b0) := argsDecEq a0 b0
    exact decidable_of_iff (a0 = b0) (by simp only [Tm.arrLit.injEq])
  case elemAt.elemAt a0 a1 b0 b1 =>
    haveI : Decidable (a0 = b0) := tmDecEq a0 b0
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Tm.elemAt.injEq])
  case setElem.setElem a0 a1 a2 b0 b1 b2 =>
    haveI : Decidable (a0 = b0) := tmDecEq a0 b0
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    haveI : Decidable (a2 = b2) := tmDecEq a2 b2
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp only [Tm.setElem.injEq])
  case lenOf.lenOf a0 b0 =>
    haveI : Decidable (a0 = b0) := tmDecEq a0 b0
    exact decidable_of_iff (a0 = b0) (by simp only [Tm.lenOf.injEq])
  case spread.spread a0 b0 =>
    haveI : Decidable (a0 = b0) := tmDecEq a0 b0
    exact decidable_of_iff (a0 = b0) (by simp only [Tm.spread.injEq])
  case throw.throw a0 b0 =>
    haveI : Decidable (a0 = b0) := tmDecEq a0 b0
    exact decidable_of_iff (a0 = b0) (by simp only [Tm.throw.injEq])
  case merge.merge a0 a1 a2 b0 b1 b2 =>
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    haveI : Decidable (a2 = b2) := tmDecEq a2 b2
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp only [Tm.merge.injEq])
  case makeKey.makeKey a0 a1 b0 b1 =>
    haveI : Decidable (a0 = b0) := tmDecEq a0 b0
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Tm.makeKey.injEq])
  case goto.goto a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 =>
    haveI : Decidable (a0 = b0) := argsDecEq a0 b0
    haveI : Decidable (a3 = b3) := argsDecEq a3 b3
    haveI : Decidable (a4 = b4) := tmDecEq a4 b4
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4)
      (by simp only [Tm.goto.injEq])
  case frame.frame a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 =>
    haveI : Decidable (a0 = b0) := argsDecEq a0 b0
    haveI : Decidable (a2 = b2) := tmDecEq a2 b2
    haveI : Decidable (a3 = b3) := argsDecEq a3 b3
    haveI : Decidable (a4 = b4) := tmDecEq a4 b4
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 ∧ a5 = b5 ∧ a6 = b6)
      (by simp only [Tm.frame.injEq])

def callCodeDecEq (a b : CallCode) : Decidable (a = b) := by
  cases a <;> cases b <;> try (solve | apply isFalse; intro h; cases h)
  case absent.absent =>
    exact isTrue rfl
  case bound.bound a0 a1 a2 b0 b1 b2 =>
    haveI : Decidable (a0 = b0) := tmDecEq a0 b0
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    haveI : Decidable (a2 = b2) := argsDecEq a2 b2
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp only [CallCode.bound.injEq])
  case graph.graph a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 =>
    haveI : Decidable (a1 = b1) := argsDecEq a1 b1
    haveI : Decidable (a4 = b4) := argsDecEq a4 b4
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 ∧ a5 = b5 ∧ a6 = b6)
      (by simp only [CallCode.graph.injEq])
def argsDecEq (a b : List Tm) : Decidable (a = b) := by
  cases a <;> cases b <;> try (solve | apply isFalse; intro h; cases h)
  case nil.nil => exact isTrue rfl
  case cons.cons a as b bs =>
    haveI : Decidable (a = b) := tmDecEq a b
    haveI : Decidable (as = bs) := argsDecEq as bs
    exact decidable_of_iff (a = b ∧ as = bs) (by simp only [List.cons.injEq])
end

instance : DecidableEq Tm := tmDecEq

/-- Unary application is the singleton case of the argument-list constructor. -/
@[match_pattern] abbrev Tm.app (f a : Tm) : Tm := .call f [a]

/-! ### The one-field spellings

A cell is an object with the single field `value`. These abbreviations are the
language the development before field names was written in, and they keep that
meaning exactly: every rule, example and proof that says `obj`, `make`, `read`
or `write` is speaking about that one field. -/

/-- An already allocated one-field object. -/
@[match_pattern] abbrev Tm.obj (l : Nat) (call : CallCode) : Tm :=
  .objAt [(valueField, l)] call (l + 1)

/-- Allocation of a one-field object. -/
@[match_pattern] abbrev Tm.make (call : CallCode) (a : Tm) : Tm :=
  .makeAt call [valueField] [a]

/-- Reading and writing that one field. -/
@[match_pattern] abbrev Tm.read (a : Tm) : Tm := .readAt valueField a
@[match_pattern] abbrev Tm.write (a b : Tm) : Tm := .writeAt valueField a b

/-- Plain-object allocation is the absent-descriptor case of `make`. -/
@[match_pattern] abbrev Tm.alloc (a : Tm) : Tm := .make .absent a

/-- The one field of a function object the program creates, which gives it a
location and so an identity: a key no source property spells, which a copy
does not take, as JavaScript's function owns no enumerable property. -/
def codeField : PropKey := "[[code]]"

/-- An already allocated function object the program created. -/
@[match_pattern] abbrev Tm.fnObj (l : Nat) (call : CallCode) : Tm :=
  .objAt [(codeField, l)] call (l + 1)

/-- The creation of a function object: its code, with its one field. -/
@[match_pattern] abbrev Tm.makeFn (call : CallCode) (a : Tm) : Tm :=
  .makeAt call [codeField] [a]


/-- The locations a fresh allocation gives its fields, in declaration order. -/
def slots (base : Nat) : List PropKey → List (PropKey × Nat)
  | [] => []
  | f :: fs => (f, base) :: slots (base + 1) fs

/-- A field of a fresh object stands for the location its position was given.
Distinct names are what makes the map a map: with a repeat, only the first
occurrence is ever found. -/
theorem lookup_slots {ns : List PropKey} (hnd : ns.Nodup) {base i : Nat}
    (hi : i < ns.length) : (slots base ns).lookup ns[i] = some (base + i) := by
  induction ns generalizing base i with
  | nil => simp at hi
  | cons a ns ih =>
    cases i with
    | zero => simp [slots]
    | succ i =>
      have hib : i < ns.length := by simpa using hi
      have hne : ns[i] ≠ a := by
        intro he
        exact (List.nodup_cons.mp hnd).1 (he ▸ List.getElem_mem hib)
      have hbeq : (ns[i] == a) = false := by simpa using hne
      simp only [slots, List.lookup, List.getElem_cons_succ, hbeq]
      rw [ih (List.nodup_cons.mp hnd).2 hib]
      congr 1
      omega

/-- Term induction exposing the body stored inside a call descriptor. -/
@[elab_as_elim] theorem Tm.induct {P : Tm → Prop}
    (var : ∀ i, P (.var i))
    (invoke : ∀ f r args, P f → P r → (∀ a ∈ args, P a) → P (.invoke f r args))
    (construct : ∀ f args, P f → (∀ a ∈ args, P a) → P (.construct f args))
    (letE : ∀ a b, P a → P b → P (.letE a b))
    (nul : P .nul) (undef : P .undef) (tru : P .tru) (fls : P .fls)
    (num : ∀ v, P (.num v))
    (str : ∀ s, P (.str s))
    (bigint : ∀ i, P (.bigint i)) (sym : ∀ i, P (.sym i))
    (objAbsent : ∀ fs oid, P (.objAt fs .absent oid))
    (objBound : ∀ fs oid t r pre, P t → P r → (∀ a ∈ pre, P a) → P (.objAt fs (.bound t r pre) oid))
    (makeBound : ∀ t r pre ns args, P t → P r → (∀ a ∈ pre, P a) → (∀ a ∈ args, P a) →
      P (.makeAt (.bound t r pre) ns args))
    (alloc : ∀ ns args, (∀ a ∈ args, P a) → P (.makeAt .absent ns args))
    (read : ∀ f a, P a → P (.readAt f a))
    (index : ∀ a key, P a → P key → P (.indexAt a key))
    (write : ∀ f a b, P a → P b → P (.writeAt f a b))
    (test : ∀ k a, P a → P (.test k a))
    (ite : ∀ c a b, P c → P a → P b → P (.ite c a b))
    (arith : ∀ op a b, P a → P b → P (.arith op a b))
    (arr : ∀ ls, P (.arr ls))
    (arrLit : ∀ inits, (∀ a ∈ inits, P a) → P (.arrLit inits))
    (elemAt : ∀ a i, P a → P i → P (.elemAt a i))
    (setElem : ∀ a i v, P a → P i → P v → P (.setElem a i v))
    (lenOf : ∀ a, P a → P (.lenOf a))
    (spread : ∀ a, P a → P (.spread a))
    (throw : ∀ a, P a → P (.throw a))
    (merge : ∀ d a b, P a → P b → P (.merge d a b))
    (makeKey : ∀ k a, P k → P a → P (.makeKey k a))
    (objGraph : ∀ fs oid n E K s caps k r, (∀ e ∈ E, P e) → (∀ a ∈ caps, P a) →
      P (.objAt fs (.graph n E K s caps k r) oid))
    (makeGraph : ∀ n E K s caps k r ns args, (∀ e ∈ E, P e) → (∀ a ∈ caps, P a) →
      (∀ a ∈ args, P a) → P (.makeAt (.graph n E K s caps k r) ns args))
    (goto : ∀ E K l L d, (∀ e ∈ E, P e) → (∀ a ∈ L, P a) → P d → P (.goto E K l L d))
    (frame : ∀ E K t L d k x, (∀ e ∈ E, P e) → P t → (∀ a ∈ L, P a) → P d →
      P (.frame E K t L d k x))
    (t : Tm) : P t := by
  apply Tm.rec (motive_1 := P)
    (motive_2 := fun c => match c with
      | .absent => True
      | .bound t r pre => P t ∧ P r ∧ ∀ a ∈ pre, P a
      | .graph _ E _ _ caps _ _ => (∀ e ∈ E, P e) ∧ ∀ a ∈ caps, P a)
    (motive_3 := fun args => ∀ a ∈ args, P a)
    var invoke construct letE nul undef tru fls num str bigint sym ?_ ?_ read index write test ite arith arr arrLit elemAt setElem lenOf spread throw merge makeKey
    (fun E K l L d hE hL hd => goto E K l L d hE hL hd)
    (fun E K t L d k x hE ht hL hd => frame E K t L d k x hE ht hL hd)
    True.intro (fun _ _ _ ht hr hp => ⟨ht, hr, hp⟩)
    (fun _ _ _ _ _ _ _ hE hc => ⟨hE, hc⟩) (by simp) (by
      intro a args ha ih v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ha
      · exact ih v hv) t
  · intro fs c oid ih
    cases c with
    | absent => exact objAbsent fs oid
    | bound t r pre => exact objBound fs oid t r pre ih.1 ih.2.1 ih.2.2
    | graph n E K s caps k r => exact objGraph fs oid n E K s caps k r ih.1 ih.2
  · intro c ns args ihc iha
    cases c with
    | absent => exact alloc ns args iha
    | bound t r pre => exact makeBound t r pre ns args ihc.1 ihc.2.1 ihc.2.2 iha
    | graph n E K s caps k r => exact makeGraph n E K s caps k r ns args ihc.1 ihc.2 iha


abbrev Val := Tm

/-! ## Values and substitution -/


/-- An operator answers only for two values, and answers a Boolean, a
number, a bigint or a string. -/
theorem primString_val {a : Tm} {s : String} (h : primString a = some s) : isVal a = true := by
  cases a <;> simp [primString] at h <;> rfl

theorem relNumeric_val {a x : Tm} (h : relNumeric a = some x) : isVal a = true := by
  cases a <;> simp [relNumeric] at h <;> rfl

theorem numericRelation_bool {op : Arith} {x y v : Tm} (h : numericRelation op x y = some v) :
    v = .tru ∨ v = .fls := by
  have hb : ∀ q, boolVal q = .tru ∨ boolVal q = .fls := fun q => by cases q <;> simp [boolVal]
  unfold numericRelation at h
  split at h <;> cases h <;> exact hb _

/-- A relational comparison answers a Boolean, for two values. -/
theorem relationalValue_result {op : Arith} {a b v : Tm} (h : relationalValue op a b = some v) :
    isVal a = true ∧ isVal b = true ∧ (v = .tru ∨ v = .fls) := by
  unfold relationalValue at h
  split at h
  · obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl, by cases relationHolds _ _ <;> simp [boolVal]⟩
  · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.mp h
    exact ⟨relNumeric_val hx, relNumeric_val hy, numericRelation_bool h⟩

theorem binop_result {op : Arith} {a b v : Tm} (h : binop op a b = some v) :
    isVal a = true ∧ isVal b = true ∧
      (v = .tru ∨ v = .fls ∨ (∃ x, v = .num x) ∨ (∃ i, v = .bigint i) ∨ ∃ s, v = .str s) := by
  have hb : ∀ q, boolVal q = .tru ∨ boolVal q = .fls := fun q => by cases q <;> simp [boolVal]
  unfold binop at h
  split at h
  · obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
    unfold strictEquals at hq
    split at hq
    · cases hq
    · rename_i hv
      simp only [Bool.not_eq_true', Bool.and_eq_false_iff, not_or, Bool.not_eq_false] at hv
      exact ⟨hv.1, hv.2, by rcases hb q with h | h <;> rw [h] <;> simp⟩
  split at h
  · obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
    unfold looseEquals at hq
    split at hq
    · cases hq
    · rename_i hv
      simp only [Bool.not_eq_true', Bool.and_eq_false_iff, not_or, Bool.not_eq_false] at hv
      exact ⟨hv.1, hv.2, by rcases hb q with h | h <;> rw [h] <;> simp⟩
  split at h
  · obtain ⟨ha, hb, hv⟩ := relationalValue_result h
    exact ⟨ha, hb, by rcases hv with rfl | rfl <;> simp⟩
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (obtain rfl := Option.some.inj h; exact ⟨rfl, rfl, by rcases hb _ with h | h <;> rw [h] <;> simp⟩)
    | (obtain rfl := Option.some.inj h; exact ⟨rfl, rfl, by simp⟩)
    | (obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h; exact ⟨rfl, rfl, by simp⟩)
    | (obtain ⟨_, ht, rfl⟩ := Option.map_eq_some_iff.mp h; exact ⟨rfl, primString_val ht, by simp⟩)
    | (obtain ⟨_, ht, rfl⟩ := Option.map_eq_some_iff.mp h; exact ⟨primString_val ht, rfl, by simp⟩)

theorem binop_values {op : Arith} {a b v : Tm} (h : binop op a b = some v) :
    isVal a = true ∧ isVal b = true ∧ isVal v = true := by
  obtain ⟨ha, hb, hv⟩ := binop_result h
  refine ⟨ha, hb, ?_⟩
  rcases hv with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl

theorem isPrim_val {a : Tm} (h : isPrim a = true) : isVal a = true := by
  cases a <;> simp_all [isPrim, isVal]

theorem isSym_val {a : Tm} (h : isSym a = true) : isVal a = true := by
  cases a <;> simp_all [isSym, isVal]

/-- An operator throws only on two values. -/
theorem binopThrows_values {op : Arith} {a b : Tm} (h : binopThrows op a b = true) :
    isVal a = true ∧ isVal b = true := by
  unfold binopThrows at h
  split at h
  · cases h
  · cases h
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨isSym_val h1, isPrim_val h2⟩
    · exact ⟨isPrim_val h1, isSym_val h2⟩

/-- An operator never both answers and throws. -/
theorem binop_not_throws {op : Arith} {a b v : Tm} (h : binop op a b = some v) :
    binopThrows op a b = false := by
  cases hc : binopThrows op a b
  · rfl
  exfalso
  unfold binopThrows at hc
  split at hc
  · cases hc
  · cases hc
  -- A bigint division or remainder by zero, or a negative exponent, has no answer.
  · split at hc <;> simp_all [binop, bigintArith, Arith.relational] <;> omega
  -- A number and a bigint answer only a comparison.
  · simp_all [binop]
  · simp_all [binop]
  -- A symbol and another primitive have no answer.
  · simp only [Bool.or_eq_true, Bool.and_eq_true] at hc
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · cases a <;> simp only [isSym, Bool.false_eq_true] at h1
      cases b <;> simp only [isPrim, Bool.false_eq_true] at h2 <;>
        simp_all [binop, primString, relationalValue, relNumeric]
    · cases b <;> simp only [isSym, Bool.false_eq_true] at h2
      cases a <;> simp only [isPrim, Bool.false_eq_true] at h1 <;>
        simp_all [binop, primString, relationalValue, relNumeric]

/-- `ToBoolean` of a number: false for the two zeros and NaN, which is the one
double not equal to itself. -/
def numberTruthy (b : UInt64) : Bool := !numberEqual b 0 && numberEqual b b

/-- Tests are total on values. Numeric equality also inspects the bits. -/
def tagHolds : Tag → Val → Bool
  | .isNul, .nul => true
  | .isUndef, .undef => true
  | .isNullish, .nul | .isNullish, .undef => true
  | .isBool, .tru => true
  | .isBool, .fls => true
  | .isNum, .num _ => true
  | .numEq bits, .num value => numberEqual value bits
  | .isStr, .str _ => true
  | .strEq s, .str t => s == t
  | .boolEq b, .tru => b
  | .boolEq b, .fls => !b
  | .bigintEq i, .bigint j => i == j
  | .isBigint, .bigint _ => true
  | .isSymbol, .sym _ => true
  | .isRef, .objAt _ .absent _ => true
  | .isFun, .objAt _ (.bound _ _ _) _ => true
  | .isFun, .objAt _ (.graph ..) _ => true
  | .truthy, .tru => true
  | .truthy, .num b => numberTruthy b
  | .truthy, .str s => s != ""
  | .truthy, .bigint i => i != 0
  | .truthy, .sym _ => true
  | .truthy, .objAt _ _ _ => true
  | .truthy, .arr _ => true
  | .isArray, .objAt fs .absent _ => (fs.lookup arrayStoreKey).isSome
  | .typeofObject, .nul => true
  | .typeofObject, .objAt _ .absent _ => true
  | .hasKey k, .objAt fs _ _ => (fs.lookup k).isSome
  | _, _ => false

mutual
def subst (j : Nat) (a : Tm) : Tm → Tm
  | .var i => if i == j then a else if j < i then .var (i - 1) else .var i
  | .invoke f r args => .invoke (subst j a f) (subst j a r) (substArgs j a args)
  | .construct f args => .construct (subst j a f) (substArgs j a args)
  | .letE x b => .letE (subst j a x) (subst (j + 1) a b)
  | .nul => .nul
  | .undef => .undef
  | .tru => .tru
  | .fls => .fls
  | .num v => .num v
  | .str s => .str s
  | .bigint i => .bigint i
  | .sym i => .sym i
  | .objAt fs .absent oid => .objAt fs .absent oid
  | .objAt fs (.bound t r pre) oid => .objAt fs (.bound (subst j a t) (subst j a r) (substArgs j a pre)) oid
  | .makeAt (.bound t r pre) ns xs =>
      .makeAt (.bound (subst j a t) (subst j a r) (substArgs j a pre)) ns (substArgs j a xs)
  | .makeAt .absent ns xs => .makeAt .absent ns (substArgs j a xs)
  | .readAt f x => .readAt f (subst j a x)
  | .indexAt x key => .indexAt (subst j a x) (subst j a key)
  | .writeAt f x y => .writeAt f (subst j a x) (subst j a y)
  | .test k x => .test k (subst j a x)
  | .ite c x y => .ite (subst j a c) (subst j a x) (subst j a y)
  | .arith op x y => .arith op (subst j a x) (subst j a y)
  | .arr ls => .arr ls
  | .arrLit xs => .arrLit (substArgs j a xs)
  | .elemAt x y => .elemAt (subst j a x) (subst j a y)
  | .setElem x y z => .setElem (subst j a x) (subst j a y) (subst j a z)
  | .lenOf x => .lenOf (subst j a x)
  | .spread x => .spread (subst j a x)
  | .throw x => .throw (subst j a x)
  | .merge d x y => .merge d (subst j a x) (subst j a y)
  | .makeKey x y => .makeKey (subst j a x) (subst j a y)
  | .objAt fs (.graph n E K s caps k r) oid => .objAt fs (.graph n E K s (substArgs j a caps) k r) oid
  | .makeAt (.graph n E K s caps k r) ns xs =>
      .makeAt (.graph n E K s (substArgs j a caps) k r) ns (substArgs j a xs)
  | .goto E K l L d => .goto E K l (substArgs j a L) (subst j a d)
  | .frame E K t L d k x => .frame E K (subst j a t) (substArgs j a L) (subst j a d) k x

termination_by structural t => t

def substArgs (j : Nat) (a : Tm) : List Tm → List Tm
  | [] => []
  | x :: xs => subst j a x :: substArgs j a xs
termination_by structural xs => xs
end

@[simp] theorem substArgs_eq_map (j : Nat) (a : Tm) (args : List Tm) :
    substArgs j a args = args.map (subst j a) := by
  induction args <;> simp_all [substArgs]

namespace CallArguments

/-- Runtime parameter binding pads missing arguments with undefined and ignores
extra values. Preparation still evaluates the entire actual list first. -/
def parameters : Nat → List Tm → List Tm
  | 0, _ => []
  | n+1, [] => .undef :: parameters n []
  | n+1, a::args => a :: parameters n args

/-- The field an array object keeps its store in: `SourceTypes.storeField`. -/
def arrayStoreField : PropKey := arrayStoreKey

/-- The field an object keeps its prototype in. No source property names it:
a read of a key the object lacks continues there (`Step.readProto`). -/
def protoField : PropKey := "[[proto]]"

/-- What invoking graph code yields: a run at its entry, the receiver in slot
0, then the `arity` parameters `parameters` binds, then the captures. Code with
a rest first allocates the store of the actuals past its parameters, a fresh
array store, and the run finds that store in slot 0, before the receiver.
Invocation itself allocates nothing: the store is allocated by the ordinary
steps of the term it yields. -/
def graphEntry (arity : Nat) (E : List Tm)
    (K : List (ControlFlow.Continuation × Option ControlFlow.Target)) (start : Nat)
    (caps : List Tm) (rest : Bool) (recv : Tm) (args : List Tm) : Tm :=
  match rest with
  | false => .goto E K start (recv :: parameters arity args ++ caps) .nul
  | true => .letE (.arrLit (args.drop arity))
      (.goto E K start (.var 0 :: recv :: parameters arity args ++ caps) .nul)

end CallArguments

/-! ### Copying own data properties

What an object spread reads (`Tm.merge`). The model's own fields are data
properties; those a spread copies are its own enumerable ones, which are the
fields under string keys other than the two the model keeps for itself, and,
for an array, the elements of its store under their index keys. -/

/-- The value a copy reads at a location. A location the heap lacks, or one
holding a term that is not a value, reads as `undefined`: no run reaches
either, and the copy stays total. -/
def heapVal (h : List Tm) (l : Nat) : Tm :=
  match h[l]? with
  | some v => if isVal v then v else .undef
  | none => .undef

/-- `key in o`: `o` owns the key, or an object along its prototype chain
does, as far as the heap reaches. A chain longer than the heap has a cycle,
which no JavaScript object has; it answers `false`. -/
def keyInChain (h : List Tm) (k : PropKey) : Nat → Tm → Bool
  | 0, _ => false
  | fuel + 1, .objAt fs _ _ => (fs.lookup k).isSome ||
      match fs.lookup CallArguments.protoField with
      | some l => keyInChain h k fuel (heapVal h l)
      | none => false
  | _ + 1, _ => false

/-- A test's answer in a heap: `tagHolds`, but `key in o`, which also reads
the objects `o`'s prototype chain reaches. Every other test reads the value
alone. -/
def tagHoldsIn (h : List Tm) : Tag → Tm → Bool
  | .hasKey k, v@(.objAt ..) => keyInChain h k (h.length + 1) v
  | t, v => tagHolds t v

/-- A test that needs no prototype: every one but `key in o` on an object
lacking the key and holding a prototype. -/
def protoFree : Tag → Tm → Bool
  | .hasKey k, .objAt fs _ _ => (fs.lookup k).isSome || (fs.lookup CallArguments.protoField).isNone
  | _, _ => true

/-- Where no prototype is read, the heap does not matter. -/
theorem tagHoldsIn_of_protoFree {h : List Tm} {t : Tag} {v : Tm} (hp : protoFree t v = true) :
    tagHoldsIn h t v = tagHolds t v := by
  unfold tagHoldsIn
  split
  · rename_i k fs c
    simp only [protoFree, Bool.or_eq_true, Option.isSome_iff_ne_none, ne_eq,
      Option.isNone_iff_eq_none] at hp
    simp only [keyInChain, tagHolds]
    rcases hp with hk | hn
    · simp [Option.isSome_iff_ne_none, hk]
    · rw [hn]; simp
  · rfl

/-- What a test's answer in a heap says of the value alone: its own answer,
or, for `key in o`, that the object reads a prototype. -/
theorem tagHolds_of_heap {h : List Tm} {t : Tag} {v : Tm} {q : Bool} (hq : tagHoldsIn h t v = q) :
    tagHolds t v = q ∨ protoFree t v = false := by
  cases hp : protoFree t v
  · exact .inr rfl
  · exact .inl ((tagHoldsIn_of_protoFree hp).symm.trans hq)

/-- A key a spread copies: a string key the model does not keep for itself
(the prototype, the array store, a function object's code field, the host
classification). A
symbol-keyed field is never copied: the model's are the library's, whose
enumerability it does not record, and
no allocation of the fragment makes one. -/
def copiedKey : PropKey → Bool
  | .str s => s != "[[proto]]" && s != "[]" && s != "[[code]]" && s != "[[host]]"
  | .sym _ => false

/-- The first entry of each key, which is the one `List.lookup` finds. -/
def firstKeys {α : Type} : List (PropKey × α) → List (PropKey × α)
  | [] => []
  | (k, x) :: ps => (k, x) :: (firstKeys ps).filter (·.1 != k)

/-- An array's elements, under their index keys, when the object holds a
store. -/
def storeData (h : List Tm) (fs : List (PropKey × Nat)) : List (PropKey × Tm) :=
  match fs.lookup arrayStoreKey with
  | some l => match h[l]? with
    | some (.arr ls) => ls.zipIdx.filterMap fun p => p.1.map fun m => (.str (toString p.2), heapVal h m)
    | _ => []
  | none => []

/-- A string's own enumerable properties: each code unit, a one-unit string,
under its index's decimal spelling (`unitString`, as `elemAt` reads it); its
`length` is not enumerable. -/
def stringData (s : String) : List (PropKey × Tm) :=
  (utf16Units s).zipIdx.map fun p => (.str (toString p.2), .str (unitString p.1))

/-- An ordinary object, or no object: not a host object. -/
def hostOwned : Tm → Bool
  | .objAt fs .absent _ => (fs.lookup hostKey).isSome
  | _ => false

/-- The own enumerable data properties a spread copies from a value: an
object's copied fields, a function's included, then an array's elements; a
string's code units at their indices; nothing from `null`, `undefined`, a
Boolean, a number, a bigint or a symbol, whose wrappers own no enumerable
property. -/
def ownData (h : List Tm) : Tm → Option (List (PropKey × Tm))
  | v@(.objAt fs _ _) => if hostOwned v then none else some (firstKeys
      ((fs.filter (copiedKey ·.1)).map (fun p => (p.1, heapVal h p.2)) ++ storeData h fs))
  | .str s => some (firstKeys (stringData s))
  | .nul | .undef | .tru | .fls | .num _ | .bigint _ | .sym _ => some []
  | _ => none

/-- The fields of the accumulator a copy is made onto: all of a plain
object's own fields, its prototype included, but its store. -/
def ownAll (h : List Tm) : Tm → Option (List (PropKey × Tm))
  | .objAt fs .absent _ => if (fs.lookup hostKey).isSome then none else some (firstKeys
      ((fs.filter (·.1 != arrayStoreKey)).map (fun p => (p.1, heapVal h p.2))))
  | _ => none

/-- The properties of `a` with `b`'s defined over them: a key `b` has takes
`b`'s value. The order of an object's fields is not observable in the model
(no operation enumerates them in order), so the ones `b` redefines are not
kept in `a`'s places. -/
def mergeData (a b : List (PropKey × Tm)) : List (PropKey × Tm) :=
  a.filter (fun p => !b.any (·.1 == p.1)) ++ b

/-- The fields a merge allocates: the accumulator's, with the source's
copied properties, less the dropped keys, defined over them. -/
def mergeParts (h : List Tm) (drop : List PropKey) (a b : Tm) : Option (List (PropKey × Tm)) := do
  let p ← ownAll h a
  let q ← ownData h b
  pure (mergeData p (q.filter fun e => !drop.contains e.1))

/-- A copied value is `undefined` or a value the heap holds. -/
theorem heapVal_mem (h : List Tm) (l : Nat) :
    heapVal h l = .undef ∨ (heapVal h l ∈ h ∧ isVal (heapVal h l) = true) := by
  unfold heapVal
  split
  · rename_i v hv
    split
    · exact .inr ⟨List.mem_of_getElem? hv, by assumption⟩
    · exact .inl rfl
  · exact .inl rfl

theorem mem_firstKeys {α : Type} : ∀ {ps : List (PropKey × α)} {p : PropKey × α},
    p ∈ firstKeys ps → p ∈ ps
  | [], _, h => by simp [firstKeys] at h
  | (k, x) :: ps, p, h => by
    simp only [firstKeys, List.mem_cons, List.mem_filter] at h
    rcases h with rfl | ⟨h, -⟩
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_firstKeys h)

theorem lookup_filter_ne {α : Type} (ps : List (PropKey × α)) {k j : PropKey} (hne : j ≠ k) :
    (ps.filter (·.1 != k)).lookup j = ps.lookup j := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨g, x⟩ := p
    by_cases hg : g = k
    · subst hg
      have : (j == g) = false := by simpa using hne
      simp [List.lookup, this, ih]
    · have hgk : (g != k) = true := by simpa using hg
      rw [List.filter_cons, if_pos hgk]
      by_cases hj : j = g
      · subst hj; simp [List.lookup]
      · have : (j == g) = false := by simpa using hj
        simp [List.lookup, this, ih]

/-- The first entry of each key is the one `lookup` finds. -/
theorem lookup_firstKeys {α : Type} : ∀ (ps : List (PropKey × α)) (j : PropKey),
    (firstKeys ps).lookup j = ps.lookup j
  | [], _ => rfl
  | (k, x) :: ps, j => by
    by_cases hj : j = k
    · subst hj; simp [firstKeys, List.lookup]
    · have : (j == k) = false := by simpa using hj
      simp only [firstKeys, List.lookup, this]
      rw [lookup_filter_ne _ hj, lookup_firstKeys ps j]

theorem firstKeys_nodup {α : Type} : ∀ (ps : List (PropKey × α)),
    ((firstKeys ps).map Prod.fst).Nodup
  | [] => by simp [firstKeys]
  | (k, x) :: ps => by
    simp only [firstKeys, List.map_cons, List.nodup_cons]
    refine ⟨?_, ?_⟩
    · intro hk
      obtain ⟨p, hp, he⟩ := List.mem_map.mp hk
      have := (List.mem_filter.mp hp).2
      simp [he] at this
    · exact (firstKeys_nodup ps).sublist (List.Sublist.map _ List.filter_sublist)

theorem mem_mergeData {a b : List (PropKey × Tm)} {p : PropKey × Tm}
    (h : p ∈ mergeData a b) : p ∈ a ∨ p ∈ b := by
  rcases List.mem_append.mp h with h | h
  · exact .inl (List.mem_filter.mp h).1
  · exact .inr h

/-- Every value a merge allocates is `undefined`, a value the heap holds, or
a string, a code unit a string source gives. -/
theorem mergeParts_vals {h : List Tm} {d : List PropKey} {a b : Tm} {ps : List (PropKey × Tm)}
    (hp : mergeParts h d a b = some ps) :
    ∀ p ∈ ps, p.2 = .undef ∨ (p.2 ∈ h ∧ isVal p.2 = true) ∨ ∃ u, p.2 = .str u := by
  simp only [mergeParts, Option.bind_eq_bind, Option.bind_eq_some_iff] at hp
  obtain ⟨pa, ha, qb, hb, he⟩ := hp
  cases he
  intro p hp
  have hA : ∀ p ∈ pa, p.2 = .undef ∨ (p.2 ∈ h ∧ isVal p.2 = true) ∨ ∃ u, p.2 = .str u := by
    unfold ownAll at ha
    split at ha
    · split at ha
      · cases ha
      cases ha
      intro p hp
      obtain ⟨r, -, rfl⟩ := List.mem_map.mp (mem_firstKeys hp)
      exact (heapVal_mem h r.2).imp_right .inl
    · cases ha
  have hB : ∀ p ∈ qb, p.2 = .undef ∨ (p.2 ∈ h ∧ isVal p.2 = true) ∨ ∃ u, p.2 = .str u := by
    unfold ownData at hb
    split at hb
    · split at hb
      · cases hb
      cases hb
      intro p hp
      rcases List.mem_append.mp (mem_firstKeys hp) with hp | hp
      · obtain ⟨r, -, rfl⟩ := List.mem_map.mp hp
        exact (heapVal_mem h r.2).imp_right .inl
      · unfold storeData at hp
        split at hp
        · split at hp
          · obtain ⟨r, -, hr⟩ := List.mem_filterMap.mp hp
            obtain ⟨m, -, rfl⟩ := Option.map_eq_some_iff.mp hr
            exact (heapVal_mem h m).imp_right .inl
          · simp at hp
        · simp at hp
    · cases hb
      intro p hp
      obtain ⟨q, -, rfl⟩ := List.mem_map.mp (mem_firstKeys hp)
      exact .inr (.inr ⟨_, rfl⟩)
    all_goals (cases hb <;> (intro p hp; simp at hp))
  rcases mem_mergeData hp with hp | hp
  · exact hA p hp
  · exact hB p (List.mem_filter.mp hp).1
abbrev Env := Nat → Tm

def push (a : Tm) (ρ : Env) : Env
  | 0 => a
  | i + 1 => ρ i

/-! Simultaneous closing substitution, leaving `d` enclosing binders intact. -/
mutual
def instantiate (d : Nat) (ρ : Env) : Tm → Tm
  | .var i => if i < d then .var i else ρ (i - d)
  | .letE a b => .letE (instantiate d ρ a) (instantiate (d + 1) ρ b)
  | .objAt fs .absent oid => .objAt fs .absent oid
  | .invoke f r args => .invoke (instantiate d ρ f) (instantiate d ρ r) (instantiateArgs d ρ args)
  | .construct f args => .construct (instantiate d ρ f) (instantiateArgs d ρ args)
  | .objAt fs (.bound t r pre) oid =>
      .objAt fs (.bound (instantiate d ρ t) (instantiate d ρ r) (instantiateArgs d ρ pre)) oid
  | .makeAt (.bound t r pre) ns args =>
      .makeAt (.bound (instantiate d ρ t) (instantiate d ρ r) (instantiateArgs d ρ pre)) ns
        (instantiateArgs d ρ args)
  | .makeAt .absent ns args => .makeAt .absent ns (instantiateArgs d ρ args)
  | .readAt f a => .readAt f (instantiate d ρ a)
  | .indexAt a key => .indexAt (instantiate d ρ a) (instantiate d ρ key)
  | .writeAt f a b => .writeAt f (instantiate d ρ a) (instantiate d ρ b)
  | .test k a => .test k (instantiate d ρ a)
  | .ite c a b => .ite (instantiate d ρ c) (instantiate d ρ a) (instantiate d ρ b)
  | .arith op a b => .arith op (instantiate d ρ a) (instantiate d ρ b)
  | .arrLit args => .arrLit (instantiateArgs d ρ args)
  | .elemAt a b => .elemAt (instantiate d ρ a) (instantiate d ρ b)
  | .setElem a b c => .setElem (instantiate d ρ a) (instantiate d ρ b) (instantiate d ρ c)
  | .lenOf a => .lenOf (instantiate d ρ a)
  | .spread a => .spread (instantiate d ρ a)
  | .throw a => .throw (instantiate d ρ a)
  | .merge dr a b => .merge dr (instantiate d ρ a) (instantiate d ρ b)
  | .makeKey k a => .makeKey (instantiate d ρ k) (instantiate d ρ a)
  | .objAt fs (.graph n E K s caps k r) oid => .objAt fs (.graph n E K s (instantiateArgs d ρ caps) k r) oid
  | .makeAt (.graph n E K s caps k r) ns args =>
      .makeAt (.graph n E K s (instantiateArgs d ρ caps) k r) ns (instantiateArgs d ρ args)
  | .goto E K l L x => .goto E K l (instantiateArgs d ρ L) (instantiate d ρ x)
  | .frame E K t L x k h => .frame E K (instantiate d ρ t) (instantiateArgs d ρ L) (instantiate d ρ x) k h
  | t => t

def instantiateArgs (d : Nat) (ρ : Env) : List Tm → List Tm
  | [] => []
  | a :: args => instantiate d ρ a :: instantiateArgs d ρ args
end

@[simp] theorem instantiateArgs_eq_map (d : Nat) (ρ : Env) (args : List Tm) :
    instantiateArgs d ρ args = args.map (instantiate d ρ) := by
  induction args <;> simp_all [instantiateArgs]

/-- A graph run's environment: its slots, then the value of every slot past them. -/
def envOf (L : List Tm) (d : Tm) : Env := fun i => L.getD i d

/-- A target's slot map on a graph run's environment, as `PointClaims.mapEnv`
applies it: slot `i` of the result is the source slot the map names, and
every slot past the map is the source's slot 0. -/
def envMap (m : Option (List Nat)) (L : List Tm) (d : Tm) : List Tm × Tm :=
  match m with
  | none => (L, d)
  | some slots => (slots.map (L.getD · d), L.getD 0 d)

theorem getD_mem_or (L : List Tm) (i : Nat) (d : Tm) : L.getD i d ∈ L ∨ L.getD i d = d := by
  by_cases h : i < L.length
  · left; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  · right; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : L.length ≤ i)]

/-- A mapped environment holds only values of the one it maps. -/
theorem envMap_mem {m : Option (List Nat)} {L : List Tm} {d x : Tm}
    (hx : x ∈ (envMap m L d).1 ∨ x = (envMap m L d).2) : x ∈ L ∨ x = d := by
  cases m with
  | none => simpa [envMap] using hx
  | some slots =>
    simp only [envMap, List.mem_map] at hx
    rcases hx with ⟨i, _, rfl⟩ | rfl
    · exact getD_mem_or L i d
    · exact getD_mem_or L 0 d

abbrev Heap := List Val

/-- **A term that throws.** `Raises t v`: `t` is `throw v` for a value `v`, in
evaluation position: under exactly the contexts `Step` evaluates in, each
constructor here the congruence rule of the same name with a throw in place of
a step. Such a term does not step (`raises_no_step`); the thrown value leaves
every context it is in, until a handler catches it. -/
inductive Raises : Tm → Tm → Prop where
  | throwV : isVal v = true → isSourceVal v = true → Raises (.throw v) v
  | throwC : Raises a v → Raises (.throw a) v
  | callL : Raises f v → Raises (.invoke f r args) v
  | callRecv : isVal f = true → Raises r v → Raises (.invoke f r args) v
  | callArg {f r a v : Tm} {args : List Tm} {i : Nat} :
      isVal f = true → isVal r = true → args[i]? = some a →
      (∀ j, j < i → ∀ w, args[j]? = some w → isVal w = true) →
      Raises a v → Raises (.invoke f r args) v
  | constructL : Raises f v → Raises (.construct f args) v
  | constructArg {f a v : Tm} {args : List Tm} {i : Nat} :
      isVal f = true → args[i]? = some a →
      (∀ j, j < i → ∀ w, args[j]? = some w → isVal w = true) →
      Raises a v → Raises (.construct f args) v
  | letC : Raises a v → Raises (.letE a b) v
  | spreadC : Raises a v → Raises (.spread a) v
  | makeArg {c : CallCode} {ns : List PropKey} {inits : List Tm} {i : Nat} {a v : Tm} :
      inits[i]? = some a →
      (∀ j, j < i → ∀ w, inits[j]? = some w → isVal w = true) →
      Raises a v → Raises (.makeAt c ns inits) v
  | readC : Raises a v → Raises (.readAt f a) v
  | indexC1 : Raises a v → Raises (.indexAt a key) v
  | indexC2 : isVal a = true → Raises key v → Raises (.indexAt a key) v
  | writeC1 : Raises a v → Raises (.writeAt f a b) v
  | writeC2 : isVal a = true → Raises b v → Raises (.writeAt f a b) v
  | testC : Raises a v → Raises (.test k a) v
  | iteC : Raises c v → Raises (.ite c t e) v
  | arithC1 : Raises a v → Raises (.arith op a b) v
  | arithC2 : isVal a = true → Raises b v → Raises (.arith op a b) v
  | arrArg {inits : List Tm} {i : Nat} {a v : Tm} : inits[i]? = some a →
      (∀ j, j < i → ∀ w, inits[j]? = some w → isVal w = true) →
      Raises a v → Raises (.arrLit inits) v
  | elemC1 : Raises a v → Raises (.elemAt a i) v
  | elemC2 : isVal a = true → Raises i v → Raises (.elemAt a i) v
  | setC1 : Raises a v → Raises (.setElem a i x) v
  | setC2 : isVal a = true → Raises i v → Raises (.setElem a i x) v
  | setC3 : isVal a = true → isVal i = true → Raises x v → Raises (.setElem a i x) v
  | lenC : Raises a v → Raises (.lenOf a) v
  | mergeC1 : Raises a v → Raises (.merge d a b) v
  | mergeC2 : isVal a = true → Raises b v → Raises (.merge d a b) v
  | makeKeyC1 : Raises k v → Raises (.makeKey k a) v
  | makeKeyC2 : isVal k = true → Raises a v → Raises (.makeKey k a) v

/-! ## One small step, threading the heap -/


inductive Step : Heap → Tm → Heap → Tm → Prop where
  | callL : Step h f h' f' → Step h (.invoke f r args) h' (.invoke f' r args)
  /-- The receiver runs after the callee and before every actual. -/
  | callRecv : isVal f = true → Step h r h' r' → Step h (.invoke f r args) h' (.invoke f r' args)
  | callArg : isVal f = true → isVal r = true → args[i]? = some a →
      (∀ j, j < i → ∀ v, args[j]? = some v → isVal v = true) →
      Step h a h' a' → Step h (.invoke f r args) h' (.invoke f r (args.set i a'))
  /-- `new` evaluates the constructor, then the actuals left to right, as a
  call does, and runs only `construct` code: `new` on call-only code, and a
  plain call of construct-only code, are stuck, as JavaScript throws. The code
  receives `undefined` for its receiver. -/
  | constructL : Step h f h' f' → Step h (.construct f args) h' (.construct f' args)
  | constructArg : isVal f = true → args[i]? = some a →
      (∀ j, j < i → ∀ v, args[j]? = some v → isVal v = true) →
      Step h a h' a' → Step h (.construct f args) h' (.construct f (args.set i a'))
  | letC : Step h a h' a' → Step h (.letE a b) h' (.letE a' b)
  | letV : isVal a = true → Step h (.letE a b) h (subst 0 a b)
  /-- A bound function forwards in one step: the receiver of this call is
  dropped, the saved one used, and the prefix goes before the actuals. -/
  | callBound : isVal r = true → (∀ a ∈ args, isVal a = true) →
      Step h (.invoke (.objAt fs (.bound t r₀ pre) oid) r args) h (.invoke t r₀ (pre ++ args))
  /-- A spread actual whose store is ready is replaced by the store's elements
  once every earlier actual is a value, so later actuals run after the read. -/
  | spreadC : Step h a h' a' → Step h (.spread a) h' (.spread a')
  | callSpread {args pre post : List Tm} {ls : List (Option Nat)} {vs : List Tm} :
      isVal f = true → isVal r = true → args = pre ++ .spread (.arr ls) :: post →
      (∀ v ∈ pre, isVal v = true) →
      readElems h ls = some vs → Step h (.invoke f r args) h (.invoke f r (pre ++ vs ++ post))
  /-- `new` reads a spread actual as a call does. -/
  | constructSpread {args pre post : List Tm} {ls : List (Option Nat)} {vs : List Tm} :
      isVal f = true → args = pre ++ .spread (.arr ls) :: post →
      (∀ v ∈ pre, isVal v = true) →
      readElems h ls = some vs → Step h (.construct f args) h (.construct f (pre ++ vs ++ post))
  /-- Initializers are evaluated left to right, like actual arguments. -/
  | makeArg {c : CallCode} {ns : List PropKey} {inits : List Tm} {i : Nat}
      {h h' : Heap} {a a' : Tm} : inits[i]? = some a →
      (∀ j, j < i → ∀ v, inits[j]? = some v → isVal v = true) →
      Step h a h' a' → Step h (.makeAt c ns inits) h' (.makeAt c ns (inits.set i a'))
  /-- Allocation takes one fresh location per named field, in order. -/
  | makeFields {c : CallCode} {ns : List PropKey} {vs : List Tm} {h : Heap} :
      (∀ v ∈ vs, isVal v = true) → ns.length = vs.length →
      Step h (.makeAt c ns vs) (h ++ vs ++ [.nul]) (.objAt (slots h.length ns) c (h.length + vs.length))
  | readC : Step h a h' a' → Step h (.readAt f a) h' (.readAt f a')
  /-- Reading and writing a field go to its location, whatever the object's code. -/
  | readField {f : PropKey} {fs : List (PropKey × Nat)} {c : CallCode} {l : Nat}
      {h : Heap} {v : Val} : fs.lookup f = some l → h[l]? = some v →
      Step h (.readAt f (.objAt fs c oid)) h v
  /-- A key the object lacks is read from its prototype, when it has one. -/
  | readProto {f : PropKey} {fs : List (PropKey × Nat)} {c : CallCode} {l : Nat}
      {h : Heap} {p : Val} : fs.lookup f = none → fs.lookup CallArguments.protoField = some l →
      h[l]? = some p → Step h (.readAt f (.objAt fs c oid)) h (.readAt f p)
  /-- JavaScript property lookup produces undefined when the name is absent
  and there is no prototype to continue at. -/
  | readMissing {f : PropKey} {fs : List (PropKey × Nat)} {c : CallCode} {h : Heap} :
      fs.lookup f = none → fs.lookup CallArguments.protoField = none →
      Step h (.readAt f (.objAt fs c oid)) h .undef
  | indexC1 : Step h a h' a' → Step h (.indexAt a key) h' (.indexAt a' key)
  | indexC2 : isVal a = true → Step h key h' key' →
      Step h (.indexAt a key) h' (.indexAt a key')
  /-- A computed key is converted by `ToPropertyKey` (`propertyKey`): a
  string, a symbol, or a number, which names the key its `ToString` spells. -/
  | indexField {key : Tm} {f : PropKey} {fs : List (PropKey × Nat)} {c : CallCode} {l : Nat}
      {h : Heap} {v : Val} : propertyKey key = some f → fs.lookup f = some l → h[l]? = some v →
      Step h (.indexAt (.objAt fs c oid) key) h v
  | indexProto {key : Tm} {f : PropKey} {fs : List (PropKey × Nat)} {c : CallCode} {l : Nat}
      {h : Heap} {p : Val} : propertyKey key = some f → fs.lookup f = none →
      fs.lookup CallArguments.protoField = some l →
      h[l]? = some p → Step h (.indexAt (.objAt fs c oid) key) h (.indexAt p key)
  | indexMissing {key : Tm} {f : PropKey} {fs : List (PropKey × Nat)} {c : CallCode} {h : Heap} :
      propertyKey key = some f → fs.lookup f = none → fs.lookup CallArguments.protoField = none →
      Step h (.indexAt (.objAt fs c oid) key) h .undef
  | writeC1 : Step h a h' a' → Step h (.writeAt f a b) h' (.writeAt f a' b)
  | writeC2 : isVal a = true → Step h b h' b' → Step h (.writeAt f a b) h' (.writeAt f a b')
  | writeField {f : PropKey} {fs : List (PropKey × Nat)} {c : CallCode} {l : Nat}
      {h : Heap} {v : Val} : isVal v = true → fs.lookup f = some l → l < h.length →
      Step h (.writeAt f (.objAt fs c oid) v) (h.set l v) .nul
  | testC : Step h a h' a' → Step h (.test k a) h' (.test k a')
  | testV : isVal v = true →
      Step h (.test k v) h (if tagHoldsIn h k v then .tru else .fls)
  | iteC : Step h c h' c' → Step h (.ite c t e) h' (.ite c' t e)
  | iteT : Step h (.ite .tru t e) h t
  | iteF : Step h (.ite .fls t e) h e
  | arithC1 : Step h a h' a' → Step h (.arith op a b) h' (.arith op a' b)
  | arithC2 : isVal a = true → Step h b h' b' → Step h (.arith op a b) h' (.arith op a b')
  /-- Two values combine in one step where `binop` answers for them. -/
  | arithV : binop op a b = some v → Step h (.arith op a b) h v
  /-- Store initializers are evaluated left to right, like fields. -/
  | arrArg {inits : List Tm} {i : Nat} {h h' : Heap} {a a' : Tm} : inits[i]? = some a →
      (∀ j, j < i → ∀ v, inits[j]? = some v → isVal v = true) →
      Step h a h' a' → Step h (.arrLit inits) h' (.arrLit (inits.set i a'))
  /-- A spread among a literal's initializers is replaced by its store's
  elements once every earlier initializer is a value, as in a call. -/
  | arrSpread {inits pre post : List Tm} {ls : List (Option Nat)} {vs : List Tm} {h : Heap} :
      inits = pre ++ .spread (.arr ls) :: post → (∀ v ∈ pre, isVal v = true) →
      readElems h ls = some vs → Step h (.arrLit inits) h (.arrLit (pre ++ vs ++ post))
  /-- A store takes one fresh location per element, in order. -/
  | arrAlloc {vs : List Tm} {h : Heap} : (∀ v ∈ vs, isVal v = true) →
      Step h (.arrLit vs) (h ++ vs) (.arr (elemSlots h.length vs.length))
  | elemC1 : Step h a h' a' → Step h (.elemAt a i) h' (.elemAt a' i)
  | elemC2 : isVal a = true → Step h i h' i' → Step h (.elemAt a i) h' (.elemAt a i')
  /-- An index naming a location reads it; any other reads `undefined`. -/
  | elemRead {ls : List (Option Nat)} {b : UInt64} {l : Nat} {h : Heap} {v : Val} :
      elemLoc ls b = some l → h[l]? = some v → Step h (.elemAt (.arr ls) (.num b)) h v
  | elemAbsent {ls : List (Option Nat)} {b : UInt64} {h : Heap} :
      elemLoc ls b = none → Step h (.elemAt (.arr ls) (.num b)) h .undef
  | setC1 : Step h a h' a' → Step h (.setElem a i v) h' (.setElem a' i v)
  | setC2 : isVal a = true → Step h i h' i' → Step h (.setElem a i v) h' (.setElem a i' v)
  | setC3 : isVal a = true → isVal i = true → Step h v h' v' →
      Step h (.setElem a i v) h' (.setElem a i v')
  /-- A present element's location takes the value; the store is unchanged. -/
  | setPresent {ls : List (Option Nat)} {b : UInt64} {l : Nat} {h : Heap} {v : Val} :
      isVal v = true → elemLoc ls b = some l → l < h.length →
      Step h (.setElem (.arr ls) (.num b) v) (h.set l v) (.arr ls)
  /-- A hole or an index past the end takes a fresh location, which the new
  store records; holes fill any gap. -/
  | setGrow {ls : List (Option Nat)} {b : UInt64} {k : Nat} {h : Heap} {v : Val} :
      isVal v = true → indexOfBits b = some k → elemLoc ls b = none →
      Step h (.setElem (.arr ls) (.num b) v) (h ++ [v]) (.arr (placeAt ls k h.length))
  | lenC : Step h a h' a' → Step h (.lenOf a) h' (.lenOf a')
  | lenV {ls : List (Option Nat)} {h : Heap} : Step h (.lenOf (.arr ls)) h (.num (bitsOfNat ls.length))
  /-- A string's length is its count of UTF-16 code units. -/
  | lenStr {s : String} {h : Heap} :
      Step h (.lenOf (.str s)) h (.num (bitsOfNat (utf16Units s).length))
  /-- A string's own index property: the code unit at an index below its
  length, `undefined` at any other number. -/
  | elemStr {s : String} {b : UInt64} {h : Heap} :
      Step h (.elemAt (.str s) (.num b)) h (codeUnitAt s b)
  /-- A throw's operand is evaluated first. -/
  | throwC : Step h a h' a' → Step h (.throw a) h' (.throw a')
  /-- Two values an operator throws on step to throwing a fresh error object. -/
  | arithThrow : binopThrows op a b = true → Step h (.arith op a b) (h ++ [.nul]) (.throw (thrownError h.length))
  /-- A merge evaluates its accumulator, then its source. -/
  | mergeC1 : Step h a h' a' → Step h (.merge d a b) h' (.merge d a' b)
  | mergeC2 : isVal a = true → Step h b h' b' → Step h (.merge d a b) h' (.merge d a b')
  /-- Both values: the properties are read now, and allocated by the
  allocation this steps to, which runs no code. -/
  | mergeV {ps : List (PropKey × Tm)} : isVal a = true → isVal b = true → mergeParts h d a b = some ps →
      Step h (.merge d a b) h (.makeAt .absent (ps.map Prod.fst) (ps.map Prod.snd))
  /-- An allocation at a computed key evaluates its key, then its initializer. -/
  | makeKeyC1 : Step h k h' k' → Step h (.makeKey k a) h' (.makeKey k' a)
  | makeKeyC2 : isVal k = true → Step h a h' a' → Step h (.makeKey k a) h' (.makeKey k a')
  /-- Both values: the key is converted, which runs no code, and the
  allocation this steps to allocates the one property. -/
  | makeKeyV {f : PropKey} : isVal a = true → propertyKey k = some f →
      Step h (.makeKey k a) h (.makeAt .absent [f] [a])
  /-- Graph code with `[[Call]]` is invoked in one step, changing no heap: its
  run starts at the entry label, the receiver in slot 0, then the parameters,
  then the captures, after collecting the rest's store when it has one
  (`CallArguments.graphEntry`). Its kind binds the receiver (`Invoke.binds`):
  sloppy code is invoked only with an object. -/
  | callGraph : isVal r = true → (∀ a ∈ args, isVal a = true) → k.binds r = true →
      Step h (.invoke (.objAt fs (.graph n E K s caps k rest) oid) r args) h
        (CallArguments.graphEntry n E K s caps rest r args)
  /-- `new` on construct-only graph code enters it as a call does, with
  `undefined` for the receiver. -/
  | constructGraph : (∀ a ∈ args, isVal a = true) →
      Step h (.construct (.objAt fs (.graph n E K s caps .construct rest) oid) args) h
        (CallArguments.graphEntry n E K s caps rest .undef args)
  /-- Entering a node instantiates its expression in the run's environment. -/
  | gotoEnter : E[l]? = some e → K[l]? = some (k, x) →
      Step h (.goto E K l L d) h (.frame E K (instantiate 0 (envOf L d) e) L d k x)
  | frameC : Step h t h' t' → Step h (.frame E K t L d k x) h' (.frame E K t' L d k x)
  /-- A returned value is the run's value. -/
  | frameRet : isVal v = true → Step h (.frame E K v L d .ret x) h v
  | frameBind : isVal v = true →
      Step h (.frame E K v L d (.bind l) x) h
        (.goto E K l.label (envMap l.mapping (v :: L) d).1 (envMap l.mapping (v :: L) d).2)
  | frameEffect : isVal v = true →
      Step h (.frame E K v L d (.effect l) x) h
        (.goto E K l.label (envMap l.mapping L d).1 (envMap l.mapping L d).2)
  | frameYes : Step h (.frame E K .tru L d (.branch y n) x) h
      (.goto E K y.label (envMap y.mapping L d).1 (envMap y.mapping L d).2)
  | frameNo : Step h (.frame E K .fls L d (.branch y n) x) h
      (.goto E K n.label (envMap n.mapping L d).1 (envMap n.mapping L d).2)
  | frameYesBind : Step h (.frame E K .tru L d (.branchBind y n) x) h
      (.goto E K y.label (envMap y.mapping (.tru :: L) d).1 (envMap y.mapping (.tru :: L) d).2)
  | frameNoBind : Step h (.frame E K .fls L d (.branchBind y n) x) h
      (.goto E K n.label (envMap n.mapping (.fls :: L) d).1 (envMap n.mapping (.fls :: L) d).2)
  | frameTag : isVal v = true →
      Step h (.frame E K v L d (.tagBind tag y n) x) h
        (.goto E K (if tagHoldsIn h tag v then y else n).label
          (envMap (if tagHoldsIn h tag v then y else n).mapping (v :: L) d).1
          (envMap (if tagHoldsIn h tag v then y else n).mapping (v :: L) d).2)
  /-- A throw out of a node with a handler goes there, the thrown value bound. -/
  | frameHandle : Raises t v →
      Step h (.frame E K t L d k (some l)) h
        (.goto E K l.label (envMap l.mapping (v :: L) d).1 (envMap l.mapping (v :: L) d).2)
  /-- A throw out of a node without one leaves the run: a throw of the same
  value, which the run's own evaluation context then carries on. -/
  | frameRaise : Raises t v → Step h (.frame E K t L d k none) h (.throw v)

/-! ### The one-field rules

Each is the single-field instance of the rule above it, and carries the name
and the statement the development used before fields were named. -/

@[simp] theorem lookup_value (l : Nat) : ([(valueField, l)] : List (PropKey × Nat)).lookup valueField = some l := by
  simp [List.lookup]

theorem Step.makeC (hs : Step h a h' a') : Step h (.make c a) h' (.make c a') :=
  .makeArg (i := 0) rfl (by intro j hj; omega) hs

theorem Step.makeV (hv : isVal v = true) :
    Step h (.make c v) (h ++ [v] ++ [.nul]) (.obj h.length c) :=
  .makeFields (by simpa using hv) rfl

theorem Step.makeFnC (hs : Step h a h' a') : Step h (.makeFn c a) h' (.makeFn c a') :=
  .makeArg (i := 0) rfl (by intro j hj; omega) hs

theorem Step.makeFnV (hv : isVal v = true) :
    Step h (.makeFn c v) (h ++ [v] ++ [.nul]) (.fnObj h.length c) :=
  .makeFields (by simpa using hv) rfl

theorem Step.readV (he : h[l]? = some v) : Step h (.read (.obj l c)) h v :=
  .readField (lookup_value l) he

theorem Step.writeV (hv : isVal v = true) (hlt : l < h.length) :
    Step h (.write (.obj l c) v) (h.set l v) .nul :=
  .writeField hv (lookup_value l) hlt

theorem Step.appR (hv : isVal f = true) (hs : Step h a h' a') :
    Step h (.app f a) h' (.app f a') :=
  .callArg (i := 0) hv rfl rfl (by intro j hj; omega) hs

/-- Inversion for the source pipeline's singleton argument lists. -/
theorem singleton_get {a b : Tm} {i : Nat} (h : [a][i]? = some b) : i = 0 ∧ b = a := by
  have hi := (List.getElem?_eq_some_iff.mp h).1
  have he : i = 0 := by simpa using hi
  subst i
  exact ⟨rfl, (Option.some.inj h).symm⟩


theorem value_no_step {v : Val} (hv : isVal v = true) {h h' t} : ¬ Step h v h' t := by
  intro hs
  cases v <;> simp [isVal] at hv <;> cases hs

theorem spread_arr_no_step {ls h h' t} : ¬ Step h (.spread (.arr ls)) h' t := by
  intro hs
  cases hs with
  | spreadC s => exact value_no_step rfl s

/-- A list with a spread in it is not all values. -/
theorem spread_not_values {args pre post : List Tm} {a : Tm}
    (he : args = pre ++ .spread a :: post) (hv : ∀ v ∈ args, isVal v = true) : False := by
  have := hv (.spread a) (by simp [he])
  simp [isVal] at this

/-- A spread whose store is ready is the first actual still to run, so no
earlier actual steps and it has no step of its own. -/
theorem spread_blocks_arg {args pre post : List Tm} {ls : List (Option Nat)}
    (he : args = pre ++ .spread (.arr ls) :: post) (hpre : ∀ v ∈ pre, isVal v = true)
    {i : Nat} {a : Tm} (hg : args[i]? = some a)
    (hb : ∀ j, j < i → ∀ v, args[j]? = some v → isVal v = true)
    {h h' a'} (s : Step h a h' a') : False := by
  subst he
  rcases Nat.lt_trichotomy i pre.length with hi | hi | hi
  · rw [List.getElem?_append_left hi] at hg
    exact value_no_step (hpre a (List.mem_of_getElem? hg)) s
  · subst hi
    rw [List.getElem?_append_right (Nat.le_refl _)] at hg
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hg
    subst hg
    exact spread_arr_no_step s
  · have := hb pre.length hi (.spread (.arr ls)) (by simp)
    simp [isVal] at this

/-- The first actual that is not a value is where a list splits. -/
theorem split_unique {pre post pre' post' : List Tm} {x x' : Tm}
    (he : pre ++ x :: post = pre' ++ x' :: post')
    (hp : ∀ v ∈ pre, isVal v = true) (hp' : ∀ v ∈ pre', isVal v = true)
    (hx : isVal x = false) (hx' : isVal x' = false) : pre = pre' ∧ x = x' ∧ post = post' := by
  induction pre generalizing pre' with
  | nil =>
    cases pre' with
    | nil => simp_all
    | cons y pre' =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at he
      have := hp' y (by simp)
      rw [← he.1] at this
      simp [hx] at this
  | cons y pre ih =>
    cases pre' with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at he
      have := hp y (by simp)
      rw [he.1] at this
      simp [hx'] at this
    | cons y' pre' =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      obtain ⟨rfl, rfl, rfl⟩ := ih he (fun v hv => hp v (by simp [hv]))
        (fun v hv => hp' v (by simp [hv]))
      exact ⟨rfl, rfl, rfl⟩

theorem nul_no_step {h h' t} : ¬ Step h .nul h' t := by intro s; cases s
theorem tru_no_step {h h' t} : ¬ Step h .tru h' t := by intro s; cases s
theorem fls_no_step {h h' t} : ¬ Step h .fls h' t := by intro s; cases s
theorem obj_no_step {h fs c h' t} : ¬ Step h (.objAt fs c oid) h' t := by intro s; cases s

/-! ### Closed values and operational inversion lemmas -/

def Closed (v : Val) : Prop := ∀ k a, subst k a v = v

theorem stuck_no_step {h h' t} : ¬ Step h (.app .nul .nul) h' t := by
  intro hs
  cases hs with
  | callL hs => exact nul_no_step hs
  | callRecv _ hs => exact value_no_step rfl hs
  | callArg _ _ hg _ hs =>
    obtain ⟨rfl, rfl⟩ := singleton_get hg
    exact nul_no_step hs
  | callSpread _ _ he _ _ => exact spread_not_values he (by simp [isVal])

/-! ### Throwing

A throwing term is neither a value nor a term that steps, and the value it
throws is determined. -/

theorem raises_not_val {t v : Tm} (h : Raises t v) : isVal t = false := by
  cases h <;> rfl

theorem raises_sourceVal {t v : Tm} (h : Raises t v) : isSourceVal v = true := by
  induction h <;> assumption

theorem raises_val {t v : Tm} (h : Raises t v) : isVal v = true := by
  induction h <;> assumption

/-- In a list evaluated left to right, the first entry that is not a value is
determined: two such positions with only values before each coincide. -/
theorem first_nonval_unique {xs : List Tm} {i j : Nat} {a b : Tm}
    (ha : xs[i]? = some a) (hb : xs[j]? = some b)
    (hi : ∀ k, k < i → ∀ w, xs[k]? = some w → isVal w = true)
    (hj : ∀ k, k < j → ∀ w, xs[k]? = some w → isVal w = true)
    (na : isVal a = false) (nb : isVal b = false) : i = j ∧ a = b := by
  have hij : i = j := by
    rcases Nat.lt_trichotomy i j with h | h | h
    · have := hj i h a ha; simp [na] at this
    · exact h
    · have := hi j h b hb; simp [nb] at this
  subst hij
  exact ⟨rfl, Option.some.inj (ha.symm.trans hb)⟩

theorem not_val_of_step {h h' t t'} (s : Step h t h' t') : isVal t = false := by
  cases ht : isVal t
  · rfl
  · exact False.elim (value_no_step ht s)

/-- A spread whose store is ready never throws. -/
theorem spread_arr_no_raise {ls : List (Option Nat)} {v : Tm} : ¬ Raises (.spread (.arr ls)) v := by
  intro h; cases h with | spreadC h => cases h

/-- A ready spread is the first actual still to run: nothing before it throws. -/
theorem spread_blocks_raise {args pre post : List Tm} {ls : List (Option Nat)}
    (he : args = pre ++ .spread (.arr ls) :: post) (hpre : ∀ w ∈ pre, isVal w = true)
    {i : Nat} {a v : Tm} (hg : args[i]? = some a)
    (hb : ∀ j, j < i → ∀ w, args[j]? = some w → isVal w = true)
    (hr : Raises a v) : False := by
  subst he
  rcases Nat.lt_trichotomy i pre.length with hi | hi | hi
  · rw [List.getElem?_append_left hi] at hg
    have := hpre a (List.mem_of_getElem? hg)
    rw [raises_not_val hr] at this; contradiction
  · subst hi
    rw [List.getElem?_append_right (Nat.le_refl _)] at hg
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hg
    subst hg
    exact spread_arr_no_raise hr
  · have := hb pre.length hi (.spread (.arr ls)) (by simp)
    simp [isVal] at this

/-- The entry after a prefix of values is the first one still to run. -/
theorem prefix_position {pre rest : List Tm} {t : Tm} (hp : ∀ w ∈ pre, isVal w = true) :
    (pre ++ t :: rest)[pre.length]? = some t ∧
      ∀ j, j < pre.length → ∀ w, (pre ++ t :: rest)[j]? = some w → isVal w = true := by
  refine ⟨by simp, ?_⟩
  intro j hj w hw
  rw [List.getElem?_append_left hj] at hw
  exact hp w (List.mem_of_getElem? hw)

/-- **A throwing term does not step.** -/
theorem raises_no_step {t v : Tm} (hr : Raises t v) : ∀ {h h' t'}, ¬ Step h t h' t' := by
  induction hr with
  | throwV hv _ => intro _ _ _ s; cases s with | throwC s => exact value_no_step hv s
  | throwC _ ih => intro _ _ _ s; cases s with | throwC s => exact ih s
  | callL hf ih =>
    intro _ _ _ s
    cases s with
    | callL s => exact ih s
    | callRecv hv _ => rw [raises_not_val hf] at hv; contradiction
    | callArg hv _ _ _ _ => rw [raises_not_val hf] at hv; contradiction
    | callBound => cases hf
    | callGraph => cases hf
    | callSpread hv _ _ _ _ => rw [raises_not_val hf] at hv; contradiction
  | callRecv hfv hr ih =>
    intro _ _ _ s
    cases s with
    | callL s => exact value_no_step hfv s
    | callRecv _ s => exact ih s
    | callArg _ hv _ _ _ => rw [raises_not_val hr] at hv; contradiction
    | callBound hv _ => rw [raises_not_val hr] at hv; contradiction
    | callGraph hv _ => rw [raises_not_val hr] at hv; contradiction
    | callSpread _ hv _ _ _ => rw [raises_not_val hr] at hv; contradiction
  | callArg hfv hrv hg hb hr ih =>
    intro _ _ _ s
    cases s with
    | callL s => exact value_no_step hfv s
    | callRecv _ s => exact value_no_step hrv s
    | callArg _ _ hg' hb' s =>
      obtain ⟨rfl, rfl⟩ := first_nonval_unique hg hg' hb hb' (raises_not_val hr) (not_val_of_step s)
      exact ih s
    | callBound _ hvs => have := hvs _ (List.mem_of_getElem? hg); rw [raises_not_val hr] at this; contradiction
    | callGraph _ hvs => have := hvs _ (List.mem_of_getElem? hg); rw [raises_not_val hr] at this; contradiction
    | callSpread _ _ he hpre _ => exact spread_blocks_raise he hpre hg hb hr
  | constructL hf ih =>
    intro _ _ _ s
    cases s with
    | constructL s => exact ih s
    | constructArg hv _ _ _ => rw [raises_not_val hf] at hv; contradiction
    | constructGraph => cases hf
    | constructSpread hv _ _ _ => rw [raises_not_val hf] at hv; contradiction
  | constructArg hfv hg hb hr ih =>
    intro _ _ _ s
    cases s with
    | constructL s => exact value_no_step hfv s
    | constructArg _ hg' hb' s =>
      obtain ⟨rfl, rfl⟩ := first_nonval_unique hg hg' hb hb' (raises_not_val hr) (not_val_of_step s)
      exact ih s
    | constructGraph hvs => have := hvs _ (List.mem_of_getElem? hg); rw [raises_not_val hr] at this; contradiction
    | constructSpread _ he hpre _ => exact spread_blocks_raise he hpre hg hb hr
  | letC hr ih =>
    intro _ _ _ s
    cases s with
    | letC s => exact ih s
    | letV hv => rw [raises_not_val hr] at hv; contradiction
  | spreadC _ ih => intro _ _ _ s; cases s with | spreadC s => exact ih s
  | makeArg hg hb hr ih =>
    intro _ _ _ s
    cases s with
    | makeArg hg' hb' s =>
      obtain ⟨rfl, rfl⟩ := first_nonval_unique hg hg' hb hb' (raises_not_val hr) (not_val_of_step s)
      exact ih s
    | makeFields hvs _ => have := hvs _ (List.mem_of_getElem? hg); rw [raises_not_val hr] at this; contradiction
  | readC hr ih =>
    intro _ _ _ s
    cases s with
    | readC s => exact ih s
    | readField => cases hr
    | readProto => cases hr
    | readMissing => cases hr
  | indexC1 hr ih =>
    intro _ _ _ s
    cases s with
    | indexC1 s => exact ih s
    | indexC2 hv _ => rw [raises_not_val hr] at hv; contradiction
    | indexField => cases hr
    | indexProto => cases hr
    | indexMissing => cases hr
  | indexC2 hv hr ih =>
    intro _ _ _ s
    cases s with
    | indexC1 s => exact value_no_step hv s
    | indexC2 _ s => exact ih s
    | indexField hk => have := propertyKey_val hk; rw [raises_not_val hr] at this; contradiction
    | indexProto hk => have := propertyKey_val hk; rw [raises_not_val hr] at this; contradiction
    | indexMissing hk => have := propertyKey_val hk; rw [raises_not_val hr] at this; contradiction
  | writeC1 hr ih =>
    intro _ _ _ s
    cases s with
    | writeC1 s => exact ih s
    | writeC2 hv _ => rw [raises_not_val hr] at hv; contradiction
    | writeField => cases hr
  | writeC2 hv hr ih =>
    intro _ _ _ s
    cases s with
    | writeC1 s => exact value_no_step hv s
    | writeC2 _ s => exact ih s
    | writeField hw _ _ => rw [raises_not_val hr] at hw; contradiction
  | testC hr ih =>
    intro _ _ _ s
    cases s with
    | testC s => exact ih s
    | testV hv => rw [raises_not_val hr] at hv; contradiction
  | iteC hr ih =>
    intro _ _ _ s
    cases s with
    | iteC s => exact ih s
    | iteT => cases hr
    | iteF => cases hr
  | arithC1 hr ih =>
    intro _ _ _ s
    cases s with
    | arithC1 s => exact ih s
    | arithC2 hv _ => rw [raises_not_val hr] at hv; contradiction
    | arithV hb => have := (binop_values hb).1; rw [raises_not_val hr] at this; contradiction
    | arithThrow ht => have := (binopThrows_values ht).1; rw [raises_not_val hr] at this; contradiction
  | arithC2 hv hr ih =>
    intro _ _ _ s
    cases s with
    | arithC1 s => exact value_no_step hv s
    | arithC2 _ s => exact ih s
    | arithV hb => have := (binop_values hb).2.1; rw [raises_not_val hr] at this; contradiction
    | arithThrow ht => have := (binopThrows_values ht).2; rw [raises_not_val hr] at this; contradiction
  | arrArg hg hb hr ih =>
    intro _ _ _ s
    cases s with
    | arrArg hg' hb' s =>
      obtain ⟨rfl, rfl⟩ := first_nonval_unique hg hg' hb hb' (raises_not_val hr) (not_val_of_step s)
      exact ih s
    | arrSpread he hpre _ => exact spread_blocks_raise he hpre hg hb hr
    | arrAlloc hvs => have := hvs _ (List.mem_of_getElem? hg); rw [raises_not_val hr] at this; contradiction
  | elemC1 hr ih =>
    intro _ _ _ s
    cases s with
    | elemC1 s => exact ih s
    | elemC2 hv _ => rw [raises_not_val hr] at hv; contradiction
    | elemRead => cases hr
    | elemAbsent => cases hr
    | elemStr => cases hr
  | elemC2 hv hr ih =>
    intro _ _ _ s
    cases s with
    | elemC1 s => exact value_no_step hv s
    | elemC2 _ s => exact ih s
    | elemRead => cases hr
    | elemAbsent => cases hr
    | elemStr => cases hr
  | setC1 hr ih =>
    intro _ _ _ s
    cases s with
    | setC1 s => exact ih s
    | setC2 hv _ => rw [raises_not_val hr] at hv; contradiction
    | setC3 hv _ _ => rw [raises_not_val hr] at hv; contradiction
    | setPresent => cases hr
    | setGrow => cases hr
  | setC2 hv hr ih =>
    intro _ _ _ s
    cases s with
    | setC1 s => exact value_no_step hv s
    | setC2 _ s => exact ih s
    | setC3 _ hi _ => rw [raises_not_val hr] at hi; contradiction
    | setPresent => cases hr
    | setGrow => cases hr
  | setC3 hv hi hr ih =>
    intro _ _ _ s
    cases s with
    | setC1 s => exact value_no_step hv s
    | setC2 _ s => exact value_no_step hi s
    | setC3 _ _ s => exact ih s
    | setPresent hw _ _ => rw [raises_not_val hr] at hw; contradiction
    | setGrow hw _ _ => rw [raises_not_val hr] at hw; contradiction
  | lenC hr ih =>
    intro _ _ _ s
    cases s with
    | lenC s => exact ih s
    | lenV => cases hr
    | lenStr => cases hr
  | mergeC1 hr ih =>
    intro _ _ _ s
    cases s with
    | mergeC1 s => exact ih s
    | mergeC2 hv _ => rw [raises_not_val hr] at hv; contradiction
    | mergeV hv _ _ => rw [raises_not_val hr] at hv; contradiction
  | mergeC2 hv hr ih =>
    intro _ _ _ s
    cases s with
    | mergeC1 s => exact value_no_step hv s
    | mergeC2 _ s => exact ih s
    | mergeV _ hw _ => rw [raises_not_val hr] at hw; contradiction
  | makeKeyC1 hr ih =>
    intro _ _ _ s
    cases s with
    | makeKeyC1 s => exact ih s
    | makeKeyC2 hv _ => rw [raises_not_val hr] at hv; contradiction
    | makeKeyV _ hk => have := propertyKey_val hk; rw [raises_not_val hr] at this; contradiction
  | makeKeyC2 hv hr ih =>
    intro _ _ _ s
    cases s with
    | makeKeyC1 s => exact value_no_step hv s
    | makeKeyC2 _ s => exact ih s
    | makeKeyV hw _ => rw [raises_not_val hr] at hw; contradiction

/-- **The thrown value is determined.** -/
theorem Raises_det {t v w : Tm} (h1 : Raises t v) (h2 : Raises t w) : v = w := by
  induction h1 generalizing w with
  | throwV hv _ =>
    cases h2 with
    | throwV => rfl
    | throwC h => rw [raises_not_val h] at hv; contradiction
  | throwC h ih =>
    cases h2 with
    | throwV hv _ => rw [raises_not_val h] at hv; contradiction
    | throwC h' => exact ih h'
  | callL h ih =>
    cases h2 with
    | callL h' => exact ih h'
    | callRecv hv _ => rw [raises_not_val h] at hv; contradiction
    | callArg hv _ _ _ _ => rw [raises_not_val h] at hv; contradiction
  | callRecv hf h ih =>
    cases h2 with
    | callL h' => rw [raises_not_val h'] at hf; contradiction
    | callRecv _ h' => exact ih h'
    | callArg _ hv _ _ _ => rw [raises_not_val h] at hv; contradiction
  | callArg hf hr hg hb h ih =>
    cases h2 with
    | callL h' => rw [raises_not_val h'] at hf; contradiction
    | callRecv _ h' => rw [raises_not_val h'] at hr; contradiction
    | callArg _ _ hg' hb' h' =>
      obtain ⟨rfl, rfl⟩ := first_nonval_unique hg hg' hb hb' (raises_not_val h) (raises_not_val h')
      exact ih h'
  | constructL h ih =>
    cases h2 with
    | constructL h' => exact ih h'
    | constructArg hv _ _ _ => rw [raises_not_val h] at hv; contradiction
  | constructArg hf hg hb h ih =>
    cases h2 with
    | constructL h' => rw [raises_not_val h'] at hf; contradiction
    | constructArg _ hg' hb' h' =>
      obtain ⟨rfl, rfl⟩ := first_nonval_unique hg hg' hb hb' (raises_not_val h) (raises_not_val h')
      exact ih h'
  | letC h ih => cases h2 with | letC h' => exact ih h'
  | spreadC h ih => cases h2 with | spreadC h' => exact ih h'
  | makeArg hg hb h ih =>
    cases h2 with
    | makeArg hg' hb' h' =>
      obtain ⟨rfl, rfl⟩ := first_nonval_unique hg hg' hb hb' (raises_not_val h) (raises_not_val h')
      exact ih h'
  | readC h ih => cases h2 with | readC h' => exact ih h'
  | indexC1 h ih =>
    cases h2 with
    | indexC1 h' => exact ih h'
    | indexC2 hv _ => rw [raises_not_val h] at hv; contradiction
  | indexC2 hv h ih =>
    cases h2 with
    | indexC1 h' => rw [raises_not_val h'] at hv; contradiction
    | indexC2 _ h' => exact ih h'
  | writeC1 h ih =>
    cases h2 with
    | writeC1 h' => exact ih h'
    | writeC2 hv _ => rw [raises_not_val h] at hv; contradiction
  | writeC2 hv h ih =>
    cases h2 with
    | writeC1 h' => rw [raises_not_val h'] at hv; contradiction
    | writeC2 _ h' => exact ih h'
  | testC h ih => cases h2 with | testC h' => exact ih h'
  | iteC h ih => cases h2 with | iteC h' => exact ih h'
  | arithC1 h ih =>
    cases h2 with
    | arithC1 h' => exact ih h'
    | arithC2 hv _ => rw [raises_not_val h] at hv; contradiction
  | arithC2 hv h ih =>
    cases h2 with
    | arithC1 h' => rw [raises_not_val h'] at hv; contradiction
    | arithC2 _ h' => exact ih h'
  | arrArg hg hb h ih =>
    cases h2 with
    | arrArg hg' hb' h' =>
      obtain ⟨rfl, rfl⟩ := first_nonval_unique hg hg' hb hb' (raises_not_val h) (raises_not_val h')
      exact ih h'
  | elemC1 h ih =>
    cases h2 with
    | elemC1 h' => exact ih h'
    | elemC2 hv _ => rw [raises_not_val h] at hv; contradiction
  | elemC2 hv h ih =>
    cases h2 with
    | elemC1 h' => rw [raises_not_val h'] at hv; contradiction
    | elemC2 _ h' => exact ih h'
  | setC1 h ih =>
    cases h2 with
    | setC1 h' => exact ih h'
    | setC2 hv _ => rw [raises_not_val h] at hv; contradiction
    | setC3 hv _ _ => rw [raises_not_val h] at hv; contradiction
  | setC2 hv h ih =>
    cases h2 with
    | setC1 h' => rw [raises_not_val h'] at hv; contradiction
    | setC2 _ h' => exact ih h'
    | setC3 _ hi _ => rw [raises_not_val h] at hi; contradiction
  | setC3 hv hi h ih =>
    cases h2 with
    | setC1 h' => rw [raises_not_val h'] at hv; contradiction
    | setC2 _ h' => rw [raises_not_val h'] at hi; contradiction
    | setC3 _ _ h' => exact ih h'
  | lenC h ih => cases h2 with | lenC h' => exact ih h'
  | mergeC1 h ih =>
    cases h2 with
    | mergeC1 h' => exact ih h'
    | mergeC2 hv _ => rw [raises_not_val h] at hv; contradiction
  | mergeC2 hv h ih =>
    cases h2 with
    | mergeC1 h' => rw [raises_not_val h'] at hv; contradiction
    | mergeC2 _ h' => exact ih h'
  | makeKeyC1 h ih =>
    cases h2 with
    | makeKeyC1 h' => exact ih h'
    | makeKeyC2 hv _ => rw [raises_not_val h] at hv; contradiction
  | makeKeyC2 hv h ih =>
    cases h2 with
    | makeKeyC1 h' => rw [raises_not_val h'] at hv; contradiction
    | makeKeyC2 _ h' => exact ih h'

/-- **Evaluation is deterministic.** One term in one heap has at most one next
state. Nothing in the safety definition says so — it quantifies existentially
over the world a step lands in — so this has to be proved, and it is what lets
two independent runs of the same program be compared. -/
theorem Step_det {h t h1 t1 h2 t2} (s1 : Step h t h1 t1) (s2 : Step h t h2 t2) :
    h1 = h2 ∧ t1 = t2 := by
  induction s1 generalizing h2 t2 with
  | constructL s ih =>
    cases s2 with
    | constructL s' => exact (ih s').imp id (congrArg (Tm.construct · _))
    | constructArg hv _ _ _ => exact False.elim (value_no_step hv s)
    | constructGraph => exact False.elim (obj_no_step s)
    | constructSpread hv _ _ _ => exact False.elim (value_no_step hv s)
  | @constructArg f args i a h h1 a1 hv hg hb s ih =>
    cases s2 with
    | constructL s' => exact False.elim (value_no_step hv s')
    | @constructArg _ _ j b _ _ b1 _ hg' hb' s' =>
      have hij : i = j := by
        by_cases he : i = j
        · exact he
        · have hlt : i < j ∨ j < i := by omega
          rcases hlt with hij | hji
          · exact False.elim (value_no_step (hb' i hij a hg) s)
          · exact False.elim (value_no_step (hb j hji b hg') s')
      subst j
      have hab : a = b := Option.some.inj (hg.symm.trans hg')
      subst b
      obtain ⟨rfl, rfl⟩ := ih s'
      exact ⟨rfl, rfl⟩
    | constructGraph hvs => exact False.elim (value_no_step (hvs a (List.mem_of_getElem? hg)) s)
    | constructSpread _ he hpre _ => exact False.elim (spread_blocks_arg he hpre hg hb s)
  | constructGraph hvs =>
    cases s2 with
    | constructL s' => exact False.elim (obj_no_step s')
    | constructArg _ hg _ s' => exact False.elim (value_no_step (hvs _ (List.mem_of_getElem? hg)) s')
    | constructGraph _ => exact ⟨rfl, rfl⟩
    | constructSpread _ he _ _ => exact False.elim (spread_not_values he hvs)
  | constructSpread hf he hpre hre =>
    cases s2 with
    | constructL s' => exact False.elim (value_no_step hf s')
    | constructArg _ hg hb s' => exact False.elim (spread_blocks_arg he hpre hg hb s')
    | constructGraph hvs => exact False.elim (spread_not_values he hvs)
    | constructSpread _ he' hpre' hre' =>
      obtain ⟨rfl, hx, rfl⟩ := split_unique (he.symm.trans he') hpre hpre' rfl rfl
      cases hx
      cases Option.some.inj (hre.symm.trans hre')
      exact ⟨rfl, rfl⟩
  | callL s ih =>
    cases s2 with
    | callL s' => exact (ih s').imp id (congrArg (Tm.invoke · _ _))
    | callRecv hv _ => exact False.elim (value_no_step hv s)
    | callArg hv _ _ _ _ => exact False.elim (value_no_step hv s)
    | callBound => exact False.elim (obj_no_step s)
    | callGraph => exact False.elim (obj_no_step s)
    | callSpread hv _ _ _ _ => exact False.elim (value_no_step hv s)
  | callRecv hf s ih =>
    cases s2 with
    | callL s' => exact False.elim (value_no_step hf s')
    | callRecv _ s' => exact (ih s').imp id (congrArg (Tm.invoke _ · _))
    | callArg _ hr _ _ _ => exact False.elim (value_no_step hr s)
    | callBound hr _ => exact False.elim (value_no_step hr s)
    | callGraph hr _ => exact False.elim (value_no_step hr s)
    | callSpread _ hr _ _ _ => exact False.elim (value_no_step hr s)
  | @callArg f r args i a h h1 a1 hv hrv hg hb s ih =>
    cases s2 with
    | callL s' => exact False.elim (value_no_step hv s')
    | callRecv _ s' => exact False.elim (value_no_step hrv s')
    | @callArg _ _ _ j b _ _ b1 _ _ hg' hb' s' =>
      have hij : i = j := by
        by_cases he : i = j
        · exact he
        · have hlt : i < j ∨ j < i := by omega
          rcases hlt with hij | hji
          · exact False.elim (value_no_step (hb' i hij a hg) s)
          · exact False.elim (value_no_step (hb j hji b hg') s')
      subst j
      have hab : a = b := Option.some.inj (hg.symm.trans hg')
      subst b
      obtain ⟨rfl, rfl⟩ := ih s'
      exact ⟨rfl, rfl⟩
    | callBound _ hvs => exact False.elim (value_no_step (hvs _ (List.mem_of_getElem? hg)) s)
    | callGraph _ hvs => exact False.elim (value_no_step (hvs _ (List.mem_of_getElem? hg)) s)
    | callSpread _ _ he hpre _ => exact False.elim (spread_blocks_arg he hpre hg hb s)
  | spreadC s ih =>
    cases s2 with
    | spreadC s' => exact (ih s').imp id (congrArg Tm.spread)
  | callSpread hf hr he hpre hre =>
    cases s2 with
    | callL s' => exact False.elim (value_no_step hf s')
    | callRecv _ s' => exact False.elim (value_no_step hr s')
    | callArg _ _ hg hb s' => exact False.elim (spread_blocks_arg he hpre hg hb s')
    | callBound _ hvs => exact False.elim (spread_not_values he hvs)
    | callGraph _ hvs => exact False.elim (spread_not_values he hvs)
    | callSpread _ _ he' hpre' hre' =>
      obtain ⟨rfl, hx, rfl⟩ := split_unique (he.symm.trans he') hpre hpre' rfl rfl
      cases hx
      cases Option.some.inj (hre.symm.trans hre')
      exact ⟨rfl, rfl⟩
  | letC hs ih =>
    cases s2 with
    | letC hs' => exact (ih hs').imp id (congrArg (Tm.letE · _))
    | letV hv => exact absurd hs (value_no_step hv)
  | letV hv =>
    cases s2 with
    | letC hs => exact absurd hs (value_no_step hv)
    | letV => exact ⟨rfl, rfl⟩
  | callBound hr hv =>
    cases s2 with
    | callL hs => exact absurd hs obj_no_step
    | callRecv _ hs => exact absurd hs (value_no_step hr)
    | callArg _ _ hg _ hs => exact absurd hs (value_no_step (hv _ (List.mem_of_getElem? hg)))
    | callBound => exact ⟨rfl, rfl⟩
    | callSpread _ _ he _ _ => exact False.elim (spread_not_values he hv)
  | callGraph hr hv =>
    cases s2 with
    | callL hs => exact absurd hs obj_no_step
    | callRecv _ hs => exact absurd hs (value_no_step hr)
    | callArg _ _ hg _ hs => exact absurd hs (value_no_step (hv _ (List.mem_of_getElem? hg)))
    | callGraph => exact ⟨rfl, rfl⟩
    | callSpread _ _ he _ _ => exact False.elim (spread_not_values he hv)
  | gotoEnter he hk =>
    cases s2 with
    | gotoEnter he' hk' =>
      cases Option.some.inj (he.symm.trans he')
      cases Option.some.inj (hk.symm.trans hk')
      exact ⟨rfl, rfl⟩
  | frameC s ih =>
    cases s2 with
    | frameC s' => obtain ⟨rfl, rfl⟩ := ih s'; exact ⟨rfl, rfl⟩
    | frameRet hv => exact False.elim (value_no_step hv s)
    | frameBind hv => exact False.elim (value_no_step hv s)
    | frameEffect hv => exact False.elim (value_no_step hv s)
    | frameYes => exact False.elim (tru_no_step s)
    | frameNo => exact False.elim (fls_no_step s)
    | frameYesBind => exact False.elim (tru_no_step s)
    | frameNoBind => exact False.elim (fls_no_step s)
    | frameTag hv => exact False.elim (value_no_step hv s)
    | frameHandle hr => exact False.elim (raises_no_step hr s)
    | frameRaise hr => exact False.elim (raises_no_step hr s)
  | frameRet hv =>
    cases s2 with
    | frameC s' => exact False.elim (value_no_step hv s')
    | frameRet => exact ⟨rfl, rfl⟩
    | frameHandle hr => rw [raises_not_val hr] at hv; contradiction
    | frameRaise hr => rw [raises_not_val hr] at hv; contradiction
  | frameBind hv =>
    cases s2 with
    | frameC s' => exact False.elim (value_no_step hv s')
    | frameBind => exact ⟨rfl, rfl⟩
    | frameHandle hr => rw [raises_not_val hr] at hv; contradiction
    | frameRaise hr => rw [raises_not_val hr] at hv; contradiction
  | frameEffect hv =>
    cases s2 with
    | frameC s' => exact False.elim (value_no_step hv s')
    | frameEffect => exact ⟨rfl, rfl⟩
    | frameHandle hr => rw [raises_not_val hr] at hv; contradiction
    | frameRaise hr => rw [raises_not_val hr] at hv; contradiction
  | frameYes =>
    cases s2 with
    | frameC s' => exact False.elim (tru_no_step s')
    | frameYes => exact ⟨rfl, rfl⟩
    | frameHandle hr => cases hr
    | frameRaise hr => cases hr
  | frameNo =>
    cases s2 with
    | frameC s' => exact False.elim (fls_no_step s')
    | frameNo => exact ⟨rfl, rfl⟩
    | frameHandle hr => cases hr
    | frameRaise hr => cases hr
  | frameYesBind =>
    cases s2 with
    | frameC s' => exact False.elim (tru_no_step s')
    | frameYesBind => exact ⟨rfl, rfl⟩
    | frameHandle hr => cases hr
    | frameRaise hr => cases hr
  | frameNoBind =>
    cases s2 with
    | frameC s' => exact False.elim (fls_no_step s')
    | frameNoBind => exact ⟨rfl, rfl⟩
    | frameHandle hr => cases hr
    | frameRaise hr => cases hr
  | frameTag hv =>
    cases s2 with
    | frameC s' => exact False.elim (value_no_step hv s')
    | frameTag => exact ⟨rfl, rfl⟩
    | frameHandle hr => rw [raises_not_val hr] at hv; contradiction
    | frameRaise hr => rw [raises_not_val hr] at hv; contradiction
  | frameHandle hr =>
    cases s2 with
    | frameC s' => exact False.elim (raises_no_step hr s')
    | frameRet hv => rw [raises_not_val hr] at hv; contradiction
    | frameBind hv => rw [raises_not_val hr] at hv; contradiction
    | frameEffect hv => rw [raises_not_val hr] at hv; contradiction
    | frameYes => cases hr
    | frameNo => cases hr
    | frameYesBind => cases hr
    | frameNoBind => cases hr
    | frameTag hv => rw [raises_not_val hr] at hv; contradiction
    | frameHandle hr' => cases Raises_det hr hr'; exact ⟨rfl, rfl⟩
  | frameRaise hr =>
    cases s2 with
    | frameC s' => exact False.elim (raises_no_step hr s')
    | frameRet hv => rw [raises_not_val hr] at hv; contradiction
    | frameBind hv => rw [raises_not_val hr] at hv; contradiction
    | frameEffect hv => rw [raises_not_val hr] at hv; contradiction
    | frameYes => cases hr
    | frameNo => cases hr
    | frameYesBind => cases hr
    | frameNoBind => cases hr
    | frameTag hv => rw [raises_not_val hr] at hv; contradiction
    | frameRaise hr' => cases Raises_det hr hr'; exact ⟨rfl, rfl⟩
  | @makeArg c ns inits i h h1 a a1 hg hb s ih =>
    cases s2 with
    | @makeArg _ _ _ j _ _ b b1 hg' hb' s' =>
      have hij : i = j := by
        by_cases he : i = j
        · exact he
        · have hlt : i < j ∨ j < i := by omega
          rcases hlt with hij | hji
          · exact False.elim (value_no_step (hb' i hij a hg) s)
          · exact False.elim (value_no_step (hb j hji b hg') s')
      subst j
      have hab : a = b := Option.some.inj (hg.symm.trans hg')
      subst b
      obtain ⟨rfl, rfl⟩ := ih s'
      exact ⟨rfl, rfl⟩
    | makeFields hvs _ => exact False.elim (value_no_step (hvs _ (List.mem_of_getElem? hg)) s)
  | makeFields hv hlen =>
    cases s2 with
    | makeArg hg _ s' => exact False.elim (value_no_step (hv _ (List.mem_of_getElem? hg)) s')
    | makeFields _ _ => exact ⟨rfl, rfl⟩
  | readC s ih =>
    cases s2 with
    | readC s' => exact (ih s').imp id (congrArg (Tm.readAt _))
    | readField _ _ => exact absurd s obj_no_step
    | readProto _ _ _ => exact absurd s obj_no_step
    | readMissing _ _ => exact absurd s obj_no_step
  | readField hl he =>
    cases s2 with
    | readC s' => exact absurd s' obj_no_step
    | readField hl' he' =>
      cases Option.some.inj (hl.symm.trans hl')
      exact ⟨rfl, Option.some.inj (he.symm.trans he')⟩
    | readProto hm _ _ => simp [hl] at hm
    | readMissing hm _ => simp [hl] at hm
  | readProto hm hp he =>
    cases s2 with
    | readC s' => exact absurd s' obj_no_step
    | readField hl _ => simp [hm] at hl
    | readProto _ hp' he' =>
      cases Option.some.inj (hp.symm.trans hp')
      cases Option.some.inj (he.symm.trans he')
      exact ⟨rfl, rfl⟩
    | readMissing _ hn => simp [hp] at hn
  | readMissing hm hn =>
    cases s2 with
    | readC s' => exact absurd s' obj_no_step
    | readField hl _ => simp [hm] at hl
    | readProto _ hp _ => simp [hn] at hp
    | readMissing _ _ => exact ⟨rfl, rfl⟩
  | indexC1 s ih =>
    cases s2 with
    | indexC1 s' => exact (ih s').imp id (congrArg (Tm.indexAt · _))
    | indexC2 hv _ => exact False.elim (value_no_step hv s)
    | indexField _ _ _ => exact absurd s obj_no_step
    | indexProto _ _ _ _ => exact absurd s obj_no_step
    | indexMissing _ _ _ => exact absurd s obj_no_step
  | indexC2 hv s ih =>
    cases s2 with
    | indexC1 s' => exact False.elim (value_no_step hv s')
    | indexC2 _ s' => exact (ih s').imp id (congrArg (Tm.indexAt _ ·))
    | indexField hk _ _ => exact False.elim (value_no_step (propertyKey_val hk) s)
    | indexProto hk _ _ _ => exact False.elim (value_no_step (propertyKey_val hk) s)
    | indexMissing hk _ _ => exact False.elim (value_no_step (propertyKey_val hk) s)
  | indexField hk hl he =>
    cases s2 with
    | indexC1 s' => exact absurd s' obj_no_step
    | indexC2 _ s' => exact False.elim (value_no_step (propertyKey_val hk) s')
    | indexField hk' hl' he' =>
      cases Option.some.inj (hk.symm.trans hk')
      cases Option.some.inj (hl.symm.trans hl')
      exact ⟨rfl, Option.some.inj (he.symm.trans he')⟩
    | indexProto hk' hm _ _ =>
      cases Option.some.inj (hk.symm.trans hk')
      simp [hl] at hm
    | indexMissing hk' hm _ =>
      cases Option.some.inj (hk.symm.trans hk')
      simp [hl] at hm
  | indexProto hk hm hp he =>
    cases s2 with
    | indexC1 s' => exact absurd s' obj_no_step
    | indexC2 _ s' => exact False.elim (value_no_step (propertyKey_val hk) s')
    | indexField hk' hl _ =>
      cases Option.some.inj (hk.symm.trans hk')
      simp [hm] at hl
    | indexProto _ _ hp' he' =>
      cases Option.some.inj (hp.symm.trans hp')
      cases Option.some.inj (he.symm.trans he')
      exact ⟨rfl, rfl⟩
    | indexMissing _ _ hn => simp [hp] at hn
  | indexMissing hk hm hn =>
    cases s2 with
    | indexC1 s' => exact absurd s' obj_no_step
    | indexC2 _ s' => exact False.elim (value_no_step (propertyKey_val hk) s')
    | indexField hk' hl _ =>
      cases Option.some.inj (hk.symm.trans hk')
      simp [hm] at hl
    | indexProto _ _ hp _ => simp [hn] at hp
    | indexMissing _ _ _ => exact ⟨rfl, rfl⟩
  | writeC1 s ih =>
    cases s2 with
    | writeC1 s' => exact (ih s').imp id (congrArg (Tm.writeAt _ · _))
    | writeC2 hv s' => exact absurd s (by intro hs; exact value_no_step hv hs)
    | writeField _ _ _ => exact absurd s obj_no_step
  | writeC2 hv s ih =>
    cases s2 with
    | writeC1 s' => exact absurd s' (by intro hs; exact value_no_step hv hs)
    | writeC2 _ s' => exact (ih s').imp id (congrArg (Tm.writeAt _ _ ·))
    | writeField hv' _ _ => exact absurd s (by intro hs; exact value_no_step hv' hs)
  | writeField hv hl hlt =>
    cases s2 with
    | writeC1 s' => exact absurd s' obj_no_step
    | writeC2 _ s' => exact absurd s' (by intro hs; exact value_no_step hv hs)
    | writeField _ hl' _ =>
      cases Option.some.inj (hl.symm.trans hl')
      exact ⟨rfl, rfl⟩
  | testC s ih =>
    cases s2 with
    | testC s' => exact (ih s').imp id (congrArg (Tm.test _))
    | testV hv => exact absurd s (by intro hs; exact value_no_step hv hs)
  | testV hv =>
    cases s2 with
    | testC s' => exact absurd s' (by intro hs; exact value_no_step hv hs)
    | testV _ => exact ⟨rfl, rfl⟩
  | iteC s ih =>
    cases s2 with
    | iteC s' => exact (ih s').imp id (congrArg (Tm.ite · _ _))
    | iteT => exact absurd s tru_no_step
    | iteF => exact absurd s fls_no_step
  | iteT =>
    cases s2 with
    | iteC s' => exact absurd s' tru_no_step
    | iteT => exact ⟨rfl, rfl⟩
  | iteF =>
    cases s2 with
    | iteC s' => exact absurd s' fls_no_step
    | iteF => exact ⟨rfl, rfl⟩
  | arithC1 s ih =>
    cases s2 with
    | arithC1 s' => exact (ih s').imp id (congrArg (Tm.arith _ · _))
    | arithC2 hv _ => exact absurd s (by intro hs; exact value_no_step hv hs)
    | arithV hb => exact absurd s (by intro hs; exact value_no_step (binop_values hb).1 hs)
    | arithThrow ht => exact absurd s (by intro hs; exact value_no_step (binopThrows_values ht).1 hs)
  | arithC2 hv s ih =>
    cases s2 with
    | arithC1 s' => exact absurd s' (by intro hs; exact value_no_step hv hs)
    | arithC2 _ s' => exact (ih s').imp id (congrArg (Tm.arith _ _ ·))
    | arithV hb => exact absurd s (by intro hs; exact value_no_step (binop_values hb).2.1 hs)
    | arithThrow ht => exact absurd s (by intro hs; exact value_no_step (binopThrows_values ht).2 hs)
  | arithV hb =>
    cases s2 with
    | arithC1 s' => exact absurd s' (by intro hs; exact value_no_step (binop_values hb).1 hs)
    | arithC2 _ s' => exact absurd s' (by intro hs; exact value_no_step (binop_values hb).2.1 hs)
    | arithV hb' => exact ⟨rfl, Option.some.inj (hb.symm.trans hb')⟩
    | arithThrow ht => simp [binop_not_throws hb] at ht
  | arithThrow ht =>
    cases s2 with
    | arithC1 s' => exact absurd s' (by intro hs; exact value_no_step (binopThrows_values ht).1 hs)
    | arithC2 _ s' => exact absurd s' (by intro hs; exact value_no_step (binopThrows_values ht).2 hs)
    | arithV hb => simp [binop_not_throws hb] at ht
    | arithThrow _ => exact ⟨rfl, rfl⟩
  | throwC s ih =>
    cases s2 with
    | throwC s' => exact (ih s').imp id (congrArg Tm.throw)
  | @arrArg inits i h h1 a a1 hg hb s ih =>
    cases s2 with
    | @arrArg _ j _ _ b b1 hg' hb' s' =>
      have hij : i = j := by
        by_cases he : i = j
        · exact he
        · have hlt : i < j ∨ j < i := by omega
          rcases hlt with hij | hji
          · exact False.elim (value_no_step (hb' i hij a hg) s)
          · exact False.elim (value_no_step (hb j hji b hg') s')
      subst j
      have hab : a = b := Option.some.inj (hg.symm.trans hg')
      subst b
      obtain ⟨rfl, rfl⟩ := ih s'
      exact ⟨rfl, rfl⟩
    | arrAlloc hvs => exact False.elim (value_no_step (hvs _ (List.mem_of_getElem? hg)) s)
    | arrSpread he hpre _ => exact False.elim (spread_blocks_arg he hpre hg hb s)
  | arrSpread he hpre hr =>
    cases s2 with
    | arrArg hg hb s' => exact False.elim (spread_blocks_arg he hpre hg hb s')
    | arrAlloc hvs => exact False.elim (spread_not_values he hvs)
    | arrSpread he' hpre' hr' =>
      obtain ⟨rfl, hx, rfl⟩ := split_unique (he.symm.trans he') hpre hpre' rfl rfl
      cases hx
      cases Option.some.inj (hr.symm.trans hr')
      exact ⟨rfl, rfl⟩
  | arrAlloc hv =>
    cases s2 with
    | arrArg hg _ s' => exact False.elim (value_no_step (hv _ (List.mem_of_getElem? hg)) s')
    | arrAlloc _ => exact ⟨rfl, rfl⟩
    | arrSpread he _ _ => exact False.elim (spread_not_values he hv)
  | elemC1 s ih =>
    cases s2 with
    | elemC1 s' => exact (ih s').imp id (congrArg (Tm.elemAt · _))
    | elemC2 hv _ => exact absurd s (by intro hs; exact value_no_step hv hs)
    | elemRead _ _ => exact absurd s (by intro hs; exact value_no_step rfl hs)
    | elemAbsent _ => exact absurd s (by intro hs; exact value_no_step rfl hs)
    | elemStr => exact absurd s (by intro hs; exact value_no_step rfl hs)
  | elemC2 hv s ih =>
    cases s2 with
    | elemC1 s' => exact absurd s' (by intro hs; exact value_no_step hv hs)
    | elemC2 _ s' => exact (ih s').imp id (congrArg (Tm.elemAt _ ·))
    | elemRead _ _ => exact absurd s (by intro hs; exact value_no_step rfl hs)
    | elemAbsent _ => exact absurd s (by intro hs; exact value_no_step rfl hs)
    | elemStr => exact absurd s (by intro hs; exact value_no_step rfl hs)
  | elemRead hl hv =>
    cases s2 with
    | elemC1 s' => exact absurd s' (by intro hs; exact value_no_step rfl hs)
    | elemC2 _ s' => exact absurd s' (by intro hs; exact value_no_step rfl hs)
    | elemRead hl' hv' =>
      cases Option.some.inj (hl.symm.trans hl')
      cases Option.some.inj (hv.symm.trans hv')
      exact ⟨rfl, rfl⟩
    | elemAbsent hn => exact absurd (hl.symm.trans hn) (by simp)
  | elemAbsent hn =>
    cases s2 with
    | elemC1 s' => exact absurd s' (by intro hs; exact value_no_step rfl hs)
    | elemC2 _ s' => exact absurd s' (by intro hs; exact value_no_step rfl hs)
    | elemRead hl' _ => exact absurd (hn.symm.trans hl') (by simp)
    | elemAbsent _ => exact ⟨rfl, rfl⟩
  | setC1 s ih =>
    cases s2 with
    | setC1 s' => exact (ih s').imp id (congrArg (Tm.setElem · _ _))
    | setC2 hv _ => exact absurd s (by intro hs; exact value_no_step hv hs)
    | setC3 hv _ _ => exact absurd s (by intro hs; exact value_no_step hv hs)
    | setPresent _ _ _ => exact absurd s (by intro hs; exact value_no_step rfl hs)
    | setGrow _ _ _ => exact absurd s (by intro hs; exact value_no_step rfl hs)
  | setC2 hv s ih =>
    cases s2 with
    | setC1 s' => exact absurd s' (by intro hs; exact value_no_step hv hs)
    | setC2 _ s' => exact (ih s').imp id (congrArg (Tm.setElem _ · _))
    | setC3 _ hi _ => exact absurd s (by intro hs; exact value_no_step hi hs)
    | setPresent _ _ _ => exact absurd s (by intro hs; exact value_no_step rfl hs)
    | setGrow _ _ _ => exact absurd s (by intro hs; exact value_no_step rfl hs)
  | setC3 hv hi s ih =>
    cases s2 with
    | setC1 s' => exact absurd s' (by intro hs; exact value_no_step hv hs)
    | setC2 _ s' => exact absurd s' (by intro hs; exact value_no_step hi hs)
    | setC3 _ _ s' => exact (ih s').imp id (congrArg (Tm.setElem _ _ ·))
    | setPresent hw _ _ => exact absurd s (by intro hs; exact value_no_step hw hs)
    | setGrow hw _ _ => exact absurd s (by intro hs; exact value_no_step hw hs)
  | setPresent hw hl hlt =>
    cases s2 with
    | setC1 s' => exact absurd s' (by intro hs; exact value_no_step rfl hs)
    | setC2 _ s' => exact absurd s' (by intro hs; exact value_no_step rfl hs)
    | setC3 _ _ s' => exact absurd s' (by intro hs; exact value_no_step hw hs)
    | setPresent _ hl' _ =>
      cases Option.some.inj (hl.symm.trans hl')
      exact ⟨rfl, rfl⟩
    | setGrow _ _ hn => exact absurd (hl.symm.trans hn) (by simp)
  | setGrow hw hk hn =>
    cases s2 with
    | setC1 s' => exact absurd s' (by intro hs; exact value_no_step rfl hs)
    | setC2 _ s' => exact absurd s' (by intro hs; exact value_no_step rfl hs)
    | setC3 _ _ s' => exact absurd s' (by intro hs; exact value_no_step hw hs)
    | setPresent _ hl' _ => exact absurd (hn.symm.trans hl') (by simp)
    | setGrow _ hk' _ =>
      cases Option.some.inj (hk.symm.trans hk')
      exact ⟨rfl, rfl⟩
  | lenC s ih =>
    cases s2 with
    | lenC s' => exact (ih s').imp id (congrArg Tm.lenOf)
    | lenV => exact absurd s (by intro hs; exact value_no_step rfl hs)
    | lenStr => exact absurd s (by intro hs; exact value_no_step rfl hs)
  | lenV =>
    cases s2 with
    | lenC s' => exact absurd s' (by intro hs; exact value_no_step rfl hs)
    | lenV => exact ⟨rfl, rfl⟩
  | lenStr =>
    cases s2 with
    | lenC s' => exact absurd s' (by intro hs; exact value_no_step rfl hs)
    | lenStr => exact ⟨rfl, rfl⟩
  | elemStr =>
    cases s2 with
    | elemC1 s' => exact absurd s' (by intro hs; exact value_no_step rfl hs)
    | elemC2 _ s' => exact absurd s' (by intro hs; exact value_no_step rfl hs)
    | elemStr => exact ⟨rfl, rfl⟩
  | mergeC1 s ih =>
    cases s2 with
    | mergeC1 s' => exact (ih s').imp id (congrArg (Tm.merge _ · _))
    | mergeC2 hv _ => exact absurd s (by intro hs; exact value_no_step hv hs)
    | mergeV hv _ _ => exact absurd s (by intro hs; exact value_no_step hv hs)
  | mergeC2 hv s ih =>
    cases s2 with
    | mergeC1 s' => exact absurd s' (by intro hs; exact value_no_step hv hs)
    | mergeC2 _ s' => exact (ih s').imp id (congrArg (Tm.merge _ _ ·))
    | mergeV _ hw _ => exact absurd s (by intro hs; exact value_no_step hw hs)
  | mergeV hv hw hp =>
    cases s2 with
    | mergeC1 s' => exact absurd s' (by intro hs; exact value_no_step hv hs)
    | mergeC2 _ s' => exact absurd s' (by intro hs; exact value_no_step hw hs)
    | mergeV _ _ hp' =>
      cases Option.some.inj (hp.symm.trans hp')
      exact ⟨rfl, rfl⟩
  | makeKeyC1 s ih =>
    cases s2 with
    | makeKeyC1 s' => exact (ih s').imp id (congrArg (Tm.makeKey · _))
    | makeKeyC2 hv _ => exact absurd s (by intro hs; exact value_no_step hv hs)
    | makeKeyV _ hk => exact absurd s (by intro hs; exact value_no_step (propertyKey_val hk) hs)
  | makeKeyC2 hv s ih =>
    cases s2 with
    | makeKeyC1 s' => exact absurd s' (by intro hs; exact value_no_step hv hs)
    | makeKeyC2 _ s' => exact (ih s').imp id (congrArg (Tm.makeKey _ ·))
    | makeKeyV hw _ => exact absurd s (by intro hs; exact value_no_step hw hs)
  | makeKeyV hv hk =>
    cases s2 with
    | makeKeyC1 s' => exact absurd s' (by intro hs; exact value_no_step (propertyKey_val hk) hs)
    | makeKeyC2 _ s' => exact absurd s' (by intro hs; exact value_no_step hv hs)
    | makeKeyV _ hk' =>
      cases Option.some.inj (hk.symm.trans hk')
      exact ⟨rfl, rfl⟩

theorem makeFn_step_inv {c : CallCode} {v : Val} (hv : isVal v = true) {h h' t}
    (hs : Step h (.makeFn c v) h' t) : h' = h ++ [v] ++ [.nul] ∧ t = .fnObj h.length c := by
  cases hs with
  | makeArg hg _ hs =>
    obtain ⟨rfl, rfl⟩ := singleton_get hg
    exact False.elim (value_no_step hv hs)
  | makeFields => exact ⟨rfl, rfl⟩

end Verification
