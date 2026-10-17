# Source model

This document explains how the admitted TypeScript values and operations are
represented in the verifier's calculus. A source contract describes the values
and permitted operations a program may rely on. An execution world assigns a
fixed type to every allocated location; current contents may vary within it.
The formal definitions belong to [SEMANTICS](SEMANTICS.md), the type language
to [POSITIVE-TYPES](POSITIVE-TYPES.md), and the checking rules to
[PROGRAM-TYPING](PROGRAM-TYPING.md). This overview connects those definitions
to source constructs and the host assumptions they require.

## The model in brief

The calculus describes execution, types and the conditions under which a
program may use a value. This section introduces the main concepts;
[SEMANTICS](SEMANTICS.md), [POSITIVE-TYPES](POSITIVE-TYPES.md) and
[PROGRAM-TYPING](PROGRAM-TYPING.md) own the formal definitions and rules.

### Values

Values include JavaScript primitives and allocated objects. Object properties
refer to heap locations. Arrays have element storage; callable objects also
carry call or constructor code. Every allocated object has an identity, including
empty objects and functions, so object equality compares identities.

Primitive operations model the supported JavaScript behavior, including IEEE-754
numbers, bigint arithmetic and string operations.
Literal type `0` includes both positive and negative zero; equality against
`0` keeps or excludes both. The [operational language](SEMANTICS.md#operational-language)
defines their numeric representation and comparison.

The supported equality
comparisons are specified under [guards](#guards) and in the
[operational language](SEMANTICS.md#operational-language). Operations requiring
unsupported coercions are refused at the source boundary.

### Source-value boundary

Let $`J`$ be the JavaScript values: primitives and allocated objects, including
arrays, functions and constructors. Internal array stores are calculus values
outside $`J`$. Source `unknown` denotes $`J`$. An unconstrained source type
parameter ranges over types contained in $`J`$; each instantiation checks that
bound. Argument-pack parameters range over argument lists separately.

Value-parameter occurrences in source signatures denote $`T\cap J`$.
Declared bounds remain instantiation obligations; dependent bounds retain
the obligations of every parameter they reference.

Inputs and results carry their source contracts. Exceptions also belong to
$`J`$: the [throw rule](PROGRAM-TYPING.md#throwing) checks this requirement,
and the operational exception rules preserve it. External call contracts use
the same safety semantics, so external code must return values meeting its
result contract and throw only JavaScript values. A catch variable has type
`unknown` and can be passed to an unconstrained generic function.

Membership in $`J`$ supplies no field, call or array-layout guarantee.
The calculus clause `source` denotes $`J`$ independently of the built-ins'
record invariants; calculus `top` also includes internal stores. The
[clause semantics](POSITIVE-TYPES.md#types-and-clauses) owns this distinction.

### Void

The source type `void` denotes the same JavaScript-value universe as `unknown`.
A `void` result supplies no guarantee about which member is returned. A `void`
parameter must support every member. Strict equality of two source values
produces a Boolean by the primitive and object equality rules. Membership
supplies no number, undefined, field or call guarantee.

### Heap and contracts

The **heap** maps locations to their current values. A **world** assigns each
allocated location a fixed type, its storage contract. A heap satisfies a world
when each stored value meets that contract. A write must preserve it. Allocation
extends the world with fresh locations; it does not change existing contracts.

A readonly view permits reading a location without permission to write it.
A writable reference must preserve the same contract through every alias.
For example, a writable Boolean cell cannot be used as a writable `true` cell,
because another alias could store `false`.

The semantic model handles recursive types using a **step index**, a natural
number bounding how much execution an approximation describes. The safety
result holds at every index. This mathematical index is separate from the
resource budget used by proof search.
[Worlds and recursive types](SEMANTICS.md#computations-and-recursive-types)
give the definitions and their relation to the cited step-indexed models.

### Current-content assertions

A cell's current contents can be more precise than its lifetime contract.
For example, `{ value: boolean = true }` describes a Boolean cell whose current
value is `true`. The observation permits a more precise read; later writes
must still satisfy the Boolean contract.

Each statement entry supplies a local interface: binding types and current
heap observations. Every incoming edge, including a loop back edge, must
establish that interface. The calculus can also retain relationships such as
two slots denoting the same value or two private cells being distinct.
The source-entry rules determine which of these facts cross a checkpoint.

An unrestricted call invalidates heap observations because the callee may write
through an alias. A certified heap-preserving call can retain facts on normal
return, under the [effect rules](#inferred-call-effects-elaboration-and-certification).
Immutable values remain available. A closure's initial heap assumptions follow
from storage contracts, rather than observations made when the closure was
created. See [source checkpoints](PROGRAM-TYPING.md#source-observation-checkpoints).

### Mutable bindings

A `let` and an assigned parameter have a storage contract fixed where they
are declared: the annotation, or the producer's proposal (TypeScript's
widened or evolved type), against which the initializer and every write are
checked. One that every closure mentioning it sees at its value when the
closure was created (no closure writes it, and no write follows such a
closure's creation) is a slot of its activation, rebound at each write: what
it holds is its type at each point, and no call, closure run or throw
changes it. Any other is a private cell, which a closure holds the identity
of ([slot or cell](SOURCE-ELABORATION.md#mutable-bindings-and-module-constants)).
A `const` copy holds a snapshot, and an unannotated constant of a
named union is held at the union's arms, as an annotated one is, an
annotated one initialized by an object literal at the arms the literal may
be of (TypeScript's narrowing on assignment); a constant's object literal
used whole where an optional field it leaves out is expected is claimed
with its exact keys
([rules](SOURCE-ELABORATION.md#mutable-bindings-and-module-constants)). A `let`
statement whose initialized bindings nothing in their scope writes, closures
included, is a `const`: each holds its initial value throughout, so a test
narrows it and a `let` pattern binds (`LET-CONST`). A written `let` held in a
cell has current contents that support primitive refinements and nullish
exclusions.
A guard can remove null or undefined from its read type until an effect
invalidates that observation.
A written `let` pattern binds hidden names, then each source name is a
cell of its own at its value.

A local may hide an outer binding of its name. The parser renames it, by
the declaration TypeScript binds each reference to, to a name no source
spells (`x@line:col`), so the lowering never meets two bindings of one name:
consistent renaming of bound variables, for `const`, `let`, parameters, patterns, closure
parameters, `for...of` and `catch` bindings in any body
([shadowing](SOURCE-ELABORATION.md#derived-source-forms)). A mention above the
declaration, a closure's included, or in its own initializer is refused, as
JavaScript's temporal dead zone throws there.

A module function is an immutable slot holding its code. A file without
imports or exports may run as a script, whose top-level functions are
properties of the global object other scripts can write; the slot rests on
the trusted assumption that other code preserves the file's top-level
bindings and their functions (the file runs as a module, or no other code
writes its globals or gives one of its functions an own `call`, `apply` or
`bind`), for a plain call
and for `.call`, `.apply` and `.bind` alike
([trust surface](DESIGN.md#trust-surface)).

### Objects and prototypes

An object's set of keys is fixed at allocation in the calculus. Writing a field
changes its location's contents. Adding a key to a fresh local object can be
represented by copying the object with the additional field and updating every
local binding that holds it. This translation is valid only when no other
reference can observe the old object, the strong update of alias types
([Smith, Walker and Morrisett 2000](REFERENCES.md#smith-walker-and-morrisett-2000)).
Source extraction checks that ownership condition;
[key-adding writes](PROGRAM-TYPING.md#key-adding-writes) states the restriction.

A record type is **open**: it describes named properties without excluding
others. An **own-key bound** adds information about which properties an object
itself owns. An upper bound lists the only permitted keys; an exclusion bound
lists keys that must be absent. Fresh object literals have known own keys.
These bounds matter for optional fields, dictionaries and native methods.

The model represents a prototype link under the reserved key `[[proto]]`.
A missing own property can be read through that link. Classes use prototype
objects for methods and distinct keys for private fields. `readonly` grants a
read capability without granting a write through that view. The exact
[record contracts](POSITIVE-TYPES.md#records) and
[class translation](SOURCE-CONTRACTS.md#classes) define these forms.

### Object literals

A literal allocates one object owning exactly the properties it writes, in
order. A spread of a literal is its fields; a spread of any other value is an
allocation from parts, copying the value's own enumerable data properties
when it is evaluated
([allocation from parts](PROGRAM-TYPING.md#allocation-from-parts)): a class
instance's methods are its prototype's and are not copied, nor is an
`Error`'s non-enumerable `message`. The model's copy takes string keys
only, where JavaScript's also takes an own enumerable symbol-keyed property:
a spread of a value whose type states a symbol-keyed field is refused, the
copy's type states symbol keys only as the source's type says JavaScript's
copy gives them (a symbol index), and the
[trust surface](DESIGN.md#trust-surface) states why no typed read observes the
difference. A
function's own enumerable properties are the fields its type states (a
callable object's) and whatever else was assigned to it, which the copy's
type leaves open; a function the program creates owns none, its one field,
which gives it an identity, being under a key no source spells. A numeric
key is the property its `ToString` spells, and a computed key naming a
`unique symbol` constant (`Symbol.iterator`, or one the program makes) is that
symbol's key; `__proto__`, any other computed key and accessors are refused.
A string's own enumerable properties are its code units at its indices, which
its copy takes; a class value's are its static fields, which the class value
holds as its fields and its copy takes; its type states the static fields it
names, and no bound. An object pattern's rest is the same copy less the
named keys. Where a part is a dictionary and every part says what it gives
under the index's keys, through an index or its exact keys, the result is a
writable dictionary at what the parts give there, the string and the symbol
keys each at their own type; a spread of an open record meets no index. `Object.assign` is the same copy, onto a fresh literal or,
as a statement, a local's own object, from sources whose types rule out an
own `__proto__`, which it would set through the prototype's setter.

### Arrays

The **built-ins** are the objects and prototypes of the JavaScript global
environment a program runs in. The array contracts below assume their
standard prototypes.

An array is one store of element locations under the reserved
store key and one object holding `Array.prototype` under `[[proto]]`, read
through the one array shape (`arrayClauseOf`,
[arrays](POSITIVE-TYPES.md#arrays)). Its own keys exclude the members declared by
`ArrayProto`, `constructor` and `then`, so `xs.map` reaches the prototype
and ordinary construction cannot be overridden; it may own other keys,
as a library may tag the arrays it manages with a symbol key. Stores may be sparse;
source `T[]` requires **readability**: every in-bounds read, including a hole's
`undefined`, meets `T`. Density is a separate, stronger guarantee. All three
spellings (`T[]`, `Array<T>`, `ReadonlyArray<T>`) use the same element-family
interpretation, including generic substitution. Element writes currently require
an in-bounds position or appending; they preserve each presence mode.
Mutable arrays are invariant;
`readonly T[]` reads only and is covariant. Arrays are `Iterable<T>` through
their prototype's `[Symbol.iterator]`, a tuple through the readonly array of
its positions. An array's `length` is read from its store, in a statement and
in a closed expression alike. An array pattern's rest over a tuple of
required positions is reads; any other is a slice, a call of the trusted
`%RestFrom:k%` ([patterns](SOURCE-ELABORATION.md#patterns)).
Every record and dictionary type, and `unknown`, is of values meeting the
**array invariant**: an object owning the store key is a built-in array,
a possibly sparse store of `unknown` values and `Array.prototype`, owning no
key it provides. Allocation keeps it, since an allocation owning the store key
is typed only as such an array and a merge copies no store; it is assumed of
every value a unit receives at such a type and of every value a function it
receives throws, and a thrown value, of `unknown`, is what a handler binds
([the array invariant](SEMANTICS.md#the-array-invariant)). So where
`Array.isArray` holds, a record arm and `unknown` are `readonly unknown[]`.

### Index signatures

An index signature describes properties in a **key class**: string keys,
canonical numeric property keys, or symbol keys. A dictionary read returns
`V | undefined` when the key may be absent. A readonly index promises values
of type `V` at present keys without granting writes.

#### Writable string index signatures

A writable index must permit every admitted write while preserving all aliases'
contracts. It is therefore invariant in its value type. A dictionary of `true`
cannot be passed as a writable dictionary of Boolean values: a caller could
store `false` through the wider view.

An own-key bound must also remain valid when external code adds an allowed key.
For example, a type that excludes `x` cannot justify a writable string index
whose callers may add `x`. Fresh literals intended as writable dictionaries are
allocated at the dictionary contract rather than using an exact-key bound to
justify that capability.

Within the source fragment, adding a key requires the ownership condition for
[key-adding writes](PROGRAM-TYPING.md#key-adding-writes). General dynamic
key-adding writes are restricted. External code is assumed to respect the
writable contract and the reserved-key restrictions.
[Dictionary typing](POSITIVE-TYPES.md#records) and
[source index operations](SOURCE-CONTRACTS.md#index-signatures) specify the
coverage checks and supported keys.

### Method members are host-relative

A method member's contract is relative to its host: read from `o` and invoked
with receiver `o` and admitted actuals, it behaves as typed, and it promises
nothing for another receiver ([`methodT`](POSITIVE-TYPES.md#records)): the
self-application of [Abadi and Cardelli 1996](REFERENCES.md#abadi-and-cardelli-1996). A
method call reads the member and binds it to its host in one term
(`bindMember`); nothing types a member read on its own. Consequences, each
forced by soundness:

- A method is not a function-typed property: the property covers the method,
  never the reverse (`const g = p.m; g()` would throw).
- Extracting a method (`const f = o.m`, `xs.forEach(o.m)`) gets nothing; the
  supported forms are `o.m.bind(o)` and class-field arrows.
- Method parameters are contravariant; TypeScript's method bivariance is
  refused.
- Interfaces with methods are covariant in results, so a class instance meets
  an interface it structurally meets, and an array meets `Iterable<T>`.
- Method members are read-only views: a write to one is refused.
- A class method taking fewer parameters than an interface's member is
  claimed at the longer signature as well, the extra actuals discarded at
  binding (`CodeOffers`); no subtyping widens an arrow's parameters.
- A method declaring `this: T` is a member whose host must meet `T`: it
  promises its signatures on a host that is a `T`, and a call proves its
  host one. The types a member's host must meet are contravariant, so a
  member stating one is no member stating none.

A generic method is a member with **quantified signatures**: a scheme the
member bound to its host meets, whatever receiver the bound function is
later given (`MethodMembers.boundOn`). It is the same host-relative promise,
read through `.bind`, so the scheme's own receivers admit every value, and a
call binds the member (`bindScheme`) and names its instance below the scheme.
Two quantified members relate as their schemes do, by the covering rule for
quantified signatures ([covered pairs](POSITIVE-TYPES.md#covered-pairs)): equal
binders, the source's bounds among the target's, the target's signatures
covered with its binders opaque, so decidable
([Pierce 1994](REFERENCES.md#pierce-1994)). Since the receiver is the host on
both sides, it is never compared, and a declaration whose generic methods take
its argument only covariantly is covariant: `Promise<A>` is below `Promise<B>`
where `A` is below `B`, by `then`'s and `catch`'s own signatures. A
generic method's binders are owned by its application
([generic methods](SOURCE-CONTRACTS.md#generic-methods)), so two instances of a
declaration, and members of two declarations, bind different parameters:
relating them needs the covering rule up to renaming the target's binders
([quantified-α](RECURSIVE-EQUATIONS.md#41-quantified-signatures)).
A class's generic method is such a member of its instance type, which its
prototype's closure, a scheme received by the instance, covers bound to the
instance ([classes](SOURCE-CONTRACTS.md#classes)).

### Exact contracts and native effects

A source declaration is lowered in full or refused. Unsupported generic
bounds, mixed value/argument-pack binders and an unguarded alias cycle are
refusals. No such failure denotes `unknown`, and no
method is dropped. This matters in result and writable positions: forgetting
a contract there would certify a value that does not satisfy its annotation.

Native contracts are reviewed separately from their TypeScript declarations.
Unrestricted `find` and `findIndex` callbacks receive `T | undefined`: a prior callback can
shrink even an initially dense array through another reference, while these
methods visit the original index range. `map` visits only present indices,
but shrinking its source can leave holes in its result. Separate overloads consume
a certified `preservesInputHeap` callback: `find`/`findIndex` can then pass `T`,
and `map` produces a dense result from its dense receiver. The fresh result
is assigned the readable `U[]` lifetime contract, so it remains writable at
the source type even when `U` admits holes. These are ordinary
qualified callback types, including when the callback is returned or bound.

**Ordinary array construction is part of the admitted semantics.** An array
owns neither `constructor` nor `then`, and the built-in `Array.prototype.constructor`,
`Array[Symbol.species]` and relevant prototype links retain their standard
behavior; `Array.prototype` and `Object.prototype` have no `then`. External code must preserve the same invariant for values it supplies
and across calls. This is an explicit host assumption, like the restrictions on
proxies and accessors; it is not a theorem about arbitrary JavaScript.

The own-key part is stated in the existing array contract and the built-ins' invariant:
`RequestJson.arrayExcludedKeys` adds `constructor` and `then` to the prototype's declared
keys. Arrays cannot acquire it through an invariant-preserving allocation,
structural alias or write. The fragment also refuses custom species definitions,
array subclass construction and the unreviewed prototype-changing APIs. It
continues to allow an ordinary record's own `constructor` field. Standard native
construction therefore needs no extra promise on each callback. `map` returns
a sparse array of its unrestricted callback's result type; `filter` and `slice` create ordinary
arrays. Density after a callback is still a separate obligation.

The runtime controls beside `ordinary-array-construction` deliberately violate
the external assumption: a custom species gives `map`/`filter` a string-valued
`length` and `slice` a non-array result. They explain why the assumption matters;
these are not accepted executions of the admitted language. Custom species can
be modeled later with explicit construction contracts. See
[`ArraySpeciesCreate`](REFERENCES.md#ecma-262).

**Standard array conversion is an enforced restriction.** Arrays may not own
`toString`, `join` or `Symbol.toPrimitive`, and their standard prototype chain
must retain those members' behavior. The same rule applies to external code.
The existing own-key invariant enforces it; `ArrayProto` also states that
`Symbol.toPrimitive` is absent or undefined. A recursive native contract admits
primitives and arrays of convertible values. Default sorting and joining can
therefore convert numeric tuples and nested arrays without calling client hooks.
The actual route is `ToPrimitive` → standard `toString` → standard `join` →
recursive element conversion, not an inference from numeric contents alone.
Custom conversion on arrays is a deliberately excluded corner case; general
objects with conversion methods still need an explicit comparator. This follows
[the utility principle](DESIGN.md#principles), and does not claim arbitrary JavaScript
arrays satisfy the restriction. The equations and native signatures are in
[prototype contracts](SOURCE-CONTRACTS.md#prototype-contracts).

`sort` with an explicit comparator accepts arbitrary element types. Its call
contracts are separate signatures of one quantified callable; passing undefined
selects the conversion-requiring contract. Existing subtyping and application
rules suffice. Native conformance remains audited, not proved against ECMA-262.

The native regression sources are also executed under Node. Source-contract
erasure is tested against both verifier entry points using a forged producer
proposal. These tests exercise premises and translation that the calculus
safety theorem does not prove. Intrinsics are collected on demand from the operations the source uses.

### Inferred call effects: elaboration and certification

A call signature may state the effect `preservesInputHeap`: on normal return,
the call leaves every previously allocated location's contents unchanged.
It may allocate fresh storage. A type guard's and an assertion function's
signatures state the effects `guards` and `asserts`, a promise about an actual
([user-defined guards](SOURCE-CONTRACTS.md#user-defined-guards)). An
**effect-qualified signature** is a signature carrying such a guarantee. `CallEffects.lean` defines its semantics; the
[effect contract](SEMANTICS.md#effect-qualified-call-contracts) and
[certification rules](SOURCE-ELABORATION.md#certifying-inferred-call-effects)
state what a certificate must establish.

This extends the language of claims beyond TypeScript annotations. Three
operations must remain distinct:

1. **Annotation translation** preserves the source contract. An ordinary
   TypeScript arrow imposes no heap-preservation guarantee. It must never become
   an effect-qualified arrow merely because a consumer needs one.
2. **Inference** proposes a stronger type for a definition, including an effect
   on each call signature. This is untrusted producer work. It can use bodies
   and inferred contracts of callees; it need not change the source annotation.
3. **Elaboration and verification** attach the proposal to the lowered
   definition and discharge its additional obligation. Lowering emits proof
   obligations; it does not establish an effect by translating syntax. Lean must
   check both ordinary body safety and the claimed effect, with the original
   annotation obligations retained. Only certified types may justify uses.

At a call, the rule consumes the qualified type of the value. It does not
inspect its source body or recheck it for the observed call. The guarantee
must survive passing, returning, capturing and generic instantiation through
ordinary type operations. An explicit annotation may forget the guarantee;
that loses precision, not soundness. Overloads carry effects per signature.
An imported implementation needs checked evidence or an explicitly documented
external assumption: its TypeScript declaration supplies neither proof nor an
implicit effect. Built-in contracts remain separately audited assumptions.

The first guarantee preserves existing heap contents on normal return and
allows fresh allocation. A call that throws supplies no heap postcondition.
Consequently, a body checker cannot carry this guarantee through a caught
exception: it must check the handler with the possibly changed heap, or have
a separately justified guarantee for exceptional exits. The current pure-body
checker does not admit such calls. Graph composition checks normal-return
postconditions node by node and refuses handlers; the independent pure-graph
rule can still certify pure handlers. Qualified-call composition retains
this distinction. No stronger external assumption is implicit here.

The guarantee is sufficient but not necessary for safe dense
`map`: mutation of unrelated state can also be safe. [Footprints](FOOTPRINTS.md)
designs effects that express that within the same inference/certification
boundary.
The body-effect checker recognizes a subset of programs satisfying the
semantic contract. An unrecognized body therefore represents an inference or
checking limit, not a restriction on the meaning of heap preservation.

The source acceptance theorem includes effect checking. Pipeline controls
exercise qualified callbacks passed or returned as values, ordinary-call
fallbacks, and forged effect claims on bodies that mutate captured storage.

### Calls

Argument lists are native: the callee is evaluated first, then
the actuals left to right; a missing trailing actual binds `undefined`, so
`x?: T` is `T | undefined` and a default's position admits `undefined`;
extra actuals are discarded after evaluation. A function type promises which
actual lists a caller may write and what the call then guarantees
(`callsT`, `restsT`), independently of the code's arity
([one meaning for callable contracts](SEMANTICS.md#one-meaning-for-callable-contracts)).
A rest parameter makes the code variadic: invocation collects the remaining
actuals into a fresh array, viewed at the rest's type: an array or a tuple of
required positions, readonly or not, or a declared alias of one, a generic
alias read through its equation at the reference's arguments. A rest typed by a binder is an argument pack,
whose contracts are over lists at the actuals' own level
([argument packs](POSITIVE-TYPES.md#argument-packs)). A closure claimed at
several signatures is checked once per signature. A spread among the actuals
is replaced by its store's elements once every earlier actual is a value;
spreads may sit at any position of fixed parameters or feed a generic
signature's inference. Into a rest, a spread followed by an actual that runs
code is copied where it is written, so the later actual cannot change what it
passes; into fixed parameters such an actual is refused
([model limits](SOURCE-FRAGMENT.md#model-limits)). A union callee is called at every
arm, its result the union of theirs; a method call on a union whose arms'
members differ reads and calls in one step dispatched on the receiver, where
every actual is a name or a literal. A union callee whose alternatives carry callable fields
is refused ([call rules](SOURCE-CONTRACTS.md#reading-the-source)).

### Primitive members

A member read on a primitive is read through the
built-in wrapper prototype (`String.prototype`, `Number.prototype`,
`BigInt.prototype`, `Boolean.prototype`) with the primitive as receiver; a
string's `length` and indices are its own
([prototype contracts](SOURCE-CONTRACTS.md#prototype-contracts)). Each member
those prototypes list states `preservesInputHeap`, so a call of one is a
fixed qualified call, and the read itself an inspection
([certification](SOURCE-ELABORATION.md#certifying-inferred-call-effects)).

### Receivers

Every signature states its receiver and every call passes one:
`undefined` for a plain call, the object for a method call, the first
argument for `.call` and `.apply`. The receiver is bound unchanged, as
strict code binds it. A sloppy function that reads no `this` is the strict
one, its receiver being unobservable. A sloppy function that reads `this`
binds an object unchanged and converts any other receiver (the global
object, a wrapper object), which the model has no step for
([graph code](SEMANTICS.md#graph-code)): its code is `sloppy`, offered only at
signatures whose receiver types hold objects only
([kinds](PROGRAM-TYPING.md#judgments-and-constructor-views)), and a sloppy
declaration reading `this` has such a receiver annotation. `.bind` allocates a forwarding descriptor whose
receiver a later `.bind` or `.call` cannot replace (`callsT_bound`).

### Generic types

A declaration is one equation, and a generic application a finite term over
the equations, unfolded one step when a check reads it, so a recursive family
of applications, however it grows, is finitely many heads
([one equation per declaration](SOURCE-CONTRACTS.md#one-equation-per-declaration),
[RECURSIVE-EQUATIONS](RECURSIVE-EQUATIONS.md)). A generic method is a
[member with quantified signatures](#method-members-are-host-relative), a
scheme whose binders its application owns; a binder intersected with ground
types is a meet label ([RECURSIVE-EQUATIONS §2.2](RECURSIVE-EQUATIONS.md#22-meaning)).

### Graphs

A body is a finite graph of nodes, each evaluating one term then
returning, binding, discarding or branching; destinations carry explicit slot
maps, checked on every edge; a node may name a handler for a throw out of its
term ([control-flow graphs](PROGRAM-TYPING.md#checked-control-flow-graphs)).
Global safety covers cycles without unrolling.

### Throws

`throw a` evaluates `a` and throws its value; a throwing term does not step,
and every evaluation context carries the throw out
([semantics](SEMANTICS.md#computations-and-recursive-types),
[rule](PROGRAM-TYPING.md#throwing)). The primitives JavaScript throws on step
to throwing an error object (`binopThrows`): a bigint division or remainder
by zero or a negative exponent, and, where the gate admits them at all, a
number mixed with a bigint or a symbol converted. A handler binds the thrown
value at `unknown`, under only the facts that hold without the heap
(`handlerFacts`), since the body may have run any effect before it threw. A
`finally` block is compiled on every way out, returns and jumps included: a
`break` or `continue` runs each `finally` it passes, innermost first, then
lands ([try](SOURCE-CONTRACTS.md#statement-forms)).

### Guards

Expression tag dispatches expand named union rows into their constituent
clauses before splitting branches. The dispatch expression must prove the
expanded type, so this preserves the original union’s meaning.

A guard is a test JavaScript defines exactly. It is followed where the model
answers it as JavaScript does, as one more tag test (`Tag`, `tagHolds`), so
it narrows by the one mechanism of tag observations (`tagSlice`), and refused
with the reason where the model would answer otherwise
([rules](SOURCE-CONTRACTS.md#guards)). The tests are `typeof` (eight shapes,
`"object"` being `typeofObject`: `null` or an object without call code),
`key in o` (`hasKey`, along the prototype chain the model holds), truthiness
(`ToBoolean`), `== null`, strict equality against a singleton of any
primitive kind, `Array.isArray` and `instanceof Array` (`isArray`: owns the
store key; a record or dictionary arm is then the built-in `readonly
unknown[]`, by the [array invariant](#arrays)), and `x instanceof C` for a
class the file declares (`hasKey` of the key only `C`'s prototype owns; it
narrows a union's arms, never `unknown`, since JavaScript gives any object
`C`'s prototype without `C`'s constructor). A test of a field of an
immutable binding's object against a singleton, or of its truthiness where
an arm leaves the field optional (an `IteratorResult`'s `done`), narrows the
object's arms; a
key found present promotes an optional field to a field, since an object
keeps its keys. A test on a mutable cell refines the read, never the cell.
`&&`, `||` and `??` return an operand, as JavaScript's do, by the same
tests; a chain of one of them reads right-nested, so each operand sees what
every earlier one answered. `x instanceof C` of a class whose chain of bases
holds a static `[Symbol.hasInstance]` is a call of that method, its result
converted by `ToBoolean`, and narrows nothing. A user-defined guard's promise
is a claim of a derived unit checked at the guard's body, and a call narrows
its argument by testing it again
([user-defined guards](SOURCE-CONTRACTS.md#user-defined-guards)).

### Async and iteration

`await`, an async function's return and completion, `for...of` and a
spread over a host iterable, an array pattern's slice rest and `for...in`
are calls of trusted **intrinsics**, values no source name spells, whose
signatures the declaration reader states
([async](SOURCE-CONTRACTS.md#async-functions-and-await),
[loops](SOURCE-CONTRACTS.md#loops-and-spreads-over-iterables)). A loop over a
host iterable steps one **iteration intrinsic** family, `%Iterate:K%`, picked
by TypeScript's type of the iterable: an array's (`%Iterate%`), a string's, a
`Set`'s, a `Map`'s and a host collection iterator's; a spread collects the
same iterator into a fresh array (`%Spread:K%`). A `for...in` whose body
reads the entry at its key, `o[k]`, where nothing that could change the entry
ran since the step, steps the dictionary's entries (`%Iterate:ForIn%`), a
fresh `[key, value]` array per key, read at its step, and the read is the
step's value: a dictionary holds no prototype, so the keys the loop visits
are its own ([statement forms](SOURCE-CONTRACTS.md#statement-forms)). None of these iterators has
a `return`, so leaving such a loop early calls nothing. An iterable the
program defines (an object with its own `[Symbol.iterator]`, an
`Iterable<T>`) runs the **iterator protocol** of
[ECMA-262](REFERENCES.md#ecma-262) as ordinary calls, each typed
by TypeScript's `Iterable`, `Iterator` and `IteratorResult` declarations: the
parser writes GetIterator, `next` read once and called per step, the result's
`done` tested (a truthiness test of a field, which refines the result to its
not-done arm) and its `value` bound. IteratorClose is a **closing region**
around the loop's body, a `finally` that runs on some ways out only: before
a `break` of the loop leaves it, before a `return` returns, and, its own
throws discarded, before a throw out of the body resumes; not at the body's
end, on a `continue`, or when the iterator is done. It calls the iterator's
`return` where it is not `undefined`, whose result must be an object. A
spread of such an iterable is collected before its statement, where nothing
the statement evaluates before it can change, and an array pattern over one
steps once per element and closes the iterator where no rest took it to its
end. No calculus rule changes: a call's callee is an assumption at its
declared type, or code the unit checks. An async function's
promise settles only to a primitive, the values that are never thenables
([nested promises](TRUST-REDUCTION.md#illustration-nested-promises)).
The model runs a body to its end; every point where other code can intervene
is an `await` or a call, across which only contracts survive.

