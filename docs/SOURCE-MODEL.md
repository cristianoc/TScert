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
declaration, a closure's included, or in its own initializer is the
binding before it is initialized ([lexical bindings before
initialization](#lexical-bindings-before-initialization)).

<a id="lexical-bindings-before-initialization"></a>
**Lexical bindings before initialization.** A `let`, `const` or class
declaration's binding exists from the entry of its scope and is
uninitialized until its declaration runs; reading, writing or `typeof` of it
then throws a `ReferenceError` (the temporal dead zone). A closure holds the
binding, never its value, so whether a read through a closure throws depends
on when the closure runs, not on where it is written: in

```ts
const visit = (n: Node): void => { if (wanted(n)) found.push(n); };
const wanted = (n: Node): boolean => n.kind === 79;
```

`visit` reads `wanted` successfully at every call made after the second
line, and throws at a call made before it.

**Scope.** The model covers a `let` or `const` that declares one name (no
pattern), in a function body or a block statement, a loop's body included.
Each entry of the block creates its bindings anew, so a closure created in
one iteration keeps that iteration's. Refused at their location, as
explicit restrictions, each the behaviour of reading a binding of an
environment the model does not represent before its initialization: an
early binding (below) declared by a pattern; one in a `switch`'s case block
(one environment for every clause, entered after the discriminant, whose
clauses may skip a declaration); a class declaration's binding; a
generator's body; a parameter default that mentions its own parameter or a
later one, a closure's mention included (`initializedBefore`); and a loop
head's binding mentioned in its own head (`for (const xs of xs)`). A module's constants keep the initialization order check
(`Sites.checkInitializationOrder`), which refuses an initialization step
that may reach a constant not yet bound; it does not model the module's dead
zone for them, a caught `ReferenceError` there or a module cycle. A
module-level `let` is a [module cell](#module-cells).

A binding is **early** when one of its mentions is in a closure created
before its initialization point, which may run at any time after its
creation, or when a
mention in the scope's own code is not dominated, within the same
activation, by the binding's **initialization point**: the write after its
initializer completed normally, which follows the initializer's own
evaluation (`let x = x` and `let a = b, b = 1` throw), one binding of a
declaration list at a time. A function literal that is a constant's whole
initializer is the exception: creating it runs nothing, so its reads of the
constant are the [recursive constant](#recursive-constants)'s self entry,
not checked accesses. Every other binding is lowered as before. A function
declaration in a body, which JavaScript creates when its block is entered
(`f(); let x = 1; function f() { return x; }` throws), is outside the
fragment (refused at the declaration); the parser's analysis takes its
creation at the block's entry.

**Representation.** An early binding $`x`$ of storage contract $`T`$ is a
cell of the block's activation, allocated when the block is entered, before
its statements,
holding the activation's **uninitialized marker** $`u`$: one fresh object per
block entry, owning the key $`\kappa_u`$ (`[[uninitialized]]`), and the only
objects that own it. This is a representation invariant, an obligation of
the lowering: every string key a JavaScript object has is represented
under $`\mathsf{esc}`$, whose image misses the model's reserved spellings
(`reservedSpelling_escapeKey`, [keys](SEMANTICS.md)); the model's own
reserved keys (`[[proto]]`, `[]`, `[[code]]`, `[[host]]`, a class's
prototype key) are other spellings; and no allocation but the marker's,
source, native or host, adds $`\kappa_u`$, so no source-visible value or
object on its prototype chain owns it. `copiedKey` excludes $`\kappa_u`$,
as it excludes `[[host]]`, though by confinement (below) no copy receives a
marker. The cell's
contract is $`T\cup U`$, with $`U`$ a label of its own whose one clause
requires $`\kappa_u`$; closures and function declarations capture the cell
itself, never its contents.

**Checked access.** A read of $`x`$ reads the cell once, tests that value
for $`\kappa_u`$ (the calculus's `hasKey`, which is false of a primitive;
never JavaScript's `in`, which throws on one), throws on the true edge, and
on the false edge proceeds with the same value, the test's slice removing
$`U`$ (`tagSlice`), so at $`T`$:

```math
\frac{\Gamma\vdash x:\mathsf{cell}(T\cup U)}
     {⟦x⟧=\mathsf{let}\ v=\mathsf{read}(x)\ \mathsf{in}\ \mathsf{if}\ \kappa_u\in v\ \mathsf{then}\ \mathsf{throw}\ \iota_{\mathsf{RE}}()\ \mathsf{else}\ v,
      \qquad \Gamma\vdash ⟦x⟧:T\ \text{on its normal edge}}\ \textsf{early-read}
```

Only checked accesses read the cell, so the marker never reaches a value
position: a return, an argument, a spread, a copy or a serialization. The
operators keep ECMAScript's order: `x = e` evaluates `e`, then checks, then
writes; `x += e`, an update and a logical assignment begin with a checked
read; `typeof x` is a checked read followed by the test. Assigning a `const`
is refused by TypeScript and is outside the fragment.

**Initialization.** The declaration's evaluation, where the source has it,
writes its initializer's value into the cell after the initializer
completes normally, checked at $`T`$; `let x;` writes `undefined`. An
initializer that throws leaves the marker, so a closure retained from that
activation throws at every later read, as JavaScript's does.

**The throw.** $`\iota_{\mathsf{RE}}`$, `%ThrowUninitialized%`, allocates a
`ReferenceError` by the realm's intrinsic constructor, whatever a source
binding of that name holds, and throws it: the read's exceptional edge,
which reaches the enclosing handler as any throw does, with no fact of the
normal edge. Its footprint is empty over storage that existed before it;
effects already performed, by an assignment's right side for one, remain.

**Precision.** A checked read always has its exceptional edge: where the
cell's current contents are known at $`T`$, the test is still undecided for
a $`T`$ that is an open record, a dictionary or `unknown`, and after a call
the cell is again at $`T\cup U`$. Safety, a value, a step or a throw, holds
either way; an exceptional guarantee that excludes the throw would need a
durable initialization fact, which the model does not have.

**Ownership.** The parser marks each early binding in the Fragment
(`markEarly`) and lists `%ThrowUninitialized%` where a file has one; Lean
lowers a marked binding as above, allocating the cells at the list's entry
(an `early` node of the flow graph), capturing the cell and the intrinsic in
every closure that mentions the binding, and lowering every mention as a
checked access, in graph code and in closure term code. A mention of an
unmarked binding before its initialization has no binding in scope there and
is refused by the lowering. The producer proposes $`T`$ and the claims at
the checked accesses; no claim can omit a check, replace the cell by a
value, or make an initialization an unchecked write
(`early-bindings`, `invalid-early-binding-stale`, run under Node; the forged
claims of `pipeline/test.mts`: a dropped contract, a contract narrower than
the annotation, a checked access claimed past the contract). The stated
type $`T`$ is the annotation, or a function literal's parameter and result
annotations; an early binding with neither is refused, and so are the
compound assignment, update and logical assignment of an early `let`, an
assignment to one in closure term code, a key-adding write of an object one
holds, and an initializer that reads its own binding.

<a id="recursive-constants"></a>
**Recursive constants.** A constant whose initializer is a function literal,
an arrow or a function expression with nothing else evaluated, reads its own
name inside the literal's body and parameter defaults:
`const visit = (n: Node): R => … visit(child) …`. Creating the literal runs
neither, so every such read runs during an invocation, after the binding
holds the closure. The read is the code's **self entry**: every invocation of
graph code enters it with the invoked object, the exact
$`\mathsf{obj}(\mathit{fs},\mathsf{graph}(\ldots))`$ the call step matched, in
the slot after the captures ([graph code](SEMANTICS.md#graph-code)); a bound
function forwards to its target first, so self is the original closure, never
the wrapper. A nested closure captures the self entry as any other slot. The
literal's code, of fixed arity, is checked from the frame with self at the
closure's claimed type, and the closure rule proves the closure meets that
whole type, its effects and exceptional guarantee included, by induction on
the step index (`funGraphSelf`,
[program typing](PROGRAM-TYPING.md#judgments-and-constructor-views)): at
budget $`n`$ every invocation runs at a lower index, where the induction
hypothesis gives self its type. The producer types the body's reads at the
constant's annotation or the literal's own signature, which its result
annotation completes; the checker derives each from the claimed type. Every
other read of a binding in its own initializer is refused at its location
(`recursive-const-before-initialization-refused`), and module initialization
order is checked as before (`Sites`).

<a id="module-cells"></a>
**Module cells.** A module-level `let x` that the module does not export,
in no form (no `export let`, no `export { x }` or alias of it), is an
[early binding](#lexical-bindings-before-initialization) of the module's
scope, whatever its mentions: a **module cell**. The initialization unit
allocates it at its entry, before any statement and before the module's
functions and classes exist, holding the module's uninitialized marker,
and binds a module constant to it, so a closure or function created before
the declaration captures the one cell, as `const get = () => x; let x = 1;
get();` needs. The declaration writes the initializer's value after it
completes normally; `let x;` writes `undefined`. Every mention of $`x`$, in
the initialization unit, in every module function and in every closure, is
a checked access, so a run that reaches $`x`$ before its initialization
throws the `ReferenceError` JavaScript throws, and no initialization order
check is needed for it:

```math
\frac{\mathtt{let}\ x\ \text{at the module's top level, not exported}\quad C_x\ \text{its one contract}}
     {\Gamma_f(x)=\mathsf{cell}(C_x\cup U)\ \text{for every unit } f\ \text{of the module}}\ \textsf{module-cell}
```

$`\mathsf{cell}(C)`$ is the private cell's invariant writable field at
$`C`$. $`C_x`$ is one contract for the binding, stated once in the claims
and the same in every unit: its annotation. The module's units read the
binding, so it is a unit boundary, whose type is written, as a module
function's signature is; an unannotated module `let` is refused at the
gate (`invalid-unannotated-module-let`). The initialization unit checks
the initializer against $`C_x`$, and every unit each of its writes,
`undefined` included for `let x: T;`; no unit narrows it. A unit's theorem assumes $`x`$ at
$`\mathsf{cell}(C_x\cup U)`$, its contents any value there at the unit's
entry and after each call; the facts a unit establishes of the contents
follow the [current-content rules](PROGRAM-TYPING.md#current-content-rules-semantic-layer):
a write or a call ends them, a join keeps only what every edge proves, and
a closure captures the cell's identity, never its contents. Composing the
units' theorems for a module execution, with the cell's contract as a
shared invariant of the heap every write preserves, is
[module composition](../WORK.md#module-composition). A `var`, whose binding
exists from the module's entry at `undefined` and may be redeclared, and an
exported `let`, a live binding importers read, are outside the fragment. A
module `let` stays a cell whatever writes it; a certified module's run checks the initialization that
allocates and initializes its cells with the module's units
(`module-cells`, `module-cell-before-initialization`,
`module-cell-saved-value`, `invalid-module-cell-stale`, run under Node;
`certified-module-cell-value-import`; a cycle of modules whose
initialization reads a cell of a module not yet evaluated throws at the
checked access, `certified-cell-cycle-value-import`, run under Node; the
forged claims of `pipeline/test.mts`: a dropped or narrowed contract, a
narrowed entry claim, a read after a writing call claimed at the earlier
value).

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
`Error`'s non-enumerable `message`. A value of a binder bounded by a record
(`B extends {…}`) is copied at its bound, the meet row it is read as being
below the bound's clauses, and a value of an intersection of records at the
one record they describe; the copy is a record of those fields, no value of
the binder, since a binder narrower than its bound may fix a field the
literal replaces: at `B := { name: "a"; size: number }`, `{ ...b, name: "x" }`
meets the bound and not `B` (`invalid-spread-binder-result`, executed under
Node by `node-runs.mts`). The model's copy takes string keys
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
symbol's key. A computed key `[k]` whose expression, a name or a member read,
TypeScript types as one string or number literal $`\ell`$ (a `const`
binding's, an enum member's) is the key $`\ell`$ spells, the number's by its
`ToString`. ECMA-262 evaluates the key expression, converts it to a property
key, then evaluates the value
([PropertyDefinitionEvaluation](REFERENCES.md#ecma-262)); converting a
string or a number runs no code, so the field is

```math
⟦[k]\colon e⟧=\mathsf{key}(\ell)\colon(⟦k⟧\ \mathtt{satisfies}\ \ell,\ ⟦e⟧)
```

the key expression evaluated where it is written, checked at $`\ell`$, then
the value (`object-computed-literal-key`). The Fragment marks the field
computed, and Lean refuses one whose key is not the key $`\ell`$ converts to
(`computedGate` in `Claims/Preparation.lean`). The check holds of the fields
the parser marks: that every computed key is marked is the parser's, a
trusted extraction obligation. A key at a union of
literals, at `string` or `number`, or written as any other expression is
refused, as the allocation's keys are then known only at run time;
`__proto__`, a key whose possible values include `Symbol.toStringTag`, and
accessors are refused.
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
`ArrayProto`, `constructor`, `then` and `toJSON`, so `xs.map` reaches the
prototype, ordinary construction cannot be overridden and `JSON.stringify`
calls no hook of an array; it may own other keys,
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
a certified callback: `find`/`findIndex` at the empty footprint can then pass `T`,
and `map` at each footprint that keeps dense prefixes
([FOOTPRINTS](FOOTPRINTS.md#the-stable-set-for-density)) produces a dense result
from its dense receiver. The fresh result
is assigned the readable `U[]` lifetime contract, so it remains writable at
the source type even when `U` admits holes. These are ordinary
qualified callback types, including when the callback is returned or bound.

**Ordinary array construction is part of the admitted semantics.** An array
owns neither `constructor` nor `then`, and the built-in `Array.prototype.constructor`,
`Array[Symbol.species]` and relevant prototype links retain their standard
behavior; `Array.prototype` and `Object.prototype` have no `then`. External code must preserve the same invariant for values it supplies
and across calls. Every array is also writable and extensible: no array is
frozen, sealed or made non-extensible, so an element write at an array index
succeeds, as the calculus's `setElem` does. The program's own code cannot
change that, since `Object.freeze`, `Object.seal`, `Object.preventExtensions`
and `Object.defineProperty` are outside the reviewed overlay of library
globals (`tools/library-globals.mts`); external code must supply such arrays.
This is an explicit host assumption, like the restrictions on
proxies and accessors; it is not a theorem about arbitrary JavaScript.

The own-key part is stated in the existing array contract and the built-ins' invariant:
`RequestJson.arrayExcludedKeys` adds `constructor`, `then` and `toJSON` to the prototype's
declared keys. No object along an array's prototype chain holds `toJSON`
(`Array.prototype`, `Object.prototype`): a host assumption, which external code
supplies and preserves for the arrays it returns, stores, passes to callbacks
or throws. Arrays cannot acquire it through an invariant-preserving allocation,
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

A call signature states a [closed footprint](FOOTPRINTS.md#changes-and-footprints):
on normal return, the call changes the contents of the previously allocated
locations holding a value and of those holding an array store at most as it
says. The empty footprint leaves every such location's contents unchanged;
`all: any` constrains none. It may allocate fresh storage. A type guard's and
an assertion function's signatures state, besides, the promises `guards` and
`asserts`, a promise about an actual
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
An imported implementation needs checked evidence
([certified imports](#certified-imports)) or an explicitly documented external
assumption: its TypeScript declaration supplies neither proof nor an implicit
effect. Built-in contracts remain separately audited assumptions.

The first guarantee preserves existing heap contents on normal return and
allows fresh allocation. A call that throws supplies no heap postcondition.
Consequently, a body checker cannot carry this guarantee through a caught
exception: it must check the handler with the possibly changed heap, or have
a separately justified guarantee for exceptional exits ([exceptional footprints](#exceptional-footprints)). The current pure-body
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

### Certified imports

An imported function of the program is read at its declaration's ordinary
signature, which states no effect. A **certified import** is read at an
effect-qualified signature that the same run certifies from the imported
declaration's code. This is the checked evidence the
[previous section](#inferred-call-effects-elaboration-and-certification)
requires; the import's TypeScript declaration still supplies none.

**Eligibility.** A read may be qualified only where its binding's value is
stable: a named import of an exported function declaration that no code of
its module reassigns. Its terminal declaration identity is the one
TypeScript resolves the import to, through re-exports; a re-exporting
module's own execution is part of the runtime module graph below. Default
imports stay refused, as the parser refuses them. Any other import is read
at its ordinary signature. Lean refuses a unit whose module's document writes
its binding, and the parser lists no module whose code it leaves unlowered
writes one.

**Two graphs.** The **qualified-dependency graph** has an edge from a unit to
each unit it reads at a qualified signature; it is acyclic. The pipeline
proposes a module after the modules it imports from, so a read that would
close a cycle is read at its ordinary signature, and Lean refuses a cycle
among the modules the planned reads name. The **runtime
module graph** is the modules' import relation as the host evaluates it,
ordinary imports and re-exports included; it may have cycles. Qualification
reasons about the first; the second bears on initialisation and binding,
below.

**The documents.** The parser lowers its documents before any claim exists,
so it lowers every module the qualified-dependency graph may need: every
program module the checked file imports a function from, transitively,
each under the checked file's TypeScript program and options, so that both
readings of a declaration resolve alike. The fragment's required `modules`
array ([the wire](FRAGMENT-FORMAT.md)) lists each once: its **artifact**,
the module identity its declarations carry (`location`) and the `sha256` of
the exact bytes lowered, then its declarations, top-level code and
functions, as a file's own fragment holds them, its own identity written as
`location`. A function of such a module is a **unit**, named by its origin:
the module's artifact, the declaration's span and its name. Origins come
from the parser's resolution and snapshot, never from a claim of the
producer's. The claims document's required `modules` array holds one claims
document per fragment module, over that module's own type table, and the
importer's claims list the imports it reads qualified (`qualified`), each by
its declaration identity. A census slice keeps its own identity: a slice verified
is not a certification of the module it was cut from.

**Failure boundary.** A module function the parser cannot lower is absent
from its module, with the parser's reason, and its module's other functions
stay. A module whose declarations or top-level code cannot be lowered is
absent: its imports are read at their ordinary signatures. An import read
at its ordinary signature is refused where that signature is not
representable in full, as today.

**What a unit's certification covers.** A unit is checked in its module's
run, as a run of that file alone checks it, over that module's own type
table: its module's initialisation (the existing initialisation unit and
order, `Extraction.lean`), its own code at its claimed signature, the
module's functions its code reads, and, recursively, every unit it reads
at a qualified signature. So the certified set is the closure of the units
the claims read qualified under the module functions they read, together with
the module's initialisation, and, recursively, the same of every unit a
module run's own claims read qualified; the module's other functions are not
checked. Every other fact of its environment is an
explicit assumption, the
[import assumption](SOURCE-CONTRACTS.md#imported-ambient-and-global-values)
its module's own run also makes. An initialiser that is not checked never
supplies a qualified signature. Lean computes the closure and restricts
each module's document and claims to it itself, whatever the producer
chose.

**Binding.** Lean reads an import at a qualified signature only where the
importer's claims list it qualified and the documents hold a unit of its
origin: the import's declaration identity names a module whose artifact
the fragment lists, and a function of it whose name is the declaration's
and whose name lies in the declaration's span. The unit is eligible: one
declaration, binders of its own none, no rest parameter, no receiver, no
guard and no promise. The two readings of
its ordinary signature, the importer's declaration document's and the
module's own annotation, are compared structurally, a mismatch refused:
the parameter and result terms, and recursively every declaration either
reaches, under the identity mapping of declaration identities: its equation,
parameters and heritage, and the written applications listed in it, in the
unit's own declaration alike, with their scopes, arguments and bounds. A
declaration lowering reads by identity rather than through a reference
(`ImplicitDependency`, the one list lowering selects them through) is
reached as a reference's target is where a term reached needs it:
`ArrayProto` for an array or tuple term, `%Stable%` and native `Promise` for
a resolution-qualified binder. Symbol keys compare by the identity of their
symbol's declaration rather than a document's index, and a visited set
closes recursive definitions. Every field of a term takes part, array presence and host
classification among them. Each of the following is refused, named by the
unit's origin: a qualified read naming no unit, a unit of another origin, a
unit not eligible, a structural mismatch, a module's claims about other bytes
than its document's, and a module run whose check fails. The
importer's evidence and the units' are checked by one `checkJson` call, so
the evidence that certifies the effect is evidence about that declaration's
code, not about a name.

**The ordinary signature is kept.** The unit is checked at its annotation's
signature with the effect added, its annotation obligations retained, as
[elaboration](#inferred-call-effects-elaboration-and-certification) states
for a module function. The importer reads the import as the unit's module
reads it (`moduleArrow` of the unit's annotation, with the footprint and
on-throw flag its claim states), which the structural comparison makes its
own declaration's signature with that effect. Its code is then known to
discard further actuals, so it may be passed where a signature binding more
parameters is expected.

**Inference.** OCaml proposes each module's effects as it proposes a
file's own (the greatest fixpoint over that module), then the importer's
claims at them. No effect
follows from a comment, a name or a module's role. The pipeline lists
qualified each eligible read whose unit has claims. Where the search over the
whole document refuses a read or a module run, its footprint refuted or its
initialisation unchecked, the pipeline withdraws those reads, proposes the
importer again, and the import is read at its ordinary signature. The final check is one
`checkJson` call over the whole document. Dense `map` needs a callback
footprint that keeps dense prefixes
([FOOTPRINTS](FOOTPRINTS.md#the-stable-set-for-density)).
`record-render`'s `parseRecord` is proposed and certified at
`{value: any, store: grow}`, in that set.

**What the theorem states.** `SourceClaimJson.checkJson_safe` states, for
the importer's document, what it states today, and the same of each module
document's certified set, each over its own frozen store: safety and its
footprint for every certified unit, and safety for the importer's
functions, each under `EnvOk` of its own inputs, the qualified import among
the importer's, and under `WorldAdm` and `HeapOk`.
It does not construct a module's environment, prove that initialisation
succeeds, or prove that the value an import binds at run time meets the
qualified signature: those are the linking obligation's.

**The linking obligation.** The conclusions combine into safety of the
linked program under a runtime invariant: at every qualified read, the
binding holds the certified unit's closure, whose captures meet its input
contracts in the current heap and world, and the module's initialisation and
all execution after it preserve that. The eligibility rule makes the first
half a property of the parser's resolution and of the host's module loader
(an exported declaration never reassigned holds its closure once its module
is evaluated); the second is the [module composition](../WORK.md#module-composition)
argument for units certified against each other's signatures, on which the
units of one module already rely. A dependency whose initialisation throws
stops the importer's evaluation: certifying a body proves no initialisation
succeeds. Until module composition is proved, the invariant is a review
obligation, listed with the import assumption and in the
[parser, extraction, declared-types and host bridges](TRUST-REDUCTION.md#the-bridges).

**A catch.** A certified import's footprint holds on normal return, and on
a throw where its effect states `onThrow`
([exceptional footprints](#exceptional-footprints)).

### Exceptional footprints

An effect may promise that its footprint also holds when the call throws:
`onThrow`. The promise covers the heap a throw leaves the call in, from the
call's entry heap, exactly as the footprint covers a normal return's. It says
nothing of the thrown value. A handler of a node calling at such a signature
then starts in a heap the footprint relates to the node's entry heap, and a
body that catches can be certified at a footprint.

**Semantics.** `SafePost Ξ T Q` states `Q` of the heap a value is returned in
and nothing of a throw. Its generalization `SafePostExc Ξ T Q R` states, in its
throw disjunct, `R h` of the heap `h` at which the term raises, whatever
value it raises:

```math
\mathsf{SafePostExc}\,\Xi\,T\,Q\,R\,(n{+}1)\,W\,h\,t \iff
(\mathsf{val}\,t \wedge T\,W\,t \wedge Q\,h\,t)
\vee (\exists v.\ \mathsf{Raises}\,t\,v \wedge \mathsf{Scoped}_0\,v \wedge \Xi\,W\,v \wedge R\,h)
\vee (\exists W'\,h'\,t'.\ \ldots \wedge \mathsf{SafePostExc}\,\Xi\,T\,Q\,R\,n\,W'\,h'\,t')
```

with the step disjunct as in `SafePost`. `SafePost Ξ T Q` is
`SafePostExc Ξ T Q (fun _ => True)`, and `erase` holds for both. An
effect $`e`$ with `onThrow` gives the arrow's run, from entry heap
$`h_0`$, the exceptional postcondition
$`R\,h \iff e.\mathsf{footprint}.\mathsf{HoldsOn}\,P\,h_0\,h`$, with
$`P`$ the locations its `receiverStore` leaves bounded, as `Effect.within`
reads them. Without `onThrow`, $`R`$ is `True`. Coverage
(`Effect.Covers`) gains one clause: an effect with `onThrow` covers one
without, and not the other way.

**Combining effects.** Two guarantees of one call combine
(`Effect.meet`) into the meet of their footprints, with `onThrow` the
conjunction of theirs. A disjunction would be unsound: an empty footprint
stated on normal return only, met with a wider one stated also on a throw,
gives no empty footprint on a throw. Where the conjunction loses a useful
guarantee, the signatures stay separately selectable, as overloads are. The
field is carried, and audited, wherever an effect is: overload combination,
weakening by an annotation, `bind`, construct signatures, and imported and
library signatures.

**What stays on normal edges.** A promise (`guards`, `asserts`) is a fact
about the arguments a normal return establishes, and `fresh` a fact about
the returned value. A throw establishes neither, so neither moves onto an
exceptional edge. A handler binds the thrown value at the graph's exception
family, `unknown`, and the thrown slot is never fresh; the slots the node
already held keep their freshness (`handlerFresh`; the candidate facts
`inferFresh` proposes flow along handler edges the same way). The handler
receives no current-content fact ([handler facts](#exceptional-footprints)).

**Composition through a body.** `GraphCode.BoundState` states the run's
invariant from the body's entry heap $`h_0`$, with $`b`$ the body's
freshness cutoff, the length of $`h_0`$: a node's run is bounded on the
locations below $`b`$, so a node may change storage the body allocated
before it, a receiver among them. The extension keeps that cutoff:

- a node with a handler is admitted when its term's run is `SafePostExc`
  whose exceptional postcondition relates the node's entry heap to the heap
  it raises in on the locations below $`b`$; the `handle` transition then
  keeps $`\Phi.\mathsf{Holds}\,h_0\,h`$ by `Closed.Holds.trans_on` with
  the invariant at the node's entry, as `enter` does for a normal return;
- the state `.raised v` keeps $`\Phi.\mathsf{Holds}\,h_0\,h`$ where the body
  claims `onThrow`; without it the state stays unconstrained;
- the `handle` transition also establishes the handler target's
  `FreshOk`, through the handler's slot mapping with the thrown slot
  non-fresh;
- each node's term is checked by the form that admits it today (an
  inspection, a typed write, a call at a selected signature), now also on
  its throws.

**Handler facts.** Ordinary graph certification checks a handler edge
(`HandlerOk`) with facts that hold in every heap: `handlerFacts` drops heap
observations, whatever the throwing call's footprint. A handler therefore
receives no current-content fact across a throw, and one that relies on a
fact the guard before the call established is refused
(`invalid-exceptional-handler-fact`, run under Node). The bounded run's
footprint and freshness are what the exceptional postcondition carries to a
handler. Keeping the facts a throw's footprint keeps would thread the
postcondition through expression checking, `HandlerOk` and `StateOk`.

Every way a node's term can raise is then covered:

- **Before the invocation.** Source lowering evaluates operands into slots
  first (`valueTerm`), so a call node raises either while reading its
  operands, which writes nothing, or in the callee. An inspection may
  allocate before it raises; it preserves the heap's prefix
  (`inspect_step`), so every location below $`b`$ keeps its contents. A typed
  write raises before it writes.
- **In the callee.** A call at a selected signature raises within the
  signature's `onThrow` footprint. In bounded certification, a node whose
  call lacks `onThrow` admits no handler, and a body containing one claims
  no `onThrow`; ordinary safety keeps every handler.
- **Defaults and intermediate mutations.** A parameter default runs as nodes
  of the declaration's graph, and earlier nodes' normal returns compose into
  the invariant, so a throw at any node is relative to the body's entry
  heap.
- **Handlers and rethrows.** A handler is a node like any other. A rethrow
  is a `throw` node without a handler, which raises at its entry heap and so
  reaches `.raised` with the invariant.

A pure graph keeps its independent operational rule, which covers its
handlers already and bounds its throws too: every step keeps the heap a
prefix (`CallEffects.prefix_safe_exc`). A node whose entry has a slot of a
type no value meets is never entered, so it is within any bound
(`GraphCode.unreachableEntry`; `never-parameter-calls`).

**What `checkJson_safe` states.** Its second conclusion, for each accepted
request with a footprint other than `top`, becomes a `SafePostExc` whose
exceptional postcondition is the footprint from the run's entry heap where
the request's effect states `onThrow`, and `True` elsewhere. Its premise
stays the exact CLI success condition. The first conclusion, plain safety,
is unchanged.

**Natives.** A native signature states `onThrow` only where its audit
covers every throw: validation errors, failures of the host, and the
operation's own errors. `Error` at a string message and `JSON.stringify` at
a JSON value write nothing they did not allocate before they return or
throw, so each states the empty footprint with `onThrow`
([library globals](SOURCE-CONTRACTS.md#library-globals)). `execFileSync`'s
[restricted form](SOURCE-CONTRACTS.md#library-modules) is audited for it;
its overlay entry in `library-modules.mts` states the empty footprint with
`onThrow`, at options whose optional fields `env?: undefined` and
`shell?: false` the argument's claim must meet. An object literal without a
spread meets them by leaving those keys out, since a literal owns exactly
the properties it writes ([object literals](#object-literals)). A literal
with a spread meets them only where each spread part's claim states the two
keys absent or at those types; leaving them out after an open spread does
not. The entry keeps the unrestricted
form beside it, so a call outside the restricted options keeps its type and
an unrestricted effect.

**The motivating chain.** `commit-records`' `git` calls `execFileSync` at
the restricted options and is certified at the empty footprint with
`onThrow`. `at` catches `git`'s throw and returns `undefined` from its
handler, so it is certified at the empty footprint. `examplesOf`,
`readRecord` and `group`'s `map` callback then compose normal-return
footprints, with the [certified import](#certified-imports) of
`parseRecord`. `node-exec-restricted` shows the first steps, and
`exceptional-footprint-handler` the same composition
for callees that build and throw an error: a declaration, a constant's
arrow, and a declaration whose handler rethrows.

**Producer and wire.** A call effect states `onThrow` in the wire
([source claims](SOURCE-CLAIMS.md)), and so does a declaration's claim beside
its footprint. OCaml proposes it for a closure and, at a greatest fixpoint
over the module, for a declaration whose every node bounds its throw
(`Source.throws_stmts`); a `try` whose block bounds its throws, with a catch
and no `finally`, is within the join of the block's and the handler's
footprints. Implementation: `HeapObservations.SafePostExc`,
`CallEffects.Effect.excPost`, `GraphCode.NodeWithin` (its `thr` flag),
`GraphCode.throwsWithin`, `GraphCode.handlerFresh`, `GraphCode.BoundState`
(its `exc` flag) and `SourceRequests.checkRequests_footprint_at`, whose
statement `checkJson_safe`'s second conclusion is.

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
those prototypes list states the empty footprint, so a call of one is a
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
keeps its keys, except in a record holding a generic method, whose only
claim is its declaration: there the field's read until a call is the value
the test found. A test on a mutable cell refines the read, never the cell.
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

