# Verification work

This is the work ledger for the independent verifier: open work, the reason
each item is open and when it closes. [DESIGN](docs/DESIGN.md) states the
architecture and decisions; [the source boundary](docs/SOURCE-FRAGMENT.md) owns
supported-fragment restrictions.

## Next steps

### Status

Progress is recorded here and nowhere else. A commit that moves an item
updates its row. The prose under [open work](#open-work) describes each item's
design, not its progress.

| Item | State | Closed when |
| --- | --- | --- |
| [A connection to ECMA-262](#a-connection-to-ecma-262) | open | the host's stated types are lemmas of a mechanized specification |
| [Constructor rests](#constructor-rests) | open | a constructor with a rest parameter is constructed and its variadic construct signature introduced |
| [Class offers across units](#class-offers-across-units) | open | a module class passed by a module function to a variadic construct signature verifies |
| [Generic methods left](#generic-methods-left) | open | `class-generic-method-bounded-refused` verifies, and members binding different numbers of binders relate |
| [Contract completeness](#restoring-completeness) | open | effect inference covers the rest wrappers, call forms and nested heap operations it is conservative for |
| [Footprints](#footprints) | open: the seven programs decided (2026-10-17) | every application form has a checked bound |
| [Keys known only at run time](#keys-known-only-at-run-time) | open | the writes listed there are typed |
| [Module composition](#module-composition) | open: certified imports checked, their units' composition reviewed (2026-10-18) | a Lean theorem composes units certified against each other's signatures |
| [Decoders' dictionary reads](#decoders-dictionary-reads) | open: the decoders take parsed JSON (2026-10-18); in `calculus` 12 of 15 functions verify, and `decodeTerm`, `decodeCode` and `termsOf` verify in 10.0 s of evidence search with candidate selection and the answered requests threaded through the document's search, 25.2 s without any reuse (user time, median of 3, 2026-10-19) | the decoders of `calculus`/`control-flow` verify in their modules within the limit |
| [Function declarations in bodies](docs/SOURCE-MODEL.md#lexical-bindings-before-initialization) | open | `function-declaration-in-body-refused` verifies: a function declared in a body is created at its block's entry, and a call of it before the block's bindings are initialized reaches their checked accesses |
| [Optional-field truthiness over unions](#optional-field-truthiness) | open: an investigation, cause unknown | `optional-field-truthiness-union-refused` verifies |
| [Exceptional footprints](#exceptional-footprints) | open: handler facts across a throw | a call's footprint on a throw carries an effect through a handler, with `checkJson_safe` concluding it |
| [Iteration left open](#iteration-left-open) | open | the iteration forms listed there are lowered |
| [Enum-member case labels](#enum-member-case-labels) | open | `switch-enum-case-narrowing` verifies |
| [Family identity controls](#family-identity-controls) | open | the identity controls HOST-FAMILIES.md lists verify or are refused as it states |
| [Effects of dispatched calls](#effects-of-dispatched-calls) | open | a method call on a union with a primitive's shape is dispatched and `split-non-empty` verifies |
| [Remaining source forms](#remaining-source-forms) | open | the forms listed there are admitted |
| [Model limits of one form each](#model-limits-of-one-form-each) | open | each limit listed there has its model support |
| [Precision](#precision) | open | the facts listed there are derivable |
| [A semantics of the Fragment](#a-semantics-of-the-fragment) | open | extraction is proved a simulation of a Lean interpreter of the Fragment |
| [Regular expressions left](#regular-expressions-left) | open | replacement callbacks, `new RegExp`, a regex's properties and structural match iterators are admitted, and `SetIterator` and `MapIterator` loops require the native mark |
| [Computed types evaluated through helper declarations](#computed-types-evaluated-through-helper-declarations) | open: a stopgap | the helper declarations are replaced by a checker endpoint (relaxed), or TypeScript's computation is checked by a source-type elaborator in Lean (checked) |
| [The any check over external declarations](#the-any-check-over-external-declarations) | open: a stated limit, relations that `any` satisfied in an outside declaration are not re-established; 447 errors in the shadowed declarations (2026-10-18) | a check re-establishes the relations and `tests/unchecked-project/gaps.mts` is refused |
| [Node's process](#nodes-process) | open: the environment write a located gap; events known only as strings refused | a write of `process.env` through a receiver-bound host setter over shared state preserving every alias's view; signals reached through iteration proven admitted |
| [JSON records by their fields](#json-records-by-their-fields) | open | a record bounded on all its own string keys meets `JsonValue`, built or validated and kept through mutation and external calls |
| [The front end's own functions](#the-front-ends-own-functions) | open: of the test infrastructure (`tools/*.mts`, `dev/*.mts`, `pipeline/*.mts` and the seven drivers of `tests/`; the fixtures `tests/unchecked-project/`, `tests/unchecked-broken/`, `pipeline/examples/`, `pipeline/imports-project/` and `pipeline/library-project/` excluded), 101 of 341 functions verify in `tools/` (2026-10-19, the missing library globals reviewed), 24 of 24 in `dev/`, 8 of 13 in `tests/` and 2 of 35 in `pipeline/` (2026-10-19, `node:assert/strict` read, 60 s step limit) | the blockers listed there are admitted or refused by a stated restriction |

### Open work

<a id="a-connection-to-ecma-262"></a>
**A connection to ECMA-262.** Proving the host's stated types as lemmas of a
mechanized specification would turn the ECMA rows of the trust surface into
theorems; the lemmas and their cost are in
[TRUST-REDUCTION](docs/TRUST-REDUCTION.md#the-host).

<a id="native-identity-beyond-the-goal"></a>
**Native identity beyond the goal.** A program-built value is kept out of
`Promise<T>` structurally: certified code writes no `[Symbol.toStringTag]`,
which Promise's prototype record requires. A native internal slot (the
`[[PromiseState]]` that ECMA-262's `IsPromise` tests) accepts the same
programs; it becomes the cheaper path once a retained program writes its own
`[Symbol.toStringTag]`, subclasses `Promise`, or `Set`, `Map`, `Date`,
`RegExp` and `Promise` are to share one mechanism. A survey of 12.9 M lines
of library and tooling code in the local repositories' `node_modules`
(2026-10-19; no application code) ranks what lies beyond the goal: custom
thenables in 19 packages, several awaited by documented use (tinyexec,
fastify's reply, postcss's `LazyResult`), which a checked thenable protocol
at `await` and resolution would admit under either choice; about 30
hand-written tags, all in library code, one tagging a non-promise
`"Promise"` (vitest); about 7 `Promise` subclasses in 5 packages, 3 of them
one generated SDK class (`APIPromise`); and, for contrast, `extends Error`
1,150 times in 236 packages, container subclasses in about 50. The
repository's own code has none of the first three.

<a id="constructor-rests"></a>
**Constructor rests.** A constructor's rest parameter is refused: `new`
constructs only code without a rest (`CallArguments.construction`), so code
collecting one needs a construction that allocates the rest store from the
actuals past its parameters, and an introduction of a variadic construct
signature from such code, as `restsT_of_graphRest` is for a function.

<a id="class-offers-across-units"></a>
**Class offers across units.** A class value is offered a signature its use
expects (a variadic construct signature, a longer one) where its binding
and the use are analysed together: at the module's statements. A module
function passing a module class to a variadic construct signature leaves the
class's claim without that signature, and the call is a search failure; the
offer needs the class claim to collect the signatures every unit's uses
expect.

<a id="generic-methods-left"></a>
**Generic methods left.** A class's generic method with a bounded binder:
the member's binder row is named by its bound, which the parser does not
spell for the closure (`class-generic-method-bounded-refused`). Members of
two declarations, or of two instances of one, binding as many binders relate
up to renaming ([generic methods](docs/SOURCE-CONTRACTS.md#generic-methods)); two
binding different numbers of binders (`m<U, V>` at `m<W>`), which TypeScript
relates by instantiating the source at the target's binders, need an instance
table naming each source signature's image at the target's binders, inside
the family entry's table. A binder a member's result accumulates
(`catch`'s `Promise<T | TResult>`) grows its family by one binder per call:
each is an application of the one equation, unfolded only when read
([RECURSIVE-EQUATIONS](docs/RECURSIVE-EQUATIONS.md)), never truncated.

<a id="restoring-completeness"></a>
**Contract completeness.** Array presence, callback effects and conversion
contracts impose separate obligations. Their current designs are stated under
[arrays](docs/SOURCE-MODEL.md#arrays), [native contracts](docs/SOURCE-MODEL.md#exact-contracts-and-native-effects) and
[effect certification](docs/SOURCE-MODEL.md#inferred-call-effects-elaboration-and-certification).
A future inference improvement must preserve these distinctions: density is
stronger than readable elements; readonly aliases do not prevent callback
mutation; and a written callback annotation cannot silently acquire a stronger
effect. A program with an arbitrary callback promising readable `U[]` for every
`U` must justify that promise even when the callback shrinks the source.

Effect inference remains conservative for some rest wrappers, call forms and
nested heap operations. Expression scheduling alone does not supply the missing
effect derivation. Code that writes only locations it allocated preserves the
heap it was called with, but a body's checked footprint separates only array
stores the body allocated, through fresh results ([footprint
precision](#footprints)). A call of a value holding a fixed
signature and its variadic extension, a module constant read as a value
elsewhere, is not certified preserving: the selected call's evidence is no
qualified application at the fixed signature. Keep the source targets and their
negative controls when extending the body-effect checker.

<a id="footprints"></a>
**Footprints.** [FOOTPRINTS](docs/FOOTPRINTS.md) states the mechanism: a
construct's fact, the operations proved to keep it, stated as closed
footprints, and Lean's node-by-node check that a callback, with what it
calls, stays within one. The checked forms are inspections, typed writes of
fields holding values, and fixed calls, variadic calls and constructions at
a selected signature, `pop`, `shift` and `reverse` at a store the body
allocated ([fresh array storage](docs/FOOTPRINTS.md#fresh-array-storage)).
Left open:

- the other application forms (a variadic construction, a call of a
  callable object, a packed call) consume no footprint, so a bounded body
  refuses them;

**Footprint precision** is deferred
([FOOTPRINTS](docs/FOOTPRINTS.md#deferred-extra-precision)): separating one
array from another beyond fresh storage, so that `pop` on an array literal
the callback allocated is admitted; and a declaration's fresh result, which
only closures state.

<a id="keys-known-only-at-run-time"></a>
**Keys known only at run time.** A write at a string key known only at run
time of an object or `null` value needs the copy to replace the prototype
where the key is `__proto__`, as the setter does; a key-adding write at a key
that may be a string or a symbol, a dispatch on the key's kind. A write adding
a key to an object a reference other than its holding locals may hold (a
callee, a closure, a `let` bound to it) needs the heap to map an object's
identity to its keys, which it does not. A key added to a class instance
whose prototype holds methods is copied with the prototype, but the copy is
typed as the record `mergeResult` gives, which states no method: it needs a
merge result at the instance's row.

<a id="module-composition"></a>
**Module composition** as a Lean theorem: the step-indexed argument that
units certified against each other's signatures compose.
[Certified imports](docs/SOURCE-MODEL.md#certified-imports) check an
imported function's code in the importer's run, at its effect-qualified
signature. `checkJson_safe` keeps its statement.
Combining a certified import's conclusion with the importer's is left to
this theorem, plus the review obligation that the import binds the certified
unit's closure ([the linking obligation](docs/SOURCE-MODEL.md#certified-imports)).

<a id="decoders-dictionary-reads"></a>
**Decoders' dictionary reads.** The decoders of `calculus.mts`,
`control-flow.mts` and `diagnostic.mts` read the wire as `Json`, what
`JSON.parse` returns without a reviver
([the contract](docs/SOURCE-CONTRACTS.md#library-globals)): a parsed object
is a dictionary of parsed data, read by key as the index's value or
`undefined`, and a key it may inherit from `Object.prototype` is refused
(`invalid-json-parse-inherited`). A constructor object's one key and its
value are `Object.entries`' pair, so no read at a key known only at run
time is needed. In `calculus`, the slice of `termsOf`, holding
`decodeTerm` and `decodeCode`, takes 29 s of evidence search and 5 s of
checking (user time, 2026-10-18). Of 29.6 s, 16.5 s are image-equivalence
checks: an instance of the array prototype's scheme, its result an array of
`source & X`, against the claim's `Term[]` row, 172 checks of 24 distinct
pairs, each direction of the costliest about 0.25 s though each side is one
clause. The time is in the structural comparison of the recursive `Term`
and `Json` union arms beneath; absorbing `source & X` into `X` before the
check takes it from 16.5 s to 16.2 s, `X` being source-valued in only 56 of
the 172 checks (a probe, 2026-10-18). Candidate selection
([structure-directed comparison](docs/UNION-SHAPES.md#9-the-implementation))
takes the structural engine's demand pairs from 470,306 to 41,560; the rerun
of each comparison it leaves unestablished costs 9.8 s and establishes none.
Within `termsOf`'s search, 107,721 subtype requests ask 3,926 distinct
questions, and the repeats take 14.7 s of 24.9 s, the refused repeats 11.9 s
([where the search time goes](docs/UNION-SHAPES.md#93-where-the-search-time-goes),
2026-10-18). `dev/lowering-dump.mts`
decodes the verifier's output with `decodeUnits`, which calls `fields` and
`nat` in `map` callbacks: imported functions, whose effect no certificate
states ([module composition](#module-composition)).

<a id="optional-field-truthiness"></a>
**Optional-field truthiness over unions**, an investigation: after
`if (o.m)`, a read of `o.m` is of `m`'s type where `o` is one record leaving
`m` optional. Where `o` is a union of records one of which requires `m` and
one leaves it optional, the claim where the test fails, without the arm
requiring `m`, is refused at the incoming edge
(`optional-field-truthiness-union-refused`), and where
each arm leaves `m` optional, the producer claims the read at `m`'s type or
`undefined` (observed 2026-10-18).

<a id="exceptional-footprints"></a>
**Exceptional footprints**: a call's promise that its footprint also holds
when it throws (`onThrow`), carried through handlers and concluded by
`checkJson_safe` ([the design](docs/SOURCE-MODEL.md#exceptional-footprints)).
Left: handlers receive no current-content facts across a throw.

- a semantic extension: `SafePost` states no postcondition on a throw, so
  `checkJson_safe` needs an exceptional conclusion tied to the exact CLI
  success condition;
- composition covering evaluation before the invocation, parameter
  defaults, intermediate mutations, handlers and rethrows;
- normal-return promises and freshness stay on normal edges: neither moves
  onto an exceptional one;
- a native states `onThrow` only where its audit covers every throw, as the
  [restricted `execFileSync`](docs/SOURCE-CONTRACTS.md#library-modules)
  audit does.

<a id="iteration-left-open"></a>
**Iteration left open.** An array pattern over a host
non-array iterable needs the pattern's reads as steps of `%Iterate:K%`, or of
the protocol. A spread of a program's iterable where the statement evaluates
code before it, and a default or nested pattern in an array pattern over one,
need the protocol's steps interleaved with that code, in the expression, not
before the statement. A generator needs a state-machine lowering, as
TypeScript's downlevel emit writes one: a closure over the suspension
point's number and the live locals, whose `next` resumes at a `switch` on
it. An element read past a readonly tuple arm's length needs a rule
reading `undefined` beyond an exact length.

<a id="enum-member-case-labels"></a>
**Enum-member case labels.** A `switch` whose `case` labels are enum
members (`case K.One:`, `case ts.SyntaxKind.SourceFile:`) narrows nothing in
the producer, where the same constants narrow in an `===` test and literal
labels narrow in a `switch` (`switch-enum-case-narrowing`, a gap). The
compiler API's code switches on `node.kind` this way.

<a id="family-identity-controls"></a>
**Family identity controls.** Of the
[identity controls](docs/HOST-FAMILIES.md#identity-through-program-code),
the cases cover a program alias and a re-export of `Node`, a generic
identity at `Identifier` and at `Node`, a verified wrapper, a record's
field holding a node (`compiler-api-family-identity`), a program literal
annotated as a node (`invalid-compiler-api-forged-node`), `{ node }` passed
where a node is expected (`invalid-compiler-api-boxed-node`), `{ ...node }`
(`invalid-compiler-api-node-spread`) and forged claims of a program
allocation at a family type (`pipeline/test.mts`). Left: a callback of
`forEachChild` reading its argument and one whose result is claimed at a
node type it did not receive, which wait on a generic method called on a
node (`compiler-api-node-callback`, a gap); a re-exported guard and a
guard's wrapper, which wait on guard recognition.

<a id="effects-of-dispatched-calls"></a>
**Effects of dispatched calls.** A method call on a union receiver is
dispatched on the receiver only where no alternative has a primitive's
shape or the alternatives read different members
([PROGRAM-TYPING](docs/PROGRAM-TYPING.md)). A dispatched call is an outer
conditional whose callee is a wrapper allocation and a member lookup, and
effect selection admits only a direct call, with evaluated operands, so a
dispatched call's effect is not established (`split-non-empty`, dispatched,
leaves `{value: keep, store: keep}` unestablished). Either the dispatch
lowers into branch nodes whose callees are evaluated values, or effects are
checked compositionally for these terms.

<a id="remaining-source-forms"></a>
**Remaining source forms.** A method call on a union of primitives,
which needs one callee contract its receiver meets. An optional call of a
method on any object (`f().m?.(a)`, `optional-method-call-object-refused`):
saving the receiver once, `let r = o; let m = r.m` then
`optional(m, callWithReceiver(m, r, a))`, admits every object and needs no
analysis of whether a second read of `o` is stable; the Fragment has no
expression binding a hidden name, so the lowering needs one. A source binder used both
as a pack and as an array value (`...args: T`, `args: T`): a binder whose instances are
arrays or tuples of required positions, its pack meaning that tuple contract's lists, so an
entry collects the fresh store at it and a spread of its value gives a list in the pack. Explicit type arguments on an element call,
which reach an element only as a generic closure's quantified claim.
User guards and assertion functions: the promise is a contract a
conjunction of arrows states, `(x: A) => boolean` with
`(x: Exclude<A, T>) => false` (an assertion function's `=> never`), which the
body is checked at, as a closure at each of its signatures; a caller narrows
through a fact the call leaves tying its result slot to its argument slot,
"an argument in `Exclude<A, T>` gave `false`", which the branch on the
result turns into a slice of the argument. Such a fact is about a type's
meaning, world- and level-indexed, where current-content facts are not; it
needs its own place in the knowledge a statement entry states. A static
initializer calling a static method reading its class, or constructing it
where construction reads an earlier static field, which runs the class's code
before the class value exists (a construction reading a later one reads
`undefined`, refused on principle); private
names in inheritance, which needs the derived construction's copy of its
base part to carry the base's private slots; a prototype member keyed by a
symbol.

<a id="model-limits-of-one-form-each"></a>
**Model limits of one form each.** Module storage (`declare let`, a
module-level `let`) needs cells every call may write, read at their declared
type. Sloppy code's `this` at a receiver type that may hold a primitive,
`undefined` or `null` needs the receiver conversion (the global object, a
wrapper). A library class as a base needs a construction rule for what its
constructor allocates. `keyof T` and `T[K]` over a function's own binder need a row whose
meaning fixes a key set, which a value set does not. `o.m?.()` needs the receiver saved
across the test. `key in o` at a key the built-in prototypes hold needs those
prototypes' keys in the model.

<a id="precision"></a>
**Precision.** Retaining heap facts across calls needs a proved
reachability or noninterference statement: the model's types do not bound
the locations a value names (`top` admits any object), so a location
allocated after a value cannot be shown unnamed by it, and the statement
needs every type's meaning to bound its value's locations by the world; set-valued clause covering (an
arrow against a union of arrows) needs a covering relation of another arity;
a vacuity escape for contradictory reference conjunctions
(`Ref null ∧ Ref bool ≤ Ref (null ∨ bool)`) is true and not derivable; the
producer's arrow search builds no nested `combine`. An element read keeps no
heap fact: it reads the heap only, but the value it finds is a value only
where the store's contract says so, which the frame rule would have to take
from the read's typing (a length is a number, and keeps them). An element
read the code guards is read at the element type or `undefined`; a member of
it is read past a nullish guard, which throws where JavaScript does, but the
value itself passed on keeps `undefined`
(`guarded-element-read-refused`): `xs[0] !== undefined && known.has(xs[0])`
needs a current-content fact about an element location, kept from the test
to the second read, as a field path would need one (`o.a !== undefined &&
f(o.a)` is refused the same way). A `flatMap` callback returning a
primitive or an array of primitives (`flat-map-scalar-result-refused`)
needs a second signature quantifying a binder bounded by the primitives,
which the first does not use: neither the producer's instance of a member
read nor Lean's search for one assigns a binder no parameter of the
selected signature names. The design question is per-signature binders, or
bounds, in a prototype member's scheme. A closure passed to `map` over an array literal of
records with different members (`closure-contextual-literal-union`) is read
at TypeScript's contextual records, `{ a: number; b?: undefined } |
{ a?: undefined; b: number }`; the producer claims it at the literals'
records `{ a: number } | { b: number }`, which state no absence of the
other's member and so are outside the parameter's records. A closure parameter at a generic declaration's anonymous record at an
instance with an optional member at a binder
(`closure-contextual-anonymous-instance-refused`: `{ v?: T }` of
`interface Opt<T> { readonly items: readonly { v?: T }[] }`, read through
`const xs = o.items; xs.map((i) => i.v)` at `o: Opt<number>`) is refused:
the compiler's synchronous API gives the instance's members but no
instantiation of `T`, and `v`'s type carries the `undefined` optionality
adds, so `v?: number` is not told from `v?: number | undefined`. Reading it
needs the instantiation from the compiler (an API extension) or a checked
elaboration of the contextual type. A key-adding write at a symbol known only at run time
(`symbol-key-growth-refused`: `d[fresh()] = 1` with `fresh(): symbol`
returning `Symbol("k")`) is refused, as the key may be `Symbol.toStringTag`;
admitting it needs a fact that the key is no tag, such as a type of the
program's own fresh symbols, and the copy rule then refuses it too, the
object's type listing no keys.

<a id="a-semantics-of-the-fragment"></a>
**A semantics of the Fragment.** The parser's rewrites and extraction rest
on review. The Fragment moves close to source JavaScript, the rewrites move
into extraction, and the Fragment gets a direct semantics in Lean: an
executable interpreter that reads it as JavaScript does, with types erased.
Extraction is proved a simulation of it. The interpreter's faithfulness to
JavaScript is tested against node, not proved: the target is fixed, so
testing converges without a mechanized specification. A rewrite chosen by a
type (`%Iterate:K%`, `%ElementAt%`) is correct under that typing premise.
The reading of declared types and the host remain trusted; the remaining
options are in [TRUST-REDUCTION](docs/TRUST-REDUCTION.md).

<a id="computed-types-evaluated-through-helper-declarations"></a>
**Computed types evaluated through helper declarations.** A computed form
naming a declaration's parameters (a bound, a default, an annotation's
computed alias) is evaluated at an application by the pinned TypeScript,
through helper declarations added to a probe program
([written applications](docs/SOURCE-CONTRACTS.md#written-applications),
`tools/type-probe.mts`): the checker offers no operation instantiating a
declaration's syntax. This is a stopgap, to be either relaxed or checked.
Relaxed: where TypeScript's API offers a direct checker endpoint for
instantiation and `keyof` (a declaration, its arguments, a parameter's
instantiated bound or default), it replaces the helper declarations and
their resolution checks. Checked: a source-type elaborator whose reductions
Lean checks, from declaration-linked bounds and completed arguments to the
semantic types, so that the correspondence to TypeScript's computation is
proved rather than trusted. Either retires the clause of the trust surface's
TypeScript row stating that "a computed form naming a declaration's
parameters, at an application, means what the checker computes for a probe
declaration" ([trust surface](docs/DESIGN.md#trust-surface)); the checked
form retires the computation's trust altogether, the relaxed one only the
probe's correspondence to the application.

<a id="the-any-check-over-external-declarations"></a>
**The any check over external declarations.** `tools/unchecked.mts` checks
the sources over external declarations whose every value-level `any` is one
opaque type (`tools/shadow-contracts.mts`). A declaration may rely on `any`
being at once a subtype and a supertype of every type, and the opaque type
is neither: the relations that `any` satisfied in an outside declaration are
not re-established, a limit the check states. The shadowed declarations do
not check (447 errors with `skipLibCheck` off, 2026-10-18), by class:

- an override or a heritage relation the base satisfies through `any` (367:
  2416, 2430, 2417, 2420), mostly Node's event emitters, whose base
  `listener: (...args: any[]) => void` an override narrows;
- a type argument meeting a constraint through `any` (49: 2344);
- a property meeting an index signature through `any` (25: 2411);
- a rest parameter `...args: any` (3: 2370), a predicate `x is any[]` over
  a parameter typed `any` (3: 2677).

An invalid declaration changes what TypeScript decides about the sources:
`f(new D())` with overloads at `B` and `D` and `D extends B` broken selects
the other overload. The same class holds the type computations the
substitution changes: `any extends string ? string : number` becomes
`number` (written: `string | number`), a type parameter's default `any`
read as `unknown` accepts every input (`Sink<T = any>`), and `A["missing"]`
over an opaque `A` is the error type inside a member. Each is a line of
`tests/unchecked-project/gaps.mts`, accepted under the stated limit. Replacing `any` by `unknown`
at a result and `never` at a parameter keeps the relations of a parameter
and a result but not of a writable property or a type argument, whose
variance the declaration's syntax does not show; no one substitution keeps
every relation `any` satisfies.

`JSON.stringify` of a function, or of an object whose `toJSON` returns
`undefined`, is `undefined` under Node, and the check types it `string`
(`gaps.mts`). Read at the overlay's `JsonValue` (primitives, read-only
arrays and string-indexed records of them, library-globals.mts), 56 calls of
the sources stringify a value that is no `JsonValue` (2026-10-19; 84 before
`JsonValue` held arrays): a value typed `unknown` (`claim-text.mts`,
`diagnostic-view.mts`), or a record a declaration types by its fields (the
Fragment, claims and flow documents, a `tsconfig.json`'s object), which
[JSON records by their fields](#json-records-by-their-fields) would admit.

<a id="nodes-process"></a>
**Node's process.** Every global is read through reviewed entries
([Node's process](docs/SOURCE-CONTRACTS.md#nodes-process)). Two forms stay
outside:

- **The environment write.** `runRoot` writes `process.env[k] = s`, a key
  `env` may not hold, visible through every alias of the object
  (`node-process-env-write`, a gap). The model's key addition is typed only
  on a local's own fresh object, a copy no other reference sees; it cannot
  justify a key visible through existing aliases. The obligation: represent
  mutable host lookup through shared state, with read and write contracts
  preserving every exported view. The operation then designed: a
  receiver-bound host setter with `env` as its audited instance, taking a
  primitive string key and value, its footprint `{value: any, store: keep}`
  on normal return, exceptions unrestricted, promising no later read equal to
  the string written (invalid names, NUL handling and platform
  normalization unaudited); the assignment lowered as receiver, key and value
  once, in order, the setter, and the saved value as the assignment's. Its
  controls: a new key and an overwrite observed through an earlier alias,
  stale narrowings refused, array density kept, `undefined`, objects and
  symbols refused with Node's coercions run, prototype-sensitive keys, fake
  receivers, mutable-view exports and forged setter claims refused.
- **Events known only as strings.** A `for...of` over an array literal of
  signal names gives each a `string`, not proven an admitted signal, so its
  registration is refused (`collections-process`, `collections-main`, gaps,
  both verified before the review).

<a id="json-records-by-their-fields"></a>
**JSON records by their fields.** A record a declaration types by its fields
(an interface, a type literal) is no `JsonValue`: a record is open, and an own
string key it does not declare may hold a `toJSON` (`invalid-json-stringify-record`,
run under Node). Admitting one needs a bound on all of its own string keys:
each a declared field whose present value is a `JsonValue`, an ordinary data
property, over a safe prototype; established where the record is built or
validated and kept through its mutations and through external calls; and a
policy for an optional field, absent or present at `undefined`.

<a id="the-front-ends-own-functions"></a>
**The front end's own functions.** Each top-level function of `tools/*.mts`,
sliced into its own file with the same-file declarations it uses, is a piece
of ordinary TypeScript the pipeline can be asked about: 337 of them. A slice
stops at its first refusal, so each blocker below hides the ones behind it.
The first blockers, by the number of slices each stops (2026-10-18; the
first three items 2026-10-19):

- a host guard answering `false`, which narrows nothing while the guard is
  read at its declared `x is T` signature
  (`compiler-api-guard-false-branch`): 18 slices of
  `fragment-statements.mts` read `elements` of a `BindingName` after
  `if (ts.isIdentifier(node)) return …`, and `knownLocal` reads `name`
  after `!ts.isSpreadAssignment(parent)` (2026-10-19, 829513e); the
  [host-guard rule](docs/COMPILER-API.md#guards) reads the call as a kind
  test refining both edges, and waits on guard recognition;
- a member read through a host node's member a test refined,
  `ts.isIdentifier(m.name) && m.name.text` (7: `staticFieldOf`,
  `staticMethodOf`, `hasInstanceClass`, `hasInstanceAlong`, `localArrow`,
  `memberOf`, and `moduleFunction` through `memberMayBeWritten`;
  2026-10-19, 829513e): a promise refines a name alone; the
  [read-equality rule](docs/HOST-FAMILIES.md#stable-members), a design,
  refines the path;
- a contextual parameter typed `(node: TypeNodeBase) => TypeTerm` (17), the
  slices of `type-term.mts` past their optional method calls;
- a callback's parameter written without a type is read at its contextual
  type, records, indexes and aliases without parameters included; no slice
  stops there;
- library globals absent from the overlay or refused (4, 2026-10-19):
  `Reflect` ([refused](docs/SOURCE-FRAGMENT.md)) (3) and `Object.hasOwn`; the
  slices `parseInt`, `Object.fromEntries`, `Array.from`, `Math.ceil`,
  `new RegExp` and `instanceof Error` stopped now stop later, at a class
  extending a class of the file (4), `Object.hasOwn`, a `Stream` declaration,
  a type alias statement, an `in` test, and the search (2);
- members of `Type` and `Checker` outside their named views (10);
- the sync API's `API` class, whose type parameter has a default (8);
  `createRequire`, whose type names a qualified one (1); `node:path`'s
  `sep`, a constant of the object the module exports (2); a default import
  (5);
- the compiler's synchronous API failing on a query (1), reported as a tool
  failure: `TypeObject.getTypes` panics converting a type reference to a
  tuple (`forInEntryReads`);
- the parser exceeding the call stack (2: `readDiagnostic`, and
  `diagnosticNode`, which another run reports as a reply of
  `Checker.getTypeFromTypeNode` the client cannot decode), cause unknown.

Of the 341 slices (2026-10-19, cb0d236), 82 fail in the producer and 69
in search; of the drivers' 48, 4 and 8. By the judgment that fails:

- reading a compiler node's member after a `ts.isX` guard or a `.parent`
  walk (the producer's "missing field": 55; in search, `forEachChild`,
  `.parent` and guard edges: about 25), and a `let` holding nodes read after
  a test (6): the compiler-node narrowing the host-families work covers;
- a user guard's promise not established by its body (`isObject`,
  `isRecord`: 9) and the reads it would narrow (about 16, `atom.required` in
  `claim-text.mts` among them), and guard closures with binders (5): guard
  recognition;
- a read of a key `in` found on an open object (4, and 2 drivers): the
  [proposal](docs/PROGRAM-TYPING.md) under review;
- a spread of a narrowed union member or a type parameter (5);
- `Number` both called and read through its members, a callable with
  readonly members no clause states (4), and the enum helpers past it (3);
- a call through a union of arrows none of which all arguments call (2, and
  2 drivers); key-adding writes through a parameter (`gate.bindings`,
  `process.env`: 2, and 2 drivers); reads at keys an inherited member may
  name (2); singletons.

Of the 24 of `dev/`, the record tools and the lowering dump, all 24 (2026-10-18), each
sliced with the same-file declarations it uses, their imports from
`record-render`, `control-flow` and `calculus` certified. `printGraph`'s
evidence search covers `decodeTerm`, which `decodeNode` reads, and takes
48 s of wall time on a machine at load 27, near the 60 s step limit; four
slices run at once exceed it (2026-10-18). `control-flow.mts` verifies
whole.

Of the 35 functions of `pipeline/*.mts`, `keepRunDirectories` and
`typeScriptErrors` verify; of the 13 of `tests/`, `docs.mts`'s six and
`rule-inventory.mts`'s `withoutBlockComments` and `alternatives`
(2026-10-19, the slices of `tests/` with `pipeline/*.mts` beside them).
Their first blockers, by the number of slices each stops:

- Node functions outside the reviewed overlay of library modules, whose
  declarations reach `Buffer` and, through `BufferConstructor`, a
  conditional type over a signature's own binder (`ImplicitArrayBuffer`),
  computed only at an instance (5): `spawnSync` and `readdirSync` with
  `withFileTypes`;
- written applications: `Pick` over a generic interface (3) and
  `ReturnType<typeof run>` (2);
- the global `setTimeout` (4), a generic function merged with a namespace;
- Node's global `structuredClone` (3), a generic function;
- a key-adding write to `process.env` (2);
- `import.meta`, `new Array(n)`, a mapped type over `Readonly` and a record at
  an index signature (1 each);
- the producer or the search (15), each a separate investigation, among them
  the two `must` helpers, whose `assert.ok` takes a message that is no literal
  and so narrows nothing.

`node:assert/strict`'s `equal` promises its actual is the expected value only
in its declaration: the promise is generic, and the producer encodes no
generic promise signature ("quantified callable claim encoding"), which a
program's own generic assertion function meets too (`node-assert-equal-promise`,
a gap).

`readFragmentFile` and `readClaimsFile` in `pipeline/verify-source.mts` read
back a document the run wrote, for a test to forge, and assert its type with
`as` (reason at the assertion) rather than decode it: no TypeScript decoder
of the Fragment or the claims document exists, and the tests reach about 100
fields deep in them. The two stay outside the goal by decision; what they
read is decoded again by Lean before anything is checked.

Two forms of the record tools are rewritten for a verifier limit, not
for a departure from the fragment; each rewrite is reverted when its limit
lifts: element reads the code already guards by a test of the same element
(`mathRoles`' `afterRelation` and `textWord`, `docs.mts`'s `numbered`;
`guarded-element-read-refused`);
and a `flatMap` callback returning a string (`card`;
`flat-map-scalar-result-refused`).

The goal is every function of the repository's own TypeScript verified:
`tools/`, `pipeline/`, `tests/` and `dev/`, about 21,000 lines (the sources
under `pipeline/examples/` are the cases' inputs, many refused by design).
Verification states safety, each function's annotated contract at every
call, not that the parser reads TypeScript correctly. A scan of that code
against the fragment (2026-10-16) gives the work, each item its own design:

- **The compiler API.** About 120 functions read TypeScript's syntax tree
  through `typescript/unstable/ast` and its checker through
  `typescript/unstable/sync`; [the compiler API](docs/COMPILER-API.md)
  specifies the contract they are verified under. Its implementation waits
  on [guard recognition](docs/HOST-FAMILIES.md#guard-recognition),
  [stable members](docs/HOST-FAMILIES.md#stable-members) and guard
  signatures for the sync API's type guards; a generic method called on a
  node, `forEachChild<T>`, is refused.
- **Guard signatures.** A guard's promise is part of its function type,
  proved at its definition and consumed at a call, for any promised type
  and across modules.
- **Bounds of every alias application.** An alias with a bounded parameter
  keeps the obligation that its arguments meet their bounds, whatever its
  body.
- <a id="regular-expressions-left"></a>**Regular expressions left.** A
  literal, `exec`, `test` and the string methods dispatching to a regex are
  admitted ([regular expressions](docs/SOURCE-CONTRACTS.md#regular-expressions)).
  Left: a replacement callback, whose argument list follows the shape
  (`(match, p₁ … pₙ, offset, input[, groups])`, every match collected before
  the first call, its result a string); `new RegExp(p, f)` of strings, a
  native regex of the conservative shape; a regex's properties, `lastIndex`
  (own, not enumerable, a number) and the accessors `source` and `flags`,
  read through reserved host-relative members so that no record view states
  them, with `in`, patterns and computed reads of their keys accounted for;
  a loop over a structural iterator TypeScript types `RegExpStringIterator`,
  through the iterator protocol; and the same native mark on `SetIterator`
  and `MapIterator`, whose loops are chosen by TypeScript's type alone.
- **The library globals left.** `Array.prototype.flatMap` (79 calls) and
  `flat`, `String.prototype.match`, `matchAll`, `padEnd`, `padStart` and
  `search`, `Object.fromEntries`, `hasOwn` and `assign`, `Array.from`,
  `Math` but `max` and `min`, `parseInt`, and `JSON.stringify` of an
  object, whose `toJSON` runs client code.
- **Node's modules.** `node:fs`, `path`, `child_process` (`spawnSync`,
  `execFileSync`, `fork` and its messages), `os`, `crypto`, `vm`, `net`,
  `module`, `assert/strict` (assertion functions) and `process`.
- **Classes and `this` parameters.** The parser's `Gate` class, the functions
  of `fragment-*.mts` declaring `this: Gate` (198 reads of `this`), and the
  error classes extending `Error`.
- **Imports between the repository's modules.** Default imports, and a
  value imported from another module certified against its signature, which [module composition](#module-composition) proves sound.
- **The code's own departures from the fragment.** Downcasting `as`
  assertions and module-level `let`: the code changes to meet the fragment.
- **Proof precision.** Of the slices past the gate, about half fail in
  proposal or search; each failure is a separate investigation.

