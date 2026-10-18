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
| [Footprints](#footprints) | open: the seven programs decided (2026-10-17) | every application form and array element writes have a checked bound |
| [Keys known only at run time](#keys-known-only-at-run-time) | open | the writes listed there are typed |
| [Module composition](#module-composition) | open: certified imports designed (2026-10-17), the design revised and approved (2026-10-18) | a Lean theorem composes units certified against each other's signatures |
| [Cell facts by tag, and label slices](#cell-fact-slices) | open: label slices and reads by a record field's or a dictionary entry's tag done (2026-10-18); `decodeTarget` passes an imported function as a callback | `decodeTarget` and `showTag` in `calculus`/`control-flow` verify in their modules |
| [Decoders' dictionary reads](#decoders-dictionary-reads) | open: the decoders take parsed JSON (2026-10-18); in `calculus` 12 of 15 functions verify, and `decodeTerm`, `decodeCode` and `termsOf` verify in 29 s of evidence search, near the 30 s limit (2026-10-18); their time waits on shape-directed comparison of discriminated unions | the decoders of `calculus`/`control-flow` verify in their modules within the limit |
| [Lexical bindings before initialization](docs/SOURCE-MODEL.md#lexical-bindings-before-initialization) | open: designed and approved (2026-10-18) | a closure reading a constant declared after it verifies, and a read before the declaration runs throws at its location |
| [Module cells](docs/SOURCE-MODEL.md#module-cells) | open: designed (2026-10-18) | a module-level `let` read and written by module functions verifies, a read before its initialization throws |
| [Optional-field truthiness over unions](#optional-field-truthiness) | open: an investigation, cause unknown | `optional-field-truthiness-union-refused` verifies |
| [Exceptional footprints](#exceptional-footprints) | open: handler facts across a throw | a call's footprint on a throw carries an effect through a handler, with `checkJson_safe` concluding it |
| [Iteration left open](#iteration-left-open) | open | the iteration forms listed there are lowered |
| [Remaining source forms](#remaining-source-forms) | open | the forms listed there are admitted |
| [Model limits of one form each](#model-limits-of-one-form-each) | open | each limit listed there has its model support |
| [Precision](#precision) | open | the facts listed there are derivable |
| [A semantics of the Fragment](#a-semantics-of-the-fragment) | open | extraction is proved a simulation of a Lean interpreter of the Fragment |
| [Regular expressions left](#regular-expressions-left) | open | replacement callbacks, `new RegExp`, a regex's properties and structural match iterators are admitted, and `SetIterator` and `MapIterator` loops require the native mark |
| [Computed types evaluated through helper declarations](#computed-types-evaluated-through-helper-declarations) | open: a stopgap | the helper declarations are replaced by a checker endpoint (relaxed), or TypeScript's computation is checked by a source-type elaborator in Lean (checked) |
| [The front end's own functions](#the-front-ends-own-functions) | open: 80 of 313 verify in `tools/` (2026-10-18, at a 60 s step limit), 21 of 24 in `dev/` (2026-10-18) and 4 of 13 in `tests/` (2026-10-17) | the blockers listed there are admitted or refused by a stated restriction |

### Open work

<a id="a-connection-to-ecma-262"></a>
**A connection to ECMA-262.** Proving the host's stated types as lemmas of a
mechanized specification would turn the ECMA rows of the trust surface into
theorems; the lemmas and their cost are in
[TRUST-REDUCTION](docs/TRUST-REDUCTION.md#the-host).

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
- an array element write has no bound; the fragment writes elements only at
  proved index singletons, and no measured program needs one.

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
[Certified imports](docs/SOURCE-MODEL.md#certified-imports), over acyclic
module graphs, check an imported function's code in the importer's run, at
its effect-qualified signature. `checkJson_safe` keeps its statement.
Combining a certified import's conclusion with the importer's is left to
this theorem, plus the review obligation that the import binds the certified
unit's closure ([the linking obligation](docs/SOURCE-MODEL.md#certified-imports)).

<a id="cell-fact-slices"></a>
**Cell facts by tag, and label slices**
([the design](docs/PROGRAM-TYPING.md#current-content-rules-semantic-layer)):
a sliced read by any heap-independent tag, and the labels of an object a
cell fact about its field excludes. A dictionary's entry takes facts as a
record's field does (`dictionary-field-tag-read`). `decodeTarget` passes
`nat`, imported from `calculus`, to `map`
([module composition](#module-composition)).

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
the 172 checks (a probe, 2026-10-18). These functions wait on
[structure-directed comparison](docs/UNION-SHAPES.md). `dev/lowering-dump.mts`
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

<a id="remaining-source-forms"></a>
**Remaining source forms.** A method call on a union of primitives,
which needs one callee contract its receiver meets. A source binder used both
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
bounds, in a prototype member's scheme.

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

<a id="the-front-ends-own-functions"></a>
**The front end's own functions.** Each top-level function of `tools/*.mts`,
sliced into its own file with the same-file declarations it uses, is a piece
of ordinary TypeScript the pipeline can be asked about: 313 of them. A slice
stops at its first refusal, so each blocker below hides the ones behind it.
The first blockers, by the number of slices each stops (2026-10-18):

- a missing annotation, or a value TypeScript types `any` or an
  anonymous record (75);
- library globals absent from the overlay or refused (10): the global
  function `parseInt` (3), `Reflect` ([refused](docs/SOURCE-FRAGMENT.md))
  (3), `Array.from`, `Object.fromEntries`, `new RegExp`, `instanceof Error`;
- a closure reading a constant declared after it (18), refused as a
  temporal-dead-zone read though the closure runs after the declaration;
  where the gate admits it, the producer fails on the unbound name
  (`localValues`, `letWrites`);
- an object built with a `then` member (12);
- members of `Type` outside its named view (11);
- module-level `let` and `var` (8); `node:path`'s `sep`, a constant of the
  object the module exports (2); a default import (3);
- the compiler's synchronous API failing on a query (3), reported as tool
  failures: `TypeObject.getTypes` panics converting a type reference to a
  tuple (`forInEntryReads`), and `Checker.getTypeAtLocation` and
  `Checker.getTypeFromTypeNode` return a reply the client cannot decode
  (`readDiagnostic`, `diagnosticNode`), cause unknown.

Twenty-nine slices reach the producer and fail there, and 48 fail in search;
`termsOf`, `decodeCode` and `decodeTerm` verify within the 60 s limit. Of the 13 functions of `tests/`, 4 verify (2026-10-17), and of the
24 of `dev/`, the record tools and the lowering dump, 21 (2026-10-18), each
sliced with the same-file declarations it uses. The first blockers of the others in
`dev/`, with the functions each stops directly and through callees:

- `group`'s range branch reads the second element of `arg.split("..")`,
  which the model types `string | undefined`: the `arg.includes("..")` test
  before it, which makes the element present, states no fact about the
  split's length (group: 1);
- in printGraph, `program.map(decodeNode)` passes an imported function as a
  callback, which a signature binding more parameters may call with further
  actuals; only a module function's own code is known to discard them
  ([module composition](#module-composition)), and so is `showTerm`, which a callback calls. A certified import of
  either needs its module's code to verify. In `control-flow` and
  `calculus` (2026-10-18), 12 of 18 functions verify, `showTag`, `showTerm`
  and `showCode` among them; `decodeTarget`, `decodeContinuation` and
  `decodeNode` pass `nat`, imported from `calculus`, to `map`, and
  `decodeTerm`, `decodeCode` and `termsOf` exceed the time limit
  ([decoders' dictionary reads](#decoders-dictionary-reads)) (printGraph: 1);
- `decodeUnits` calls `fields` and `nat`, imported from `calculus`, in
  `map` callbacks, which an import's ordinary signature makes sparse
  ([module composition](#module-composition)) (decodeUnits: 1).

In `tests/`, `docs.mts`'s `withoutCode`, `prose`, `slug` and `compare`
verify; the others stop at a namespace import, Node's `Buffer` type, `join`
of `node:path`, `Number` read as a value, or a top-level block.

Two forms of the record tools are rewritten for a verifier limit, not
for a departure from the fragment; each rewrite is reverted when its limit
lifts: element reads the code already guards by a test of the same element
(`mathRoles`' `afterRelation` and `textWord`; `guarded-element-read-refused`);
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
  on reading rules 2 and 4 and the node invariant (the restricted-value
  policy and `NodeList` hold), a compact
  representation of kind sets in claims and evidence, and guard signatures
  for the sync API's type guards.
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

