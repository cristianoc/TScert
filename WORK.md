# Verification work

The work ledger of the independent verifier: each open item, why it is open
and when it closes. [DESIGN](docs/DESIGN.md) states the architecture and
decisions; [the source boundary](docs/SOURCE-FRAGMENT.md) owns the
supported-fragment restrictions.

## Status

Progress is recorded here and nowhere else. A commit that moves an item
updates its row, and a closed item's row and prose are deleted: the commit
record keeps what it did. The prose under [open work](#open-work) describes
each item's design and evidence, not its progress.

| Item | State | Closed when |
| --- | --- | --- |
| [Coverage of the front end](#the-front-ends-own-functions) | open: the census of 3a6d2c0 at a 300 s step limit verifies 156 of 441 functions of `tools/`, 1158 of 12150 statements (9.5%), with no timeout (2026-10-23); 24 of 24 functions of `dev/`, 9 of 13 of `tests/` and 3 of 37 of `pipeline/` (2026-10-19, 60 s step limit) | every function of `tools/`, `dev/`, `tests/` and `pipeline/` verifies or is refused by a stated restriction |
| [Decoders' dictionary reads](#decoders-dictionary-reads) | open: in `calculus` 12 of 15 functions verify; `decodeTerm`, `decodeCode` and `termsOf` verify in 10.0 s of evidence search with candidate selection and the answered requests threaded through the document's search, 25.2 s without any reuse (user time, median of 3, 2026-10-19) | the decoders of `calculus`/`control-flow` verify in their modules within the limit |
| [The search of `protocolPattern`](#fragment-statements-search-meets) | open: 73 s of CPU alone on dca7c93's artifacts; in the census of both slices at a 600 s limit each search takes 73 s (2026-10-22) | `fragment-statements.mts#protocolPattern` and `#patternStmt` finish their search within 30 s alone |
| [Stated type guards of the sync API](#stated-type-guards) | open | a unit calling `isUnionType` and the `this is X` methods of `Type` it uses verifies at the contract's stated promises |
| [The sync API's checking wrapper](#sync-api-checking-wrapper) | open | `make suite` runs the front end's sync-API calls through the wrapper C5 describes |
| [The compiler API's full shape check](#compiler-api-shape-check) | open | C3 checks every member and child kind over the corpus it names, the absent required members exactly the corrections |
| [Enum-member case labels](#enum-member-case-labels) | open | `switch-enum-case-narrowing` verifies |
| [Slices of the value universe](#universe-slices) | open: a design | `typeof v === "object" && v !== null` narrows `unknown`, and the guards over `unknown` promise what their tests establish |
| [A key found on an open object](#key-on-open-object) | open: a design | `if (typeof v === "object" && v !== null && "k" in v) return v.k` verifies, with the lookup invariant proved |
| [A guard's promise on a field](#guard-promise-field) | open | `str(o.name); o.name.length` verifies: an assertion or a guard on a field narrows the field's current content |
| [A guard's answer held in a constant](#guard-answer-constant) | open | `const ok = isRecord(v); if (ok) return v;` verifies |
| [Guard overloads beyond `filter`'s](#guard-overloads) | open | `shadow-contracts.mts`'s `print`, which reads its array at `string[]` after `every` answers `true` at a guard, and `filter-guard-value-refused` verify |
| [A conditional's join past an arm's read](#conditional-optional-field) | open | `o.v != null ? o.v : ""` and `o.v !== undefined ? o.v : null` with `o: { v?: string \| null }` verify |
| [Investigation of generic equality in a condition](#generic-equality-condition) | open: an investigation, cause unknown | `if (left !== right) return 1;` with `left, right: T` verifies, as `return left !== right` does, and the Boolean-return lowering applies to every function's return |
| [Investigation of a negated first read of an element](#negated-first-read) | open: an investigation, cause unknown | `const d = list[0]; if (!d.initializer) return -1;` over a program record verifies |
| [Investigation of a literal guard over `JsonValue \| undefined`](#literal-guard-json-read) | open: an investigation, cause unknown | `guard-literal-json-read-refused` verifies |
| [Investigation of a field written before a spread of a literal arm](#field-before-literal-arm) | open: an investigation, cause unknown | the cause of `object-spread-field-before-literal`'s refusal is established, with a reproducer and a concrete repair obligation |
| [Investigation of an alias of function types met with a record](#callable-alias-meet) | open: an investigation, cause unknown | `spread-intersection-callable-alias` verifies |
| [Investigation of a member two intersection operands state](#meet-member-disagreement) | open: an investigation, cause unknown | the cause of `path-test-intersection-disagree`'s refusal is established, with a reproducer and a concrete repair obligation |
| [Investigation of assigned parameters with defaults](#assigned-parameters-with-defaults) | open: an investigation, cause unknown | the cause of the producer's "assignment to immutable binding" refusal is established for both function declarations and closures, with a reproducer for each and a concrete repair obligation |
| [Constructor rests](#constructor-rests) | open | a constructor with a rest parameter is constructed and its variadic construct signature introduced |
| [Class offers across units](#class-offers-across-units) | open | a module class passed by a module function to a variadic construct signature verifies |
| [Generic methods left](#generic-methods-left) | open | `class-generic-method-bounded-refused` verifies, and members binding different numbers of binders relate |
| [Contract completeness](#restoring-completeness) | open | effect inference covers the rest wrappers, call forms and nested heap operations it is conservative for |
| [Effects of dispatched calls](#effects-of-dispatched-calls) | open | a method call on a union with a primitive's shape is dispatched and `split-non-empty` verifies |
| [Footprints](#footprints) | open: the seven programs decided (2026-10-17) | every application form has a checked bound |
| [Exceptional footprints](#exceptional-footprints) | open: handler facts across a throw | a call's footprint on a throw carries an effect through a handler, with `checkJson_safe` concluding it |
| [Class methods' effects](#class-methods-effects) | open: the draft's design accepted by the owner (2026-10-23): D1 (a), stated effects, and D2–D6 as the draft recommends | callbacks calling a class instance's methods use effects stated with `Within<…>` and certified in each definition's own module |
| [Async and generator code](#async-and-generator-code) | open | an async function's entry and resumption are checked by an asynchronous entry judgment, and `%Await%`, `%AsyncReturn%` and `%AsyncComplete%` leave the trust surface |
| [Function declarations in bodies](docs/SOURCE-MODEL.md#lexical-bindings-before-initialization) | open | `function-declaration-in-body-refused` verifies: a function declared in a body is created at its block's entry, and a call of it before the block's bindings are initialized reaches their checked accesses |
| [Iteration left open](#iteration-left-open) | open | the iteration forms listed there are lowered |
| [Keys known only at run time](#keys-known-only-at-run-time) | open | the writes listed there are typed |
| [Remaining source forms](#remaining-source-forms) | open | the forms listed there are admitted |
| [Model limits of one form each](#model-limits-of-one-form-each) | open | each limit listed there has its model support |
| [Regular expressions left](#regular-expressions-left) | open | replacement callbacks, a native regex from `new RegExp`, a regex's properties and structural match iterators are admitted, and `SetIterator` and `MapIterator` loops require the native mark |
| [JSON records by their fields](#json-records-by-their-fields) | open | a record bounded on all its own string keys meets `JsonValue`, built or validated and kept through mutation and external calls |
| [Node's process](#nodes-process) | open: the environment write a located gap; events known only as strings refused | a write of `process.env` through a receiver-bound host setter over shared state preserving every alias's view; signals reached through iteration proven admitted |
| [Precision](#precision) | open | the facts listed there are derivable |
| [Module composition](#module-composition) | open: certified imports checked, their units' composition reviewed (2026-10-18) | a Lean theorem composes units certified against each other's signatures |
| [A semantics of the Fragment](#a-semantics-of-the-fragment) | open | extraction is proved a simulation of a Lean interpreter of the Fragment |
| [A connection to ECMA-262](#a-connection-to-ecma-262) | open | the host's stated types are lemmas of a mechanized specification |
| [Computed types evaluated through helper declarations](#computed-types-evaluated-through-helper-declarations) | open: a stopgap | the helper declarations are replaced by a checker endpoint (relaxed), or TypeScript's computation is checked by a source-type elaborator in Lean (checked) |
| [The any check over external declarations](#the-any-check-over-external-declarations) | open: a stated limit, relations that `any` satisfied in an outside declaration are not re-established; 447 errors in the shadowed declarations (2026-10-18) | a check re-establishes the relations and `tests/unchecked-project/gaps.mts` is refused |
| [Structure-directed comparison's lemmas](#union-shapes-lemmas) | open: proved outside the repository against 84b326a | the lemmas UNION-SHAPES states are Lean modules of `lean/Verification/Types/`, checked by the build |
| [Selected discovery and the rerun](#union-shapes-discovery) | open | the selected search is proved to find every certificate the full search finds, and the rerun is removed where that theorem applies |
| [Selection rules the data names](#union-shapes-candidates) | open | R6, R7, open target arms and shared literals each have a rule with its lemma, or a measurement shows it unneeded |
| [Observed stages beyond macOS](#observed-stages-beyond-macos) | open: the parse and TypeScript's diagnostics replay on macOS only | the compiler's reads are confined and observed on Linux, and the stages replay there |
| [Verification server](docs/drafts/verification-server.md) | a draft; D1–D7 open, kept as a draft by the owner (2026-10-23) | per-function verdicts on real files over the stage store, replacing census slicing |

## Open work

<a id="next-steps"></a>

### Coverage of the front end

<a id="the-front-ends-own-functions"></a>
**The front end's own functions.** The goal is every function of the
repository's own TypeScript verified: `tools/`, `pipeline/`, `tests/` and
`dev/` (the sources under `pipeline/examples/` are the cases' inputs, many
refused by design). Verification states safety, each function's annotated
contract at every call, not that the parser reads TypeScript correctly. The
census slices each top-level function, with the same-file declarations it
uses, into a file of its own and runs it through the pipeline
([measuring coverage](AGENTS.md#measuring-coverage-once-on-main),
[statement coverage](docs/DESIGN.md#statement-coverage)). A slice stops at
its first refusal, so each blocker hides those behind it.

The first refusals of the 285 slices of `tools/` that do not verify in the
census of 3a6d2c0 (300 s step limit, 2026-10-23): 133 at the gate, 26 in
the producer and 126 in search.

- At the gate: `node:path`'s `sep`, a constant of the object the module
  exports (27); Node's declarations reached through `Buffer`,
  `TextDecoder` and `createHash`'s `TransformOptions`, among them the
  written application `Buffer<ImplicitArrayBuffer<…>>`, a conditional type
  over a signature's own binder (25); members of the sync API's `Type`,
  `Checker` and `Symbol` outside their named views, `isUnionType` among
  them ([stated type guards](#stated-type-guards); 16); a mapped type over
  `Readonly` naming its key (13); `process.platform`, outside the reviewed
  globals (6); an annotated destructuring pattern (6); the sync API's `API`
  class, whose type parameter has a default, and a conditional type over a
  type parameter in its declarations (10); an `instanceof` whose right
  operand is no class of the file (3); `Reflect` and
  `Object.getPrototypeOf` (3).
- In the producer: a read through a field holding an object beside `null`
  or `undefined` (8); a key read after an `in` test on an open object
  ([a key found on an open object](#key-on-open-object); 5); a member a
  test did not narrow ("missing field", 5).
- In search: an edge that does not establish the claims at its target (53);
  an expression's node-typing claim (20) or return-contract claim (8); a
  closure lowered differently under one of its signatures (8); a closure's
  expression claim (7) or signature claim outside its annotation (6); an
  assignment to a binding that is no mutable local
  ([assigned parameters with defaults](#assigned-parameters-with-defaults);
  6); a guard's promise not met at a return (5); `Number`, a callable with
  members (4).

Of `pipeline/*.mts` and `tests/` (2026-10-19, 60 s step limit), the first
blockers are Node's `Buffer` through `readFileSync` and `spawnSync` without
an encoding, the worker's socket (`Duplex`, a member the checker
synthesises), a member read after `assert` narrowed a union, key-adding
writes to `process.env`, and the producer or the search, each a separate
investigation, among them the two `must` helpers, whose `assert.ok` takes a
message that is no literal and so narrows nothing. `node:assert/strict`'s
`equal` promises its actual is the expected value only in its declaration:
the promise is generic, and the producer encodes no generic promise
signature ("quantified callable claim encoding"), which a program's own
generic assertion function meets too (`node-assert-equal-promise`, a gap).

`readFragmentFile` and `readClaimsFile` in `pipeline/verify-source.mts` read
back a document the run wrote, for a test to forge, and assert its type with
`as` (reason at the assertion) rather than decode it: no TypeScript decoder
of the Fragment or the claims document exists, and the tests reach about 100
fields deep in them. The two stay outside the goal by decision; what they
read is decoded again by Lean before anything is checked.

<a id="decoders-dictionary-reads"></a>
**Decoders' dictionary reads.** The decoders of `calculus.mts`,
`control-flow.mts` and `diagnostic.mts` read the wire as `Json`, what
`JSON.parse` returns without a reviver
([the contract](docs/SOURCE-CONTRACTS.md#library-globals)): a parsed object
is a dictionary of parsed data, read by key as the index's value or
`undefined`, and a key it may inherit from `Object.prototype` is refused
(`invalid-json-parse-inherited`). A constructor object's one key and its
value are `Object.entries`' pair, so no read at a key known only at run
time is needed. The search time of `termsOf`, holding `decodeTerm` and
`decodeCode`, is in image-equivalence checks of an instance of the array
prototype's scheme against the claim's `Term[]` row, whose cost is the
structural comparison of the recursive `Term` and `Json` union arms beneath
([structure-directed comparison](docs/UNION-SHAPES.md); measured
2026-10-18). `dev/lowering-dump.mts` decodes the verifier's output with
`decodeUnits`, which calls `fields` and `nat` in `map` callbacks: imported
functions, whose effect no certificate states
([module composition](#module-composition)).

<a id="fragment-statements-search-meets"></a>
**The search of `protocolPattern`.** On dca7c93's artifacts the slice of
`fragment-statements.mts#protocolPattern` refuses at `assignedNames` after
73 s of CPU in its search stage alone (2026-10-22). About half of it is the
graph search's subtype comparisons (table growth, coverage of the greatest
fixed point, the kernel's check of it, and image checks of candidate
instances), a sixth is lowering, a seventh is the expression claims'
search, and a sixth is checking the graphs' certificates, of which half is
one instance's image table, checked again at each of 264 evidence nodes
that cite it.

### The compiler API's contract

[COMPILER-API](docs/COMPILER-API.md) states the contract the front end's
calls of TypeScript's compiler API are verified under. Three of its pieces
are designs no code implements.

<a id="stated-type-guards"></a>
**Stated type guards of the sync API.** The `this is X` methods of `Type`
and the sync functions `isTupleType`, `isTypeReference` and `isUnionType`
test bits of `flags` and `objectFlags`, so they are no kind tests; the
contract states, for each one a unit uses, the promise and the members of
`X` it covers, with the declaration text reviewed
([views and stated type guards](docs/COMPILER-API.md#the-sync-api), T7).
Consuming them needs, of guard signatures: an imported guard function whose
promise a contract states, carried in the function type through the import
and through a namespace member read, narrowing an immutable binding
argument at the call; a `this is X` method, a member promise about the
receiver, consumed at `t.isUnionType()` with `t` an immutable binding; a
promise over an object type `X`, the refinement a meet with `X`; and the
provenance of a stated promise in the evidence, so that a promise from
`compiler-api.mts` appears in the trust report. `hostViews` reads the
`this is X` methods as members outside `Type`'s view until then.

<a id="sync-api-checking-wrapper"></a>
**The sync API's checking wrapper (C5).** During `make suite`, the front
end's calls into the sync API run through a wrapper that compares each
result with its declared type and, after each stated type guard returns
`true`, calls the members its promise covers; the lifetime controls run
under Node ([binding the contract](docs/COMPILER-API.md#binding-the-contract-to-the-implementation)).

<a id="compiler-api-shape-check"></a>
**The compiler API's full shape check (C3).** `make compiler-api-shapes`
checks the presence of each required property over its corpus. The check
as designed covers every node of `tools/*.mts`, `tests/*.mts`, `dev/*.mts`,
`pipeline/**/*.ts`, the standard library's `.d.ts` files and a JavaScript
file with JSDoc: each node has every member its shape states required,
every child within its member's declared kinds, and the absent required
members are exactly the corrections
([binding the contract](docs/COMPILER-API.md#binding-the-contract-to-the-implementation)).

<a id="enum-member-case-labels"></a>
**Enum-member case labels.** A `switch` whose `case` labels are enum
members (`case K.One:`, `case ts.SyntaxKind.SourceFile:`) narrows nothing in
the producer, where the same constants narrow in an `===` test and literal
labels narrow in a `switch` (`switch-enum-case-narrowing`, a gap). The
compiler API's code switches on `node.kind` this way.

### Guards and narrowing

<a id="universe-slices"></a>
**Slices of the value universe.** A tag test on a value at `unknown`
narrows nothing: `typeof v === "object" && v !== null` leaves `v` at
`unknown`. Every source value is of exactly one kind (`null`, `undefined`, a
Boolean, a number, a string, a bigint, a symbol, an object without call
code, or one with call code), so the source universe $`J`$ is the disjoint
union of the primitive clauses, $`J_{\mathrm{ref}}`$ and
$`J_{\mathrm{fun}}`$ ([the source-value boundary](docs/SOURCE-MODEL.md#source-value-boundary)),
and `tagHolds` of each shape tag is decided by the kind alone. The design:
where a test of a tag answers $`q`$ on a value at the `source` clause, the
value is at the union of the kinds whose members answer $`q`$, a primitive
kind its existing clause and $`J_{\mathrm{ref}}`$, $`J_{\mathrm{fun}}`$ new
clauses, the `source` clause restricted to the kind:

```math
\frac{\Gamma\vdash x:J\qquad \mathsf{typeof}\ x = \texttt{"object"}\ \text{answers}\ \mathsf{true}\qquad x\neq\mathsf{null}\ \text{answers}\ \mathsf{true}}
     {\Gamma\vdash x:J_{\mathrm{ref}}}\ \textsf{slice-object}
\qquad
\frac{\Gamma\vdash x:J_{\mathrm{ref}}\qquad \mathsf{Array.isArray}(x)\ \text{answers}\ \mathsf{false}}
     {\Gamma\vdash x:J_{\mathrm{ref}}\setminus\mathsf{arrays}}\ \textsf{slice-non-array}
```

$`J_{\mathrm{ref}}\setminus\mathsf{arrays}`$ is $`J_{\mathrm{ref}}`$ with an
own-key bound excluding the store key. The partition is a lemma of
`isSourceVal` and `tagHolds` by cases; a test's answer on a slot is a value
fact, so a call does not end it.

The slices do not give the dictionary view
`{ readonly [key: string]: unknown }`: a member of
$`J_{\mathrm{ref}}\setminus\mathsf{arrays}`$ may own a prototype (a class
instance) or be a host object (a `Map`, a `Date`), which pass the same
tests. A guard over `unknown` testing exactly those stays refused, and the
front end's readers test them over `JsonValue`
([source rewrites](docs/SOURCE-REWRITES.md#a-dictionary-guard-over-unknown)).
Reading a key after `"k" in v` on $`J_{\mathrm{ref}}`$ needs a rule of its
own,

```math
\frac{\Gamma\vdash v:J_{\mathrm{ref}}\qquad \texttt{"k" in } v\ \text{answers}\ \mathsf{true}\qquad v\ \text{no host object}}
     {\Gamma\vdash v.\mathtt{k} : J}\ \textsf{read-present}
```

sound where the calculus's read finds what JavaScript's does and every
source-keyed field of an object of $`J`$ holds a value of $`J`$ (the
`source` row's invariant, `sourceTy_exc`). Its premise "no host object" is
its limit: a host object's prototype holds accessors (`Map.prototype.size`)
that JavaScript runs and the calculus's read does not, and no test the
guards write establishes it. Source `object` holds classes, and `k in C` of
a class is refused (measured 2026-10-19), so a guard promising `object`
loses the slice its body tested. The guards over `unknown` in
`claim-text.mts`, `claim.mts`, `type-graph.mts` and `diagnostic-view.mts`
(6 slices refused at their promise, 3 more behind them) wait on the slices
and on their own promises.

<a id="key-on-open-object"></a>
**A key found on an open object.** A value that `typeof v === "object"`,
`v !== null` and `"k" in v` admit holds an object of an open record clause
$`c`$ stating no key $`k`$ and no bound excluding it; the test
$`\mathsf{hasKey}(k)`$ has no answer on $`c`$, and the read `v.k` TypeScript
then admits has no rule: the producer stops at "field read on non-object"
(5 slices of `tools/` in the census of 3a6d2c0). The proposed rule reads it
at $`\top`$:

```math
\frac{\Gamma\vdash v:c\quad c\ \text{an open record clause}\quad k\ \text{a string key}\notin\mathrm{objectProtoKeys}\quad c\ \text{excludes host values}}
     {\Gamma\vdash v.k:\top}\ \textsf{read-unstated}
```

It changes the model: it adds an invariant to what `checkJson_safe`'s
premise says about inputs. Under the current premises it is unsound: the
record meaning (`recT`) constrains the named fields only, so an unnamed key
may hold a location outside the heap, an unconstrained `[[proto]]` can
leave the lookup without a result, and a host object's property may be a
getter. The rule needs:

- a lookup invariant, part of the premise on inputs and preserved by every
  step: every object's field locations are valid heap locations and its
  prototype links lead through such objects, so a lookup of any key steps
  to a value; its preservation and the read rule proved in Lean;
- the plain-data caller assumption extended to the properties a value's
  type leaves unstated and to the prototype chain a read traverses;
- host values excluded (`excludesHost`) unless a reviewed contract grants
  the read;
- `objectProtoKeys` kept refused, and symbol keys outside the rule;
- array own-key exclusions preserved: reading at $`\top`$ grants no
  ownership and no write.

Controls: the positive shape above and a decoder over `JSON.parse`'s
result; a read at `toString` after `"toString" in v`, a host value and a
symbol key stay refused; a write at the key is not admitted.

<a id="guard-promise-field"></a>
**A guard's promise on a field.** A promise narrows an actual that is an
immutable name: `str(o.name)` (`asserts v is string`) leaves `o.name` at its
type, and a field's current-content facts hold primitive atoms only. The
promise of a call whose actual is a field read, a primitive one, would be a
current-content fact of the field through the read's link (`claim.mts`'s
`atom` and `decodeClaimType`).

<a id="guard-answer-constant"></a>
**A guard's answer held in a constant.** `const ok = isRecord(v)` keeps the
call's promise on the call's result, an implication of its slot, which no
statement entry carries: `if (ok) return v` reads `v` at its declared type,
and a narrowed claim there is refused at the edge. Carrying implications in
entry claims is a fact kind of its own.

<a id="guard-overloads"></a>
**Guard overloads beyond `filter`'s.** TypeScript's `every<S>` narrows the
array to `readonly S[]` where it answers `true` at a guard, and `find<S>`
returns `S | undefined`. Neither is a contract of the native at the top
footprint a closure's promise signature is checked at
([prototype contracts](docs/SOURCE-CONTRACTS.md#prototype-contracts)): a
callback may append untested elements or replace tested ones before `every`
answers, and `find` passes `undefined` at positions a callback removed. Both
hold at a callback keeping array stores, which a promise signature can state
once a promise row's code is checked at a footprint (`effectChecked` checks
it at the top one alone). A guard read as a value meets `filter`'s guard
overload once its promise signature is adapted to the callback's longer one,
as a module function's slot meets a longer plain signature
(`filter-guard-value-refused`).

<a id="conditional-optional-field"></a>
**A conditional's join past an arm's read.**
Lean's search refuses both functions at the edge from the arm that reads
`o.v` into the point after the conditional, "the edge from node 2 does not
establish the claims at this point":

```typescript
type Opt = { v?: string | null };
export function defined(o: Opt): string | null {
  return o.v !== undefined ? o.v : null;
}
export function loose(o: Opt): string {
  return o.v != null ? o.v : "";
}
```

Cause (observed in `loose`'s claims and its refused edge): the producer
claims the arm's read of `o` at a view of the field, `{ v: null | string }`,
which states what a read of `v` gives and no contract of the record, and
the arm's entry holds `o` at that claim (`executionArmContext`). The point
after the conditional claims `o` at its declared `Opt`, which the view is
not within; every other slot of the edge is within its claim (the
diagnostic names another slot). The same test with two returns has no
point after the read, and `let r = ""; if (o.v != null) r = o.v; return r;`
verifies, its join claiming `o` at the union of `Opt` and the view; without
a read of `o` in the arm, `o.v != null ? 1 : 2` verifies. Repair
obligation: the point after a conditional holds each slot at what every arm
leaves it, as a statement's join does, or an arm's entry holds a slot at
its type met with the read's claim.

### Investigations

Each is a refusal whose cause is not established.

<a id="generic-equality-condition"></a>
**Generic equality in a condition.** A strict or loose
comparison of two values of a type parameter verifies as a returned value,
`return left !== right`, and is refused as a statement's condition, `if
(left !== right) return 1;`, with `left, right: T` (2026-10-19). The search
fails; the message it reports ("strict equality with a value of a type
parameter: neither operand is known to be a primitive or an object") is the
producer's diagnostic of the comparison (`expression_values.ml`), not a
located obligation, and which judgment fails is unknown. The Boolean-return
lowering, which turns a return into a condition, is scoped to type guards
and assertion functions until this holds: applied to every return, it
refuses `loose-equality` and `generic-unknown-arguments`, which keep their
outcomes.

<a id="negated-first-read"></a>
**A negated first read of an element.** With `type
Declaration = { readonly kind?: string; readonly initializer?: string }`,
`const d = list[0]; if (!d.initializer) return -1; return 0;` is refused
before search at the read `d.initializer` ("read receiver must name a cell
contract", `Plans.readCell`), on f91d657 and on the branch of
[mapped aliases](docs/PROGRAM-TYPING.md#mapped-aliases) (2026-10-22). The same function
with `if (d.initializer) return 1;`, or with `d` read before the test
(`read-narrows-path`'s `returned`), verifies, and so does the negated test
over a compiler node (`ts.VariableDeclarationList`'s first declaration).
Which receiver type the negation's lowering hands the read is unknown.

<a id="literal-guard-json-read"></a>
**A literal guard over `JsonValue | undefined`.**
`isDense(value: JsonValue | undefined): value is "dense"` returning `value
=== "dense"` is refused at its true return, the literal `true` at the first
code unit of `return` ("the promised argument is not within the promise at
this return"), where the diagnostic gives the argument's claim as
`JsonValue`, `undefined` removed, and not `"dense"`
(`guard-literal-json-read-refused`). The same guard over `unknown`,
`JsonValue`, `string`, `string | undefined`, `null | string` or `string |
number` verifies (2026-10-19). Which step of the comparison's narrowing
keeps the whole of `JsonValue` is unknown. The front end's literal guards
(`isArrayPresence`, `isIndexClass` in `type-graph.mts`) take `unknown`,
which verifies.

<a id="field-before-literal-arm"></a>
**A field written before a spread of a literal arm.**
`object-spread-field-before-literal`: `{ name: "x", ...(dots ? { name: 1 } :
{}) }` is claimed at `{ name: number } | { name: string }`, and the search
finds no derivation, reporting the claim available for the literal as
`{ name: "x" }`. The same literal with the field after the spread verifies
(`object-spread-exact-literals`'s `later`). Observed on 784c8b8 and on the
branch alike (2026-10-22).

<a id="callable-alias-meet"></a>
**An alias of function types met with a record.**
`type Calls = (() => number) & ((n: number) => number)` met with
`{ tag: string }` in a parameter's annotation is refused by Lean's reading
of the declarations: "the intersection is empty". The same three operands
written in the annotation verify (`spread-intersection-callable-grouping`).
Which step of the declaration's normalization yields no clause is not
established.

<a id="meet-member-disagreement"></a>
**A member two intersection operands state.** With
`binder: Param<string> & { bound: "a" | "b" | null }`,
`if (binder.bound) return binder.bound;` at `"a" | "b" | "none"` is refused
(`path-test-intersection-disagree`): the producer reads the member at the
first operand's `string | null`. Proposing it at `"a" | "b" | null` instead,
the operands' meet, the search found no derivation of the condition's read
at that type, though Lean's row states `bound` at both (observed
2026-10-22).

<a id="assigned-parameters-with-defaults"></a>
**Assigned parameters with defaults.** The producer refuses
assignment to a parameter with a default with "assignment to immutable
binding", for function declarations and closures alike. A concrete example
is the following function and its equivalent arrow closure:

```typescript
type Shape =
  | { kind: "circle"; radius: number }
  | { kind: "square"; side: number };
function f(s: Shape = { kind: "square", side: 1 }): number {
  if (s.kind === "circle") return 0;
  s = { kind: "square", side: 2 };
  return s.side;
}
```

The investigation concerns the producer's treatment of the parameter's
binding through default evaluation and subsequent assignment.

### Callables, classes and effects

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

Footprint precision is deferred
([FOOTPRINTS](docs/FOOTPRINTS.md#deferred-extra-precision)): separating one
array from another beyond fresh storage, so that `pop` on an array literal
the callback allocated is admitted; and a declaration's fresh result, which
only closures state.

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

<a id="class-methods-effects"></a>
**Class methods' effects.** [The draft](docs/drafts/method-effects.md)
states effects of a class's members in their result annotations with
`Within<{ value; store; onThrow? }, T>`, read by declaration identity and
certified from each definition's body in its own module. The owner's
decisions (2026-10-23): D1 (a), stated effects; D2 the `Within<…>`
spelling; D3 `no-return` as an independent first step; D4 T3's extension to
the callback-free node methods' footprints, `forEachChild` excluded; D5
reachability deferred, `Gate`'s `shift` stacks rewritten instead, and the
node-list stable store its own host-family item; D6 an override whose effect exceeds its base's statement refused at
the subclass.

<a id="async-and-generator-code"></a>
**Async and generator code.** `await` and an async body's returns are calls
of intrinsic values at declared signatures (`%Await%`, `%AsyncReturn%`,
`%AsyncComplete%`; [async](docs/SOURCE-CONTRACTS.md#async-functions-and-await)),
a row of the trust surface. Discharging that trust needs an asynchronous
entry judgment
$`\Gamma,\mathsf{this}:R,\mathsf{argv}:\alpha\vdash_G^{\mathsf{async}} t:\mathsf{PromiseSpec}(B,E)`$
checking entry and resumption (parameter initialization, promise
resolution, thenable assimilation, rejection, and state invariants across
suspension), introduced by an **Async-Code** rule giving `asyncCode(t)` the
call contract $`[(R;\alpha)\xrightarrow{\bot}\mathsf{PromiseSpec}(B,E)]`$,
entry failures counted as rejections; $`\mathsf{PromiseSpec}`$ constrains
fulfillment and rejection, not settlement. A generator needs a protocol
$`\Pi`$ of `next`, `throw` and `return` with a **Generator-Code** rule
$`[(R;\alpha)\xrightarrow{E_{\mathrm{entry}}}\mathsf{Generator}(\Pi)]`$
whose transitions supply stateful contracts for those methods. Both
premises need an async/coroutine logic of the execution semantics
([CALLABLES](docs/CALLABLES.md)).


### Source forms and the model

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
constructor allocates; `Error` has one, its message on the instance's first
link ([a class extending `Error`](docs/SOURCE-ELABORATION.md#a-class-extending-error)),
which serves while ownness, descriptors and the prototype of an instance are
refused. The Error family's general mechanism is a store of non-enumerable own
properties: reads and ownness tests see it, enumeration and copies exclude
it, the instance's prototype stays `D.prototype`, and a write or redefinition
and every subclass's construction act on it; it admits `TypeError` and the
other native errors, `hasOwnProperty("message")` and `Object.getPrototypeOf`. `keyof T` and `T[K]` over a function's own binder need a row whose
meaning fixes a key set, which a value set does not. `o.m?.()` needs the receiver saved
across the test. `key in o` at a key the built-in prototypes hold needs those
prototypes' keys in the model.

<a id="regular-expressions-left"></a>
**Regular expressions left.** A
literal, `exec`, `test` and the string methods dispatching to a regex are
admitted ([regular expressions](docs/SOURCE-CONTRACTS.md#regular-expressions)).
Left: a replacement callback, whose argument list follows the shape
(`(match, p₁ … pₙ, offset, input[, groups])`, every match collected before
the first call, its result a string); a native regex of the conservative
shape for `new RegExp(p, f)` of strings, which is read as the structural
regex a `RegExp` annotation states (`regexp-dynamic`); a regex's properties, `lastIndex`
(own, not enumerable, a number) and the accessors `source` and `flags`,
read through reserved host-relative members so that no record view states
them, with `in`, patterns and computed reads of their keys accounted for;
a loop over a structural iterator TypeScript types `RegExpStringIterator`,
through the iterator protocol; and the same native mark on `SetIterator`
and `MapIterator`, whose loops are chosen by TypeScript's type alone.

<a id="json-records-by-their-fields"></a>
**JSON records by their fields.** A record a declaration types by its fields
(an interface, a type literal) is no `JsonValue`: a record is open, and an own
string key it does not declare may hold a `toJSON` (`invalid-json-stringify-record`,
run under Node). Admitting one needs a bound on all of its own string keys:
each a declared field whose present value is a `JsonValue`, an ordinary data
property, over a safe prototype; established where the record is built or
validated and kept through its mutations and through external calls; and a
policy for an optional field, absent or present at `undefined`. The claim
printer's lifter (`liftType`, `liftClause` and `treeAtom` in
`claim-text.mts`) builds such records and passes them at `JsonValue`, and is
refused there. A general form of the bound: a fresh object literal
establishes it where it is built, its own keys being the literal's, and the
bound is preserved through the object's mutations and through calls.

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

### Proofs, precision and trust

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
f(o.a)` is refused the same way). An optional chain's truthy or present
result narrows the value the chain saved, not the binding it was read from
(`optional-chain-receiver-not-narrowed`: `if (o?.inner) use(o)`), which
needs the chain's test related to the receiver's slot. A `flatMap` callback returning a
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

The record tools are written around two of these limits, and each form is
restored when its limit lifts: element reads the code already guards by a
test of the same element (`record-render.mts`'s `mathRoles`, its
`afterRelation` and `textWord`, and `docs.mts`'s `numbered`;
`guarded-element-read-refused`), and a `flatMap` callback returning a string
(`record-render.mts`'s `card`; `flat-map-scalar-result-refused`).

**Field facts across calls** are deferred, measured (2026-10-19): a call
step keeps no current-content fact, and keeping those a call's checked
footprint leaves true would move the evidence search of 7 functions of the
front end's census past the fact's loss at an empty-footprint call, none
more at a `value: keep` footprint, and 3 more only where every step keeps
them; search completes for 2 (`completes`, `heapAtom`), and the others stop
at a later obligation. The measurement kept facts in search's untrusted step
choice and in the producer's proposals, with the checker unchanged; no
function was verified by it.

<a id="module-composition"></a>
**Module composition** as a Lean theorem: the step-indexed argument that
units certified against each other's signatures compose.
[Certified imports](docs/SOURCE-MODEL.md#certified-imports) check an
imported function's code in the importer's run, at its effect-qualified
signature. `checkJson_safe` keeps its statement.
Combining a certified import's conclusion with the importer's is left to
this theorem, plus the review obligation that the import binds the certified
unit's closure ([the linking obligation](docs/SOURCE-MODEL.md#certified-imports)).

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

<a id="a-connection-to-ecma-262"></a>
**A connection to ECMA-262.** Proving the host's stated types as lemmas of a
mechanized specification would turn the ECMA rows of the trust surface into
theorems; the lemmas and their cost are in
[TRUST-REDUCTION](docs/TRUST-REDUCTION.md#the-host).

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

### Structure-directed comparison

[UNION-SHAPES](docs/UNION-SHAPES.md) states the comparison and its
selection rules R1–R7, of which the structural engine implements R1–R5.

<a id="union-shapes-lemmas"></a>
**The lemmas in the repository.** The lemmas UNION-SHAPES states of its
rules (`covers_shape`, `str_excluded`, `str_included`, `views_exclude`,
`fields_exclude`, the `refs_exclude` family, `dict_needs_among`,
`separation`, `numSlice_sound` and `numSlice_exact`, and the `valid'`
lemmas) were checked in a file outside the repository against the library
at 84b326a; within the repository they are conjectures until they are
modules of `lean/Verification/Types/` the build checks.

<a id="union-shapes-discovery"></a>
**Selected discovery and the rerun.** `valid_selected` keeps a completed
certificate valid under selection. That the selected search finds it needs
the certificate restricted to the root and the dependencies of its
coverings, with every premise and piece of evidence kept, and a selected
discovery whose universe contains that restriction, its pruning monotone on
it. The engine does not represent those dependencies: `demandPairs`
enumerates `clausesOf` where coverage reads `sourceClauses ++ meetSources`;
`TabRen` discharges a premise through another row; `rowArrows` derives arrow
evidence from every row, and `compareStepStateCore` reads instance members
from every row of the table; growth detection (`grows`) depends on the rows
already inserted. The change this needs is one dependency representation
that discovery produces and coverage, arrow evidence and member discovery
read, each covering naming the pairs and the evidence it uses; it changes
the engine's interface. The rerun of a comparison selection leaves
unestablished is then removed where the preservation theorem applies, and
kept elsewhere.

<a id="union-shapes-candidates"></a>
**Selection rules the data names.** R6 (decomposition of a source spanning
cells) and R7 (compact cell sets, which represent `statementsOnPath`'s
number-literal tables as one atom) are specified and not implemented; with
evidence sharing they are ranked by what remains of `statementsOnPath`'s
run. Two candidates have no rule yet: open target arms, a record source
whose literal keys a target arm leaves open, which needs a fact that the
arm cannot hold the source's literal (an own-key bound excluding the key);
and shared literals, arms sharing a literal, which a second discriminant
key read by R3 may separate.

### The stage store

<a id="observed-stages-beyond-macos"></a>
**Observed stages beyond macOS.** The parse and TypeScript's diagnostics
replay as [observed stages](docs/STAGE-STORE.md#observed-stages) where the
compiler runs confined by `sandbox-exec`, on macOS; elsewhere their
observations are incomplete and they execute without replay. A confinement
on Linux that kills the compiler on a read outside the API's five queries,
with its identity in the pre-key, makes them replay there. One case's
parse executes on macOS too, its observations incomplete:
`invalid-compiler-api-guard-subpath`, a specifier the package found does
not resolve.
