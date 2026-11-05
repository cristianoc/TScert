# Source rewrites

Changes made to TScert's own TypeScript so that it verifies, each with the
property of the original code that TScert cannot establish and the general
rewrite that removes it. Each entry is a small instance of an operation
TScert is meant to support in general: given code it refuses, propose the
rewrite that makes it sound, or show the behaviour the refusal guards
against.

A rewrite here never weakens a check or hides a behaviour: it either states
a type the code already relies on, adds the check a type promised, or makes
an implicit correlation explicit. A change made for a reason other than
soundness (a tool's defect) is listed apart. A rewrite that a fix of the
verifier would make unnecessary is not one: that fix goes to the verifier.

## Deciding what a refusal of TScert's code calls for

A refusal of TScert's own code is answered by the first of these routes
that establishes what the refusal asks, at acceptable cost:

1. **Support:** a rule or a contract admits the construct, where it has
   useful reach (measured by the census past the first refusal) and a
   proportionate implementation, with complete contracts and the acceptance
   theorem kept.
2. **A runtime check:** the code checks the property it needs, where an
   executable check establishes all of it, also over time under mutation
   and aliasing. A check of a value's shape establishes no effect.
3. **A repair:** the code changes where the refusal exposes a defect (the
   rewrites below), keeping the intended behaviour.
4. **Avoidance:** the code drops the construct where support is costly, its
   use rare by the census, and a rewrite is observationally equivalent:
   the same returns, exceptions, mutations, method identities, aliasing,
   receivers and asynchronous effects, for every input and reachable state
   its callers admit. Passing the verifier shows no equivalence. The
   avoided form is listed under [constructs avoided](#constructs-avoided),
   and its case is written in the equivalent form, which verifies.
5. **A host boundary:** a necessary operation on an external service that
   no rule can model moves to the smallest module performing it, whose
   signatures only the intended host value inhabits and grant no more than
   the operation: its callers are verified against them, its own functions
   stay refused, and its contract is audited against the service and
   stated with every effect ([host boundaries](#host-boundaries)).
6. **A trusted unit:** local code exempt from checking, for a narrow unit
   the owner approves, reported with its full contract and what depends on
   it. It is never disguised as a host boundary, and no route falls back
   to it.
7. **A proof:** a Lean proof of the property, where the semantics it needs
   exist or building them has wider value. A proof whose hypotheses state
   the host's behaviour keeps those assumptions.
Each route answers a correct program. A case is refused, as a negative
case, only where its program is unsafe, shown by running it under Node. A
correct program no route answers yet stays a gap, open work in
[WORK.md](../WORK.md#status) with what each route would need. Coverage
pressure is evidence of value, not permission to weaken safety.

What TScert verifies of its own front end is its source as it stands: code
checked, host boundaries and their contracts, trusted units and refused
functions are reported apart, and a result under a host contract is no proof
of the host's implementation.

The support route for array rest collection is specified under
[patterns](SOURCE-ELABORATION.md#patterns).

## Unsafe examples

### Reference arguments mapped through an unrestricted callback

`blocker-prep-reference-args-map` returns `{ ...t, args: t.args.map(a => go(a)) }`
as `TypeTerm`, whose reference arm requires a readable `TypeTerm[]` in `args`.
For two arguments, a `go` callback that calls `t.args.pop()` and returns its
argument meets the written callback contract. The map captures length 2,
visits index 0 and skips the removed index 1. The returned reference holds
an array of length 2 with a hole at index 1; reading `result.args[1].k`
throws `TypeError` under Node.

The [native map contract](SOURCE-CONTRACTS.md#prototype-contracts) permits
holes with unrestricted callbacks. This is a negative case under the
[route criteria](#deciding-what-a-refusal-of-tscerts-code-calls-for).
`blocker-prep-reference-args-map-preserving` requires
`Within<{ value: "any"; store: "grow" }, TypeTerm>` from `go`; the existing
[effect checks](FOOTPRINTS.md) and native map contract establish the readable
result, and the reference construction verifies. This adds no external
assumption. The compiler's own branding traversal retains a checked
[brand-predicate footprint](#the-brand-predicates-normal-return-footprint)
through its recursive calls and declaration context.

### Installation records mapped through an unrestricted callback

`blocker-prep-captured-map-records` maps `active` through a callback
`root: (s: string) => string`, then compares pairs through `entries()`
and `slice(i + 1)`. For `active = ["a", "b"]`, a root callback that
executes `active.pop()` and returns its argument meets that contract.
The map captures length 2, visits index 0 and skips the removed index 1,
leaving a hole. The first pairwise comparison reads `b.root` where `b`
is `undefined`; execution of this fixture under Node throws `TypeError`.

The [native map contract](SOURCE-CONTRACTS.md#prototype-contracts) permits
holes with unrestricted callbacks. This original example is a negative
case under the [route criteria](#deciding-what-a-refusal-of-tscerts-code-calls-for).
`blocker-prep-captured-map-records-preserving` states a callback with
`Within<{ value: "any"; store: "grow" }, string>` as its result.
The existing [effect checks](FOOTPRINTS.md) establish readable presence
from that requirement, and the complete iteration verifies with the
inferred `found` binding. This is a checked function contract and adds
no external assumption.

### An inferred map result with an unrestricted callback

`blocker-round-inferred-map-result` takes `read: (x: number) => Form`,
uses `xs.map((x) => read(x))` as an inferred local function result, then
maps that result and returns it as `Form[]`.

For `xs = [1, 2]`, a `read` callback that calls `xs.pop()` and returns
`{ receiver: null }` meets its written contract. The first map captures
length 2, invokes `read` at index 0, and skips the removed index 1. The
second map preserves that hole. Execution of the fixture under Node gives
length 2, `1 in result === false`, and `result[1] === undefined`;
`result[1].receiver` throws `TypeError`. The returned array therefore fails
its readable `Form[]` contract.

The [native map contract](SOURCE-CONTRACTS.md#prototype-contracts) permits
holes for unrestricted callbacks. The receiver refusal prevents consuming
that sparse result as a readable array. This is a negative case under the
[route criteria](#deciding-what-a-refusal-of-tscerts-code-calls-for): its
written result contract is unsafe. The separate
[overlay field repair](#overlay-fields-consumed-by-the-signature-helper)
establishes the helper argument contract in `selectGlobal`.

## Rewrites

### Installation records built by a singleton flatMap

`installations` in `tools/family-activation.mts` collects completed root
lookups before checking marker, root and guard ownership. Its singleton
`flatMap` appends one record for each description visited by native array
iteration. The existing [native array contract](SOURCE-CONTRACTS.md#prototype-contracts)
establishes dense output even when a lookup changes the input array.

```ts
const found = active.flatMap(description => [
  { description, root: installationRoot(description) },
]);
```

- **Defect:** `map` captures the input length and leaves a result hole for
  an index removed before its visit. The ownership loop reads every result
  entry and dereferences its fields. A filesystem provider can trigger
  this defect through the real `installationRoot`: Node's experimental VFS
  calls a provider's `statSync`, which can shrink an aliased active-family
  array without replacing a standard method.
- **Repair:** `flatMap` keeps completed lookup records densely packed.
  Both operations capture the entry length, visit present indices in
  order and skip indices removed before their visit. The repair changes
  the hole case: a two-family input shrunk to one during its first lookup
  gives a length-two holed map result and a `TypeError` in the comparison;
  singleton `flatMap` returns the one completed record when its ownership
  checks pass. A lookup that throws still aborts collection before those
  checks. This traversal does not promise a snapshot of families removed
  during a lookup.
- **Preserved behavior:** when lookups preserve the dense input array,
  both forms compute the same records with the same description references,
  lookup order, observations and ownership checks. Comparisons under Node
  with real package lookup for zero, one and two installations, repeated
  markers and repeated roots agree on records, exceptions and filesystem
  observations. This equivalence is conditional on input preservation.
- **Evidence and cost:** `blocker-round-installation-records` verifies the
  real lookup and captured comparisons. A Node 26.13.0 VFS probe executes
  both complete bodies with the real lookup and a shrinking provider,
  obtaining the hole and `TypeError` versus a dense single-record return.
  The first description retains its identity, and the filesystem and array
  method identities remain unchanged. One temporary singleton array is
  allocated per visited family. The repair adds no callback restriction,
  VFS exclusion or external assumption. The arbitrary-callback map
  counterexample remains `blocker-prep-captured-map-records`.

### Callable JSON fields printed through an optional read domain

`atomText` and `bareAtomText` in `tools/claim-text.mts` accept `JsonRead`,
the result of reading a `JsonObject` field. A malformed callable atom can
lack its `function` or `bag` field. The existing object and array guards
handle `undefined`, mark the text as incomplete and print `«type»` for
that part. `printType` accepts `JsonValue` and checks the complete claim
shape independently before returning the text and its `printable` flag.

- **Repair:** the two internal parameter annotations state the domain
  their existing guards handle, including an absent field.
- **Equivalence:** annotations erase under Node. Both parameter changes
  leave every executable statement intact, so returns, exceptions and
  writes are identical for every input. The public printer's input and
  output contracts remain the same.
- **Evidence:** `blocker-round-callable-json-fields` exercises a recursive
  JSON field read with the optional domain; `tests/claim-text.mts` runs the
  actual printer with complete callable parts, either part absent and both
  parts absent, checking the full text and its completeness flag.

### Part collection through a store-preserving traversal

`tools/fragment-parts.mts#partsOf` collects direct parts by passing identity
callbacks that append to a fresh array into a traversal. Its `map`
parameter states `(m: PartMap) => Within<{ value: "any"; store: "grow" }, unknown>`.
The callers in `directParts` and `codeParts` supply `mapExprParts`,
`mapStmtParts`, `mapPatternParts` and `mapFunctionParts` through closures.
Each traversal carries the same store-preserving contract.

The parameter retains the effect that these supplied traversals establish.
The existing [stated-effect checks](SOURCE-ELABORATION.md#stated-effects)
check each supplied closure and the collector's body. An ordinary function
parameter permits shrinking shared arrays, which cannot establish the
collector's written store-preserving effect.

The annotation is erased: calls, callback order, collected part identities,
returns, exceptions and mutations agree for every internal caller.
`blocker-prep-part-map-effect` exercises this contract repair. It adds no
rule or external assumption.

### Promise binder maps with concrete writable bounds

`tools/declaration-graph.mts#promisedBinders` maps value binders with the
`SourceTypeParameter<TypeTerm>` contract. `promisedMethods` maps scheme
binders with their complete contract, including `default` and `span`.
Each callback states its result contract. The existing
[allocation checks](SOURCE-CLAIMS.md) check the replacement bound as
`TypeTerm | null` and retain the other fields through object spread.

The generic signature `B extends { name: string; bound: TypeTerm | null }`
with result `B[]` promises more than replacing `bound` establishes. `B`
can require an atom bound with a `name` field. The generic helper in
`invalid-prep-generic-binder-map` returns an intersection bound for that
input. Under Node, an input bound with `k: "atom"` and `name: "string"`
produces a returned bound with `k: "intersection"` and `name === undefined`.
Reading that bound's `name.length` throws `TypeError`. The written `B[]`
contract therefore fails.

The concrete contracts describe the two callers' actual storage. The map
retains unselected binder identities and allocates the same spread records
for selected binders, preserving resolution slots and scheme metadata.
The bound test, intersection parts and span reads keep their evaluation
order. This repair adds no external assumption.

### Numeric literal text checked before conversion

`tools/claim-text.mts#bareAtomText` prints `numberlit` and `numlit` atoms
from JSON data. The claim decoder requires a string in `v`; conversion by
`Number` also accepts non-string values such as `[]`, whose number is zero.
The numeric branch requires `typeof atom.v === "string"` before testing
`Number.isFinite(Number(atom.v))` and returns that string directly.

- **Repair:** numeric literal text retains its string domain at the read.
  Finite conversion alone does not establish that domain. Malformed
  non-string values reach the printer's unavailable-atom fallback instead
  of appearing as numeric literal text (an empty array otherwise prints an
  empty string). Valid numeric text keeps its exact spelling, including
  leading zeros and whitespace.
- **Mechanism:** the existing [global conversion contracts](SOURCE-CONTRACTS.md#library-globals)
  admit the checked string. The runtime check adds no rule or external
  assumption. General JSON object coercion requires its conversion hooks
  and effects; this literal format requires text.
- **Scope:** `invalid-string-object` exercises the numeric branch used by
  `bareAtomText`, `atomText` and their callers. The malformed-output control
  in `tests/claim-text.mts` checks the diagnostic fallback for non-string
  fields and the spelling of valid numeric fields.
- **Commit:** the introducing commit.

### A reduce callback returning a writable statement array

`tools/fragment-statements.mts#switchStmt` states `Stmt[]` on the
callback that wraps the accumulator in a block and spreads the next
clause’s statements. Its initial accumulator, `dispatch`, also states
`Stmt[]`. The existing [allocation and closure checks](SOURCE-CLAIMS.md)
establish those writable contracts.

- **Repair:** the callback result annotation supplies the element contract
  to the fresh array and its block record. The array admits the complete
  `Stmt` union, including statements returned by `this.statements`; the
  block’s body retains its `Stmt[]` contract. The initial array carries
  the same writable element
  contract into `reduce`.
- **Behaviour:** the annotation is erased. Both forms invoke `reduce`
  with the same receiver, callback and initial accumulator. Each callback
  allocates the same block record, evaluates `gate.span(c)` and `label(c)`
  before `this.statements(c.statements)`, and spreads the same array in
  the same order. Returns, exceptions, mutations, method identities,
  receivers, aliases and asynchronous effects agree for every admitted
  input and reachable state.
- **Scope:** `blocker-prep-reduce-block-spread` states the callback result
  and initial accumulator contracts. The repair adds no external assumption.
- **Commit:** the introducing commit.

### A probe request's fresh document array

`tools/declaration-graph.mts#withOwnProject` allocates the probe request's
`closeFiles` array at `DocumentIdentifier[]`, whose element contract is
`string | { uri: string }`. An immutable local is that array when `opened`
is true and `undefined` otherwise. The existing
[allocation checks](SOURCE-CLAIMS.md) establish the complete writable
contract before the array enters the request. `withProject` and
`clientErrors` reach this helper.

- **Repair:** the conditional spread tests the local itself. Its array arm
  supplies the field at its full contract; its other arm omits the key.
  The source keeps the shared `Set` expression at one site.
- **Behaviour:** the initializer reads an initialized boolean and string,
  allocating an ordinary array only on the true arm. These operations
  commute with the API's data-method read: the package declares
  `updateSnapshot` as a class method, and `openCompiler` installs its own
  ordinary wrapper before returning the API. The existing
  [T4 relation](COMPILER-API.md#trust) covers that read's value and client-code
  behavior. The true request's own keys are `closeFiles`, `openProjects`,
  `fileChanges`, in that order; the false request's are `openProjects`,
  `fileChanges`. The argument evaluates the same `Set` expression once,
  after method lookup and with the same iteration and callback order.
  Method identity, receiver, file values, flag updates, cache replacements,
  disposal and exception propagation agree for every admitted input and
  reachable state.
- **Scope:** `blocker-next-conditional-array-context` checks the fresh
  contract; its Node observation checks the receiver and both presence
  arms. The repair adds no external assumption. The
  [complete-request construction](#a-snapshot-request-with-a-conditional-spread)
  describes `projectFor`'s separate request.
- **Commit:** the introducing commit.

### A flow document assembled from decoded values

`decodeFlowDocument` in `tools/source-flow.mts` uses the existing
[fresh-result decoder pattern](#a-decoders-result-asserted-over-parsed-storage).
Its input type, `Json`, describes JSON values; the return type,
`FlowDocument`, promises writable graphs, nodes, actions and execution plans.

- **Repair:** field decoders return their checked values in fresh records
  and arrays. Each action and execution variant constructs its complete
  declared shape. The graph decoder retains these typed results through
  its return. Widening the input to `unknown` before a closing assertion
  supplies neither the graph contract nor protection from writes through
  a parsed-value alias.
- **Behaviour:** exact-field checks, validation order, node identities,
  edge bounds and duplicate-owner checks determine admission. For parsed
  JSON, the returned document has the same fields and values as its input,
  in fresh storage throughout. Both production callers in
  `pipeline/verify-source.mts` serialize that document immediately. Property
  insertion order follows the decoder's record literals. Mutating an input
  after decoding leaves the returned document unchanged.
- **Scope:** `blocker-round-decoder-erased-assertion` checks the typed
  construction and return. A control in `pipeline/test.mts` checks malformed
  graph documents and the independence of decoded spans from input writes.
  The repair adds no external assumption.
- **Commit:** the introducing commit.

### Optional prototype bounds looked up by binder name

`OverlayEntry.bounds` in `tools/array-prototype.mts` holds a native
`Map<string, TypeTerm>`. The `join` and `toString` entries supply `T`'s
conversion bound, and `prototype` reads `entry.bounds?.get(name) ?? null`
for each binder. The existing [Map contract](SOURCE-CONTRACTS.md#prototype-contracts)
establishes the lookup.

- **Repair:** binder names identify entries supplied by the overlay. A
  dictionary read can find `Object.prototype.constructor` or `toString`
  at an absent own key and pass that function as a type bound. A Map
  returns a supplied bound or `undefined`, giving `null` for an absent
  bound. This is the [runtime-key table repair](#a-dictionary-read-at-a-key-known-only-at-run-time).
- **Behaviour:** the two built-in tables contain the same `T` bound.
  Present entries retain their type-term identity; absent entries give
  `null`. At inherited names the repair supplies the intended absent
  bound. Each table is allocated once with its overlay entry.
- **Scope:** `blocker-round-optional-dictionary-read` verifies the optional
  native Map lookup. `invalid-round-optional-dictionary-read` retains the
  dictionary form: an empty object at `constructor` or `toString` returns
  a function despite its `string | null` result annotation, as running
  the fixture under Node shows. `primitivePrototype` and
  `functionPrototype` reach the same lookup through `prototype`. The
  repair adds no external assumption.
- **Commit:** the introducing commit.

### Overlay fields consumed by the signature helper

`selectGlobal` in `tools/declaration-graph.mts` passes the result of
`reviewedForms` to its local `forms` helper. The resolved entry holds
`forms?: Stated[]`; `GlobalEntry` permits that writable field to hold
either an array or a function producing one.

- **Repair:** the helper parameter is
  `Pick<GlobalEntry, "admit" | "effect"> | undefined`, the two fields
  its body reads. A full writable `GlobalEntry` view would permit replacing
  the resolved entry’s array with a function. The existing
  [record checks](POSITIVE-TYPES.md#records) establish the smaller contract.
- **Behaviour:** the annotation is erased. Both forms read the same
  `admit` and `effect` values, invoke the same signature reader and maps,
  and allocate the same signature records and arrays in the same order.
  Returns, exceptions, mutations, method identities, aliases, receivers
  and asynchronous effects agree for every admitted input.
- **Scope:** `blocker-round-resolved-overlay-map-result` represents the call with
  a resolved entry and the helper’s consumed field. Its unannotated map
  result is used by a second map. The repair adds no external assumption.
- **Commit:** the introducing commit.

### Mapped binder records with their writable contract

`pruned` in `tools/written-applications.mts#writtenApplications` states
`SourceTypeParameter<TypeTerm>` on the callback that allocates each binder
record. The `bound` field holds a type term or null, and `resolution` holds
resolution slots or null. The existing [allocation and closure checks](SOURCE-CLAIMS.md)
establish that full writable contract before the enclosing array reaches
`filter` and the function's return.

- **Repair:** the callback's result annotation retains the writable field
  contracts required by the returned binder groups. Inference from the
  literal `resolution: null` alone supplies a narrower writable field.
- **Behaviour:** the annotation is erased. The same filters and maps run
  in the same order, read the same names and bounds, allocate the same
  records and arrays, and discard the same empty groups. Returns,
  exceptions, mutations, receivers and aliases agree for every input
  admitted by the existing contracts.
- **Scope:** `blocker-round-mapped-filter-length` checks nested maps and
  the final length filter with a nullable writable field. The repair adds
  no external assumption.
- **Commit:** the introducing commit.

### A generic class method's binder records with their writable contract

`classInstance` in `tools/type-term.mts` maps a generic method's type
parameters to binder records with `resolution: null` and places the array
in a scheme's `binders`, whose element is `SourceTypeParameter<TypeTerm>`
with its `default` and `span`. Inferred from the literals, the array's
writable element contract was narrower than the scheme's, which an
invariant array does not meet ("no rule derives this makeAt").

- **Repair:** the callback's result annotation states
  `SchemeTerm["binders"][number]`, as
  [mapped binder records](#mapped-binder-records-with-their-writable-contract)
  do. The annotation is erased; the same records are allocated in the same
  order.
- **Scope:** the rule is the one `blocker-round-mapped-filter-length`
  shows. The repair adds no external assumption.
- **Commit:** the introducing commit.

### A conditional pair's fixed positions

The callable `Object.assign` branch in `tools/fragment-expressions.mts#expr`
states `[TypeTerm, TypeTerm]` on the pattern binding `functionType` and
`bagType`. Each conditional arm constructs exactly two elements. The existing
[array and tuple checks](SOURCE-ELABORATION.md) establish both positions
before the returned `withValue` record consumes them as required fields.

- **Repair:** the tuple annotation retains the fixed positions that the
  fresh arrays establish. An inferred array contract loses those positions,
  so its destructured elements may be `undefined` in the model.
- **Behaviour:** the annotation is erased. The same conditional tests run,
  and the selected arm evaluates its first call before its second call,
  allocates the same pair and binds the same values. Calls, exceptions,
  mutations, aliases, receivers and returned records agree for every input
  admitted by the existing contracts.
- **Scope:** `blocker-round-conditional-pair-fields` checks the annotated
  conditional and required record fields. The repair adds no external
  assumption.
- **Commit:** the introducing commit.

### Readonly fields in the optional-parameter helper

`firstOptional` in `tools/fragment-support.mts` reads `questionToken` to
find the first optional parameter. Its callers pass compiler parameter
nodes, including the array passed to the constructor-parameter `map`
callback in `tools/fragment-classes.mts`.

- **Repair:** the helper's element contract states
  `{ readonly questionToken?: unknown; readonly initializer?: unknown }`.
  A writable field at `unknown` would permit replacing a compiler node's
  narrower field with any value. Readonly fields state the access the
  helper uses and admit the nodes through the existing
  [record rules](POSITIVE-TYPES.md#records). The annotation changes no
  execution.
- **Scope:** `blocker-gap-round-optional-parameter` verifies the call inside
  `map`; `blocker-gap-round-optional-parameter-writable` retains the
  writable-field refusal. This repair adds no external assumption.
- **Commit:** the introducing commit.

### Readonly member names in the type reader's key helpers

`members` and `classInstance` in `tools/type-term.mts` read each member's
key through a local `named` helper, whose parameter was
`TypeElement & { name?: Node }` (`ts.ClassElement & { name?: Node }` in
`classInstance`). A writable optional field at `Node` would permit
replacing a compiler node's narrower `name` with any node, so a property
signature's node did not meet it ("no rule derives this invoke" at
`named(member, message)`).

- **Repair:** the parameters state `{ readonly name?: Node }`, the access
  the helpers use, as the
  [optional-parameter helper](#readonly-fields-in-the-optional-parameter-helper)
  does; the record rules admit the nodes. The annotation changes no
  execution.
- **Scope:** the rule is the one `blocker-gap-round-optional-parameter`
  shows. This repair adds no external assumption.
- **Commit:** the introducing commit.

### The type reader's native collections typed as natives

`visitType` in `tools/type-term.mts` states `{value: any, store: grow}` and
extends the binder names in scope with `new Set([...bound, …])`; its
`bound` parameter was a `ReadonlySet<string>`. `readTypeTerm` reads
`scope.wildcard?.get(…)`, a `ReadonlyMap`. Each admits a program object
whose iterator or `get` runs code, so the step could change any location
("the footprint claimed for 'visitType' is not established by its body",
then for `readTypeTerm`).

- **Repair:** `bound` is a `Set<string>`, the native set every caller
  passes (the default `new Set()` or the walk's own `new Set(…)`), and
  `TermScope.wildcard` is a `Map`, the one `wildcardReadings` builds. A
  native set's iterator and a native map's `get` run no client code
  ([iteration intrinsics](../tools/intrinsics.mts),
  [collection overlays](../tools/array-prototype.mts)), within
  `{value: any, store: keep}`. The `visit` callback still receives the set
  as a `ReadonlySet<string>`. The annotations change no execution and add
  no assumption.
- **Scope:** `set-spread-stated-footprint`; `invalid-readonly-set-has-effect`
  keeps a program `ReadonlySet` whose iterator writes.
- **Commit:** the introducing commit.

### The shadow prelude's definitions typed as a native map

`prelude` in `tools/shadow-contracts.mts` spreads
`[...definitions.values()]`, where the module constant `definitions` is the
`new Map(…)` built from the library overlay's definitions; its annotation
was `ReadonlyMap<string, TypeDefinition>`. A spread keeps the host's
collection iteration, which a program's object meeting the `ReadonlyMap`
view need not give ("no derivation of its node-typing claim" at the spread,
as in `spread-readonly-map-values-refused`).

- **Repair:** `definitions` is a `Map<string, TypeDefinition>`, the native
  map its initializer builds; no code writes it. The annotation changes no
  execution and adds no assumption.
- **Scope:** `spread-readonly-map-values-refused` keeps the spread of a
  `ReadonlyMap`'s values refused.
- **Commit:** the introducing commit.

### An indexed access's projections built densely

`indexedAccess` in `tools/computed-types.mts` projects an object type at
its keys. A union's or an intersection's parts were projected by
`object.parts.map(part => project(part, depth + 1))`; `project` reads the
compiler through `context`, whose members state no effect, so the native
`map` may leave a hole, and the result did not meet `union`'s `TypeTerm[]`
(as in `blocker-round-inferred-map-result`). A record's found fields were
kept by `parts.filter((p): p is TypeTerm => p !== null)`, whose inferred
parameter the producer claims at the arms of `TypeTerm | null` without
selecting `filter`'s guard signature, so `found` was claimed with `null`
("no derivation of its node-typing claim" at `union(found)`).

- **Avoidance:** each projection pushes into a fresh `TypeTerm[]` in a
  `for...of` loop, which visits the same parts in the same order and
  leaves no hole; the guard names its parameter `p: TypeTerm | null`, the
  type TypeScript infers. Returns, exceptions and effects are those of the
  `map` and `filter` forms on an array without holes.
- **Scope:** `blocker-last-indexed-access-fields`;
  `blocker-last-guard-param-inferred` keeps the inferred parameter as a gap.
- **Commit:** the introducing commit.

### Mapped arms with a store-preserving callback

`liftLabels` in `tools/claim-text.mts` binds its `map` callback as `armOf`,
with a `JsonValue` parameter and the result contract
`Within<{ value: "any"; store: "grow" }, Arm>`, where `Arm` is the record
holding a count and a deferred lifting function. The existing
[footprint checks](FOOTPRINTS.md) require preservation evidence for that definition;
the existing [native map contract](SOURCE-CONTRACTS.md#prototype-contracts)
uses it to retain readable array presence for reduction and iteration.

- **Repair:** the callback's own signature retains the parameter contract
  and states the preservation needed by its consumer. The body is checked
  at that signature before `map` consumes it. Constructing a deferred
  function does not execute its body; its later invocation has its own call
  contract.
- **Behaviour:** the annotation is erased. The same callbacks run in the
  same order, allocate the same arm records and deferred functions, count
  the same clauses and lift the same selected arms. Returns, exceptions,
  mutations, receivers and aliases are unchanged. Allocating the callback
  before reading `map` runs no client code under the existing stable
  standard-object assumption.
- **Scope:** `blocker-gap-round-captured-arms-reduction-preserving` checks
  the full reduction, bounded iteration and final `flatMap` with a store-preserving
  splitting function. `blocker-gap-round-captured-arms-reduction` retains the
  ordinary splitting signature: it permits removing a later input during
  `map`, leaving a hole that iteration visits as `undefined`. The repair
  adds no external assumption.
- **Commit:** the introducing commit.

The private `atEachFootprint` helper in `tools/array-prototype.mts` applies
this pattern at its `signature` parameter. Its result is
`Within<{ value: "keep"; store: "keep" }, { params: TypeTerm[]; result: TypeTerm }>`.
The complete data contract stays explicit; each provider must establish the
preserving footprint at the call. The providers construct records, arrays
and effect descriptions without writing existing locations. The helper's
map consequently retains readable result presence.

The annotation is erased: the same footprint array is visited in the same
order, each provider runs once per visited value, and the same records are
spread and returned. Returns, exceptions, mutations and aliases are
unchanged for those checked providers. `blocker-next-footprint-factory`
checks the private factory and its preserving provider;
`invalid-footprint-factory-provider` supplies a shrinking provider that
cannot meet the parameter contract and leaves an absent result position
under Node. This source repair adds no external assumption.

### A cache callback's nullable answer field

`realOf` in `tools/files.mts` supplies `attemptAnswer` with a callback
whose result is `{ answer: string | null }`. The annotation gives both
fresh records the writable field contract that the cache holds. This uses
the existing [allocation and closure checks](SOURCE-CLAIMS.md).

- **Repair:** the result annotation retains the cache's full storage
  contract at allocation. Separate inferred string and null writable
  fields cannot supply that invariant contract.
- **Behaviour:** the annotation is erased. The callback resolves the same
  path, handles the same errors, allocates the same records and returns
  the same answer. Cache operations, observations, aliases and exceptions
  are unchanged.
- **Scope:** `blocker-gap-round-cache-answer` checks the annotated callback;
  `blocker-gap-round-cache-answer-inferred` retains the inferred-field
  refusal. The repair adds no external assumption.
- **Commit:** the introducing commit.

### A forward visitor helper with a store-preserving contract

`letWrites` in `tools/fragment-expressions.mts` captures `outermostIs`
before that helper is initialized. Its callable binding states
`(top: Node, n: Node) => Within<{ value: "any"; store: "keep" }, boolean>`.
The existing [early-binding checks](SOURCE-ELABORATION.md#lexical-bindings-before-initialization)
check initialization and reads at that storage contract, and the existing
[closure checks](SOURCE-ELABORATION.md#stated-effects) certify its footprint.

- **Repair:** the written callable contract retains the array-store
  preservation established by the helper body. A forward capture reads
  the storage contract; parameter and Boolean result annotations alone
  give it an unrestricted call effect. The helper assigns its local
  traversal binding, so its stated footprint permits value writes.
- **Behaviour:** the annotation is erased. Closure allocation order,
  capture, traversal, calls, returns, exceptions and mutations are the
  same for every compiler node admitted by the existing host contract.
- **Scope:** `blocker-gap-round-visitor-effect` and
  `blocker-gap-round-visitor-effect-unstated` exercise the qualified
  binding. The repair adds no external assumption.
- **Commit:** the introducing commit.

### A missing field key printed explicitly

`bareAtomText` in `tools/claim-text.mts` prints malformed producer fields
as well as valid ones. A JSON dictionary read may yield `undefined` for
an absent `name`. The existing [JSON contract](SOURCE-CONTRACTS.md#json-and-error)
accepts JSON data and returns a string.

- **Runtime check and repair:** the fallback tests `key === undefined`
  and supplies the text `"undefined"`; its other arm serializes JSON data.
  The string and symbol tests retain their order. The existing narrowing
  and call checks establish the serialization obligation.
- **Behaviour:** at an absent name, the enclosing string addition converts
  the original serialization result `undefined` to `"undefined"`. The
  explicit text gives the same field name and optional suffix. At every
  other value, the same serialization or symbol formatting runs. The
  omitted call on `undefined` runs no client code, allocates no object and
  throws no exception under the existing standard-object assumption.
- **Scope:** `blocker-gap-round-key-stringify` exercises the explicit
  missing-name text. `invalid-gap-round-key-stringify` retains the original
  call on a possibly absent key, whose direct return can be `undefined`
  despite its `string` annotation. The repair adds no external assumption.
- **Commit:** the introducing commit.

### Declaration locations retained as JSON data

`makeProbe` in `tools/type-probe.mts` compares declarations by serializing
locations. Its `where` callback states `readonly (string | number)[] |
string`: an ordinary location is a fresh array of a file name and two
offsets, and an inserted location without an original is `"the probe"`.
The existing [JSON contract](SOURCE-CONTRACTS.md#json-and-error) admits
these values.

- **Repair:** the result annotation retains the data grammar established
  by the callback body. A result at `unknown` supplies no JSON data
  contract to the second map. The allocation,
  closure and JSON checks establish the stated contract.
- **Behaviour:** the annotation is erased. Both maps visit the same
  declarations in order, resolve each declaration once, and serialize the
  same arrays, strings and null values before sorting. Returns, throws,
  allocations and aliases are unchanged.
- **Scope:** `blocker-gap-round-locations-map` uses compiler declarations,
  whose existing host contract states the effect of `resolve`.
  `invalid-gap-round-locations-map` retains the unknown-result refusal.
  `invalid-gap-round-locations-map-shrinking` is the structural callback
  example: its `resolve` field states no effect, so it may shrink the
  array during the first map and leave a hole the returned `string[]`
  reads as `undefined`, as running it under Node shows. The repair adds no
  external assumption.
- **Commit:** the introducing commit.

### Captured mapped arrays passed to flatMap

`liftLabels` in `tools/claim-text.mts` builds an array of functions and
passes it to `flatMap`. A map callback with arbitrary effects gives a
potentially sparse result. The [prototype contract](SOURCE-CONTRACTS.md#prototype-contracts)
accepts that receiver and gives the callback a sparse third argument.

- **Support:** the existing native contract and array-presence checks
  establish the call. The source retains its operations and annotations.
- **Scope:** `blocker-gap-round-captured-arms` isolates this call;
  `blocker-gap-round-captured-arms-reduction` contains the full reduction
  and iteration example. `invalid-flat-map-sparse-callback` checks that a
  visited entry gives no presence guarantee for other indices. The native
  contract states the existing standard-object assumption.
- **Commit:** the introducing commit.

### Conditional mapped arrays passed to filter

`lowerFile` in `tools/fragment-parse.mts` holds either a `map` result or a
`flatMap` result in `lowered`, then repeatedly filters it. The unrestricted
map callback permits holes in its result. The existing
[filter contract](SOURCE-CONTRACTS.md#prototype-contracts) admits the sparse
receiver and states the same presence mode for the callback's array
argument, using the existing array-presence checks.

- **Support:** the source retains its conditional, mutable binding and
  callbacks. No information is discarded at these sites.
- **Scope:** `blocker-round-conditional-map-cell` exercises the conditional
  receiver; `native-filter-sparse` covers ordinary and guard callbacks;
  `invalid-filter-sparse-callback` checks the callback's third argument.
  The contract uses the existing standard-object assumption.
- **Case shape:** both initializer arms allocate `{ source, item }`
  entries, corresponding to the production `{ s, fn }` entries. The filter
  reads `item.value`; the final projection reads `item` from the saved
  `kept` result inside the loop. This exercises the allocation-shaped
  element union and states the final projection's receiver directly.
- **Commit:** the introducing commit.

### Decoded records returned by async workers

`tools/unchecked.mts` gives its worker result the type `Result`, whose
`readonly then?: undefined` member states the lifetime non-thenable
contract required by [async resolution](SOURCE-CONTRACTS.md#async-functions-and-await).
`check` and `decodeResult` each allocate the result as a fresh literal
with only `files` and `found`; `runPart` returns the decoded record.

- **Repair:** the result annotations retain the absence of a callable
  `then` that these allocations establish. The existing record allocation
  and async-resolution checks establish the contract at its producers
  and consume it at the async return.
- **Behaviour:** annotations are erased. Decoding reads the same members,
  allocates the same records and arrays, and returns the same object;
  the worker retains its exceptions, promise resolution and object identity.
- **Scope:** `invalid-async-object` shows the typed decoder and async return.
  `invalid-async-open-record` retains the refusal for an unrestricted record.
  The standard prototype assumptions are those of async resolution.

### Native method maps with writable field contracts

`collect` in `tools/declaration-graph.mts` maps the native Promise
fields twice: it amends callable contracts, then gives prototype slots an
`unknown` type. Both callbacks state the existing field type from
`TypeTerm`, and the replacement atom is allocated as `TypeTerm`.

- **Repair:** these annotations give each fresh writable field its full
  storage contract. A narrower inferred literal cannot subsequently serve
  as a writable field of the full union type. The existing allocation and
  closure checks establish the stated contracts.
- **Behaviour:** annotations are erased. Each map visits the same fields
  in the same order, returns the same original fields on its unchanged
  arms, and allocates the same records on its replacement arms. The
  replacement atom is evaluated after the method test and before the field
  copy; both read only local data with no intervening call. The returned
  keys, values, identities and aliases are the same.
- **Scope:** `blocker-gap-round-native-method-map` exercises the stated
  contracts; `blocker-gap-round-native-method-map-inferred` exercises the
  [equivalent explicit form](#inferred-writable-fields-in-native-method-maps).
  The repair adds no external assumption.
- **Commit:** the introducing commit.

### A compiler node's initializer read through its parent

The compiler-kind rewrite is described under
[constructs avoided](#an-initializer-read-after-an-in-test-on-an-open-compiler-node).

### A graph field holding a lookup function

`FamilyGraph.constantName` in `tools/host-families.mts` states its result
as `Within<{ value: "keep"; store: "keep" }, string>`. The declaration
reader supplies a lookup over saved constants, followed by `String` on a
number or string when no constant matches. The lookup reads its inputs
and preserves values and array stores.

- **Repair:** the field retains the supplied function's effect, and its
  definition in `tools/declaration-graph.mts` states the same effect. The
  existing [stated-effect checks](SOURCE-ELABORATION.md#stated-effects)
  require a definition to meet that statement. These erased annotations
  preserve the calls, receivers, results and exceptions.
- **Scope:** `blocker-gap-round-graph-find` checks the field call in a
  `find` callback and a supplied lookup definition. Preserving the array
  store keeps every visited position present. `invalid-graph-find-effect`
  retains the ordinary-function contract, which permits an alias to shrink
  the array and requires the callback to accept `undefined`. The repair
  uses the existing effect and native `find` contracts and adds no external
  assumption.
- **Commit:** the introducing commit.

### A primitive overlay enumerated through an open record

`primitiveOverlay` in `tools/array-prototype.mts` states both a readonly
string dictionary of overlay-entry arrays and the required keys
`string`, `number` and `boolean`. Its initializer supplies those three
arrays. The dictionary retains the value contract of every own string
key when `reviewedEntries` enumerates it with `Object.values`.

- **Repair:** the dictionary annotation preserves the initializer’s value
  contract alongside its required keys. A finite-key record alone leaves
  other own values unconstrained, so enumeration supplies `unknown`
  elements to the enclosing `flatMap` callback. The annotation is erased
  and changes no execution.
- **Repair:** `interfaceOverlay` states its constructed `Map` type. Its
  `values()` iterator retains the host identity that the existing spread
  contract requires; a structural `ReadonlyMap` may supply a client iterator.
  This annotation also changes no execution.
  `spread-readonly-map-values-refused` retains the structural iterator’s
  spread refusal.
- **Scope:** the existing [dictionary enumeration contract](SOURCE-CONTRACTS.md#library-globals)
  and closure checks establish the obligation.
  `blocker-gap-round-nested-filter` exercises the nested callbacks;
  `invalid-gap-round-nested-filter` retains the finite-key-only refusal.
  No external assumption is added.
- **Commit:** the introducing commit.

### An array pattern's first element after a length test

The `Object.assign` branch of `expr` in `tools/fragment-expressions.mts`
requires a target, rejects spread arguments, and binds
`const [target, ...sources] = node.arguments`. Its length test establishes
that a target is present at run time. The array contract states no lower
length bound ([index reads](PROGRAM-TYPING.md#reads-at-an-index-from-the-length)),
so the destructured value's checked type includes `undefined`.

- **Runtime check:** `target === undefined` calls `gate.fail` before
  `gate.expr(target)`. Narrowing the saved value establishes its argument
  type independently of subsequent reads or calls. Compiler node arrays
  supply nodes at their positions, so the check preserves the accepted
  source programs and their lowering.
- **Indexed guards:** `wrappedMethodCall` saves the first argument of a
  lowered intrinsic before testing it and assigning its receiver. Its
  `read` comes from `expr` or `chainLink`; `Gate.intrinsic` holds the ordinary
  argument arrays those readers construct, including the literal arrays for
  `%ElementAt%`, `%ByteAt%` and `%Read:k%`. The guard and assignment have no
  intervening call or write. Saving the first read therefore preserves the
  receiver, failure and evaluation order for these AST arrays. The callee
  checks remain before that read; member reconstruction, token lookup,
  reductions and source-argument mapping remain afterward.
  Repeated indexed truthiness would require checked knowledge connecting a
  particular store position to its observed value. The existing linked-read
  rule connects named fields; array reads use the required, optional and
  rest position rules. Narrowing a saved value uses the existing binding
  rule without strengthening the array's invariant storage contract.
  `blocker-next-indexed-refinement` checks the saved element.
- **Scope:** `blocker-gap-round-assign-target` checks the saved value;
  `blocker-gap-round-assign-target-length-only` checks the equivalent
  form of the [avoided length-only read](#an-array-target-justified-only-by-length).
  The direct check uses the existing narrowing rules and adds no external
  assumption.
- **Commit:** the introducing commit.

### An early captured function's returned function type

`collectDeclarations` in `tools/declaration-graph.mts` creates closures
that mention `capturedAt` before its declaration. Its outer arrow states
the result type `(parameter: ts.TypeParameterDeclaration) => TypeTerm`,
the signature of the inner arrow it returns.

- **Repair:** the annotation retains the function type at the early
  binding's storage contract. The existing [early-binding checks](SOURCE-ELABORATION.md#lexical-bindings-before-initialization)
  check initialization and reads against that contract. The annotation is
  erased and changes no execution; `blocker-gap-round-early-capture`
  exercises the same returned-function annotation.
- **Scope:** the existing function and early-binding mechanisms establish
  the obligation, with no external assumption.
- **Commit:** the introducing commit.

### A part union that leaves its other arm's key unstated

The `build` expression's parts in `tools/fragment.mts` are named fields
or spread operands. A named field's contract states `spread?: never`, as
`ObjectPart` in `tools/fragment-support.mts` does. This records the grammar
its constructors supply: a named field carries `name` and `e`, and a
spread carries `spread`. The existing record contracts and narrowing on
`undefined` establish which value the traversal reads.

- **Repair:** `mapExprParts` tests `p.spread !== undefined` before mapping
  the spread operand. The named arm's stated optional field reads only
  `undefined`; an arbitrary value or getter at that key does not meet its
  contract. An `in` test on a union leaving the key unstated cannot
  establish that read's type or effect. The case `invalid-in-union-read`
  states the repaired contract; `invalid-in-union-part` retains the
  unstated-key refusal and `invalid-in-union-getter` exercises the getter
  under Node.
- **Repair:** the declaration-name read in `writtenApplications` tests
  the declaration kinds that terminate its enclosing walk. Each kind
  states its `name` member in the compiler API contract. The kind tests
  retain the walk's established fact at the read.
- **Scope:** these repairs use the existing record and host-family
  contracts and add no external assumption.
- **Commit:** the introducing commit.

### The host identity of an alias-expansion set

`TermScope.expandingAliases` in `tools/type-term.mts` holds the set of
associated-result aliases being expanded. Its sole supplied value is a
fresh `Set` copied from the enclosing scope and extended with the alias.
Copying requires the host iterator contract; a structural `ReadonlySet`
also admits client-defined iterators
([collection construction](SOURCE-CONTRACTS.md#library-globals)).

- **Repair:** the field states `Set<TypeAliasDeclaration>`, the type of
  every value supplied to it. Its readers use `has` and copy it with
  `new Set(scope.expandingAliases ?? [])`. The annotation retains the
  host identity established by construction; it changes no execution.
- **Support:** the existing constructor forms state the array and host-set
  alternatives in one parameter at the same element type. The producer
  compares union arms through their declarations when selecting a form;
  Lean checks each argument against that form. The case
  `blocker-census-set-copy` states the same host identity, while
  `invalid-set-copy-readonly` exercises the structural input's refusal.
- **Commit:** the introducing commit.

### A guard that promises more than its body checks

`isRecordList(v): v is Record<string, unknown>[]` returned
`Array.isArray(v)`, and `isList(v): v is unknown[]` promised a writable
array of any elements. TypeScript does not check a guard's promise; TScert
does, and refuses it.

- **Rewrite:** the guard promises what its body establishes:
  `isList(v): v is readonly unknown[]`, and a reader checks each element
  where it reads it. A first rewrite, `Array.isArray(v) && v.every(isObject)`,
  was still unsound: `every` skips holes, so `new Array(1)` passed with an
  `undefined` element.
- **Pattern:** a type predicate's promise is narrowed to the body's tests,
  or the body gains the tests the promise needs, element by element where
  the promise is about elements.
- **Commits:** 4db5021, 54aa29f (`tools/claim-text.mts`, `tools/diagnostic-view.mts`).

### A dictionary guard over `unknown`

The readers of claims, type graphs and diagnostics took `unknown` and used
`typeof v === "object" && v !== null` as a guard for a dictionary. For an
arbitrary value that test admits class instances and host objects, so the
dictionary promise cannot be established, and every helper built on it was
refused.

- **Rewrite:** the readers take `JsonValue` (`null | boolean | number |
  string | readonly JsonValue[] | { readonly [key: string]: JsonValue }`),
  the type of what they actually read, over which the same tests decide
  the arms.
- **Pattern:** a value read as data is typed by the data's grammar at the
  boundary where it enters (`JSON.parse`, a decoder), not as `unknown`
  inspected by structural tests.
- **Commit:** 795f331 (`tools/calculus.mts`, `claim-text.mts`, `claim.mts`,
  `type-graph.mts`, `diagnostic-view.mts`).

### An annotation weaker than the value the code relies on

`bigintValue` took `unknown` and read a field after an `in` test on an open
object, which no rule admits; `readExplanations` read `JSON.parse`'s result
as `unknown` the same way.

- **Rewrite:** state the type the producer of the value guarantees: the
  synchronous API's bigint literal value (kept `unknown` where the API may
  leave it absent, and spelled only when it is a bigint), and `JSON.parse`'s
  result at a declared JSON type.
- **Pattern:** replace a test-and-read on an open object by the declared type
  of the value's source, where that source's contract states it.
- **Commits:** 2288e06, c76d588 (`tools/computed-types.mts`,
  `pipeline/verify-source.mts`).

### A function called through a field whose annotation states no effect

A method of the gate held as a field (`Gate.abrupt: typeof
statements.abrupt`) and called in a `findIndex` callback, `list.findIndex((s)
=> gate.abrupt(s))`, is read at the field's contract, its annotation, an
ordinary arrow, which states no effect
([calls through a location](SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification)).
A `Gate` whose `abrupt` shrinks the list through another reference is a
value of the type, so the callback is `findIndex`'s unrestricted one, its
element `Statement | undefined`. Only the module function the field is
initialised with keeps the list, and no annotation states that the field
holds it.

- **Rewrite:** a function that reads nothing of the gate is a module
  function recursing through its own binding, `abrupt(s: Statement):
  boolean`, called as `abrupt(s)`; `Gate` holds no field for it. Its effect
  is certified from its body.
- **Pattern:** a function that needs nothing of the object it is reached
  through is called by its binding, whose certified signature a call reads.
- **Commit:** ec3d161 (`tools/fragment-statements.mts`,
  `tools/fragment-parse.mts`).

### A key tested with `in` on an open record

The gate's answers for a node (`staticType`, `contextualParam`,
`assignTypes`, `computedType`, `blockType`, `completion`, `symbolName` of
`tools/declaration-graph.mts`) were each a result or `{ refused: string }`,
read with `if (inferred && "refused" in inferred) gate.fail(node,
inferred.refused)`. After the test the result arm stays possible: an open
record may own `refused` at any type, so reading `inferred.refused` as a
string is refused on principle (`invalid-in-open`,
`invalid-in-open-closure`).

- **Rewrite:** every answer is one shape, `Answered<T>`, `{ ok: true; value:
  T } | { ok: false; refused: string }`, produced and read by its `ok` tag.
- **Pattern:** an `in` test that stands for a tag becomes a tag.
- **Commit:** a3755f0 (`tools/declaration-graph.mts`,
  `fragment-parse.mts`, `fragment-expressions.mts`, `fragment-classes.mts`).

### An index read whose range a check elsewhere establishes

`Object.assign`'s callable form read `const initial = node.arguments[1]` and
tested `ts.isObjectLiteralExpression(initial)`
(`tools/fragment-expressions.mts`), after `callableAssign`
(`fragment-support.mts`) had tested `node.arguments.length === 2` and the
two arguments. TypeScript types an index read at the element type; at run
time a read past the end gives `undefined`, so TScert reads it at
`Expression | undefined`. A compiler-API guard's promise holds on its
domain, the family's nodes ([the domain obligation](HOST-FAMILIES.md#calls)),
so the guard narrowed nothing for an argument that may be `undefined`, and
the read `initial.properties` after it was refused ("missing field
properties"). The length test that makes the read in range was in another
function, an implicit correlation.

- **Rewrite:** the check returns what it establishes: `callableAssign`
  returns the call, the arrow and the object literal it tested, or null,
  testing each argument against `undefined` before its guard, and its
  callers read those.
- **Pattern:** a value whose presence another function checks becomes that
  function's result.
- **Commit:** 87afc37 (`tools/fragment-support.mts`,
  `fragment-parse.mts`, `fragment-expressions.mts`).

### A rest parameter's reading tested with `in`

`restPositions` (`tools/type-term.mts`) read a rest parameter's type as
`{ positions: TypeTerm[] } | { element: TypeTerm }`, and `signatures` and
the declaration graph's signatures told the arms apart with
`"positions" in contract`. After the test the `element` arm stays
possible, since an open record may own `positions` at any type, so reading
`contract.positions` was refused on principle ("missing field
positions").

- **Rewrite:** each arm carries `k`, `{ k: "positions"; positions }` or
  `{ k: "element"; element }` (`RestPositions`), produced and read by `k`.
- **Pattern:** an `in` test that stands for a tag becomes a tag.
- **Commit:** ddb9b4f (`tools/type-term.mts`,
  `declaration-graph.mts`).

### A cache in an optional field of a shared object

`Gate.resolve` (`tools/fragment-expressions.mts`) built the file's bindings
on its first call and stored them with `gate.bindings = bindings`, the field
declared `bindings?: Map<Node, Map<string, Node>>`. A value of type `Gate`
may lack an optional key, so the write may add a key to the object, which
the gate's other holders see; the calculus types a key-adding write only as
the copy of a local's own fresh object
([key-adding writes](PROGRAM-TYPING.md#key-adding-writes)), so the write is
refused on principle (`invalid-optional-write-alias`).

- **Rewrite:** the field is always owned, `bindings: Map<Node, Map<string,
  Node>> | null = null`, and `resolve` reads it into a local, building and
  storing the table where it is `null`.
- **Pattern:** a field written after construction is declared with an
  initializer and a type that holds its absent state (`T | null`), so a
  write replaces its value and adds no key.
- **Commit:** 1fd49eb (`tools/fragment-parse.mts`,
  `fragment-expressions.mts`).

### A `map` callback calling a method of a structurally typed object

`protocolPattern` (`tools/fragment-statements.mts`) built its bindings as
`const bindings: BindingAst[] = named.map(({ cell, name }) => ({ …, name:
gate.local(name), namePos: gate.span(name), … }))`, and its `let` cells by a
`map` callback calling `site.span()`. A method reached through a value of a
class's or an object type is read at its signature, which states no effect:
any value of the type may hold a method that changes any storage. So each
callback is unrestricted, `map` takes its signature with holes
([natives](FOOTPRINTS.md#natives)), and its result is no `BindingAst[]`
(`invalid-map-method-call-effect`, run under Node: a `Names` whose `local`
pops the mapped array leaves a hole). The array mapped here is local and
reaches no such method, which only separating storage an unknown call cannot
reach would show ([deferred precision](FOOTPRINTS.md#deferred-extra-precision)).

- **Rewrite:** each array is built by a `for...of` loop pushing onto a fresh
  `BindingAst[]`, calling the methods in the same order; `push` keeps the
  array dense whatever the calls do (`map-method-loop-push`).
- **Pattern:** an array whose elements need calls of unbounded effect is
  collected by a loop pushing them, rather than by a `map` callback.
- **Commit:** 9ed9407 (`tools/fragment-statements.mts`).

### A stack popped through a field

`Gate.enterTypeParams` and `leaveTypeParams` (`tools/fragment-parse.mts`)
left a frame with `this.typeParamScopes.shift()` and
`this.resolutionScopes.shift()`, and `protocolForOf`
(`tools/fragment-statements.mts`) handed `closeStatements` a site record
whose `entry` and `span` were `entries.shift()` and `spans.shift()`. A
`shift` of a store the call did not allocate changes it beyond `grow`, so a
statement of `{value: any, store: grow}` on the gate's lowering code, which
`expr`'s contract closure needs
([the draft's §5](drafts/method-effects.md#5-what-a-statement-may-say)),
does not hold of a body calling them, although no reader keeps either stack
and no other code reaches the site lists. Showing that a shrinking store is
unreachable from the caller is the
[deferred precision](FOOTPRINTS.md#deferred-extra-precision). The rewrite
is an exception to the stance above, approved by the owner for the
statements that need it (D5, 2026-10-23).

- **Rewrite:** the stack fields lose `readonly`, and leaving a frame writes
  each field with its remainder, `this.typeParamScopes =
  this.typeParamScopes.slice(1)`, `leaveTypeParams` keeping its order and
  its refusal of an empty stack; the site record reads each list at its own
  counter, `entries[nextEntry++]` and `spans[nextSpan++]`, each keeping its
  exhaustion check.
- **Pattern:** a stack or queue whose holders read it only through one
  field is popped by writing the field with its remainder, and a list
  consumed in order is read at a counter; a field or cell write is within
  `{value: any, store: keep}`.
- **Commit:** 84cb902 (`tools/fragment-parse.mts`,
  `tools/fragment-statements.mts`).

### Mutually exclusive fields in an open union

`guardOf` (`tools/fragment-guards.mts`) and `samePromise`
(`tools/type-graph.mts`) selected a promise with `"guards" in promise`.
The annotation `{ guards: { param: number } } | { asserts: { param:
number } }` permits the assertion arm to own `guards` at another type.
Presence alone therefore cannot justify the subsequent parameter read.
`blocker-in-field-narrowing` demonstrates the same missing guarantee by
returning `undefined` from a function annotated to return `number`.

- **Rewrite:** state the exclusivity the constructors provide: the other
  arm declares the selection field optional at `never`, and readers test
  its value against `undefined`.
- **Pattern:** a union selected by the presence of a field states that
  field's absence on its other arm. The field's defined value selects the
  arm. This preserves the objects each constructor produces.
- **Functions:** `guardOf`, `samePromise`; compiler setup's `identify`,
  `current`, `compilerChoice`, `launcher`, `openFrontEndCompiler`;
  `lowerModuleText`, `parseModules`; `writtenApplications`;
  `expr`, `objectFields`; `importedGuard`, `importedExport`; and the
  declaration graph's `reexported` and global selection in `collectDeclarations`.
  Their contracts are `CallPromise`, `Installation`,
  `CompilerImplementation`, `LoweredModule`, `Determined`, `ObjectPart`,
  and the results of `identify`, `importedExport`, and `selectGlobal`.
- **Commit:** the introducing commit, `State the contracts used by the front end's negative patterns`.

### A decoder's result asserted over parsed storage

`decodeLabels` and `decodeGraph` (`tools/type-graph.mts`) and
`decodeClaimType` (`tools/claim.mts`) checked a parsed document field by
field and closed with an assertion of the decoded type (`return v as
Labels`, `return value as TypeGraph`, `return o as ClaimType`);
`isClosedFootprint` and `isCallEffect` promised `ClosedFootprint` and
`CallEffect` of the parsed object they tested. A check of the current
contents establishes nothing of the storage's contract: the parsed list
stays a `Json[]` its caller may write a string into, which the asserted
`number[]` then holds (`invalid-decoder-closing-assertion`, run under Node:
`typeof first('[1]')` is `"string"`), and a test of a field's value does not
bound the values written there later.

- **Rewrite:** each decoder returns fresh storage built from the values it
  checked: a list by `map`, each element tested as `map` visits it; an
  object as a literal of its checked fields, an optional field present
  where the document has it; a clause and a claim atom by the decoder of
  its kind, the kind found in a list of the kinds (`CLAUSE_KEYS`,
  `STRING_CLAUSE_KEYS`, `ATOM_KINDS`) that does not compile where it differs
  from its union. `decodeClosedFootprint` and `decodeCallEffect` take the
  guards' place, answering `undefined` where they answered false.
  `ClosedFootprint`, `CallEffect` and the fields and children of
  `CallPromise` are readonly, a control forging an effect constructing its
  replacement as a fresh object, and `CallPromise` states its two arms
  alone. Every decoder accepts the documents the original accepted and
  throws the original's message at the first malformed part, in the
  original's order; its result has the fields of the parsed object, which
  the decoders require exactly, and is another object, whose identity no
  caller compares. The `refs` and `dict` clauses state the `stable` field
  the decoder accepts, and a diagnostic record's `types` is the document's
  rows, which `readDiagnostic` checks with `decodeGraph` and its view prints
  as JSON.
- **Pattern:** a decoder of parsed JSON returns fresh storage of the values
  it checked.
- **Functions:** `decodeLabels`, `decodeGraph`, `decodeClosedFootprint`,
  `decodeCallEffect` (`tools/type-graph.mts`); `decodeClaimType`, `atom`,
  `recordAtom`, `functionAtom` (`tools/claim.mts`); `isOrdinary`
  (`tools/claim-text.mts`); the two effect edits in the filter-guard
  forged-evidence control; `decoder-fresh-result` is the pattern as a case.
- **Commits:** `State the contracts used by the front end's negative
  patterns`, which made the effect types readonly, and the introducing
  commit.

### Type terms compared through their semantic fields

`tools/array-prototype.mts#mergeRefusal` compares a member's kind,
optionality, readonly flag, type parameter bounds and signatures. Each term
is represented by [`termText`](../tools/named-record.mts), the shared
printer of the `TypeTerm` grammar. Binder substitutions use the same term
text beside each binder name, in the native map's iteration order. Fresh
outer records and arrays contain strings, Booleans and null and are keyed
by `JSON.stringify`. The complete method/property union is intersected with
`JsonObject` at its allocation, retaining both its named fields and its
recursive data bound.

- **Repair:** an ordinary `TypeTerm` record describes its named fields;
  it does not constrain every additional string key to recursively plain
  data. Naming the semantic fields retains the whole term contract without
  exposing arbitrary extra keys through `Object.entries`.
- **Equality:** term location spans and reference argument locations do not
  distinguish contracts. A declaration identity's span does. Field insertion
  order and extra own fields do not distinguish the same term. The shared
  printer owns these decisions; the merge reader owns its member flags and
  binder names.
- **Member checks:** traversal order, binder order, member flags, signature
  alternatives and unsupported-syntax refusals are the merge reader's. Its
  result states a refusal and the set of admitted member names. The internal
  key uses the term grammar's equality decisions.
- **Effects:** term printing reads the declared data fields under its checked
  normal-return footprint. The surrounding arrays and objects are fresh
  plain data. Native map iteration and its order retain the existing
  collection contract. The comparison introduces no external assumption.
- **Scope:** `blocker-round-binder-entries` supplies a source-owned term through
  the map's ordinary `TypeTerm` boundary. The generic native-map spread case
  and recursive dictionary-printer case exercise their independent contracts.

### An intersection owning its writable parts

`tools/type-term.mts#oneTerm` returns a sole function term directly and
constructs an intersection for the other arities. The intersection's
`parts` array permits every `TypeTerm`; its input array permits only
function terms. An intersection therefore owns a fresh array constructed
at the full element contract.

- **Repair:** copy the function terms into fresh `TypeTerm[]` storage.
  Publishing the input through the broader writable result lets a caller
  replace a function with an atom through `parts`, then read the original
  function array at a value without `params`.
- **Counterexample:** `invalid-prep-intersection-function-array` publishes
  the shared array. Writing an atom through the intersection and reading
  `functions[0].params.length` throws `TypeError` under Node. The repaired
  `blocker-prep-intersection-function-array` retains the original functions
  through that write and returns the same function object for a singleton.
- **Behaviour:** the terms and their order are retained. Empty and multiple
  terms receive independent writable storage; the singleton's identity is
  retained. Writes through an intersection leave the input array's
  function-only contract intact.


### A promise executor inheriting `any` from its context

The top level of `tools/unchecked.mts` collects each worker's result
through `new Promise<{ files: string[]; found: Found[] }>((done, fail) =>
…)`. TypeScript types the unannotated executor parameters from
`PromiseConstructor`: `done` as `(value: T | PromiseLike<T>) => void` and
`fail` as `(reason?: any) => void`, so `fail` has no stated contract and
the functions reading it (`check`, `findIn`, `decodeResult` in the census
of b81675f) are refused with the reason `blocker-contextual-any` shows.

- **Rewrite:** the executor states its parameters,
  `done: (result: { files: string[]; found: Found[] }) => void` and
  `fail: (reason: unknown) => void`, as `library-new-promise` does. The
  promise's resolving functions accept every argument these types admit,
  so the executor's calls and the promise's settlement are unchanged.
- **Pattern:** a callback whose context types a parameter `any` states the
  weakest contract its body uses.
- **Functions:** the module's top level, read by `check`, `findIn` and
  `decodeResult`.
- **Commit:** the introducing commit, `A promise executor of unchecked.mts states its resolving functions`.

### An import phase read through an undeclared host field

`importedModules` (`tools/fragment-parse.mts`) tested `"isTypeOnly" in
clause` and then `clause.isTypeOnly === true`. Equality checks the value,
so the open-union counterexample does not apply to this expression.
The compiler's `ImportClause` contract declares `phaseModifier`; its shared
runtime node also exposes an `isTypeOnly` getter reading the low phase bit.
For the supported ordinary and type imports, the two tests agree.

- **Rewrite:** read `clause.phaseModifier === ts.SyntaxKind.TypeKeyword`.
- **Pattern:** read a host object's declared member for the operation it
  represents. A shared runtime getter does not extend a host view's contract.
- **Functions:** `importedModules`, `namespaceMembers`, `importBindings`,
  and the declaration graph's local `closure` in `collectDeclarations`.
- **Commit:** the introducing commit, `State the contracts used by the front end's negative patterns`.

### A node's child read through `Reflect.get`

`argumentsOf` (`tools/type-probe.mts`) read an application's type
arguments as `Reflect.get(use, "typeArguments")` of a `Node`, kept the
result where it was an array and filtered its elements by a `kind` key.
`Reflect.get` runs [[Get]], which calls a getter no type states
([`Object` and `Reflect`](SOURCE-CONTRACTS.md#object-and-reflect)). On a
syntax node it calls the package's `RemoteNode` getter, which reads the
child its kind's child list names (`getNamedChild`,
`dist/api/node/node.generated.js:293-304`) and `undefined` for a kind
whose list has no `typeArguments`. The nine kinds whose list has it
(`childProperties` of `dist/api/node/protocol.generated.js`) each declare
`typeArguments?: NodeArray<TypeNode>`, which the call discarded.

- **Rewrite:** `typeArgumentsOf` (`tools/syntax.mts`), the compiler's guards
  of those nine kinds, then the declared member: `node.typeArguments ?? []`
  where one passes, and `[]` otherwise. It returns the node list itself
  where the original returned a fresh array of its elements; the one caller
  spreads it and reads its length, which see the same nodes. In its own
  module, the nine kinds join the arms of its run alone, and a caller reads
  its signature.
- **Pattern:** read a host object's declared member for the operation it
  represents, as for [an import phase](#an-import-phase-read-through-an-undeclared-host-field).
- **Functions:** `argumentsOf`, which `typeArgumentsOf` replaces, and
  `makeProbe`, which calls it.
  The other child fields use [their declared kinds](#compiler-children-read-at-their-declared-kinds).
- **Commit:** the introducing commit, `Reflect.ownKeys and a prototype compared with Object.prototype are read; a node's type arguments by their declared member`.

### A host test whose result its contract leaves unknown

`installed` (`tools/files.mts`) returned `statSync(path).isFile()` as a
`boolean`. A `Stats`'s `isFile` calls `this._checkModeProperty`, a writable
property of `Stats.prototype` other code may replace, so its contract
states the result `unknown` ([library modules](SOURCE-CONTRACTS.md#library-modules)),
and the return was refused.

- **Rewrite:** a runtime check, `statSync(path).isFile() === true`. It
  excludes one behaviour: with `_checkModeProperty` replaced by one
  answering a value other than a Boolean (`() => 7`), the original returned
  that value (7) where its annotation promises a `boolean`; the rewrite
  returns `false`. With Node's own prototypes the two agree.
- **Pattern:** a host predicate whose contract leaves its result `unknown`
  is compared with `true` where the code promises a Boolean.
- **Functions:** `installed`.
- **Commit:** 5c3f858.

### A parsed JSON value read as `unknown`

The readers of a package manifest (`digestOf`, `checkInventory` and
`checkedGuards` of `tools/family-activation.mts`, `originOf` of
`tools/declaration-graph.mts`, `manifestField` of `tools/files.mts`) and of
a worker's output (`isResult` of `tools/unchecked.mts`) typed
`JSON.parse`'s result `unknown` and read a member after `"k" in v`, which
no rule admits on an open object ("field read on non-object"), and
converted a member with `String`, which is admitted at a primitive only.
The parse had established the value's grammar, which the annotation
discarded.

- **Rewrite:** the parsed value keeps `Json`, `JSON.parse`'s result
  (`tools/calculus.mts`), and one reader per format reads it:
  `manifestMember` (`tools/files.mts`) returns an object's member at a
  manifest key, undefined at a non-object or an array; `decodeResult`
  returns the worker's result as fresh objects of its fields, or null.
  `"k" in v` and `v[k]` agree with these where neither `Object.prototype`
  nor `Array.prototype` holds the key, which the keys' types restrict them
  to, and a parsed array owns only its indices and its length.
  `stringOfJson` (`tools/calculus.mts`) converts a member as
  `String` does, by its arms: a primitive by a template literal; an array by
  joining its elements' conversions with commas, an element `null` or a hole
  as the empty string, nested arrays walked through a chain of positions; an
  object as `"[object Object]"`, or a `TypeError` with Node's
  message where the object owns `toString`, which JSON data never makes
  callable. Each reader throws where the original threw: `JSON.parse`'s `SyntaxError` of a text that is no
  JSON, in `digestOf`, `checkInventory`, `checkedGuards` and `originOf`;
  `manifestField` catches it and answers undefined, as the original did;
  `decodeResult` answers null where `isResult` answered false. One
  behaviour differs: the conversion of nested arrays uses no call stack, so
  an array nested deeply enough that Node's own `Array.prototype.join`
  exhausts the stack (a `RangeError`; 10,000 levels do under Node 26)
  converts to its text.

  `decodeResult`'s objects hold only the fields its callers read, where the
  original passed on the parsed object with any further members.
- **Pattern:** a value `JSON.parse` returns keeps its JSON type from the
  parse onward, and is read through a decoder of its format.
- **Functions:** `digestOf`, `checkInventory`, `checkedGuards`, `originOf`,
  `manifestField`, `relativeImportTargets`, `isResult`
  (rewritten as `decodeResult`), and their callers; `json-parse-manifest` is the pattern
  as a case.
- **Commit:** the introducing commit, `Parsed manifests and worker results keep their JSON type`.

### A scope copied with its hooks

`TermScope` in `tools/type-term.mts` is a record of own function fields.
Alias expansion, quantified signatures and generic class members copy that
record with a spread and override the hooks whose bindings change. The
record contracts and object-copy checks establish which hooks the copy
holds ([object spread](SOURCE-ELABORATION.md#object-spreads)).

- **Repair:** `fail`, `named`, `stated`, `associated`, `associatedAlias`,
  `symbol`, `literalKey`, `privateName` and `equation` are function fields.
  A method contract permits a member on the prototype, which a spread
  does not copy. The scope constructors in `type-term.mts`,
  `fragment-parse.mts`, `declaration-graph.mts` and `array-prototype.mts`
  allocate these hooks as own properties; their bodies use their arguments
  and closed-over values. Their field types retain each result and stated
  effect.
- **Cases:** `blocker-gap-round-scope-spread` copies the scope and overrides
  the alias hooks and source file. `invalid-object-spread-method` retains
  the refusal of a copy whose required hook may be inherited.

### A scope's hook read as an optional method

`TermScope` (`tools/type-term.mts`) declared its hooks `record`,
`computed`, `awaited`, `keys`, `modifiers` and `enumerated` as optional
methods, and the readers that pass one on or implement it apart from a
scope typed it by indexed access, `TermScope["record"]` or
`NonNullable<TermScope["computed"]>`. An optional method's function takes
the object it is a member of as its receiver, so the indexed access is a
function received by a `TermScope`
([indexed-optional-method](SOURCE-CONTRACTS.md#computed-types)), which a
reader calling it with no receiver does not give; `typeTerm` passed
`scope.record?.bind(scope)`, a method read off its object, which the
fragment refuses. Every implementation is an arrow, which uses no receiver.

- **Rewrite:** each hook's function type is written out as a named
  function type (`RecordHook`, `ComputedHook`, `AwaitedHook`, `KeysHook`,
  `ModifiersHook`, `EnumeratedHook`), and `TermScope` holds each as a field
  of that type; `typeTerm` and the parser pass `scope.record` as the value
  it is. An arrow ignores the receiver `.bind` gave it, so the calls return,
  throw and mutate as before.
- **Pattern:** a hook a scope holds and its readers pass on is a field of a
  function type, called without a receiver.
- **Functions:** `typeTerm`, `expandMapped`, `expandIdentity` and their
  callers in `tools/type-term.mts`; `libraryTerm`, `collect` and
  `collectDeclarations` (`tools/declaration-graph.mts`); `settleTerm`
  (`tools/named-record.mts`); `blocker-indexed-optional-method` (the
  method's function called with no receiver, a negative case) and
  `blocker-optional-method-bind` (a gap case) are the refused forms.
- **Commit:** the introducing commit, `A scope's hooks are fields of written function types`.

### A dictionary read at a key known only at run time

Tables built in TScert's code were records read at a string computed at run
time: the guard table's helper texts (`helpers`, read at
`module#name` in `checkedGuards` of `tools/family-activation.mts`), each
loaded module's exports (`entryLoaded[entry.name]`, `declaring[entry.name]`,
`target[imported.name]`, `namespace[imported]`, `entry?.[enum]` there), the
reviewed interfaces (`interfaceOverlay` of `tools/array-prototype.mts`, read
in `collect`), the intrinsics' definitions (`intrinsics`) and the
diagnostic variants' fields (`readDiagnostic`). Decoders of JSON read a
value at a key drawn from a list typed `string` (`atomText` and
`liftClause` of `tools/claim-text.mts`, `knowledge` of
`tools/diagnostic.mts`). Every object inherits `Object.prototype`'s
members, so a read at a string the object may lack can find `toString` or
`constructor`, a function where the type says a value or nothing, and TScert
refuses it (`invalid-dictionary-inherited-key`, run under Node). In
`checkedGuards` the defect was reachable: an import named `constructor`
passed `imported.name in target` and read `Object.prototype.constructor`,
and `readDiagnostic` read `variants["toString"]`, a function, as a field
list.

- **Rewrite:** a table built in the code and looked up at a run-time string
  is a `Map`, read by `get` and `has`, which find only the entries it was
  given: the module exports are a `Map` of each loaded namespace's entries,
  `hostEnumModules` (`tools/compiler-api.mts`) holds each namespace's, and
  the guard table states its helpers as pairs (`GuardTable.helpers`,
  `tools/host-families.mts`; `dev/guard-table.mts` writes them), each key
  once, from which `checkedGuards` builds a `Map` and refuses a table that
  states a key twice. Pairs keep the table's JSON form, which the stage
  keys hash (`activeFamilies()` in `pipeline/parse-stage.mts`); a `Map`
  serializes to `{}`. A JSON value read at keys from a fixed list is read
  at keys whose type is the union of those literals (`ClauseKey` of
  `tools/type-graph.mts`, `"call" | "construct" | "array"`), or by name
  (`k.cells`, `k.values`). Behaviour is kept at every key the tables hold;
  at a key naming an inherited member, a lookup finds nothing: the import
  binds no export, the diagnostic line is no diagnostic, and `intrinsics`
  throws `no intrinsic`.
- **Pattern:** a lookup at a string known only at run time is a `Map`'s; a
  read of a record is at a key whose type names no member of
  `Object.prototype`.
- **Functions:** `checkedGuards`, `importedExport`, `hostEnumObject`,
  `tagEnumObject`, `activatedModules`, `collect`, `intrinsics`,
  `readDiagnostic`, `knowledge`, `atomText`, `liftClause`, and their
  callers; `invalid-dictionary-inherited-key` is the refused read as a
  case.
- **Commit:** the introducing commit, `Run-time lookups go through a Map`.

### A field reread after a callback writing other storage

`atomText` (`tools/claim-text.mts`) printed an array atom by
`atom.required.map((t) => typeText(t, state))` and then
`atom.optional.map(…)`, both after `isList(atom.required) &&
isList(atom.optional)`, and a function atom's parameters by
`atom.params.map(…)` after `typeText(atom.this, state)`. `typeText` writes
`state.printable`, so the call keeps no heap fact
([a call that keeps the heap](PROGRAM-TYPING.md#a-call-that-keeps-the-heap)),
and the second read of the field is at its contract, a JSON value that may
be no array ("a read of map through a field holding an object beside null
or undefined"; `invalid-guard-field-call`, run under Node, is a callback
that writes the field). The atom is parsed data `state` does not reach,
which only separating storage an unknown call cannot reach would show
([deferred precision](FOOTPRINTS.md#deferred-extra-precision)).

- **Rewrite:** each tested field is read into a constant before the first
  call of `typeText`: `const requiredTypes = atom.required`, `optionalTypes`,
  `params`. A read of a field of a parsed object has no effect, so reading
  it earlier gives the value the later read gave.
- **Pattern:** a field a guard tested is read into a constant before a call
  that changes storage, rather than read again after it.
- **Functions:** `atomText`, and `typeText`, `printType` and the others
  calling it; `liftClause`, whose store clause maps `required` and
  `optional` through `liftType`, which writes `types.lifted`, and the
  functions calling it (`liftLabels`, `treeAtom`, `liftSignatures`).
- **Presence guards:** the array printer saves `atom.presence` immediately
  before calling `isArrayPresence`, and tests and prints that same value.
  The imported guard's ordinary signature permits value writes; its
  predicate applies to its argument value. Its implementation compares its
  argument with three primitive strings and writes no storage. The printer's
  actual callers supply ordinary data fields: `recordType` prints a `lift`
  result, internal `shown` and `treeAtom` print constructed lift results, and
  the printer controls supply object literals. The presence field's value
  stays unchanged during this guard call for these callers. Earlier recursive
  printing calls finish before the saved read. `blocker-next-presence-snapshot`
  checks the saved value through the real imported guard contract.
- **Commit:** the introducing commit, `Fields atomText's guards test are read before its callbacks run`;
  for `liftClause`, `A field's narrowing survives a map or forEach call whose callback changes nothing`.

### A wire document's strings checked at `unknown`

`illFormedString` of `tools/wire-strings.mts`, which finds a string of a
wire document that is not well-formed Unicode, took the document at
`unknown` and read `value.pos` after `"pos" in value` on an open object
("field read on non-object"). Its readers
pass a value `JSON.parse` returned; its writers (`parseFile`,
`parseFragment` and `lowerModuleText` of `tools/fragment-parse.mts`) pass
the document they are about to write with `JSON.stringify`, whose strings
are the strings the text carries.

- **Rewrite:** the check takes `Json`, `JSON.parse`'s result. A reader
  passes its parsed value (`decodeFlowDocument` and `decodeGraph` take
  `Json`); a writer passes the text it writes to
  `requireWellFormedText` or `wellFormedTextRefusal`, which parse the text
  back and check that, where the text holds an escape `\ud8`–`\udf`:
  `JSON.stringify` writes a lone surrogate as such an escape and a
  well-formed string as itself, so a text without one holds no lone
  surrogate. A writer refuses the same documents with the same message: a
  string of the document is a string of the text, and the nearest
  enclosing object stating `pos` states the same span in the text. The
  span is written as `[start,end)` where `pos` is two numbers, as every
  span of the Fragment is, and left out otherwise, where the original
  joined any array.
- **Pattern:** a check of the data a document carries reads the document
  as the format's parsed value: at the reader, the parse; at the writer,
  the text parsed back.
- **Functions:** `illFormedString`, `requireWellFormed`,
  `wellFormedRefusal`, `requireWellFormedText`, `wellFormedTextRefusal`;
  `invalid-lone-surrogate-string` is the writer's refusal as a case.
- **Commit:** the introducing commit, `A wire document's strings are checked at its JSON type`.

### A `Map` constructed with no type arguments

`query` in `tools/client-prototype.mts` stored `new Map()` into the memo of
a client's snapshots and of a snapshot's answers. TypeScript reads a
construction with no arguments by `MapConstructor`'s first signature,
`new (): Map<any, any>`, so the value is a `Map<any, any>` assigned where a
typed `Map` is held ("a call to the generic function 'Map' needs its type
arguments" in `query` and `guardClientRequests`, census of b81675f).

- **Rewrite:** state the type arguments the holding binding has:
  `new Map<unknown, Map<string, string>>()` and `new Map<string, string>()`.
- **Pattern:** a construction of a generic class whose type arguments
  TypeScript would read as `any` states them.
- **Commit:** 467af18b.

### A type alias recognised by a guard accepting a JSDoc `@typedef`

The front end recognised a type alias declaration with the compiler's
`ts.isTypeAliasDeclaration(node)` and then read its members
(`node.typeParameters`, `node.name`). The guard also accepts a JavaScript
file's `@typedef` (`JSTypeAliasDeclaration`), and is read by what its code
accepts ([guard recognition](HOST-FAMILIES.md#guard-recognition)), so its
true edge holds both kinds: it reads the members both shapes state
([audited shapes](COMPILER-API.md#audited-shapes)) and gives no
`TypeAliasDeclaration`. The
front end reads TypeScript files only, where the guard and the kind test
accept the same nodes ([restrictions](COMPILER-API.md#restrictions)).

- **Rewrite:** `isTypeAlias(node): node is Within<{ value: "keep"; store:
  "keep" }, TypeAliasDeclaration>` of `tools/syntax.mts` tests
  `node.kind === SyntaxKind.TypeAliasDeclaration`, and every recognition of
  a type alias in `tools/`, `dev/` and `tests/` calls it. Its promise is what
  its test establishes, so its true edge reads the declaration's members; on
  a JavaScript `@typedef` it answers `false`. It states the empty footprint
  ([stated effects](SOURCE-ELABORATION.md#stated-effects)), so a caller
  stating its own effect (`resolve`, `moduleFunction` and `inertRead` of
  `fragment-expressions.mts`, `typeStatement` of `fragment-statements.mts`)
  reads it within that effect.
- **Pattern:** a node is recognised by the kind whose members the code
  reads, where the compiler's guard accepts more kinds than that one.
- **Functions:** `isTypeAlias`, and the 33 functions reading an alias's
  members after the guard; `compiler-api-alias-kind-guard` is the guard
  and its reads as a case, and `blocker-type-alias-guard-member` a read of
  a member both kinds state after `ts.isTypeAliasDeclaration`.
- **Commit:** the introducing commit, `A type alias is recognised by its kind, excluding the JSDoc typedef`.

### A type node or an import recognised by a guard accepting another kind

The front end found the type node at a span with `ts.isTypeNode(node)`
(`typeNodeAt`, `computedAt` of `tools/declaration-graph.mts`) and returned
it at `TypeNode`, and recognised import declarations with
`ts.isImportDeclaration` (`importBindings`, `statementsOnPath`, and
`lowerFile`'s collection of `importNodes` in `tools/fragment-parse.mts`) and
used them as `ImportDeclaration`s. `isTypeNode` also accepts
`ExpressionWithTypeArguments` (kind 234), whose interface extends
`MemberExpressionBase` and no `TypeNodeBase`
([the node invariant](COMPILER-API.md#the-node-invariant)), and
`isImportDeclaration` also accepts `JSImportDeclaration` (346), a kind of
its own ([audited shapes](COMPILER-API.md#audited-shapes)): the code lacked
the test that excludes the other kind, so its true edge gave no `TypeNode`
or `ImportDeclaration` and the claimed result was refused. The spans the
front end asks for are of type annotations, and the files it reads are
TypeScript files, where neither other kind occurs at those points
([restrictions](COMPILER-API.md#restrictions)).

- **Rewrite:** `typeNodeAt` and `computedAt` test
  `ts.isTypeNode(node) && !ts.isExpressionWithTypeArguments(node)`, as
  `tools/written-applications.mts` does; `isImport(node): node is Within<{
  value: "keep"; store: "keep" }, ImportDeclaration>` of `tools/syntax.mts`
  tests `node.kind === SyntaxKind.ImportDeclaration`, and the three import
  sites call it.
- **Call boundary:** `readScope` of `tools/fragment-statements.mts` calls
  `isImport(st)` before passing `st` to `importedNames`, whose parameter is
  `ImportDeclaration`. The exact-kind test establishes that parameter's
  contract; `ts.isImportDeclaration` also admits kind 346. The case
  `blocker-census-import-guard-call` exercises the exact-kind guard and
  call, and `invalid-compiler-api-import-guard-call` preserves the broader
  compiler guard's refused call.
- **Pattern:** a node is recognised by the kind whose members the code
  reads, where the compiler's guard accepts more kinds than that one (as
  [`isTypeAlias`](#a-type-alias-recognised-by-a-guard-accepting-a-jsdoc-typedef)).
- **Functions:** `typeNodeAt`, `computedAt`, `statementsOnPath` (verified
  after the rewrite), `importBindings`, `lowerFile` (refused at later
  obligations); `blocker-compiler-api-type-node` is the guard's refusal as a
  case. `namespaceMembers` (`tools/namespace-members.mts`) calls `isImport`
  in its three import filters, whose predicates promise `ImportDeclaration`.
  `elaborationComputedMembers` tests the same before passing a member's
  descendant to `computedForm`, which answers `null` at kind 234, so the
  walk takes the same steps.
- **Commit:** the introducing commit, `A type node and an import are recognised by their kinds`;
  `namespaceMembers`, `Repairs and loop forms for the host cluster's own functions`.

### A binder bounded by a record with a writable field

`attemptAnswer` in `tools/files.mts` bounds its binder by
`{ answer: string | null }`, and `kindOf` calls it at
`{ answer: Kind }`, a narrower field type. A writable field's contract is
invariant, so the instance is outside the bound ("quantified call does not
satisfy the closure's bound: cannot establish object ≤ object" in the twelve
functions of `files.mts` that reach `kindOf`, census of b81675f).
`attemptAnswer` only reads the field.

- **Rewrite:** the bound is `{ readonly answer: string | null }`.
- **Pattern:** a bound states the access the generic body makes: a field the
  body only reads is readonly in the bound.
- **Commit:** the introducing commit.

### A typed tree walked as `unknown`

Five walks took a value of a known grammar at `unknown` and found its nodes
by key name: `namesArray` (`tools/declaration-graph.mts`, the type terms of
the declaration document's lists), `deferredIn` (`tools/named-record.mts`,
a declaration document, a lowered file and an imported module's entry),
`namesRead` (`tools/fragment-support.mts`, a Fragment expression),
`renamedModule` (`tools/fragment-parse.mts`, an imported module's entry)
and the visit of `presentObligation` (`tools/diagnostic-view.mts`, a
decoded calculus term). Each read a member after `"k" in v` on an object
of unknown type, which no rule admits ("missing field k"), and recursed
through `Object.values`. The value's type had
established its grammar, which the parameter's annotation discarded, and a
node kind added to the grammar was met by whatever key names it happened
to share.

- **Rewrite:** each grammar has one typed traversal of a node's parts, an
  exhaustive switch on its kind, so that a kind added to the grammar fails
  to compile until its parts are listed: `typeParts` (`tools/type-term.mts`)
  for type terms, which `visitType` and `someType` fold; the maps
  `mapExprParts`, `mapStmtParts`, `mapPatternParts`, `mapFunctionParts`
  and `mapDocument` (`tools/fragment-parts.mts`) for the Fragment AST and
  the declaration document, of which `forEachPart`, `documentHolds`,
  `moduleHolds` and `astHolds` are folds and `deepPartMap` the map of
  every part under a node; and `termParts` and `codeTerms`
  (`tools/diagnostic-view.mts`) for calculus terms. `namesArray` and
  `deferredInDocument`, `deferredInAst`, `deferredInModule` ask whether a
  document's type terms, or its declaration identities, hold a given node;
  `namesRead` folds the expressions under one; `renamedModule` maps a
  module's identities, binder names and application sites; the summary
  reads the slots among a term's parts, the parts of a part, and its call
  code's terms. Each answers what the walk it replaces answered: run side
  by side over every pipeline case's documents (2,363 cases), they agreed
  on every value (2,081 `namesArray` lists, 2,102 files' and 21 modules'
  deferred tests, the names read of every expression of 2,102 files, 21
  renamed modules, 257 summaries' slots), and on the slots of 2,788
  generated terms.
- **Pattern:** a value of a declared grammar is walked through that
  grammar's typed traversal.
- **Functions:** `namesArray`, `deferredIn` (rewritten as
  `deferredInDocument`, `deferredInAst` and `deferredInModule`),
  `namesRead`, `renamedModule`, `presentObligation`, and their callers;
  `typed-tree-fold` is the pattern as a case, and
  `blocker-in-unknown-walk` the refused walk. Two sites reading an
  object the compiler provides have no grammar of TScert's to walk:
  `privateClient` uses [the compiler-client boundary](#the-compiler-client-and-its-child-process),
  and the [syntax child readers](#compiler-children-read-at-their-declared-kinds)
  use the compiler node contract.
- **Commit:** the introducing commit, `Typed trees are walked through their grammar's typed traversal`.

### Type terms compared as untyped data

`sameIndex` (`tools/type-term.mts`) decides whether two index signatures
state the same contract, and compared their value terms with `sameData`, an
equality over `unknown`: it listed each object's entries with
`Object.entries`, at an array too, and recursed on the values. Its callers
hold `TypeTerm`s, which the parameter type discarded. Over `unknown`, the
call at an object is the overload at `{}`, whose parameter excludes host
objects ([excluding host values](HOST-FAMILIES.md#excluding-host-values)),
and `object` does not; the call at an array, which TypeScript resolves to
the generic overload, meets no dictionary.

- **Rewrite:** `sameTerm(a: TypeTerm, b: TypeTerm)` compares two terms by
  their kind, field by field, each `span` left out, and `sameIndex` calls
  it; a call effect's promise, a `JsonObject` of one key, is compared by
  its `JSON.stringify` text. A kind added to `TypeTerm` fails the
  compilation of `sameTerm`'s `switch`; a field added to a kind is compared
  only once `sameTerm` names it. Two terms that `sameData` called different
  only for the order of their fields' insertion are equal.
- **Pattern:** a comparison of data the caller has typed takes that type,
  and reads each field its type states.
- **Functions:** `sameIndex`, `sameTerm` and its helpers, and the functions
  of `tools/type-term.mts` reaching them.
- **Commit:** the introducing commit, `Index contracts are compared as type terms, kind by kind`.

### A caught error's fields read after `instanceof`

The front end recovers the payload of its own errors through private weak
identity tables. A catch binds `unknown`; `instanceof C` alone establishes
no field initialized by `C`, since an object can share its prototype without
having run its constructor (`instanceof-unknown-refused`).

- **Rewrite:** `declarationError` and `ioFailure` register each error in a
  module-private `WeakMap<object, Payload>`. `declarationSpanOf` and
  `ioFailureOf` first test for a non-null object, then return its
  registered payload or `undefined`. Lookup preserves the entry, so the
  same error can be handled repeatedly. The tables do not keep an otherwise
  unreachable error alive; collection timing is unspecified. A gate refusal
  is a plain `Error` whose message carries its location, and has no payload.
- **Observable contract:** a declaration refusal is an `Error` with the supplied message and optional
  cause, and its registered payload is the supplied span. These errors have
  no public `pos` or `at` field. Spans and causes retain their supplied
  identities; registration is not a deep snapshot. An I/O failure carries
  its operation, path, message and cause, and its registered payload holds
  that cause. `orAbsent` returns `null` whenever the same registered failure's
  cause denotes absence, including repeated calls; other errors propagate
  by identity. `toolFailureOf` attributes an I/O failure to the operation
  site, skipping the maker's frame. A foreign value, including a structurally
  matching error or a proxy, has no registration. Lookup invokes no property
  access or user callback on that value.
- **Trust:** these lookups use the audited standard
  [WeakMap contract](SOURCE-CONTRACTS.md#weak-tables), including the assumption
  that standard objects and their methods are not tampered with.
- **Functions:** `lowerFile`,
  `collectDeclarations`, `orAbsent` and `io` use these payloads.
  `tests/caught-errors.mts` exercises the real I/O helpers, repeated
  handling and caller attribution; `tests/trusted-inputs.mts` checks repeated
  lookup of a declaration refusal from the actual declaration collector.
- **Pattern:** what a thrown value carries is found by its identity in a
  table its maker fills, rather than read off the caught value.
- **Commit:** the introducing commit, `Caught errors' fields are found in their maker's weak table; WeakMap gets a contract`.

### A caught value's message read by its descriptor

`messageOf` (`tools/thrown.mts`) supplies the text of what was thrown to
`ioFailure`, `CompilerFailure`, `stackExhaustion` and the front end's
reports. It read `thrown.message` after `thrown instanceof Error`, and
`String(thrown)` otherwise. `instanceof Error` constrains only the prototype
chain, so `message` may hold any value (`invalid-instanceof-error-message`,
run under Node: a number); the read may run a getter; and `String` of an
object runs its `toString`, `valueOf` or `Symbol.toPrimitive`.

- **Route:** a runtime check, with no assumption about what code throws.
- **Source:** a primitive is converted by `String`, which runs no code of a
  primitive's. Of an object or a function, `messageOf` binds
  `Object.getOwnPropertyDescriptor(thrown, "message")?.value` to a constant
  and returns it where `typeof` says it is a string. An `Error` owning no
  `message` gives `""`, the message `Error.prototype` holds; any other
  object gives the fixed text `a thrown object that owns no string
  message`. `stackExhaustion` compares `messageOf(thrown)`.
- **Behaviour:** an error's own string message, the empty message of
  `new Error()` and a primitive's text are unchanged. A message that is no
  own data string, an object's own conversion hooks and a function give the
  fixed text, where they gave the hook's or the getter's result, or threw
  its exception. An object deriving from an error inherits no text but
  `""`. No getter, conversion hook or proxy `get`, `has` or
  `getPrototypeOf` trap runs.
- **Support:** the descriptor of a value that may be a host object hands
  its field to the program only as a string: the constant's read is the
  intrinsic `%OwnString%`
  ([`Object` and `Reflect`](SOURCE-CONTRACTS.md#object-and-reflect)),
  which admits any operand. It extends the descriptor's contract and states
  no new assumption: [[GetOwnProperty]] runs no code, as `Object.hasOwn`'s
  admission of host objects states, and no object is a proxy
  ([trust surface](DESIGN.md#trust-surface)).
- **Evidence:** `caught-message` and `invalid-caught-message-declared`
  (run under Node: a number declared `string`); `tests/tool-failures.mts`
  runs the real formatter and `ioFailure` on a number message, a message
  getter, a proxy, own conversion hooks, a function, primitives and errors,
  and checks that no code of the thrown value ran and that the wrapper keeps
  its cause's identity.
- **Pattern:** a caught value's text is read by its own data descriptor,
  tested a string, never by a lookup or a conversion of the object.
- **Functions:** `messageOf`, `stackExhaustion`, `CompilerFailure`,
  `IoFailure` and `ioFailure`, and the functions reaching them.
- **Commit:** the introducing commit, `Read a caught value's message by its own data descriptor`.

### A type term's text made by a replacer

Three keys of type terms, a term's text with its spans aside, were made by
`JSON.stringify` with a replacer function dropping the `span` keys:
`termText` (`tools/named-record.mts`, the key of a computed declaration's
instance and the comparison of a member or an index an interface and its
base both declare), `written` (the overlay's stated arguments against a
contextual type's, `collectDeclarations` of `tools/declaration-graph.mts`)
and `unspanned` (the readings of a family's member, `collect`). A replacer
is client code `JSON.stringify` calls on every member, with the holder as
`this` and the value after its `toJSON`, and its result is serialized in
turn: the call is refused (`invalid-json-stringify-replacer`), and so is
`JSON.stringify` of a type term without one, a record type no `JsonValue`
admits. Supporting a replacer would take the serialization of
the arbitrary value it returns, which is the refusal of a record type
again. The callers hold `TypeTerm`s, whose grammar the parameter type
`unknown` discarded.

- **Rewrite:** `termText(t: TypeTerm)` writes a term's text kind by kind,
  each kind's fields in the order `TypeTerm` declares them, as JSON:
  `JSON.stringify` serializes only its strings and numbers. A declaration
  identity's span is written (`identityText`); any other span, and a
  reference's argument spans, are left out. `termsText`, `fieldText` and
  `indexText` write a list of terms, an object type's field and an index
  signature. All three keys are `termText`'s, so `written` and `unspanned`
  read a declaration identity's span, and `written` no reference's
  argument spans. Over every term of the 2,110 declaration documents the
  pipeline cases make (1,171,836 terms, 104,404 fields, 271 index
  signatures), the replacer's `termText` and the new one partition the
  terms, the fields and the indexes alike, but for classes that differ
  only in the order their fields were made in (73 of terms, 21 of
  fields); `unspanned`'s classes split once, at two declarations of
  `Date` in `lib.es5.d.ts`, and `written`'s merge where only a
  reference's argument spans differ. Run side by side in every pipeline
  case, the 542 texts the sites made (262 by `unspanned`, 276 instance
  keys, 4 fields) are the replacer's texts, character for character, and
  every case keeps its outcome. A kind added to `TypeTerm` fails the
  compilation of `termText`'s `switch`; a field added to a kind is written
  only once `termText` names it. Two terms the replacer's texts called
  different only for the order their fields were made in have one text.
  A function signature's call promise, `{ guards: { param } }` or
  `{ asserts: { param } }`, is written by `promiseText` from its one key
  and its parameter, the text `JSON.stringify` gives such an object, and
  `sameEffect` (`tools/type-term.mts`) compares two promises by their key
  and parameter (`samePromise`): a promise type is a record type no
  `JsonValue` admits, so `JSON.stringify` of one is refused
  (`invalid-stated-effect-stringify`). Every promise is built fresh with
  that one key, each an object literal of it (`promiseEffect`,
  `decodeCallEffect`, the reviewed contracts), so the texts and the
  answers are the same.
- **Pattern:** a key of data the caller has typed is written from that
  type, field by field.
- **Functions:** `termText` and its helpers, `recordShape`'s `inherit`,
  `instanceOf` and `collect`'s member readings
  (`tools/declaration-graph.mts`), and `collectDeclarations`'s check of
  stated arguments; `typed-tree-text` is the pattern as a case, and
  `invalid-json-stringify-replacer` the refused call.
- **Commit:** the introducing commit, `A type term's text is written kind by kind from its type`.

### Optional fields added to an annotated local

`inferredTerm` (`tools/computed-types.mts`) collected an object type's index
signatures into `const indexes: { stringIndex: … | null; numberIndex?: …;
symbolIndex?: … } = { stringIndex: null }`, writing `numberIndex` and
`symbolIndex` in a loop, and spread `indexes` into its result. A key-adding
write's copy keeps an optional field of the accumulator only where its type
excludes a prototype, which a record of optional fields does not state
([restriction L7](COMPILER-API.md#restrictions)): the copy after `indexes.numberIndex = index`
is typed without `symbolIndex`, which the annotation requires where the
loop's paths join.

- **Rewrite:** each index is a `let` local, `null` until its signature is
  read, and the result states each present one by a conditional spread,
  `...(numberIndex ? { numberIndex } : {})`. Field values and omission are
  preserved. The number and symbol fields occur in a fixed order; their
  enumeration and JSON serialization order can differ from discovery order.
- **Pattern:** an object whose optional fields are found one at a time is
  built whole once they are known.
- **Functions:** `inferredTerm`.
- **Commit:** the introducing commit.

### An array result annotated wider and writable

`typesOf` (`tools/unchecked.mts`) returned the array form of
`getTypeAtLocation`, a `(Type | undefined)[]`, at its annotation
`(Type | undefined | null)[]`, the `null` standing for a node the compiler
panics on. TypeScript reads arrays covariantly; a writable array's element
contract is invariant ([arrays](POSITIVE-TYPES.md#arrays)), so the return is
refused, though no caller writes the result: `findIn` only reads it.

- **Rewrite:** the result is annotated `readonly (Type | undefined | null)[]`,
  which every array of a narrower element meets. The function's code and
  values are unchanged.
- **Pattern:** a result only read is annotated as a readonly array.
- **Functions:** `typesOf`.
- **Commit:** the introducing commit.

### A fresh array's writable element contract

`expr` (`tools/fragment-expressions.mts`) keeps the named-field arm of
`ObjectPart` with `flatMap`. That arm has the optional exclusion
`spread?: never`; the allocation's writable `fields` array admits fields
without that exclusion. A writable array's element contract is invariant
([arrays](POSITIVE-TYPES.md#arrays)): a wider alias could insert a field
that the narrower element contract excludes.

- **Rewrite:** `flatMap`'s type argument is the allocation's field element
  type, `Extract<Expr, { k: "alloc" }>["fields"][number]`. Each callback
  result meets that type when its array is allocated, and the fresh result
  has the destination's writable element contract. The type argument is
  erased; the same callbacks return the same objects in the same order,
  with the same calls, reads and allocations.
- **Pattern:** state a fresh array's intended writable element contract
  when creating it, before any alias holds it at a narrower contract.
- **Cases:** `blocker-flat-map-narrow-field` states that contract;
  `invalid-flat-map-narrow-field` keeps the inferred narrower array and
  its refused widening.
- **Functions:** `expr` and the expression readers that call it;
  `footprintReading` (`tools/host-families.mts`) places a fresh copy,
  `[...each(type)]`, of its array of function terms in an intersection's
  writable `parts: TypeTerm[]`, where `each`'s result is also a scheme's
  signatures.
- **Commit:** the introducing commit.

### Construct signatures collected at one writable record contract

`selectGlobal` (`tools/declaration-graph.mts`) collects construct signatures
from the overlay and from declarations. Its destination holds
`{ binders: string[]; type: TypeTerm }`. A callback returning an empty
`binders` array and a constructor arm has a narrower inferred writable
record unless its result states that full contract.
The later callback that computes a key from the type reads the collected
records at the destination contract. Both the array element contract and the
writable `type` field are invariant
([writable fields](POSITIVE-TYPES.md#records)).

- **Repair:** each callback allocating a construct form states its full
  result contract, `ConstructForm`. The fresh empty array admits strings
  and the fresh `type` field admits `TypeTerm` at allocation. The result
  annotation supplies the destination contract. Each term allocation states
  its constructor arm of `TypeTerm`. These annotations are erased; calls,
  reads, allocations and returned objects have the same order and values.
- **Mechanism:** the existing contextual checks of fresh records and
  arrays establish their declared writable contracts.
- **Cases:** `blocker-census-spread-nested-field` states the JSON data
  contract of its records and retains serialization and deduplication;
  `invalid-census-spread-nested-field` keeps the narrower allocation and
  its refused callback parameter.
- **Comparison:** construct forms use their binder names and
  [type text](#constructor-forms-compared-by-their-type-text) as their key.

### Constructor forms compared by their type text

`selectGlobal` in `tools/declaration-graph.mts` collects constructor forms
at `{ binders: string[]; type: TypeTerm }`. Its key is
`JSON.stringify([f.binders, termText(f.type)])`.

- **Mechanism:** the [type text writer](#a-type-terms-text-made-by-a-replacer)
  writes each kind's fields, including call effects and promises. Its
  contract preserves the heap. The final serialization visits the binder
  strings and that text, under the existing
  [JSON contract](SOURCE-CONTRACTS.md#json-and-error).
- **Rewrite:** `CallPromise` states its mutually exclusive guard and
  assertion fields. The constructor form retains the full `TypeTerm`
  contract. The key reads the term through `termText`.
- **Behaviour:** forms with equal binder names and equal type text share
  a key. `Map` retains the last form for each key. Type text omits term
  spans and reference argument spans, and includes declaration identity
  spans, as its writer specifies. Thus constructor signatures differing
  only in term locations share one form. The retained form keeps its
  original type and source spans. The key changes no contract's fields,
  bounds or call effects.
- **JSON data construction:** `blocker-census-nested-field-json` exercises
  the separate construction mechanism for serializing a nested spread:
  its form and term annotations retain readonly JSON data bounds. The
  producer combines disjoint named fields and indexes in a fresh record's
  allocation hint; the existing [allocation checks](SOURCE-CLAIMS.md)
  check every index bound against the named fields too.
  `invalid-census-nested-field-json` checks an existing open record given a
  data intersection: under Node, an additional `toJSON` returns `undefined`
  despite the function's string result.
- **Functions:** `selectGlobal`.
- **Commit:** the introducing commit.

### A resolved URL read through URL members

`resolveObserved` parsed the URL Node's resolver answers with `new URL` and
read its `protocol`, `search` and `hash`; `observeResolution` resolved a
relative specifier with `new URL(specifier, pathToFileURL(parent))`, and
`family-activation.mts` read `pathToFileURL(path).href`. A URL the program
holds is opaque ([Node's `URL`](SOURCE-CONTRACTS.md#nodes-url)): other
code it reaches may give it, or its search parameters, an own member that
a later read of a member or a conversion runs, so no member is read.

- **Rewrite:** the program holds serialized URLs only. `pathToFileHref`
  and `resolveHref`, the host boundary [URLs as strings](#urls-as-strings),
  stand for `pathToFileURL(path).href` and `new URL(input, base).href`;
  `fileURLToPath` takes the string. The resolver's answer is tested as a
  string: it names a file where it starts with `file:`, and is kept where
  its query and its fragment are empty or absent (`emptyQueryAndFragment`:
  nothing follows the first `#`, and nothing follows the first `?` before
  it).
- **Observable contract:** the same results, throws and file-system
  observations on every URL the resolver answers. The resolver answers a
  URL in serialized form, its scheme in lowercase at the start and `?` and
  `#` in its path percent-encoded, so a `file:` prefix is its protocol, the
  first `#` starts its fragment and the first `?` before it its query; the
  fragment may hold `?` and `#`. `search` and `hash` are `""` exactly where
  that query and fragment are empty or absent, which the default resolver
  makes of an empty delimiter by dropping it and `--preserve-symlinks`
  keeps. A URL base converts to its `href`, and `fileURLToPath` of a URL's
  `href` parses a URL with the same path. `tests/node-runs.mts` compares
  both forms on what the resolver answers for empty and non-empty queries
  and fragments, with and without `--preserve-symlinks`, on other
  serialized URLs (other schemes, encoded `?`, `#` and space, a fragment
  holding `?`), and on specifiers with encodings, queries, fragments and an
  invalid URL (Node 25.2.1, 2026-10-29).
- **Functions:** `files.mts#resolveObserved`, `files.mts#observeResolution`
  and the two reads of `family-activation.mts`; `blocker-node-url-import`
  shows the rewritten form.
- **Pattern:** a URL crosses a call boundary as its serialization.
- **Commit:** the introducing commit, `node:url and URL overlay contracts; host boundaries for URL strings and a child's output`.

### A module's location read from `import.meta`

The front end passed `import.meta.url`, `import.meta.dirname` and
`import.meta.filename` where a string is required. Each read is `unknown`
([module metadata](SOURCE-CONTRACTS.md#module-metadata)): `dirname` and
`filename` are absent for a module not loaded from a `file:` URL, and `url`
is whatever the module's wrapper holds, which other code reaches through
`require.cache`. Each use was refused.

- **Rewrite:** a runtime check, `moduleLocation(import.meta.dirname)`
  (`tools/files.mts`), which throws unless the value is a string and
  returns it otherwise. It excludes one behaviour: where the read is not a
  string, the original passed it on to a parameter typed `string`
  (`path.resolve`, `path.join`, `fileURLToPath`, `createRequire`,
  `nodeResolve`, `current`); the rewrite throws at the read. Where it is a
  string, the two agree.
- **Pattern:** a location `import.meta` holds is checked to be a string
  where the code requires one.
- **Functions:** the module bindings `repository` (`family-activation.mts`),
  `using` (`compiler-channel.mts`), `requireModule` (`files.mts`) and
  `resolvableDeclaration` (`intrinsics.mts`), `activatedModules`,
  `useInstallationForTests` and `unchecked.mts`'s worker spawn.
- **Commit:** the introducing commit.

### A validator table read at a document's key

`decodeGraph` (`tools/type-graph.mts`) checked an object clause by reading
its table of validators at the clause's first key,
`check[Object.keys(c)[0]]`, the table typed as a record at every string, and
a string clause by `c in STRING_CLAUSE_TEXT`. An empty clause has no first
key, and a read past the end is `undefined`, which no record index admits
("record index requires a string key"); both lookups also find
`Object.prototype`'s members: a clause `{ "toString": … }` passed, checked
by `Object.prototype.toString`, and the string clause `"constructor"`
passed the `in` test.

- **Rewrite:** the clause's key and body are its first own entry
  (`Object.entries`); its kind is the element of `CLAUSE_KEYS`, the list of
  `ClauseKey`'s literals, that `find` finds equal to the key, and the table,
  a record at `ClauseKey` alone, is read at that kind; a string clause is
  tested by `Object.hasOwn`. A type alias, `EveryClauseKey`, fails to
  compile where `CLAUSE_KEYS` lacks a key of `ClauseKey`. For a clause
  whose key is one of the table's kinds, the same validator runs on the
  same body, and the same error is thrown in the same order: "unknown graph
  clause" for an unknown key before "unexpected type graph fields" for a
  second key. The values are the document's own data properties, which
  `Object.entries` and an index read give alike, in the order `Object.keys`
  gives. An empty clause throws "unknown graph clause" as before; a key or
  string naming an inherited member is refused with it.
- **Pattern:** a key read from a document selects a table's entry by
  equality with the table's literal keys.

### A predicate's index read before its kind is tested

`contextualCallable` in `collectDeclarations` (`tools/declaration-graph.mts`)
read a signature's type predicate's `parameterIndex` before testing its
`kind`, and took `about === undefined` to exclude a predicate about
`this`. The client holds the server's index, 0, for such a predicate,
where its declaration states `undefined`, and the contract's views of the
`this` predicates state no index
([audits](COMPILER-API.md#audits-of-sync-members)), so the read on the
whole union was refused.

- **Rewrite:** the kind is tested first, refusing every predicate but one
  about a parameter, tested or asserted, with the same reason; then the
  index and the type are read, and a predicate with no type, a parameter
  with no declaration or a rest is refused as before. On a predicate about
  a parameter both forms read the same fields and give the same term. On
  one about `this` both refuse with
  the same reason; the original also resolved the declaration of the
  parameter at the index where the signature has one, a request whose
  result it discarded, which the rewrite makes no more.
- **Pattern:** a member a union's arms state differently is read after the
  test that selects the arms stating it.
- **Functions:** `declaration-graph.mts#collectDeclarations`.
- **Commit:** the introducing commit.

### Error prototype fields at their member contract

`tools/library-globals.mts#errorInstance` constructs the two prototype
fields of the modeled `Error`: `message` and `name`. Its local field
constructor states the element contract of `TypeTerm`'s object fields.
The fresh nested atom states its `k` and `name` through that result
contract. The existing contextual checks of fresh records and arrays
establish the writable field and array contracts.

The annotations are erased. The constructor evaluates the same two calls,
allocates the same objects and arrays in the same order, and retains the
same `span` references. `blocker-round-error-field-array` exercises this
construction. The native `Error` contract is described in
[library globals](SOURCE-CONTRACTS.md#library-globals).

### An open record spread over the fields written before it

`tools/declaration-graph.mts#namesArray` constructs a document from its
three parts by naming `values`, `applications` and `definitions`, after
fresh empty `roots` and `symbols` arrays. Its sole caller in
`closeDeclarations` supplies a fresh object literal with exactly those
three own data properties in that order. All three source arrays retain
their identity, contents and holes; both forms allocate the same two empty
arrays and one document in the same order and own key order. The argument
object is unescaped and carries no getter or additional own key, so named
reads and the spread have the same returns, exceptions and effects over
all states this caller admits. `documentHolds` reads the document's named
parts. `blocker-round-document-parts` exercises the complete construction.
The avoided form is `{ roots: [], symbols: [], ...parts }`; an open
`parts` contract permits additional own keys to replace the initial ones.
Supporting that form generally requires a checked bound on those keys.


`assertEntry` (`tools/library-modules.mts`) built each `node:assert/strict`
entry as `{ module, name, signature, ...(member === undefined ? {} : { member }), ...entry }`,
with `entry` at `Omit<ModuleEntry, "module" | "name" | "signature" | "member">`.
That type is an open record: a value meeting it may own `module`, `name`,
`signature` or `member`, of any type, and the spread, written last, copies
them over the fields before it. The result is not established at
`ModuleEntry` ("no derivation of its return-contract claim").

- **Rewrite:** `entry` is at `Pick<ModuleEntry, "stated" | "effect" |
  "promise" | "lowering">`, and `assertMember`, annotated to return a
  `ModuleEntry`, builds one entry, copying each of those four fields by
  name, an optional one by a conditional spread where it is defined;
  `assertEntry` pushes one entry per member, in order, onto a fresh
  `ModuleEntry[]`. (`members.map(…)` infers its element type from the
  callback, and the writable array it returns is refused at
  `ModuleEntry[]`.)
- **Observable contract:** every caller passes an object literal stating
  only some of those four fields, none of them `undefined`, and an array
  `members` with no hole, so the result holds the same entries in the same
  order, each with the same fields at the same values. The fields' order changes:
  `stated`, `effect`, `promise` and `lowering` follow `member` in that
  order; nothing reads the entries' key order.
- **Pattern:** a record built from a partial one copies the fields it
  needs by name.
- **Functions:** `library-modules.mts#assertEntry` and `assertMember`, through them
  `moduleEntries` and `moduleObjectDefault`.
- **Commit:** the introducing commit.

### One signature or several in one field

A reviewed global's entry (`GlobalEntry`, `tools/library-globals.mts`)
stated its signatures in one field, `stated`, holding a `Stated` record or
an array of them, and its readers told them apart with `Array.isArray`. An
open record may be an array carrying its keys (`invalid-isarray-record`),
so on the arm where the test holds the value is `readonly unknown[]`, whose
elements are no `Stated`, and the forms read from it were refused.

- **Rewrite:** the entry states one signature in `stated` and several in a
  field of their own, `forms`, each a value or a function of the library
  and view references; an entry stating both is refused. `stated: s` reads
  as the one form `[s]`, as the array test made of it, and `forms: fs` as
  `fs`; the `Set` and `Map` constructors' iterable overloads move their
  lists to `forms`, and `Map`'s other overloads, stated by the same
  function with one form each, state the list of it. Every entry's forms, and so the declarations read,
  are unchanged.
- **Pattern:** a field holding one value or a list of them is two fields,
  each holding one shape.
- **Functions:** `selectGlobal`, `globalFunction`.
- **Commit:** the introducing commit.

### A field's function passed to `map`

The typed traversals (`tools/fragment-parts.mts`) map a node's lists by a
function a record field holds, `list.map(m.expr)`, with `PartMap`'s field
typed `(e: Expr) => …`. `map` calls it with the element, its index and the
array, and a function of that type may take a further optional parameter
the index fills (`invalid-callable-field-callback`, run under Node), so the
call is refused. Every function the traversals store there is TScert's
own code of one parameter, which discards the actuals past it; the
field's type did not state that.

- **Rewrite:** each field of `PartMap` and `DocumentMap`, the functions
  `deepPartMap` takes, the `identity` test `documentHolds`, `moduleHolds`
  and `astHolds` take (passed to `some`) and the `go` that
  `tools/type-term.mts#mapTypeParts` takes, takes its further actuals at a
  rest of `unknown`,
  `(e: Expr, ...further: unknown[]) => …`. A function of one parameter
  meets that type from its code, and `map` passes the index and the array
  there (`blocker-callable-field-callback`). Every call and every value
  stored is unchanged.
- **Pattern:** a field whose function is passed where more actuals are
  passed than its type names takes them at a rest of `unknown`.
- **Functions:** `mapExprParts`, `mapStmtParts`, `mapFunctionParts`,
  `mapDocument`, `deepPartMap`, `documentHolds`, `moduleHolds`, `astHolds`,
  `renamedModule`; `FamilyGraph.questioned` (`tools/host-families.mts`),
  passed to `some` in `familyTable`, whose local `flatten`, passed to
  `flatMap`, is called by an arrow of one parameter instead; `mapTypeParts`,
  `substitute` and `settleTerm`.
- **Commit:** the introducing commit; `mapTypeParts`'s, `Repair callback
  arity and receiver contracts in the type readers`.

### An imported predicate passed to `filter`

`typeQuery` in `tools/computed-types.mts` and `lowerFile` in
`tools/fragment-parse.mts` passed `isStatic`, imported from
`tools/syntax.mts`, to `filter` and `some`, which call it with the element,
its index and the array. An import is known by its type alone, and a
function of the type `(node: Node) => boolean` may read a further optional
parameter the index fills (`invalid-callable-field-callback`).

- **Rewrite:** each call site passes `member => isStatic(member)`, a closure
  of one parameter, offered the callback's signature. `isStatic` is an arrow
  of one parameter, so it discards the index and the array either way, and
  each element is tested once, in order, as before.
- **Functions:** `typeQuery`, `lowerFile` and their callers.
- **Commit:** `Repair callback arity and receiver contracts in the type readers`.

### The type syntax readers' effect

The computed-type evaluator (`tools/computed-types.mts`) reads each member
of a union with the reader its alias application gives it,
`kept.map(member => member.read(member.node))` in `distributed`, and
passes the result to a union's `parts`. The readers were typed
`(node: TypeNode) => TypeTerm`, which states no effect, so the `map`
callback could change any store and its result could hold holes; the
union's record was refused at its `parts`. Every reader the evaluator
receives is the type reader's, which grows stores and changes nothing else.

- **Repair:** the readers are of the type `TypeReader`, `(node: TypeNode)
  => Within<{ value: "any"; store: "grow" }, TypeTerm>`, in
  `ComputedContext.applied`, the alias members and every function of the
  evaluator taking one, so `map` keeps a dense result
  ([`map`'s stable callback](SOURCE-CONTRACTS.md#prototype-contracts)). The
  `Set` and `Map` the evaluator constructs state their type arguments, as
  [a `Map` constructed with no type arguments](#a-map-constructed-with-no-type-arguments)
  does. The annotations change no execution.
- **Functions:** `distributed`, `computedType`, `aliasApplication`.
- **Commit:** `State the type syntax readers' effect and commit flatMap results at a later use`.

### The computed-type context's hooks read as values

`ComputedContext` (`tools/computed-types.mts`) declared `alias` and `unique`
as methods. `computedType`, `aliasApplication` and `unionMembers` pass
`context.alias` to `computedAlias`, and `literalUnion` receives
`context.unique`: a method read off its object is no function value
([method members](SOURCE-MODEL.md#method-members-are-host-relative)), so the
reads were refused. The one implementation, `computedContext` in
`tools/declaration-graph.mts`, allocates both as arrows, which use no
receiver.

- **Repair:** `alias` and `unique` are fields of function types, as
  [a scope's hooks](#a-scopes-hook-read-as-an-optional-method) are. The
  arrows are the same values, called with the same arguments; the
  annotation changes no execution.
- **Functions:** `computedType`, `aliasApplication`, `unionMembers`,
  `distributed`, `typeQuery`.
- **Commit:** `Repair callback arity and receiver contracts in the type readers`.

### Active recording membership

`tools/files.mts` holds active recordings in an insertion-ordered `Set`.
Each observation creates a fresh record; a retained ledger enters only when
its record is absent. `enterLedger` returns the record it activates, or null
when that record is already active. `leaveLedger` removes that saved identity. A mutable alias may
replace a ledger's recording during a callback; cleanup belongs to the record
activated at entry. Reading the replacement for cleanup can remove an enclosing
activation and misattribute subsequent observations. The mutable-alias control
in `tests/shared-work.mts` exercises that failure. `withLedger` pairs these
operations around an arbitrary callback, including a callback that shrinks arrays.

Set membership updates have the existing
[native footprints](SOURCE-CONTRACTS.md#native-footprints): arbitrary value
changes and preserved array stores. The helper statements are checked from
their bodies. `active-ledger-footprint` exercises these statements and a
composition whose callback preserves stores on both normal and exceptional
returns. The example states the callback's `onThrow` guarantee explicitly
([footprints](FOOTPRINTS.md)).

Named inputs select the nearest active stage by scanning a snapshot in reverse
insertion order. Ledger validation suspends the active set and restores its
snapshot in insertion order. The shared-work controls exercise repeated ledger
entry, exceptional exit, validation restoration and nested named inputs.

### A native instance set read through a structural interface

`tools/declaration-graph.mts#promisedDefinitions` takes `localInstances` as
`Set<string>`. Its sole caller constructs that set from the current
module's instance names immediately before the call. The native set's
[reviewed membership operation](SOURCE-CONTRACTS.md#prototype-contracts)
retains its preserving effect. The callback's complete body, including
`promisedMethods`, uses the existing inferred-effect certification; its
map result retains readable definition storage.

A structural `ReadonlySet<string>` states a Boolean `has` method whose
contract permits effects. An implementation can pop the definition input
while answering `false`. Mapping two definitions then leaves a result of
length two with no second index, and reading that definition's `module`
throws `TypeError` under Node. The negative
`invalid-round-promised-readonly-set` exercises this contract with a complete
structural set implementation, without changing a standard method.

The repair retains the native input the caller already supplies. The
annotation is erased; callback order, selected definition identities,
cloned fields, null expressions, exceptions and mutations are unchanged.
`blocker-round-owned-promised-definitions` checks an owned set through the
same boundary. This uses the existing native-set contract and adds no
external assumption.

The same repair passes `stated` and `classes` to
`tools/declaration-graph.mts#externalStatements` as `Set<string>`: its sole
caller builds both with `new Set`, and its `visitType` callback tests them
with `has` inside the visitor's stated `{value: any, store: grow}`, which a
structural `has` stating no effect does not meet. The annotation is erased.

### A request's method named by converting an unknown argument

`guard` in `tools/compiler-channel.mts` names a failed `apiRequest` or
`apiRequestBinary` by `String(args[0])`, where `args` is
`readonly unknown[]`. Converting an object runs its `toString` or
`Symbol.toPrimitive`, code no type states.

- **Repair:** the request is named by its first argument where that is a
  string, and by its member otherwise. The package passes the method name,
  a string, so the failure's message is unchanged for every request it
  sends.
- **Functions:** `guard`.
- **Commit:** the introducing commit.

### Record fields a reader takes at a wider contract

`familyTable` in `tools/host-families.mts` passes its own members, records
holding a writable `TypeElement[]`, to `combine`, which takes
`FlatMember`'s `members: readonly TypeElement[]`; `presentObligation` in
`tools/diagnostic-view.mts` passes a diagnostic record holding `types: Json`
to `recordType`, which takes `Table`'s `types: JsonValue`. A writable
field's contract is invariant, so neither argument meets its parameter.
Neither reader writes these fields.

`familyTable` also returns its local functions, `flatten` among them
returning `FlatMember[]`, in `FamilyTable`'s fields, which state
`readonly FlatMember[]` results.

- **Repair:** `FlatMember`'s three fields, `Table`'s two and
  `FamilyTable`'s eleven are readonly. No code writes them; the values,
  reads and calls are unchanged.
- **Functions:** `familyTable`, `presentObligation`.
- **Commit:** the introducing commit.

### A tag member's type read through `in` and an assertion

`familyTable` read a tag member's type by `"type" in signature`, then
asserted `signature.type as TypeNode`. The `in` test admits a method, an
index or a call signature, each of which has a `type`, and the open read
gives `unknown`, so the assertion stood for a missing check.

- **Repair:** the member is tested with
  `ts.isPropertySignatureDeclaration`, and its `type` read at that kind. A
  tag is a property; a family stating its tag by another member fails with
  the same message as one stating none.
- **Functions:** `familyTable`.
- **Commit:** the introducing commit.

### Tag values ordered after a test of one operand's kind

`compareTags` in `tools/host-families.mts` compared two tag values with
`<` after `typeof a !== typeof b` was false, a test that narrows neither
operand, so the comparison was of a `number | string` with a
`number | string`, which converts a string compared with a number.

- **Repair:** each operand's kind is tested on its own: a number before a
  string, two numbers by difference, two strings by `<` and `>`. Every
  answer is the same.
- **Functions:** `compareTags`, read by `familyTable`.
- **Commit:** the introducing commit.

### A mapped slot read at an index the mapping may lack

`presentObligation` compares each required slot with
`available[mapping[i]]` and serialized both sides with `JSON.stringify`.
`mapping[i]` is `undefined` past the mapping's length, and `JSON.stringify`
takes a `JsonValue`, never `undefined`.

- **Repair:** `availableAt(i)` answers `undefined` where the mapping names
  no source slot, and `sameType` compares `undefined` by identity before
  serializing. `available[undefined]` read the absent key `"undefined"`, so
  every answer is the same.
- **Functions:** `presentObligation`.
- **Commit:** the introducing commit.

### Resolution slots built at their field's contract

`intrinsics` in `tools/intrinsics.mts` stored `resolvableSlots("X")`, a
record whose `result` is a `string`, in a binder's writable
`resolution: ResolutionSlots | null`, whose `result` is `string | null`.

- **Repair:** the binder's resolution is `resolutionSlots("X",
  "resolvable")`, a fresh record of the same two strings at
  `ResolutionSlots`; the result binder still reads `resolvableSlots`'s
  `result`. No code compares resolutions by identity.
- **Functions:** `intrinsics`.

### The claim printers and lifter with stated growth

The printers of `tools/claim-text.mts` (`atomText`, `bareAtomText`,
`typeText`) and its lifter (`cell`, `liftClause`, `liftSignatures`,
`liftType`, `liftLabels`, `treeAtom`) read producer JSON, write only the
print state, fresh arrays and records and the table's memo, and map arrays
with callbacks that call one another. A map result is dense only at a
callback whose footprint is at most `grow`
([`map`](SOURCE-CONTRACTS.md#prototype-contracts)), and the lifter's records
are passed at `JsonValue`.

- **Repair:** each of these functions, each callback the lifter maps with,
  and `textOf`, the text of a lifted part, state
  `Within<{ value: "any"; store: "grow" }, T>`, with the
  [stated-effect](SOURCE-ELABORATION.md#stated-effects) rule checking every
  body. The imported helpers they call state their footprints, each checked
  at its own definition: `isArrayPresence` and `presencePrefix` the empty
  one, `decodeCallEffect`, `decodeClosedFootprint` and `decodeKinds`
  (`tools/type-graph.mts`) and `stringOfJson` (`tools/calculus.mts`)
  growth. `isOrdinary` compares a decoded effect with `ordinaryEffect`
  field by field. The report types `Shown`, `ShownField` and `ShownRecord`
  and the record's `indexes` state the index signature
  `readonly [key: string]: JsonValue` that their fields meet, so a record is
  passed at `JsonValue` without an implicit index signature; the dictionary
  branch of `liftClause` builds its record from the record's six named
  fields, the keys the record holds. The table's `names` is a `Map`, the
  native `lift` builds, whose `get` runs no client code
  ([native collections](#the-type-readers-native-collections-typed-as-natives)).
- **Repair:** a value read and then tested is read once into a constant:
  `rowAt` reads `types.rows`, `cell`'s callbacks read a pair's key, and
  `primitiveKind` finds the kind in the primitive table and returns it
  ([a guard that promises more](#a-guard-that-promises-more-than-its-body-checks)).
  `atomText` collects its metadata as entries and builds the object with
  `Object.fromEntries`, so it writes only a fresh array. Every conversion of
  a JSON value or an absent read to text is `stringOfJson`, which converts
  as `String` does ([a parsed JSON value](#a-parsed-json-value-read-as-unknown)),
  and the memo key of an absent label list is the text `"undefined"`, the
  interpolation of an absent serialization.
- **Equivalence:** the annotations are erased. A read once is the value the
  repeated reads gave: no code runs between them that writes the read
  object. `Object.fromEntries` defines the same keys in the same order as
  separate writes, and `JSON.stringify` serializes the same object.
  `stringOfJson` and `String` agree on every JSON value and on `undefined`,
  in result and in exception, except on an array nested deeply enough that
  `String` exhausts the call stack, where `stringOfJson` returns the text
  (`tests/claim-text.mts` compares them on a 3,000-level array, which an
  unknown atom kind prints as `«1»`).
  `isOrdinary`'s comparisons are `sameEffect`'s at `ordinaryEffect`, whose
  promise and kind lists are `null`. `textOf` is `printType`'s text without
  the claim decoding, whose answer the text does not read; the two differ
  only where the decoding exhausts the call stack, a `RangeError`
  `printType` passes on. Returns, other exceptions, mutations and aliases
  are unchanged.
- **Trust:** `numberOfBits` (`tools/type-graph.mts`) states the empty
  footprint. Its body, which no rule admits (`DataView` has no reviewed
  entry), allocates an `ArrayBuffer` and a `DataView` over it, converts its
  string argument by `BigInt`, which runs no client code and throws a
  `SyntaxError` on a malformed one, and writes and reads only the fresh
  buffer, under the untampered standard objects assumption.
- **Scope:** `blocker-claim-lift-forms` checks a growing memoized lift
  over a dense receiver returning a record that states its index signature.
- **Commit:** the introducing commit.

### A symbol table's map predicate stating the empty footprint

`tableReading` in `tools/compiler-api.mts` tests `type.result` and reads
its `reference` and `args` across a call of its `isLibraryMap` parameter.
A parameter typed `(id) => boolean` may replace `type.result` before the
second read, which then reads a field of the declared union
(`invalid-next-table-predicate-mutation`: run under Node, the classifier
returns `undefined` as its `number[]`).

- **Repair:** the parameter states
  `Within<{ value: "keep"; store: "keep" }, boolean>`, which its one caller's
  predicate, a module-name and name comparison, meets. The annotation is
  erased.
- **Scope:** `blocker-next-table-predicate-preservation`. No external
  assumption is added.

### Effects stated where the expression front end calls through a function type

Several helpers of the expression and statement front end call a function
held in a parameter, a record field or a gate method whose type is an
ordinary arrow, which states no effect: `readOf`'s `local`, `extendChain`'s
`link`, the `check` field and `value` parameter of `objectFields`'
`literalKey` and `valued` closures, `Gate.termScope`, which `guardOf`
calls, `classBody`, which `classStmt` calls, and the declarations
`classBody` calls, `signature` (`tools/type-term.mts`), `errorBase` and
`errorOptions` (`tools/library-globals.mts`), `localClass`, which
`classStmt` calls, and `Gate.moduleRestType` and `typeParameterMentioned`,
which `functionDecl`'s `map` callback calls, which stated none. Each call
was read at an unrestricted contract, so the caller's statement `{value: any, store: grow}`
was refused ("the footprint claimed for … is not established by its body").

- **Repair:** each function type states the footprint the functions passed
  there meet, `Within<{ value: "any"; store: "grow" }, R>`
  ([stated effects](SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification)).
  A caller's unit relies on the statement as written, reading the function
  at its claimed signature and effect; the statement is established where
  the unit certifying the stating function is accepted
  ([modules and code units](DESIGN.md#modules-and-code-units)). In the
  census of `17db34ea` the units of `signature`, `errorOptions` and
  `localClass` are accepted, and so are the initializations of
  `tools/syntax.mts` and `tools/fragment-support.mts`, which certify the
  closures `nameOf` and `errorBase`.
  `readOf` takes its names as the native `Set` its callers build, whose
  `has` has a reviewed contract, as `functionDeclarations`' map does.
- **Statements no accepted unit establishes:** in the census of
  `17db34ea` the initialization of `tools/fragment-parse.mts`, which
  certifies `Gate`'s methods, and the unit of `classBody` are refused, so
  these statements are assumed by their callers and audited by reading:
  - `Gate.termScope`: allocates a record of arrow functions over the gate;
    it calls none of them.
  - `Gate.moduleRestType`: reads the parameter's syntax and types it
    through `typeOf`, `restType`, `typeParameterMentioned` and
    `restPositions`, each stating `{value: any, store: grow}`, and `find`
    at a callback that only reads; it writes nothing.
  - `classBody` (`tools/fragment-classes.mts`): its unit is refused at the
    footprint it states. Its body writes fields of records
    and arrays it allocates (`push`, field writes on fresh records), calls
    gate methods stating `{value: any, store: grow}`, and reads the
    compiler's nodes; the audit found no operation outside that footprint,
    which no accepted unit confirms.
- **Behaviour:** the annotations are erased; every call, argument and
  result is unchanged.
- **Commit:** the introducing commit.

### A parent walk at the parent's host contract

`tools/fragment-support.mts#jumpTarget` walks `parent` links from a
`break` or `continue` with `let parent = node.parent`, which TypeScript
types `Node`. The compiler's host contract gives `parent` as
`Node | undefined` (a source file has none), so the binding's inferred
contract could not hold the next link.

- **Repair:** the binding states `Node | undefined`, the contract the loop
  test already handles.
- **Behaviour:** the annotation is erased; the same links are read and the
  same node is returned.
- **Commit:** the introducing commit.

### A destructuring element's assignment held as its node

`tools/fragment-statements.mts#assignedSteps` held `el`'s test as a Boolean,
`const assigned = ts.isBinaryExpression(el) && …`, and read `el.left` and
`el.right` under `assigned` after a test of `el` against `SpreadElement`;
the producer kept no narrowing of `el` through the constant there
("missing field left"). Its `before` and `write` arrays were inferred at
the element types of their literals, which a writable `Node[]` result field
does not hold.

- **Repair:** the constant holds the binary node or `null`, and the reads go
  through it; `before` and `write` state `Node[]`.
- **Behaviour:** the same tests run in the same order on the same node; the
  annotations are erased. Each returned step holds the same nodes.
- **Commit:** the introducing commit.

### Reads stated as reading only

`tools/syntax.mts#childOf` and `nameOf` read a child of a compiler node
through kind tests, and `tools/fragment-support.mts#firstOptional` finds a
parameter's index with `findIndex` over a field read; each stated
`{value: any, store: grow}`. `staticPrivate` calls `nameOf` in a `find`
callback, and `find` at a callback that may grow a store passes `undefined`
past a shrunk length, outside the callback's `ClassElement` parameter;
`lambda` calls `firstOptional` in a loop over its parameters, whose array a
call that may grow stores does not keep as the loop's head states it.

- **Repair:** each states `{value: keep, store: keep}`, which its body,
  kind tests, field reads and a `findIndex` at a callback within the same
  footprint, establishes: the units of `childOf` and `firstOptional` and
  the initialization of `tools/syntax.mts`, which certifies `nameOf`, are
  accepted in the census of `17db34ea`
  ([effects stated](#effects-stated-where-the-expression-front-end-calls-through-a-function-type)).
- **Behaviour:** the annotations are erased.
- **Commit:** the introducing commit.

### Values the expression and class front ends read again, held once

Five sites of the expression and class front ends read a value again where
its earlier test or construction no longer types it:

- `lambda` held its receiver test as a Boolean, `const stated = !!head &&
  …`, and read `head` and `head.type` under it after calls; the producer
  kept no narrowing of `head` through the constant across them.

- `binary`'s field write tested `node.left` against `PropertyAccessExpression`,
  then read `node.left` again after `gate.staticPrivate` and
  `gate.memberKey`, calls within `{value: any, store: grow}`; the read was
  not at the tested arm.
- `lambda` read `defaults[i]` in `...(defaults[i] ? { default: defaults[i] }
  : {})`; an element read twice is two reads, the second not narrowed by
  the first. Its parameter loop tested `p !== parameters[parameters.length -
  1]` and read the parameter's `questionToken`, `initializer` and
  `dotDotDotToken` in nested tests, after which the search kept no
  knowledge of those fields where the loop's later test reads them again.
- `classBody` built the base read's receiver as `{ ...derivedBase, pos:
  extendsAt }`, a spread of a binding typed `Expr`, which the code had just
  set to `{ k: "id", pos: extendsAt, name: slot }`.
- `classBody` declared its prototype fields `{ name; e }[]` and passed them
  where an allocation's fields are `{ name; e; computed?: true }[]`: a
  writable array's element contract is its own, not a narrower one.

- **Repair:** `lambda` holds the `this` parameter, or `null`, and its
  checked annotation in one record, and walks its parameters by index,
  reading each child the checks test once and testing the index against
  the last one; `binary` holds the write target in a
  constant tested once;
  `lambda` holds each default in a constant; the base read writes its
  record, `{ k: "id", pos: extendsAt, name: slot }`; the prototype fields
  state the allocation's element type.
- **Behaviour:** the same tests run on the same nodes in the same order
  (the parameter array is a fresh copy of a node list, dense, which nothing
  writes, and holds each node once, so a parameter is the last element
  exactly where its index is the last; a compiler node's children are
  stable reads, so reading one once or at each test gives the same value);
  the base read's record has the same keys in the same order, its `pos`
  the same array; annotations are erased.
- **Commit:** the introducing commit.

### A function's parameter records at a named type

`tools/fragment-statements.mts#functionDecl` maps the declaration's
parameters to records `{ name, pos, type, ...(rest ? { rest: true } : {}) }`
and reads them in a second `map` callback, as
`tools/fragment-expressions.mts#lambda` does a closure's. The callback's parameter type
was the instance of the anonymous record TypeScript inferred for the first
`map`, whose optional `rest` the compiler's API gives only with the
`undefined` optionality adds; the parser refuses such a contextual type.

- **Repair:** the records are the named types `FunctionParamAst` and
  `LambdaParamAst` of `tools/fragment.mts`, which `FunctionAst.params` and
  the lambda expression's `params` hold, and the first callbacks state them
  as their results; the callback mapping the parameters'
  types, run through the generic `headerTypes`, states `TypeTerm`.
- **Behaviour:** the annotation is erased; the records are unchanged.
- **Commit:** the introducing commit.

### Merged declaration lists stored at a readonly element contract

`collectDeclarations` in `tools/declaration-graph.mts` keeps `partners`,
each declaration's ordered merged parts. `resolutionPromise` and
`resolutionLibraryInterface` store their `InterfaceDeclaration[]` there,
at the map's `TypeDeclaration[]` values; every reader of the map only reads
the lists. A writable array's element contract is invariant
([arrays](POSITIVE-TYPES.md#arrays)), so the stored list was refused.

- **Repair:** the map and the helpers' parameters state
  `readonly TypeDeclaration[]` values, which each stored list meets. The
  annotation is erased.
- **Functions:** `resolutionPromise`, `resolutionLibraryInterface`.
- **Commit:** the introducing commit.

### A built-in module test stating its empty footprint

`builtinModule` in `tools/files.mts` calls `node:module`'s `isBuiltin`,
whose [entry](SOURCE-CONTRACTS.md#library-modules) states the empty
footprint, and its annotation stated no effect. `nodeOrigin`
(`tools/declaration-graph.mts`) calls it in a `map` callback, whose result
then admitted holes ([the stable set](FOOTPRINTS.md#the-stable-set-for-density)).

- **Repair:** the arrow's result states `Within<{ value: "keep"; store:
  "keep" }, boolean>`, which its body establishes. Its value is unchanged.
- **Functions:** `nodeOrigin`.
- **Commit:** the introducing commit.

### A guard passed to `filter` by name

`filter` takes its guard overload at a callback stating a promise. A guard
passed by name meets it where its code discards the actuals past its
parameters: a module function without a rest parameter. A module constant
holding an arrow, and an imported function, are known by their types, which
admit a function reading the index and the array as well. So
`nodes.filter(isTypeDeclaration)`, with `isTypeDeclaration` a constant
arrow in `tools/declaration-graph.mts`, and
`client.statements.filter(isImport)`, with `isImport` imported from
`tools/syntax.mts`, kept their receivers' element types.

- **Repair:** `isTypeDeclaration` is a function declaration, its body the
  arrow's; it is defined before any module code runs, and every call
  returns the same answer. `importBindings` passes
  `(n): n is ImportDeclaration => isImport(n)`, which calls the same guard
  with the same node, once per element.
  The host-family reading tests `f.members.some(m => readsAsOptionalUnknown(m))`,
  an imported predicate passed to `some` the same way.
- **Functions:** `resolutionParametersOf`, `resolutionDeclarationOf`,
  `importBindings`.
- **Commit:** the introducing commit.

### Compiler diagnostics read at readonly field contracts

`resolutionClean` in `tools/declaration-graph.mts` filters the compiler's
diagnostics with `untypedAmbientField`, keeps them in a map of
`{ pos; end; text }` lists, and reports each as a `SeenDiagnostic` whose
`start` and `end` are `getLineAndCharacterOfPosition`'s results;
`clientErrors` builds the same records. The compiler's `Diagnostic` and
`LineAndCharacter` fields are readonly, and a writable field's contract
does not admit them.

- **Repair:** `untypedAmbientField`'s parameter, the map's elements and
  `SeenDiagnostic`'s `start` and `end` state readonly fields. No reader
  writes them: `pipeline/parse-stage.mts` decodes fresh records, and
  `verify-source.mts` reads `line` and `character`. The annotations are
  erased.
- **Functions:** `resolutionClean`, `clientErrors`.
- **Commit:** the introducing commit.

### A record argument copying an optional field by name

`resolutionLibrary` in `tools/declaration-graph.mts` built its template
scope as `{ source, annotation: false, ...exactOptional, fail, named }`,
with `exactOptional` at the open record `{ exactOptional?: boolean }`, which
may own `source` or `annotation` and replace the fields before it
([an open record spread](#an-open-record-spread-over-the-fields-written-before-it)).

- **Repair:** the scope copies `exactOptional.exactOptional` by name,
  through a conditional spread where it is defined. Its one producer,
  `withProject`, makes either `{}` or `{ exactOptional: b }`, a fresh literal
  with no other key, so the scope has the same keys, in the same order,
  at the same values.
- **Functions:** `resolutionLibrary`.
- **Commit:** the introducing commit.

### Headings collected by index around a cached file-system read

`resolutionStatedType` in `tools/declaration-graph.mts` mapped its parts to
`{ origin, heading }` records, each origin read by `declarationOrigin`,
which consults a cache of file-system observations and states no effect:
the mapped array admitted holes, and `typeEntry` reads a readable list. Its
heading's end was `isTypeAlias(part) ? part.end : part.members.pos`; a
user guard's false edge refines nothing, so `members` was read at the whole
`TypeDeclaration`.

- **Repair:** a loop over the indices below `parts.length` pushes each
  record onto a fresh array, skipping a hole, which `parts`, a fresh
  `filter` result no callee reaches, has none of. The end tests
  `ts.isInterfaceDeclaration(part) || ts.isClassDeclaration(part)` first,
  which holds exactly where `isTypeAlias` does not, the parts being type
  declarations. Each record is made from the same calls in the same order.
- **Functions:** `resolutionStatedType`.
- **Commit:** the introducing commit.

The host-family reading of `collectDeclarations` collects four more lists
so, each over an array no callee reaches, each element made by a local
function stating no effect: an open declaration's union parts (`arm`), a
residual field's readings (`readMember`), a generic arm's references
(`reference`) and the method owners (`methodBase`). Each is the same calls
in the same order.

### A session fault read once per collection step

`collect` and `restore` in `tools/declaration-session.mts` tested the
module's `let fault`, a union of fault records, and then read a member
of the variant the test selected. A test does not narrow a cell holding an
object ("a read of document on a `let` holding a union of objects").

- **Repair:** each reads `fault` once into a constant `injected`, where it
  first tested it, and tests and reads the constant. Only
  `injectSessionFaultForTests` and these branches assign `fault`, and none
  runs between the read and the tests, so each test sees the same record.
- **Functions:** `restore`, `collect`, `inDeclarationSession`.
- **Commit:** the introducing commit.

### A collection's result checked before its return

`collect` in `tools/declaration-session.mts` kept `use`'s result in
`let value: T | undefined` across a `try` whose `catch` saves the error,
and returned `value as T` where no error was saved: an assertion of what
the control flow established.

- **Runtime check:** the result is kept as `{ value }` in a `let` starting
  at `null`, and after the rethrow of a saved error a `null` result throws.
  A `try` without a saved error assigned the record, so the check never
  fails; returns, exceptions and effects are those of the assertion's form.
- **Functions:** `collect`, `inDeclarationSession`.
- **Commit:** the introducing commit.

### Telemetry restored by its binding

`asideForTests` in `tools/declaration-session.mts` restored the counters
with `Object.assign(telemetry, counts)`, an assignment onto an object
another reference may hold.

- **Repair:** `telemetry` is a `let`, and `asideForTests` assigns it the
  copy it took. The object is the module's own: `declarationSessionTelemetry`
  returns a copy and every other read goes through the binding, so each
  later read sees the same counts.
- **Functions:** `asideForTests`.
- **Commit:** the introducing commit.

### A numeric disjunct tested before a member path's refinement

`overlaidInterface` in `tools/declaration-graph.mts` refused a member with
`!ts.isMethodSignatureDeclaration(member) || member.typeParameters?.length
|| member.postfixToken`. The graph computes the first two disjuncts' value
and tests it twice, before the last disjunct and for the `if`; the second
test's false edge, reachable only at a falsy number, joins the statement
after the `if` without `postfixToken`'s refinement, which the producer
claims there ("the edge … does not establish the claims at this point").

- **Repair:** the second disjunct is `!!member.typeParameters?.length`, a
  Boolean with the same truthiness, so the value's true test refines it to
  `true` and its second false edge has no value.
- **Functions:** `overlaidInterface`, and through it `collect` and
  `collectFrom`.
- **Commit:** the introducing commit.

## Constructs avoided

Constructs TScert's code once used, refused because sound support is not
proportionate to their use, and written out of the code by an equivalent
form ([deciding](#deciding-what-a-refusal-of-tscerts-code-calls-for)).

### Results of an unrestricted callback collected by a loop

`iterationIntrinsic` and `intrinsics` in `tools/intrinsics.mts` and
`familyTable` in `tools/host-families.mts` built arrays with `map` whose
callbacks call functions of no stated effect (the type readers `view` and
`nativeCollection`, a definition's maker, the family graph's `fail`,
`name` and `text`), then read the results as readable arrays: mapped
again, spread or passed at `readonly T[]`. Such a callback may remove a
later element of the receiver, so the
[native map contract](SOURCE-CONTRACTS.md#prototype-contracts) gives the
result holes ([an inferred map result with an unrestricted callback](#an-inferred-map-result-with-an-unrestricted-callback)).

- **Avoided form and cost:** `xs.map(f)` with `f` of no stated effect, its
  result read as dense. Support needs each callback's preservation stated
  and checked through the readers' parameters and the family graph's
  fields, a contract change to every caller.
- **Equivalent form:** `const out: T[] = []; for (const x of xs)
  out.push(f(x, …))`, the position `i` read as `out.length`. Each receiver
  (`kinds`, the description's `values`, `members` and `bases`, the snapshot
  `[...needed]`) is an array no callback reaches: a fresh local, or data of
  a family description no callback writes. So the loop visits the same
  elements in the same order as `map` with the same arguments, the
  callbacks run the same calls, and the result holds the same values at
  the same positions; exceptions leave at the same call. Alongside,
  `iterationIntrinsic`'s `[param, element]`, destructured from either of
  two array literals, is read as `only[1]` and `only[2]` of the single part
  or the two unions in the same order; `intrinsics`' three `import.meta`
  entries, spread from `Object.fromEntries`, are written as computed keys in
  the same position, and its `{ name, ...make() }` copies the maker's two
  fields explicitly, the maker's fresh record owning exactly them.
- **Scope:** `unrestricted-callback-loop-results` verifies the loop form;
  `blocker-round-inferred-map-result` keeps the map form's refusal.

### An optional literal field added before a record escapes

`tools/files.mts#observedNoting` allocates its `Recording` without a
`stage` key and executes `if (stage) recording.stage = true` before
passing the record to `attemptOf`, `inheritLedger` or the active set.
The existing [key-adding write rule](PROGRAM-TYPING.md#key-adding-writes)
checks the write on this fresh record against `stage?: true`.
`observed` and the process-cache and resolution callers share this
construction; `newLedger` constructs a record without a stage key.

- **Avoided form and cost:** the conditional spread
  `...(stage ? { stage: true } : {})` supplies a writable field whose
  inferred boolean contract loses the literal requirement of `stage?: true`.
  The binding annotation is refused. Carrying that literal requirement
  through conditional spread needs additional contextual inference;
  the direct write uses the existing fresh-object checks for this one
  construction.
- **Equivalence:** both forms evaluate the same `Map` and `Set`
  constructors, then the same initial fields in the same order. The fresh
  record is unescaped until its optional key is complete. For a false flag,
  neither form gives it a `stage` key. For a true flag, both give it a last
  own data property `stage` with value `true`, writable, enumerable and
  configurable. Under the existing untampered-standard-objects assumption,
  `Object.prototype` supplies no setter for `stage`, so the fresh-object
  assignment invokes no callback and has the same effect as the spread's
  property definition. Constructor exceptions occur before either record
  is exposed. Returns, exceptions, receivers, aliases, mutations and
  asynchronous effects agree for every admitted flag and recording state.
  The `Recording` contract and every read of its optional field remain
  `true | undefined`.
- **Scope:** `blocker-round-recording-stage` checks both branches through
  the complete recording contract. No host contract or external assumption
  is added.

### An array's entries iterated by index

`quantified` and `signatures` in `tools/type-term.mts` walked an array with
its positions, `for (const [index, p] of xs.entries())`, inside the type
reader's stated `{value: any, store: grow}`. The overlay reads
`ReadonlyArray.prototype.entries` as an `IterableIterator`, a structural
iterator whose `next` states no effect, so the loop could change any
location ("the footprint claimed for 'quantified' is not established by
its body").

- **Avoided form and cost:** support would read an array's `entries()` as
  a native iterator stepping its array: a marked iterator kind whose step
  reads the array's current length and element at the array's presence,
  through the parser's iteration kinds and the overlay. Nine other loops
  of `tools/` use the form; the two in `quantified` and its same-file callees
  and the walk
  over a constructor's statements in `fragment-classes.mts#classBody` are
  written out.
- **Equivalence:** `for (let index = 0; index < xs.length; index++) {
  const p = xs[index]; … }` reads the array's length before each step and
  its element at the index, as the array iterator's step does
  (CreateArrayIterator), and runs the body with the same bindings; `continue`
  steps the index as the iterator would. The added check of `p` answers
  only at a hole, which none of the arrays has: `typeParameters` is a
  compiler node list, `ordinary` a fresh copy of one, and a constructor's
  statements a node list or a one-element literal. Returns, exceptions,
  mutations and receivers agree for every array its callers pass.
- **Scope:** `array-index-loop-footprint`.

### A closure called by an earlier closure

`tools/fragment-statements.mts#switchStmt` declares `plain`, which calls
`enumLabel`, before `enumLabel`. `plain`'s body mentions a binding declared
after it, an early binding ([lexical bindings before
initialization](SOURCE-ELABORATION.md#lexical-bindings-before-initialization)),
whose contract is the arrow its annotations write, which states no effect.
So `plain`, and `switchStmt`'s call of `clauses.every` with it, are within
no footprint, and `switchStmt`'s statement `{value: any, store: grow}` is
refused.

- **Avoided form and cost:** an early binding of a closure read by an
  earlier closure. Carrying the closure's inferred effect onto its early
  binding's contract needs the rounds of inference [recursive
  constants](SOURCE-ELABORATION.md#recursive-constants) have, for every early binding; the census shows this one site.
- **Equivalence:** `enumLabel` is declared before `plain`. Both
  initializers are arrow functions: evaluating one creates a closure and
  runs no code, so it neither throws nor writes. Nothing between the two
  declarations calls either, and `plain` is first called after both are
  initialized; each closure captures the same bindings. Returns,
  exceptions, mutations, receivers, aliases and asynchronous effects agree
  for every input.
- **Scope:** `closure-declared-before-reader` verifies the equivalent form
  inside a stated footprint. No host contract or external assumption is
  added.

### A compiler stored after its opening counter

`tools/fragment-parse.mts#projectFor` saves the return of
`openFrontEndCompiler` in a local `created`, increments `openings`, and
assigns `created` to the module cell `compiler`. `openText` and `openFile`
consume the same project lookup. The local retains the returned API value
through the counter update; the existing assignment and guard checks
establish the compiler cell's non-null value at the branch join.

- **Avoided form and cost:** assigning `compiler` before incrementing the
  captured `openings` counter requires retaining a fact about one captured
  cell through a write to another. The closure's input contracts supply no
  separation fact for those cells. Supporting that source order requires
  establishing their separation through closure capture;
  this single initialization shared by the census callers uses the
  existing checks through an equivalent order instead.
- **Equivalence:** both orders call the opener with the same arguments
  before either subsequent module-cell write. A returned API is held locally;
  `openings` has primitive `number` contents and its increment performs
  no coercion callback. Assignment to either lexical cell invokes no code.
  Thus no observer can run between the two cell writes. Both orders leave
  the same counter and compiler, then perform the same set lookup and
  snapshot requests with the same receivers. If opening throws, neither
  subsequent write executes. The increment and lexical assignment cannot throw for
  these initialized cells. Returns, exceptions, mutations, method
  identities, aliases and asynchronous effects agree for every input and
  reachable parser state. Compiler callbacks during opening retain their
  original position before both writes; snapshot calls continue to read
  the module cell at each call.
- **Scope:** `blocker-round-parser-held-compiler` exercises this order with
  an API argument. `blocker-prep-snapshot-conditional-spread` exercises the
  separate complete-request construction. The rewrite adds no rule,
  host contract or external assumption.

### A first-match callback calling an imported type reader

`tools/computed-types.mts#inexpressible` describes the member selected by
`inexpressiblePart`: a `for...of` loop returns the first member for which
`literalUnion(member, [0, 0])` returns `null`. If every member is expressible,
it selects the original type. `computedType` and
`aliasApplication` reach this operation through their diagnostics.

- **Avoided form and cost:** `parts.find(p => literalUnion(p, [0, 0]) === null)`
  requires a callback whose calls preserve array stores. The imported
  `literalUnion` contract states no such effect, and its optional `unique`
  callback admits arbitrary effects. Supporting this call with that form
  requires a separate checked effect for the two-argument use and complete
  effect contracts for its compiler API calls. The three census sites share
  this one search; the loop uses the existing
  [iteration checks](SOURCE-ELABORATION.md#the-iterator-protocol) and the ordinary imported
  contract.
- **Equivalence scope:** the callers supply
  [compiler API type objects](COMPILER-API.md#the-package-at-run-time),
  whose fields are data fields and whose member arrays are fresh. The type
  predicates read flags. In the two-argument `literalUnion` call, `unique`
  is absent. That call reads these fields, obtains its own fresh member
  array and builds local terms; primitive conversions receive only primitive
  values. It neither exposes nor changes the outer `parts` array. Thus its
  length and present entries stay fixed during the search.
- **Equivalent behaviour:** under the existing stable-standard-objects
  assumption, `find` and the array iterator visit the same entries in order,
  call `literalUnion` with the same type and fresh span pair, and stop at the
  first `null`. Both select that member or the original type, then format
  the same description. An exception in the reader propagates before any
  description; the standard array iterator has no `return` hook. No source
  array or compiler object is written. This equivalence concerns the actual
  reader and compiler API values; it does not apply to an arbitrary callback
  that changes its receiver array.
- **Scope:** `blocker-prep-host-find-callback` exercises the returning loop
  over the same union of compiler arrays. This rewrite adds no host contract
  or external assumption.

### An overlay entry's signatures tested by a conjunction and `every`

`tools/shadow-contracts.mts#statedSignatures` returned `undefined` where
`entry.stated === undefined && entry.forms === undefined`, and returned its
printed list where `printed.every((p): p is string => p !== null)`. Where
the conjunction is false, the producer claims the entry at the union of its
record with `stated` present and its record with `forms` present; the
verifier's evaluation of the conjunction joins the two outcomes before the
`if` branches and keeps the record as declared, so the incoming edge of the
next statement is refused. `every`'s `this is S[]` is no contract of the
native ([prototype contracts](SOURCE-CONTRACTS.md#prototype-contracts)).

- **Avoided form and cost:** the conjunction of two presence tests of
  optional fields. Claiming the join the verifier keeps needs the producer
  to model that join of field refinements; the census shows this one site.
- **Equivalence:** `if (entry.stated === undefined) { if (entry.forms ===
  undefined) return undefined; }` reads the same fields in the same order
  and returns exactly where both are `undefined`. `printed` is a fresh array
  no other reference holds; `printed.filter((p): p is string => p !==
  null)` visits the same entries, and the comparison of lengths answers as
  `every` does, so the function returns a fresh array of the same strings,
  or `null`, where it returned `printed` or `null`. The overlay entries are
  plain records whose `stated` and `forms` are data properties. Returns,
  exceptions, mutations and receivers agree for every entry.
- **Scope:** `stated-signatures-presence`. No host contract or external
  assumption is added.
- **The same list in `indexedAccess`:** `tools/computed-types.mts#indexedAccess`
  kept the fields an object type gives a list of keys by `every`'s guard
  before `union(parts)`; it compares the length of
  `parts.filter((p): p is TypeTerm => p !== null)` with `parts`'s and
  passes the filtered list. `parts` is the fresh result of a `map` no other
  reference holds, and `union` receives the same terms in the same order.

### A command-line argument checked by a top-level statement

`tools/unchecked.mts` read its `--project` argument into `projectDir` and
then threw the usage error in a top-level `if (projectDir === undefined)`,
a statement outside the fragment, which the census omits: its `runPart`
then read `projectDir` at `string | undefined` where an argument list of
strings is built, in `decodeResult` and `findIn`.

- **Avoided form and cost:** a top-level test narrowing a module constant
  that later closures read. Supporting top-level statements is a change of
  the fragment; this one site needs none.
- **Equivalence:** `projectDir` is initialized by `present(args[projectAt +
  1])` where a `--project` flag is given, a module function that throws the
  same `Error` with the same message where the argument is absent and
  returns it otherwise. The throw happens during the constant's
  initialization instead of the next statement; nothing runs between them,
  and the module's later statements run in both forms exactly where no
  error was thrown.
- **Scope:** `module-argument-presence`. No host contract or external
  assumption is added.

### A saved nullable session tested before its ledger

`tools/declaration-session.mts#settleDeclarationSession` tests
`s !== null && s.ledger === ledger` before clearing `retained` and calling
`close(s)`. `inDeclarationAttempt` calls this function at an attempt's end.
The existing [guard checks](SOURCE-ELABORATION.md#guards) establish that the
saved local `s` holds a session through the writes to module state.

- **Avoided form and cost:** `s?.ledger === ledger` requires carrying the
  correlation between the optional-chain result and its receiver to the
  call after `retained = null`. The supplied census names one test shared
  by two functions. An explicit receiver test uses the existing narrowing
  checks; extending correlation inference for this single test has little
  reach relative to that rewrite.
- **Equivalence:** `s` is a saved local of type `Session | null`, and
  `ledger` is an object. For null, the optional chain yields `undefined`,
  whose strict equality with `ledger` is false; the explicit null test
  also skips the body. For a session, both forms read `s.ledger` once and
  compare it with the same object. The receiver test calls no code and
  writes no state. The body keeps its order: clear `retained`, update the
  telemetry, then close the same saved session. Returns, exceptions,
  mutations, method identities, aliases, receivers and asynchronous
  effects agree for every admitted input and reachable state.
- **Scope:** `blocker-prep-session-after-clear` checks the saved local
  through the module-cell write and close call. This rewrite adds no
  external assumption.

### A recording flag written through a shared reference

`tools/files.mts#inputRead`, also called by `noteInput`, marks every active
non-stage, non-ledger recording as dependent on a named input. `Recording`
requires `readsInput: boolean`; `observedNoting` and `newLedger` initialize
it to `false`. The assignment `r.readsInput = true` uses the existing
[write rule](PROGRAM-TYPING.md#key-adding-writes) for a field already
present. `optional-write-refused` shows the required field and an alias
reading it after the write.

- **Avoided form:** `readsInput?: true`, initially omitted, makes the write
  add a key through a shared reference. Supporting it requires proving that
  every alias permits the added key, beyond the existing local fresh-object
  mechanism. The census sites are `inputRead` and its caller `noteInput`.
- **Behaviour:** the flag records a two-state fact. Its consumer in
  `observedNoting` tests `recording.readsInput === true`; both an omitted
  flag and `false` give `false`, and marking gives `true`. Recordings keep
  their identities and all other fields; reads and writes keep their order.
  TScert's callers use ledger operations; they do not enumerate or test
  presence of this flag. The required field makes this internal state
  explicit at construction, including on ledgers, which `inputRead` skips.
  Returns, failures, cache retention and observation propagation agree for
  those callers. The named-input controls in `tests/observed-stages.mts`
  exercise caches inside and around stages, including replay.
- **Scope:** this rewrite uses no new rule or external assumption.
  `invalid-optional-write-alias` retains the refusal's safety example:
  two references to `{}` permit optional number and string fields;
  adding the number makes the string reference's `toUpperCase()` throw
  `TypeError` under Node.

### A mapped array replaced by filtered arrays in a loop

`tools/fragment-parse.mts#lowerFile` keeps its conditional map/flatMap
result in `initial`, runs the first filter, and initializes `lowered` with
that filter's result. Further rounds replace `lowered` with another filter
result. The existing [filter contract](SOURCE-CONTRACTS.md#prototype-contracts)
establishes the same presence mode at initialization and every assignment;
the final projection uses the existing [closure checks](SOURCE-CLAIMS.md).

- **Avoided form and cost:** initializing the mutable loop binding with a
  potentially sparse map result and replacing it with filter results
  requires different array-presence alternatives at the loop and a
  stronger fact at its exit. The six census sites share one loop. Splitting
  its first round uses the existing checks without extending loop inference.
- **Equivalent form:** the first filter runs unconditionally after the same
  initial map or flatMap. Its result length is compared with `initial.length`,
  exactly the receiver length used by the original first round. Each further
  round computes the absent names, filters, compares lengths and saves the
  result in the same order. Holes in the initial array therefore cause the
  same further rounds, including every callback's effects. The same fresh
  arrays and records reach the final map; field reads, returned values,
  aliases, mutations, exceptions and nontermination are unchanged. The
  private local bindings expose no additional value to callbacks. Later enum
  and module initialization lowering retains its order.
- **Scope:** `blocker-prep-captured-filter-map` exercises the first-round
  split and the final projection. This rewrite adds no external assumption.
- **Commit:** the introducing commit.

### A snapshot request with a conditional spread

`tools/fragment-parse.mts#projectFor` selects a complete request literal
for `compiler.updateSnapshot`: both branches supply `openFiles`, and the
changed branch also supplies `fileChanges.changed`. `openText` and
`openFile` reach that call through `projectFor`. The existing
[allocation and call checks](SOURCE-CLAIMS.md) establish each request.

- **Avoided form and cost:** `{ openFiles: [absolute], ...(changed ?
  { fileChanges: { changed: [absolute] } } : {}) }` requires the merged
  record to retain the writable request's nested field and array contracts.
  An explicit `UpdateSnapshotParams` annotation also leaves that allocation
  refused. The supplied census names this one request through three
  functions; complete literals use the existing checks without extending
  merge inference for it.
- **Equivalence:** `changed` is a local boolean, and `absolute` a string.
  Both forms read the same compiler method before allocating its argument,
  allocate fresh arrays and records, and call it once with the compiler as
  receiver. The changed request has own keys `openFiles`, then
  `fileChanges`, whose own `changed` array contains the same string; the
  other request has only `openFiles`. The spread's temporary plain record
  stays local and runs no getters. Standard prototypes supply no replaced
  hooks under the existing policy. Returns, exceptions, mutations, method
  identities, aliases, receivers and asynchronous effects agree for every
  admitted input and reachable state.
- **Scope:** `blocker-prep-snapshot-conditional-spread` checks both request
  branches. The rewrite adds no external assumption.
- **Commit:** the introducing commit.

### Compiler children read at their declared kinds

`tools/syntax.mts#childOf` and `#childrenOf` use the existing
[compiler family contracts](COMPILER-API.md#the-node-invariant) and
[kind guards](COMPILER-API.md#guards). Each key selects guards for the
kinds whose `childProperties` entry in the installed package's
`dist/api/node/protocol.generated.js` contains that key. A successful
guard supplies the declared member; the other kinds return `undefined`
or an empty list.

- **Repair:** a compiler child's declaration supplies its node type or
  node-list type. Reading it through `Reflect.get` into `unknown` discards
  that contract, then attempts to reconstruct a compiler node from its
  `kind` field. The kind guards retain the host identity and field type.
- **Avoided form and cost:** `Reflect.get(node, key)` runs the target's
  `[[Get]]`, including arbitrary getters and a supplied receiver in the
  general operation. The supplied 2026-11-01 census names two functions
  using this form. Their fixed child keys already have contracts in the compiler
  family, so the direct reads use existing checks.
- **Behaviour:** `RemoteNode`'s shared child getters call `getNamedChild`
  (`dist/api/node/node.generated.js`). It returns `undefined` for a key
  absent from that kind's child list. For a listed key, the direct read
  invokes the same getter with the same receiver once. The child contracts
  supply nodes, whose numeric `kind` passes the original `isNode` test.
  Compiler node lists are fixed and dense; `filter(() => true)` returns
  the same elements in the same order in a fresh ordinary array, as the
  original filter does. The kind reads are stable and run no client code.
  Returns, throws, mutations, receivers, element identities and list
  aliases therefore agree for admitted compiler nodes.
- **Scope:** `invalid-reflect-get-getter` exercises representative single-child
  and child-list reads in the rewritten form. `invalid-reflect-get-array`
  retains the general getter counterexample: under Node its getter removes
  the element the function promises to return as a number, so it returns
  `undefined`.
  The rewrite adds no host contract or external assumption.
- **Commit:** the introducing commit.

### A generic observed value assigned across try/finally

`tools/files.mts#observedNoting` initializes `value` with an immediately
invoked arrow whose `try` returns `run()` and whose `finally` removes the
recording and clears the attempt where it began one. The existing
[closure and allocation checks](SOURCE-CLAIMS.md) establish the returned
generic value and the observed result record.

- **Avoided form and cost:** `let value: T; try { value = run(); } finally
  { cleanup(); }` followed by record allocation needs the assignment's
  generic type to survive the cleanup and subsequent calls. The supplied
  census names this one allocation through five callers. In the isolated
  case, an explicit result-record annotation also leaves the allocation
  refused with a possibly undefined value. The returning initializer uses
  the existing checks without extending assignment inference for this site.
- **Behaviour:** the arrow is invoked once, immediately, and cannot escape.
  Both forms call the same `run` once, then execute the same cleanup before
  collecting and sorting observations or reading recording fields. Normal
  cleanup preserves the returned value or propagates the original throw;
  throwing cleanup replaces either completion with its throw. The extra
  arrow holds only the existing bindings and has no observable identity.
  Returns, exceptions, mutations, aliases, receivers and asynchronous effects
  agree for every admitted input and reachable state.
- **Scope:** `blocker-prep-observed-generic-record` uses the returning
  initializer. `observed`, `remembered`, `nodeResolve` and `resolveObserved`
  reach the same `observedNoting` allocation. The rewrite adds no external
  assumption or native contract.
- **Commit:** the introducing commit.

### A compiler call's first argument justified only by length

The `.apply`, `.call` and `.bind` branches of
`tools/fragment-expressions.mts#expr` save `node.arguments[0]`, reject
`undefined`, and pass the saved receiver to `gate.expr`. This uses the
existing [saved-target check](#an-array-patterns-first-element-after-a-length-test)
and binding narrowing rules. The length-only form requires a relation
between array length and element presence through intervening calls;
the array types state no lower length bound.

- **Equivalent form:** retain the length, spread and receiver-form checks,
  then check the saved first argument before constructing the lowered call.
  The compiler's [node-list contract](COMPILER-API.md#node-lists) supplies a
  fixed dense list of compiler nodes. A nonempty list therefore supplies a
  node at index zero, and the added rejection is unreachable for admitted
  inputs. Saving that node before the span and expression readers preserves
  the value: those calls cannot change the compiler list or its elements.
  The checks and binding invoke no client code. Both forms have the same
  returns, exceptions, mutations, method identities, aliases, receivers and
  asynchronous effects under that contract. The preceding checks reject
  empty lists and spread arguments in the same order.
- **Scope:** `blocker-prep-host-first-argument` exercises the saved receiver
  across the span and expression-reader calls. The runtime check adds no
  external assumption. The three indexed reads in `expr` share this form;
  the other census functions include it through their dependency on `expr`.
- **Commit:** the introducing commit.

### String keys retained through mapped-type collection

`tools/type-term.mts#expandIdentity` collects the keys of a mapped identity
into a fresh `string[]`. String literals contribute their text, numeric
literals contribute `numericKey`'s string result, unions recurse, and
`never` contributes no key. Every other key form is refused.

- **Repair:** the collection retains the string contract its insertions
  establish. `PropertyKey` also admits the `{ symbol: number }` encoding;
  widening the element contract to that union loses the primitive domain
  required by the existing [conversion contract](SOURCE-CONTRACTS.md#library-globals)
  at `String(n)` in the missing-field diagnostic.
- **Avoided form and cost:** converting an element read through
  `PropertyKey[]` requires a contract for object coercion and its callbacks.
  The collection's inputs require only primitive conversion, which its
  `string[]` contract states directly.
- **Behaviour:** the local collection has the same elements and order.
  Its callers receive the same fields or exceptions; the annotation
  changes no execution. Symbol keys remain subject to the collector's
  existing refusal.
- **Scope:** `mapped-identity-string-key` collects a string and converts its
  mapped elements. Its header names `expandIdentity` and `typeParts`, a
  caller in the same recursive group. The repair adds no external
  assumption.
- **Commit:** the introducing commit.

### A conditional expression spreading an optional-never arm

`tools/fragment-parts.mts#mapExprParts` maps a build's parts with a block
callback: `if (p.spread !== undefined)` returns the copied spread part;
the following return copies the named part. The same traversal supplies
`deepPartMap`, `directParts`, `forEachPart`, `fragmentTypes`, `moduleHolds`
and `astHolds`.

- **Route:** avoidance through the existing [branch refinements](PROGRAM-TYPING.md#refinement-under-an-observed-outcome)
  and [object merge checks](PROGRAM-TYPING.md#allocation-from-parts).
- **Avoided form and cost:** a conditional expression whose arms spread
  the tested object. Closure expression plans refine tested slots by tags;
  the optional field's observation needs the statement graph's read links
  to narrow the receiver. Extending those expression plans requires carrying
  the field observation and its validity through each arm's effects. A block
  callback expresses this site's branch with the existing checks.
- **Behaviour:** both callbacks test the same field once, then copy the same
  object's enumerable own properties before reading the selected field and
  calling `m.expr` once. They overwrite the same key with that call's result.
  They return the same fresh object, retain extra copied properties and
  aliases, and propagate the same exceptions. The block adds no read, call,
  mutation or asynchronous effect, and keeps `m` as the method receiver.
- **Scope:** `blocker-prep-optional-part-spread` uses the build-part union's
  named arm and optional `spread?: never`, with the mapper's stated `grow`
  effect. The [merge proposal](PROGRAM-TYPING.md#allocation-from-parts) retains
  optional fields at the empty type: they state that the key is absent.
  Every proposed merge remains subject to the existing merge checker.
  A forged-claim control claims that the open spread arm's copy lacks
  `name`; evidence production and checking both refuse that claim.
  The rewrite adds no external assumption.
- **Commit:** the introducing commit.

### A decoder's result asserted through unknown

`tools/diagnostic.mts#readDiagnostic` returns a diagnostic variant built
from typed decoded values, using the existing
[fresh decoder storage](#a-decoders-result-asserted-over-parsed-storage)
pattern. Its field decoders return their checked
contracts: outcome, span, source map, heap knowledge and node. Each variant's
fresh record states its complete writable contract through the existing
[allocation checks](SOURCE-CLAIMS.md).

- **Route:** a repair. A decoder that validates fields and discards the
  decoded values loses the contracts it needs to construct its result.
  Saving those values and allocating each variant retains those contracts.
  The decoder requires a source map for expression claims, direct
  obligations and source refusals, and a source node for node typing.
  Null values at these required fields yield `undefined`. Heap observation
  tags carry the decoded tag representation that their result type states.
- **Avoided form and cost:** a mutable dictionary of `unknown` values,
  followed by `as unknown as ObligationDiagnostic`. Assertions are
  obligations, so the intermediate `unknown` supplies no evidence for the
  record. Proving such an assertion requires the same field and variant
  contracts that direct construction states. A successful field test also
  cannot strengthen the storage contract of a writable alias.
- **Behaviour:** the input is parsed inside the decoder; its objects have
  no outside holders. The decoder returns fresh records and arrays from
  the saved checked values. Required-field checks enforce the stated
  result contract on malformed metadata. All diagnostic variants retain
  their fields, optional names and required-result labels. Metadata remains
  explanatory and does not decide certificate acceptance.
- **Scope:** `blocker-round-decoder-record-assertion` constructs a fresh
  result from a saved string. `invalid-decoder-record-alias` retains the
  double assertion on an input with an outside writable holder: writing a
  number through that holder makes the returned string read fail under
  Node. The wire controls in `tests/diagnostic.mts` cover every variant and
  malformed required fields. The repair adds no external assumption.
- **Commit:** the introducing commit.

### A negative object guard before primitive conversion

`tools/claim-text.mts#bareAtomText` prints malformed JSON atoms. After its
array check and negative object guard, it tests `typeof atom` for string,
number and Boolean, and `atom === null`, before calling `String(atom)`.
These tests establish the primitive domain of the existing [conversion contract](SOURCE-CONTRACTS.md#library-globals).

- **Route:** a runtime check. The JSON input contract retains the source
  value’s recursive shape; the explicit tests establish the conversion’s
  domain directly through the existing conditional checks.
- **Avoided form and cost:** using `!isObject(atom)` after the array check
  as the sole evidence for primitive conversion.
  The [guard’s positive promise](SOURCE-ELABORATION.md#user-defined-guards)
  states a dictionary view. Its false result supplies no converse promise
  excluding every object. Supporting that inference requires a checked
  converse for the guard; direct primitive tests suffice at this site.
- **Behaviour:** every admitted JSON value is a primitive, an array or a
  dictionary. The array branch returns first. On the remaining values,
  the explicit tests select exactly the values the original object test
  rejected. The fallback after the primitive tests is unreachable on that
  domain. The object guard retains its dictionary promise for subsequent
  field reads. Both forms set `state.printable` to false and apply the same
  conversion to the same primitive. Dictionaries follow the same printing
  branches. The tests invoke no client code, allocate nothing and write
  nothing; returns, exceptions, mutations, receivers and aliases agree.
- **Scope:** `blocker-round-unknown-string` exercises the JSON input and
  explicit primitive tests. Arbitrary object conversion requires accounting
  for conversion hooks and their effects. This rewrite adds no trust.
- **Commit:** the introducing commit.

### Host member reads after a generic guard

`tools/type-probe.mts#nodeAt` and the `marked` visitor in `makeProbe`
save `const node: Node = n` before testing `test(n)`. The guard narrows
`n` through an intersection with the generic parameter `N`; the member reads
use `node`, and the assignment to `found` uses the guarded `n`.

- **Avoided form and cost:** reading `n.end` after the generic guard and
  `n.getStart(file)` asks evidence search to read a union of host kinds
  through an intersection with `N`. The existing read summaries consume
  the receiver's named members; generic intersections require a derivation
  exposing their clause restriction before those summaries apply. The two
  supplied census sites need only the existing `Node` member view, which
  the alias retains through the existing
  [read checks](HOST-FAMILIES.md#stable-members).
- **Behaviour:** binding an immutable local to `n` runs no client code and
  retains the same object. The guard runs before `getStart`, which uses
  the same receiver and file argument; `end` is read only if both preceding
  tests succeed. The alias saves no property value, so mutations by the
  guard or method are seen by subsequent reads. The same guarded object is
  assigned to `found`, and the same `forEachChild` runs in the other arm.
  Returns, exceptions, mutations, method identities and aliases agree for
  every input admitted by the existing contracts.
- **Scope:** `blocker-round-generic-host-guard` verifies the aliased form.
  The rewrite adds no rule or external assumption.
- **Commit:** the introducing commit.

### Mapping a private snapshot before appending to its result

`familyTable` in `tools/host-families.mts` builds its arms with an explicit
loop over `[...groups.values()].sort(...)`, appending each `g.arm()` to a
fresh `FamilyArm[]`. It then appends the residual arm when one exists.
The existing [array and loop checks](SOURCE-ELABORATION.md) establish the
result's writable element contract.

- **Avoided form:** `snapshot.map(g => g.arm())`, followed by `push` on
  the result. An unrestricted callback gives `map` a possibly sparse
  result. Establishing that this particular callback cannot reach the
  private snapshot requires information beyond its callable contract.
  The supplied census identifies one site in `familyTable`. Tracking which
  fresh arrays a callback can reach would add a general analysis for this
  single use; the explicit loop uses the existing allocation and call rules.
- **Equivalence:** the snapshot is a fresh dense array of the map's values,
  sorted before any arm runs. Neither the snapshot nor the result reaches
  an arm function. Both forms call each saved arm once, in sorted order,
  with the group as its receiver, and save the returned value before the
  next call. Mutations of the groups or their map cannot change the saved
  sequence. Both propagate the first exception and append the same residual
  arm after all calls return. The result is fresh in both forms, with the
  same elements and element aliases. Under the existing stable standard-object
  assumption, array allocation, iteration, `map` and `push` invoke no
  additional client code here.
- **Scope:** `blocker-round-mapped-array-push` uses a fresh `slice` snapshot
  and an explicit loop, so its callback may mutate the original input
  without changing the visited sequence. Mapping that snapshot reproduces
  the receiver refusal. `invalid-round-mapped-array-push` retains a shared
  receiver: a callback that clears a two-element input leaves the second
  result position absent, and a later `push` preserves that hole. Running
  this fixture under Node returns `undefined` at that position. This
  avoidance adds no external assumption.
- **Commit:** the introducing commit.

### A named record widened to a JSON dictionary

`tools/files.mts#entriesRead` retains a readonly string index of readonly
string arrays on the fresh `{ files, directories }` record before
serialization. `GuardClosure` in `tools/guard-closure.mts` retains a
readonly string index whose values are file-digest dictionaries or module-edge
arrays. Its named `files` and `edges` fields keep their precise types.
The existing [record allocation checks](POSITIVE-TYPES.md#records) establish
the key bound, and the [JSON serialization contract](SOURCE-CONTRACTS.md#library-globals)
consumes it.

- **Repair:** fresh allocation establishes the complete key contract.
  Keeping it in the local annotation and the returned closure type prevents
  its loss before `JSON.stringify`. Directory listing and guard activation
  serialize the same records through their existing callers.
- **Avoided form and cost:** a named record with only its field types is
  open. General conversion to a JSON dictionary cannot establish that extra
  keys hold JSON values: a hidden callable `toJSON` can change the result
  and run client code. Retaining the known index contract needs no new rule
  or inspection of keys at runtime.
- **Behaviour:** the annotations are erased. The same literals allocate
  the same fields in the same order, with the same arrays and dictionaries.
  Serialization reads the same keys and values. Returns, serialized bytes,
  exceptions, mutations, aliases, receivers and asynchronous effects agree
  for the records these callers construct; the rewrite adds no execution.
- **Scope:** `named-implicit-index` checks construction and a function result
  retaining the index contract before serialization.
  `invalid-named-implicit-index` retains the open-record conversion: under
  Node an extra string-valued key survives its promised number dictionary.
  `invalid-json-stringify-record` exercises a hidden `toJSON` hook under
  Node. This repair adds no external assumption.
- **Observation records:** `tools/files.mts#Noted` intersects its named
  `observation` and `node` fields with `JsonObject`. The readonly string
  index bounds every additional key by the recursive JSON-value contract;
  the named writable fields retain their tuple and boolean contracts.
  `noteIn` is the sole writer of the private recording's answer map and
  allocates ordinary `{ observation, node }` records in that order.
  `observedNoting` snapshots and sorts those records; the cache and ledger
  retain that type. Every typed producer and consumer checks the complete
  bound. `resolveObserved` compares their existing JSON serializations.
  The annotations are erased, so allocation, traversal, key order and bytes
  are identical. `blocker-next-noted-json` exercises serialization through
  the retained index contract.
- **Commit:** the introducing commit.

### A formatting callback narrowed by an earlier every statement

`tools/shadow-contracts.mts#printSignature` states `string | null` on the
parameter of the callback formatting each parameter's printed type. The
existing [conversion checks](SOURCE-CONTRACTS.md#prototype-contracts)
admit interpolation of both strings and null. The preceding `every` test
retains its guard and early return.

- **Avoided form and cost:** the inferred callback parameter is `string`
  after the statement testing `every`. Certifying that narrower callback
  requires carrying the [elements fact](FOOTPRINTS.md#the-elements-fact)
  across the statement. This formatting operation accepts the full nullable
  element contract, so its written parameter uses the existing closure and
  conversion checks. The five supplied census sites share this callback
  through `printSignature` and its callers.
- **Behaviour:** the annotation is erased. Both forms evaluate the same
  `every` test, early returns, result and rest checks, and `map` callback
  bodies in the same order. They read the same methods, use the same
  receivers, allocate the same arrays and strings, and have the same
  returns, exceptions, mutations and aliases for every input admitted by
  their contracts. The callback can format null, though the preceding test
  returns before that call for an array containing null.
- **Scope:** `blocker-round-every-map-narrowing` checks the written nullable
  callback parameter.
- **Trust:** no external contract or assumption is added.
- **Commit:** the introducing commit.

### An optional native Map copied at explicit type arguments

`tools/family-activation.mts#activatedModules` copies the modules held by a
private `Loaded` value, or constructs an empty map when no guard table is
loaded. `checkedGuards` constructs that outer map with
`new Map<string, ReadonlyMap<string, unknown>>()` and supplies the sole
`Loaded` record. `loadedGuards`, `activateGuards` and the `activeTables`
cache carry that record's contract.

- **Repair:** `Loaded.modules` retains the outer native `Map` contract its
  provider supplies. Each namespace value keeps its structural
  `ReadonlyMap<string, unknown>` contract. This is the existing
  [native-map boundary repair](#native-probe-files-at-their-callback-boundary).
  The [native constructor overlay](SOURCE-CONTRACTS.md#library-globals)
  states the copy with either that native view or `undefined` as its input.
- **Avoided form:** `new Map(loadedGuards(description.guards, root)?.modules)`.
  Generic inference connects named applications and several union shapes;
  it has no matching path from an optional native map to a union of a
  parameterized native view and `undefined`. The optional constructor form
  alone therefore does not infer the key and value arguments. Supporting
  that inference requires matching structured union arms before collecting
  their binder constraints.
- **Equivalent form:**
  `new Map<string, ReadonlyMap<string, unknown>>(loadedGuards(description.guards, root)?.modules)`.
  The field annotation and constructor arguments are erased. The same
  guard lookup, property read and native constructor execute in the same
  order, with the same entries, identities, receivers, aliases, mutations,
  exceptions and asynchronous effects. The explicit arguments use the
  existing generic instantiation checks and add no runtime work.
- **Scope:** `blocker-next-optional-native-map-copy` checks the optional
  native copy with explicit arguments; `blocker-collection-from-iterable`
  checks inference for a definite native map. The structural iterator
  boundary remains `invalid-map-from-readonly-map`: its entry getter can
  mutate another array under Node. The constructor's existing native
  iterator and standard-object assumptions suffice.

### A native placement Map widened to ReadonlyMap

`tools/fragment-statements.mts#markEarly` accepts
`Map<FunctionDeclaration, number>`, the result contract of
`functionPlacement`. Its sole caller, `hoisting`, passes that constructed
map directly. The [native collection contract](SOURCE-CONTRACTS.md#library-globals)
retains the native iterator returned by `keys()`, so the existing array
spread checks establish the fresh array's element contract.

- **Repair:** retain the producer's `Map` contract at the parameter. A
  structural `ReadonlyMap` admits client implementations whose `keys()`
  returns a protocol iterator; array spread requires native iteration here.
- **Avoided form and cost:** widening this native map to `ReadonlyMap`
  before spreading its keys loses the iterator identity. General protocol
  spread requires checking iterator calls and their effects during array
  construction. This site already supplies a native map; retaining its
  contract uses the existing native spread mechanism.
- **Behaviour:** the annotation is erased. The same map, `keys` method,
  iterator and spread execute in the same order. The resulting array has
  the same keys, order and identities; returns, exceptions, mutations,
  aliases and receivers are unchanged for every map this caller supplies.
- **Scope:** `blocker-round-map-keys-spread` states the retained `Map`
  parameter. This repair adds no external assumption or rule.
- **Commit:** the introducing commit.

`tools/fragment-statements.mts#functionDeclarations` receives the same map
from its sole caller, `statements`, and reads it by `get` inside its
statement `{value: any, store: grow}`.

- **Repair:** its parameter states `Map<FunctionDeclaration, number>`. A
  structural `ReadonlyMap`'s `get` may be any client function, which states
  no effect (`invalid-readonly-set-has-effect` shows the same of
  `ReadonlySet`'s `has`); the native `get` changes no location.
- **Behaviour:** the annotation is erased; the same map's `get` runs with
  the same key and receiver, and its answers, returns, exceptions,
  mutations and aliases are unchanged for the one map the caller supplies.
- **Scope:** `map-parameter-get-footprint` states a `Map` parameter read by
  `get` inside a stated footprint. No external assumption or rule is added.
- **Commit:** the introducing commit.

### A live compiler overlay with checked read effects

`tools/files.mts#compilerOverlay` exposes `get` and `has` with the
existing [footprint contract](FOOTPRINTS.md). Each arrow calls the captured
native map's corresponding method with that map as its receiver. The
[native collection contract](SOURCE-CONTRACTS.md#library-globals)
establishes preservation of values and stores on normal return.

- **Repair:** `openFrontEndCompiler` receives the native `Map` supplied by
  its callers and passes its checked read interface to `compilerFileSystem`.
  The interface retains the effect contract at the read-only boundary.
- **Behaviour:** each lookup reads the live map. Mutations through the
  caller's map alias affect subsequent lookups. The adapter allocates one
  record and two arrows; each call forwards the same key and receiver and
  returns the native method's answer.
- **Scope:** `compiler-overlay-footprint` checks the real adapter inside an
  array map and observes a later update through its alias under Node.
  `invalid-compiler-overlay-footprint` uses an unrestricted structural
  `ReadonlyMap` reader that shrinks the source array during mapping; Node
  observes a hole in the result. The compiler's other file-system callbacks
  retain their own effect obligations.
- **Commit:** the introducing commit.

### Native merge binders widened to ReadonlyMap

`tools/array-prototype.mts#mergeRefusal` gives `Binders` the type
`Map<string, TypeTerm>`. Its `positional` helper constructs each initial
map with `new Map`; the recursive `visit` receives either that map or the
`substitution` map constructed for a base declaration. The existing
[native collection contract](SOURCE-CONTRACTS.md#library-globals) retains
the native iterator returned by `entries()`, whose spread supplies the
array used by the [semantic contract key](#type-terms-compared-through-their-semantic-fields).

- **Repair:** the annotation retains the native contract established by
  both producers.
- **Avoided form and cost:** widening these maps to structural
  `ReadonlyMap` permits client-defined entry iterators. General protocol
  spread requires checking iterator calls and their effects during array
  construction. This single census site already constructs native maps,
  so retaining their contract uses the existing native spread checks.
- **Behaviour:** the annotation is erased. The same maps, `entries`
  methods, iterators and spreads execute in the same order. Entry arrays,
  key and value identities, serialization, returns, exceptions, mutations,
  aliases and receivers agree for every input the callers supply.
- **Scope:** `blocker-round-map-entries-spread` states the native `Map`
  parameter supplied at this site. This repair adds no rule or external
  assumption.
- **Commit:** the introducing commit.

### An optional-chain result tested before a conditional record

`tools/fragment-classes.mts#classBody` tests
`base && base.proto && baseType` before allocating `baseProto`. The avoided
form is `base?.proto && baseType`. In that form, the incoming-edge check
receives a nullable temporary where the selected arm requires a string,
even with the existing store-preserving contract of `Gate.span`.
Supporting the form requires carrying the optional-chain result's
truthiness through the conjunction's temporary claims. The supplied census
sites are `classBody` and its caller `classStmt`, both containing this one
expression; an explicit receiver test uses the existing branch checks.

- **Equivalent form:** `base` is a class record or null. For null, both
  conditions select the null arm without reading `proto` or `baseType`.
  For a record, both read the same data field once in the condition, test
  its truthiness, and test `baseType` only when it is truthy. The selected
  arm evaluates the same fields in the same order, including the call to
  `gate.span` and the later read of `base.proto`. The extra test of the
  saved receiver invokes no code. Returns, exceptions, mutations, aliases,
  receivers and allocations agree under the existing caller contract.
- **Scope:** `blocker-round-conditional-record-join` states the same
  preservation contract as `Gate.span` and checks the explicit condition.
  `invalid-round-conditional-record-call` gives the callback an ordinary
  signature: under Node, a callback setting `base.proto = null` produces
  `{ k: "id", pos: 1, name: null }`, outside its result contract. The
  explicit test alone does not justify preservation across that call.
- **Trust:** no external contract or assumption is added.
- **Commit:** the introducing commit.

### An optional host list tested through a property receiver

`readTypeTerm`, `constructorForms`, `members` and `classInstance` in
`tools/type-term.mts` save a compiler node's `typeParameters` list in a
local binding, test that binding's optional `length`, and use that same
binding for the list argument or traversal.

- **Avoided form:** `if (!node.typeParameters?.length) return …;`
  followed by `quantified(…, node.typeParameters, …)`, and the corresponding
  positive tests. The existing [optional-chain test lowering](SOURCE-ELABORATION.md#optional-chains)
  exposes narrowing for a local receiver. Extending that lowering to repeat
  a property receiver requires evidence about its reads: an arbitrary getter
  may return different values or run code on each read. A saved binding uses
  the existing narrowing rules and retains the identity of the tested list.
- **Equivalent form:** `const typeParameters = node.typeParameters;`
  followed by `if (!typeParameters?.length) return …;` and use of
  `typeParameters`. The [compiler node contract](COMPILER-API.md#trust)
  gives stable, transparent member reads. The type reader preserves these
  node members between the test and use. Absent and empty lists select the
  same branch; a nonempty list supplies the same object to the same calls
  and traversals. Saving the list changes no return, exception, modeled
  mutation, allocation, method identity, alias, receiver or asynchronous
  effect under that contract. Compiler getters' hidden caches fall within
  its transparency requirement. This equivalence concerns compiler nodes;
  it does not assert repeated reads of an arbitrary JavaScript property
  have one value.
- **Scope:** `blocker-round-optional-host-list` checks the saved-list form
  with a `FunctionTypeNode` and a readonly array parameter. The rewrite adds
  no host model or trust assumption.
- **Commit:** the introducing commit.

### An array target justified only by length

The `Object.assign` branch uses the [saved-target check](#an-array-patterns-first-element-after-a-length-test).
The avoided form tests only `node.arguments.length` before destructuring
and passing the first element to `gate.expr`. Supporting that form requires
relating array length and element presence through the binding schedule and
its effects. The supplied census has no remaining sites for this construct;
the existing direct check establishes the obligation with the binding
narrowing rules.

- **Equivalent form:** keep the length test, spread rejection and array
  pattern, and test the saved target for `undefined` before using it.
  For compiler argument arrays, the nonempty array supplies a compiler node
  at position zero. Destructuring and the saved-value comparison invoke no
  client code under the existing standard-object assumption, so the added
  branch is unreachable for those inputs. Empty arrays and spread arguments
  fail at the same preceding checks. Returns, exceptions, source evaluation
  order, allocations, mutations, aliases and receivers are the same for every
  input admitted by that compiler contract. This equivalence is specific to
  compiler argument arrays; a sparse general JavaScript array can yield
  `undefined` despite positive length.
- **Scope:** `blocker-gap-round-assign-target-length-only` uses the checked
  form. It adds no external assumption or native contract.
- **Commit:** the introducing commit.

### Inferred writable fields in native method maps

`collect` in `tools/declaration-graph.mts` states `NativeField` on both
native-field map callbacks and `TypeTerm` on the replacement atom, as in
[the writable field repair](#native-method-maps-with-writable-field-contracts).
The inferred form gives fresh writable fields narrower literal contracts;
using those fields at the full union requires broader allocation contracts.
The supplied census has no remaining sites for this form. Extending
inference to choose those storage contracts has no additional measured
reach for this case; explicit annotations use the existing allocation and
closure checks.

- **Equivalent form:** each callback states its field result type. The
  replacement atom is bound as `TypeTerm` after the method test and before
  the field copy. Annotations erase, and the atom allocation reads only
  local bindings. Between that allocation and the copy, neither form calls
  code or mutates the input. Both maps visit the same fields in the same
  order, preserve the original fields on unchanged arms, and allocate the
  same objects on replacement arms. Returns, exceptions, mutations, method
  identities, aliases, receivers and asynchronous effects agree under the
  existing source contracts.
- **Scope:** `blocker-gap-round-native-method-map-inferred` verifies this
  equivalent form. The rewrite adds no external assumption.
- **Commit:** the introducing commit.

### A forward-captured helper without a stated effect

The [forward visitor helper](#a-forward-visitor-helper-with-a-store-preserving-contract)
states its effect on its callable binding. An ordinary arrow signature
with parameter and result types alone permits arbitrary store changes;
a recursive visitor capturing that binding cannot establish store preservation.

- **Avoided form:** `const outermostIs = (top: Node, n: Node): boolean => …`
  captured before initialization by a recursive visitor whose caller requires
  a store-preserving effect.
- **Equivalent form:** the binding states
  `(top: Node, n: Node) => Within<{ value: "any"; store: "keep" }, boolean>`.
  The existing initialization and closure checks certify the definition.
  Type annotations erase, so both forms have identical runtime code,
  including allocation order, receivers, aliases, exceptions and mutations.
- **Reason:** the supplied census has no sites for the unstated form.
  Inferring a stronger contract for a forward-captured binding would require
  extending inference across initialization; the written contract expresses
  the needed property through the existing mechanism at no runtime cost.
- **Scope:** `blocker-gap-round-visitor-effect-unstated` verifies in this form.
  The production helper uses the same contract. No external assumption is added.

### An initializer read after an `in` test on an open compiler node

`writtenApplications` in `tools/written-applications.mts` excludes another
module's executable initializers from its type traversal. Its
`isInitializer` helper saves `node.parent`, tests its compiler kind, and
compares its `initializer` child with `node`. The avoided form tests
`"initializer" in node.parent` before reading `node.parent.initializer`.
An `in` test on open `Node` does not state the field's value contract.
Supporting that form would require reasoning about an unstated key on an
open host-family member for a lookup expressible through the existing
[compiler node contracts](COMPILER-API.md#the-node-invariant).

- **Equivalent form:** the installed package's `protocol.generated.js`
  lists `initializer` at exactly eleven kinds: variable declarations,
  parameters, binding elements, enum members, property signatures and
  declarations, property assignments, JSX attributes, and `for`, `for-in`
  and `for-of` statements. At these kinds the guards expose the child
  field. At every other kind `RemoteNode.getNamedChild` yields
  `undefined`, which cannot equal the input node. Under the existing
  compiler host contract, parent and child reads are stable and guards
  only test the kind. Saving the parent and testing these kinds therefore
  gives the same Boolean, with the same exceptions, mutations, identities,
  aliases and receivers, and no asynchronous effects.
- **Scope:** `blocker-gap-round-parent-initializer` and
  `blocker-gap-round-parent-initializer-open-node` exercise the kind-based
  lookup. The rewrite adds no external assumption.
- **Commit:** the introducing commit.

### A decoded context saved before label validation

`readDiagnostic` in `tools/diagnostic.mts` saves `claim.context` in a local
binding before testing it with `Array.isArray` and visiting its labels.
The existing [binding narrowing](SOURCE-ELABORATION.md#guards) establishes
the local array view. Object-valued current contents of a mutable field
would require extending the [current-content assertions](SOURCE-MODEL.md#current-content-assertions)
beyond primitive values. The saved binding establishes the obligation
with the existing rules.

- **Equivalent form:** the claim comes from `JSON.parse`, so its context is
  a data property. The local binding holds the same array reference as both
  field reads. Between the test and the context traversal, the only calls
  decode `available`'s labels into fresh arrays through `decodeLabels`.
  `decodeLabels` tests arrays and integer bounds and maps to a fresh result;
  it writes neither the claim nor its context. Under the existing standard
  prototype assumption, the same array supplies the same `forEach` method
  and receiver. Both traversals visit the same elements in the same order,
  with the same results and exceptions. Saving the reference adds no object
  allocation or asynchronous effect.
- **Scope:** `blocker-gap-round-optional-for-each` and
  `blocker-gap-round-optional-for-each-field` exercise the saved
  reference, including callbacks with arbitrary effects.
  Equivalence for the decoder relies on its concrete read-only label
  validation; a caller-supplied callback could replace the field between
  traversals. The rewrite adds no external assumption.
- **Commit:** the introducing commit.

### An array pattern over a `Set`

`parameterIndex` in `makeProbe` (`tools/type-probe.mts`) collected each
declaration's type parameter position into a `Set` and read its first
element with `const [index] = indexes`. An array pattern over a host
iterable other than an array is refused at its element read;
support would step the host's iterator in a
pattern's lowering, for this one site of the census of b81675f.

- **Equivalent form:** the loop keeps the first position and whether every
  later one equals it, and returns that position where they all do and it
  is not negative, as the `Set` of one element did. The loop runs the same
  calls in the same order; positions are integers, which `Set` compares as
  `!==` does.
- **Commit:** 467af18b.

### A method call on the instance under construction

The `Gate` constructor (`tools/fragment-parse.mts`) assigned its field
`scope` from `this.termScope()`, a record of hooks closing over the gate.
A constructor's statement or field assignment reading `this` is refused
because the instance is allocated at the constructor's end from one value per field
([model limits](SOURCE-FRAGMENT.md#model-limits)). Support would allocate the
instance before the call and add its remaining fields afterwards, writes
adding keys to an object the method's closures already hold, for this one
site of the census of 6be11ce, which blocks 769 statements of 7 functions.

- **Equivalent form:** each reader of the term scope calls `termScope()`
  where it read the field. The record holds the gate's `readonly` `file`
  and hooks that read the gate's fields when they run, so each call's
  record answers every hook as the field's record did. No reader compares
  records by identity or keeps one, and no code reads the gate's own keys.
- **Commit:** the introducing commit, `A gate's term scope is computed
  where it is read`.

### Overloads of a function stating an effect

`resolutionSlots` in `tools/type-term.mts` stated its effect on an
implementation beside two overloads, the first giving the call at
`"resolvable"` a result of type `string`. A statement on an overloaded
declaration is refused where the declaration is read
([fragment boundary](SOURCE-FRAGMENT.md),
`invalid-stated-overload-value-import`,
`invalid-stated-one-overload-value-import`), and an overloaded declaration
in the checked file is refused at its overloads
(`invalid-method-effect-overload`). It is the one overloaded function declaration
of `tools/`. Support would certify one body at each overload's signature
and effect, for this one site.

- **Equivalent form:** `resolvableSlots(name)` returns the record
  `resolutionSlots(name, "resolvable")` returns, at the type the first
  overload stated, and `intrinsics` (`tools/intrinsics.mts`), the one
  caller reading its result as a `string`, calls it; `resolutionSlots`
  keeps its implementation's signature. Overloads run no code, and each
  call builds a fresh record of the same two strings.
- **Commit:** the introducing commit, `resolutionSlots states its effect
  at one signature; resolvableSlots states the resolvable result`.

### A spread of a program's iterable in a conditional's branch

`visitType` in `tools/type-term.mts` bound its scope with
`term.k !== "scheme" ? bound : new Set([...bound, ...binders])`, a spread of
a `ReadonlySet` in a conditional's branch. JavaScript evaluates the test
once, then steps the iterator in the branch the test selects; the lowering
collects a spread before its statement, a place the test, a member read,
does not reach (`blocker-spread-in-conditional`). Support would lower a
declaration whose value is a conditional into one branch per test outcome,
with the narrowing of each, for this one site of the census of 6be11ce, which
blocks 757 statements of 30 functions.

- **Equivalent form:** `inner` starts as `bound`, and where `term.k ===
  "scheme"` a `const` collects the new `Set`, its statement's first
  evaluation, which `inner` then holds. `term.k` is read once and compared
  strictly, as before; the `Set` is built from the same operands in the same
  order; `inner` is a local no closure reads, holding the same value at each
  later read.
- **Commit:** the introducing commit, `visitType builds a scheme's scope in
  an if, so the spread of bound runs first in its statement`.

`leavesLoop` in `tools/fragment-support.mts`, called by `completes`, held
the labels its blocks declare in a `ReadonlySet` and extended them with
`s.label === null ? inner : new Set([...inner, s.label])`, the same
construct, which the census of 945fa80 refuses in `completes`.

- **Equivalent form:** the labels are a `readonly string[]`, extended by
  `[...inner, s.label]`, a spread of an array, and tested by `includes`.
  Labels are strings, which `includes` compares as `Set`'s `has` does; no
  code mutates the labels or reads their identity, and a repeated label
  changes no test.
- **Commit:** the introducing commit, `leavesLoop holds a block's labels
  in an array`.

### A write at the index `indexOf` finds

`flatten` in `familyTable` (`tools/host-families.mts`) gathered the members
an interface states under one name: it found the entry for the name with
`find`, and replaced it with a copy holding one more member by
`own[own.indexOf(existing)] = …`. The key is typed `number`, and a write at
a key no contract names has no rule
([arrays](PROGRAM-TYPING.md#arrays)): `indexOf`
gives -1 for an element it does not find, and a write at or past the
length extends the array, leaving holes (`blocker-array-index-of-write`).
Support would relate the index to the array's elements and length, for
this site and one more of the census of 4d25222: `classInstance`
(`tools/type-term.mts`) replaced the field of an ambient class's first
overload of a method by the field joining a later overload's signatures,
`fields[fields.indexOf(overload)] = joined`.

- **Equivalent form:** the entry's members are a writable array, and the
  found entry gets the member by `existing.members.push(m)`
  (`array-found-element-update`). Each entry is created in this loop and
  read only by `find`'s test of its name before the loop ends, so keeping
  the first entry and extending its array leaves `own` holding the same
  names, owners and members in the same order as replacing it with a copy;
  the calls of `graph.name` and `graph.fail` run as before.
- **Equivalent form in `classInstance`:** the map of overloads by name
  keeps the joined field, and the instance's fields are the collected ones
  with each field replaced by the map's entry for its name, read once the
  members are collected. The map holds an entry only for a field it was
  given, under that field's name, and its entry for a name is the latest
  join; member names are distinct (`named` refuses a second), so each
  replaced field is the one the index write replaced, at its position. The
  collected array is local and read by nothing else, so returning the
  mapped copy gives the same fields in the same order.
- **Commit:** the introducing commit, `familyTable gathers a name's members
  without a write at a computed index`; for `classInstance`, the introducing
  commit.

### A `this is X` method of the compiler's `Type`

`literalUnion`, `generic`, `distributed` and the other readers of checker
types in `tools/computed-types.mts`, `makeProbe` (`tools/type-probe.mts`),
`isAny`, `writtenContext` (`tools/unchecked.mts`) and the declaration
reader (`tools/declaration-graph.mts`) tested a type by its
method, `type.isUnionType()`, and read the promised member, `getTypes()`. A
`this is X` predicate's promise is about the receiver, which is no actual of
a call, and `Type`'s view lists no such method
(`invalid-compiler-api-type-method`); support would add a receiver promise
to the calculus's promise signatures and their theorems, for sites the
predicate functions of the same names serve
([stated type guards](COMPILER-API.md#stated-type-guards)), which block 667
statements of 17 functions in the census of 6be11ce.

- **Equivalent form:** each call `t.isX()` becomes `isX(t)`, the sync API's
  function of that name (`isClassOrInterface` becomes
  `isClassOrInterfaceType`). `TypeObject`'s method is
  `isX() { return isX(this); }`, calling the module's function, which the
  import binds (`dist/api/sync/api.js`, audited 2026-10-29); with the
  prototype unchanged, which no verified code reaches
  ([host provenance](COMPILER-API.md#host-provenance)) and external code
  leaves as T8 states, the call computes the same answer from the same reads
  of the same object, and `t` is evaluated once in both forms.
- **Commit:** the introducing commit, `The sync API's type predicates are
  stated guards`.

### A spread of a record of readonly fields

`tools/type-graph.mts#footprintEffect` constructs the nine fields of a
`CallEffect` from its footprint and optional guarantees. The options have
type `Partial<Omit<CallEffect, "footprint">>`; an omitted or `undefined`
option gives the field its `false` or `null` default. Explicit `false` and
`null` retain those values. `promiseEffect` supplies its promise through
this constructor. `withPromise` copies an effect's nine fields with a
replacement promise, retaining every other guarantee. All three constructors
state checked normal-return preservation of values and stores: their bodies
read metadata and allocate fresh records through the existing footprint rules.

A `CallEffect` has readonly fields. Such a record permits host values,
whose own keys the type does not enumerate. Object spread requires a
contract that excludes them
([excluding host values](HOST-FAMILIES.md#excluding-host-values),
`invalid-compiler-api-node-spread`).

- **Equivalent form:** the effect's known footprint and selected guarantees
  are passed to `footprintEffect`. A promise update of existing metadata
  calls `withPromise`. The replaced operands are ordinary effects constructed
  by the metadata factories; they own exactly the nine data properties in
  constructor order. Construction retains the same values and key order,
  including the identities of the footprint, promise and element-kind arrays.
  `withPromise` retains the unchanged fields of its input. The one-argument
  constructor calls retain their defaults. At these sites the arguments are
  lexical reads, reads of ordinary data properties and fresh literals. They
  invoke no code, and the intermediate allocations are unobserved.
- **Avoided form and cost:** `{ ...emptyEffect, onThrow: true }` and
  `{ ...footprintEffect(footprint), promise }` spread a readonly contract.
  Tracking the constructor's fresh value through that annotation would
  establish a stronger fact than its readers need. Explicit construction
  uses the existing object checks. A custom call allocates an options record
  and its result; the avoided form allocates its result and, for an inline
  constructor operand, the intermediate effect record. A promise update
  allocates its result and retains the input effect.
- **Scope:** `blocker-prep-effect-spread` constructs an on-throw effect;
  `blocker-round-collection-effect` constructs a native collection guard's
  promise. `spread-readonly-record-refused` retains the host exclusion.
  `tools/library-modules.mts` retains its readonly effect spreads with the
  same host-exclusion obligation ([catalog scope](../WORK.md#status)).
  `tools/compiler-api.mts#requestReading` copies its local effect's nine
  fields explicitly; that local owns those fields and no code writes it.
- **Commit:** the introducing commit.

### A parameter type computed from a compiler-API method

`tools/declaration-session.mts` and `tools/compiler-channel.mts` named a
snapshot request's type `NonNullable<Parameters<API["updateSnapshot"]>[0]>`,
and `openCompiler`'s parameter `ConstructorParameters<typeof API>[0]`. An
indexed access reads a member's declared annotation, which a method has
none of (`blocker-api-indexed-method`), and `ConstructorParameters` of a
generic class's `typeof` is refused. Support
would read a method member and the constructor of a generic host class at
its instance's arguments through the class's view, for these three sites of
the census of 4d25222, which block 245 statements of 13 functions.

- **Equivalent form:** the request's type is `UpdateSnapshotParams` of
  `typescript/unstable/proto`, the declaration the view's
  `updateSnapshot(params?: FromLSP extends true ? LSPUpdateSnapshotParams :
  UpdateSnapshotParams)` names, and `openCompiler`'s parameter is
  `APIOptions | LSPConnectionOptions | undefined`, the constructor's
  `options?: APIOptions | LSPConnectionOptions`. TypeScript evaluates `API`
  at its default `FromLSP = false`, so the conditional is its false arm, and
  `NonNullable` drops the `undefined` the optional parameter adds: the
  types are identical, which a mutual-inclusion check of both pairs under
  `tools/tsconfig.json` confirms. Types are erased, and the imports are
  type-only, so the code runs as before.
- **Commit:** the introducing commit.

### Node's declared type-stripper export

`tools/strip-types.mts` reads `nodeModule.stripTypeScriptTypes` and checks
that it is callable before using it. The pinned Node declarations state
this export; the call retains its declared function type. The
[module overlay](SOURCE-CONTRACTS.md#library-modules) states its one-string
call.

- **Avoided form:** `Object.getOwnPropertyDescriptor(nodeModule,
  "stripTypeScriptTypes")?.value`, which passes a module namespace as an
  ordinary value.
  [Namespace imports](SOURCE-ELABORATION.md#namespace-imports) are used
  through their member reads.
- **Equivalent form:** `nodeModule.stripTypeScriptTypes`. An ES module
  namespace's named export is an own data property, so its value is the
  descriptor's value. An absent export gives `undefined` in both forms;
  the callable check and conversion of the result remain. The
  call reads the export directly under the standard-object assumption
  that the Node built-in and its exported function are untampered. The
  native function ignores its receiver.
- **Evidence:** `blocker-prep-namespace-descriptor` reads the export and
  calls its one-string form; `strip-types.mts#stripTypes` is its census site.
- **Commit:** the introducing commit.

### Generic rest forwarding for callback service views

`tools/declaration-graph.mts#declarationServices` groups callback destinations
through twelve views of the original `DeclarationOptions` object. Each
view holds that object. The callback views are `bindingAnswers`,
`operationAnswers`, `typeAnswers`, `enumAnswers` and `observations`. Their consumers invoke members
directly, including `resolutionClean`'s call of `observations.seen`.
A method call selects the callback once before evaluating its arguments and
supplies the options object as its receiver.

The avoided form creates a getter for every callback. Each getter selects
its destination and returns a generic rest closure forwarding through
`Reflect.apply(answer, options, args)`. An abstract argument pack describes
lists of values; collecting those values into a fresh array needs a store
contract related to that pack. The existing rest-array allocation checks
represent arrays and required-position tuples, while the abstract pack has
no such store row ([calls](SOURCE-MODEL.md#calls)).

Request views retain property reads at their consumers. Each array read
already supplies its `?? []` default there; an absent request creates the
same fresh default at that read. The completion-presence test reads
`typeAnswers.completion`, the callback the options object supplies, once
before its truthiness test. Input and policy views read the same fields.

The views preserve the consumer protocol's callback reads, receiver,
argument evaluation order and arity, returns, exceptions and alias mutation.
An argument replacing the destination cannot replace the selected callback;
an absent destination skips its arguments. The views are private and their
consumers neither enumerate the groups nor extract callbacks for later
invocation. Equivalence is scoped to these consumers: the views expose the
options object's keys and identity if inspected as ordinary objects.
The rewrite removes forwarding allocations and adds no runtime check or
external assumption. Existing record views and optional method calls check
`blocker-round-generic-rest-answer`.

`closure-rest-pack-refused` uses an ordinary `number[]` rest in its local
counting closure. Its exported `count(): number` supplies exactly `1, 2`
and observes the collected length; the generic tuple parameter contributes
no further observation. The equivalent function returns `2`. This case
exercises the ordinary rest-array check; generic argument-pack rest closures
retain the [model limit](SOURCE-FRAGMENT.md#model-limits).

### A map over a literal holding a possibly absent first element

`liftClause` in `tools/claim-text.mts` lifted a reference clause's cells as
`[first, ...rest].map((c, i) => cell(types, c, depth - 1, i === 0 ? views : []))`,
`first` a `JsonValue | undefined`. An array literal is stated `readable`
where no type is expected of it, and a readable array whose elements admit
`undefined` is not known to be dense, so the map result may hold holes and
does not meet `shown`'s `ReadonlyArray<JsonValue>`.

- **Avoided form and cost:** support would state a literal written without
  holes as dense, a change to every unannotated array literal's contract.
- **Equivalent form:** `[cell(types, first, depth - 1, views), ...rest.map(later)]`,
  with `later` stating `{value: any, store: grow}`. `rest` is a
  `readonly JsonValue[]`, whose readable elements exclude `undefined`, so it
  holds no hole; the cells are lifted in the same order with the same views,
  and the literal holds the same records. Returns, exceptions and mutations
  agree.
- **Scope:** `blocker-claim-lift-forms`.

### A closure reading a binding narrowed outside it

`liftLabels` in `tools/claim-text.mts` tested `both && label === falseLabel`
and `name !== undefined` and returned closures reading `name`. A closure
reads a captured binding at its declared type, and a binding tested only
outside it keeps that type inside.

- **Avoided form and cost:** support would carry an enclosing narrowing
  into a closure's captures.
- **Equivalent form:** `pairTrue` and `pairFalse` hold the pair's labels
  where both are present and `undefined` otherwise; a label, a `JsonValue`,
  is never `undefined`, so `label === pairFalse` holds exactly where
  `both && label === falseLabel` held. The tested name is copied into a
  constant typed `string` that the closure captures. Returns, exceptions
  and mutations agree.
- **Scope:** `blocker-claim-lift-forms`.

### A record literal whose discriminant a conditional selects

`tools/fragment-expressions.mts#chainLink` built a call record as
`{ k: method ? "invoke" : "apply", pos, callee, args, …spreads }`, expected
at `Expr`. Its `k` is the union `"invoke" | "apply"`, a record no arm of
`Expr` holds: TypeScript admits it by distributing the record over the
discriminant's members, which the subtyping of the calculus does not do.

- **Avoided form and cost:** support needs a subtyping rule distributing a
  record over the literal members of one field, with its soundness proof;
  the census shows this one site at a discriminated union.
- **Equivalence:** `if (method) return { k: "invoke", … }; return { k:
  "apply", … }` tests `method`, then evaluates `pos`, `object`, `args` and
  `spreads.length` in the original order, and the invoke arm spreads
  `typeArgs` where it has any. The apply arm omits the `typeArgs` spread,
  which there spread `{}` and added no key. The returned record has the
  same keys in the same order and the same values.
- **Scope:** `blocker-conditional-discriminant-record`.

### A loop replacing a binding's record on each pass

`tools/fragment-expressions.mts#template` folded a template's spans with
`for (const part of node.templateSpans) { acc = { k: "arith", …, l: acc,
r: gate.expr(…) }; acc = { … } }`. A `for...of` loop that replaces a
binding's record with a fresh one on each pass is refused at the loop's
entry: the loop head's knowledge from the back edge separates the fresh
record from the loop's iterator, which the entry edge does not state
(`blocker-for-of-fresh-record`, a gap in WORK.md).

- **Avoided form and cost:** support is a change to how the search
  generalizes separation knowledge at a loop head; this round writes the
  one site out.
- **Equivalence:** `node.templateSpans.reduce((acc, part) => …, head)`
  visits the same spans in order: the span list is a compiler node array,
  dense, which `gate.expr` does not change (the compiler's tree is read
  only under its host contract). Each step evaluates the substitution with
  `gate.expr` and allocates the two records in the original order, and the
  last answer is returned; `reduce`'s length read once and the iterator's
  per step agree on a list that does not change.
- **Scope:** `blocker-compiler-api-template-reduce`.

## Host boundaries

Operations of TScert's code on an external service that no rule models,
each in the smallest module performing it, its callers verified against
its signatures and its own functions refused ([deciding](#deciding-what-a-refusal-of-tscerts-code-calls-for)).

### The compiler client's prototype

The compiler channel checks that an `API`'s private client has its request
methods and wraps every request, so that its failure is a `CompilerFailure`
and its answer is noted in the compiler's ledger, and answers a snapshot's
query asked again from memory. The methods are own data properties of the
client's class prototype, reachable only through `Object.getPrototypeOf`,
which has no entry: its result may be `Array.prototype`, or a class's
prototype that passes `instanceof` for its base while holding none of the
base's fields (`invalid-get-prototype-array-prototype`). No form within the
language reads them: a read through the client can run a getter.

The census sites `clientHasMethod` and `guardClientRequests` are the
boundary's implementation. Their direct prototype reads rely on this
contract. Its caller `invalid-error-subclass-prototype` verifies the
`clientHasMethod` signature, and `blocker-client-prototype` verifies the
request wrapper's caller; `blocker-client-prototype-forged` refuses an
ordinary object presented as an API.

The general prototype-observation source represented by the first case's
name is safe but outside the fragment:

```ts
class Decline extends Error {}
export function proto(): object | null {
  return Object.getPrototypeOf(new Decline("x"));
}
```

It returns `Decline.prototype` under Node. Its return annotation is true;
exposing arbitrary prototypes requires a model admitting values such as
`Array.prototype` and class prototypes lacking their instances' fields.
The compiler uses its declared request operations through the boundary.

- **Boundary:** `tools/client-prototype.mts`. Its functions take the `API`
  itself, a compiler API value only the package makes, whose private members
  no ordinary object has (`blocker-client-prototype-forged`).
  `clientHasMethod(api, member)` tests one of the six request members.
  `guardClientRequests(api, around)` wraps all six, once per class prototype:
  each wrapper calls `around(member, receiver, args, send)`, `send` sends the
  request once, while `around` runs, and the wrapper returns the request's
  answer itself; it throws when `around` returned without sending, and
  throws the request's failure when `around` returned after it failed. The
  memo of a snapshot's queries is in the boundary.
- **What callers get:** request guards expose neither the prototype nor a
  way to answer a request. The private-client accessor has the separate
  [client and child-process contract](#the-compiler-client-and-its-child-process).
  The channel's `around` (the ledger, the failure
  conversion) is verified against these signatures (`blocker-client-prototype`).
- **Contract, audited against the package** (`dist/api/sync/client.js`,
  `api.js`): the request methods are own data properties of `Client`'s
  prototype; the package catches no error of a request; `apiRequest` returns
  a fresh `JSON.parse` of the reply, or `undefined` for an empty one. Every
  client of the process shares the prototype, so the first call wraps every
  client's requests. A query of a held snapshot asked again is answered by
  reading back the earlier answer's JSON text, which assumes the compiler
  answers it the same each time (query omission, a conjecture).
- **Method provenance in the front end:** TypeScript 7.0.2's
  `dist/api/sync/api.js` allocates `API.prototype.updateSnapshot` as an
  ordinary class method; `dist/api/sync/client.js` does the same for
  `Client.prototype.close` and the six request methods. In the front end's
  opening and wrapping paths, these function objects retain
  `Function.prototype` and own no `call`, `apply` or `bind` property. This
  follows from their audited allocation and the writes in those paths,
  together with the standard-prototype policy.
  `openCompiler` constructs the API, binds its `updateSnapshot`, then
  installs the document-counting wrapper on that instance.
  `guardClientRequests` captures the six original request methods before
  replacing the prototype's slots; its sole front-end caller supplies the
  ledger and failure-handling callback. `releaseCompiler` captures the
  client's `close` before installing its wrapper. A repeated close wraps
  that same front-end function. These wrappers are ordinary functions
  created by the front end; they retain the saved methods and their
  receivers, and write no invocation property of those functions.
  This audit concerns the package-created instances and these permitted
  replacements used by the front end. A callable signature or a `typeof`
  test alone does not establish method-function provenance. F3's guard
  identity, F5's unwritten bindings and T6's direct-call behavior have their
  stated [host-contract scope](COMPILER-API.md#trust); the general source
  [confinement requirement](SOURCE-ELABORATION.md#calls-through-functionprototypecall)
  applies to escaped and caller-supplied functions.
- **What depends on it:** the functions of `compiler-channel.mts` that check
  or guard the client, and every use of the compiler API in the process:
  every client shares the wrapped prototype, so each answer the package
  returns passes through the wrapper.
- **Commit:** the introducing commit, `Confine Object.getPrototypeOf to a
  host boundary of the compiler channel`.

### The compiler client and its child process

This extends [the compiler-client boundary](#the-compiler-clients-prototype).
`tools/client-prototype.mts#checkedPrivateClient(api)` performs the package's
private-client lookup and checks its close method, request methods and child
members. `tools/compiler-channel.mts#privateClient` calls that accessor.
The boundary accepts the nominal compiler `API`, whose private client the
package constructs. General object tests cannot establish a native child's
method signatures, callback behavior or changing process fields. Supporting
those operations requires their external contracts regardless of how the
nested object is narrowed.

- **Contract:** the accessor returns the API's client itself. `close()` uses
  that client as receiver, calls its channel's `close()` and returns void on
  normal completion. `channel.child` is the channel's Node `ChildProcess`:
  `pid` is a number or undefined, `exitCode` a number or null, and
  `signalCode` a string or null. `kill("SIGKILL")` uses the child as receiver
  and returns a boolean on normal completion. `once("exit", listener)`
  registers the listener once and returns the child; the listener is called
  when Node emits exit, with the exit code and signal arguments, which this
  zero-parameter listener discards. Calls may throw; no preservation effect
  is promised. Process fields change as Node observes termination, and
  listeners may run other code.
- **Behavior:** the lookup uses the same `fieldOf` reads, member tests and
  request-member loop, in the same order, with the same errors. It returns
  the original client, channel and child identities. Callers' ledger keys,
  method receivers, close-method replacement and later child reads retain
  their original objects.
- **Audit:** TypeScript 7.0.2's local `dist/api/sync/api.js` constructs its
  client; `dist/api/sync/client.js` constructs `SyncRpcChannel` and forwards
  `close`; `dist/api/syncChannel.js` stores the result of Node's `spawn` in
  `child`. Channel close removes the child from its live set, closes its pipe
  and streams, signals the child, and resets its descriptors, swallowing
  exceptions within that operation. The front end's close wrapper announces
  the process end and invokes the saved method with the same receiver.
- **Trust:** the package retains this private layout, Node supplies the
  stated child-process behavior, and external code preserves those private
  object contracts. The front end's close wrapper satisfies the same void
  contract. Runtime shape tests detect missing members; they do not prove
  these external contracts. This trust is outside the calculus theorem and
  requires owner review. It includes the policy assumption about stable
  standard objects and prototypes.
- **Scope:** `blocker-prep-private-client-assertion` verifies the accessor's
  caller. The accessor's implementation remains outside that proof; its
  assertion is confined to the external operation. `tests/tool-failures.mts`
  exercises opening and abandoning a real compiler and observing its exit.
  `compilerLedger`, `abandonCompiler` and `abandon` consume this contract.

### URLs as strings

The front end's two operations on WHATWG URLs, each from strings to a
string. A URL the program held could reach other code, which may give it
or its search parameters an own member that a later read of its `href`
runs ([Node's `URL`](SOURCE-CONTRACTS.md#nodes-url)); the boundary holds
each URL it makes inside one function.

- **Boundary:** `tools/url-strings.mts`. `pathToFileHref(path)` is
  `pathToFileURL(path).href`, and `resolveHref(input, base)` is
  `new URL(input, base).href`.
- **What callers get:** a string, the URL's serialization; never a URL.
  Callers are verified against `(string) => string` and
  `(string, string) => string`, which state no effect
  (`blocker-node-url-import`).
- **Contract, audited against Node 25.2.1's `lib/internal/url.js`:** each
  function constructs a URL, reads its `href` once and returns it; the URL
  reaches no other code, since Node's URL construction publishes nothing
  (no diagnostics channel) and the function passes it nowhere. The `href`
  getter of a URL whose search parameters no code has read serializes its
  parsed record. Under the approved policy that standard objects and
  prototypes are not tampered with, the getter is `URL.prototype`'s and
  runs no other code. `pathToFileHref` resolves a relative path against
  `process.cwd()`, so its result depends on the working directory, and
  for a relative path throws what `process.cwd()` throws (the working
  directory removed: ENOENT, run under Node 25.2.1); a NUL character is
  encoded as `%00`;
  `resolveHref` throws a `TypeError` where its input is no URL relative to
  the base, or the base is no URL.
- **Its own functions:** both verify. Each body is the composite read
  `new URL(…).href` or `pathToFileURL(…).href`, which the overlays state as
  a call of an intrinsic from strings to a string
  ([Node's `URL`](SOURCE-CONTRACTS.md#nodes-url), `node-url-fresh-href`):
  the contract above, stated where the read is written.
- **What depends on it:** `files.mts#observeResolution`,
  `files.mts#resolveObserved` and `family-activation.mts`'s module URLs.
- **Commit:** the introducing commit, `node:url and URL overlay contracts; host boundaries for URL strings and a child's output`;
  the serializing reads, `Repairs and loop forms for the host cluster's own functions`.

### A child's output

`unchecked.mts` runs each part of its check in a child process and reads
the child's standard output. Node publishes a child on a diagnostics
channel before `spawn` returns, so other code may hold it: replace its
`stdout` (an own getter answering anything) or its methods, change the
stream's encoding, remove listeners, or emit `data`, `close` and `error`
with any arguments and any number of them, no standard prototype changed;
out of file descriptors, `spawn` returns before it assigns `stdout`. No
contract a program could hold the child at states all of that, so the
program holds none.

- **Boundary:** `tools/child-output.mts`.
  `runChild(command, args): Promise<ChildOutput>`, with
  `ChildOutput = { code: number | null; signal: string | null; stdout: string }`,
  runs the command with standard input ignored, standard output collected
  and standard error inherited.
- **What callers get:** a promise of plain values, never a child, a stream
  or a listener. Callers are verified against that signature, which states
  no effect (`blocker-node-child-output`).
- **Contract, what TScert relies on:** the promise, where it settles,
  resolves to a value of `ChildOutput`'s types or rejects with an `Error`
  of a fixed message, and settles once. Every value is checked before it
  is used: a `data` event other than one string, and a `close` event other
  than a number or `null` and a string or `null`, reject; an event after
  settling is ignored before its arguments are read; an `error` event
  rejects without its payload being read, so no getter or conversion of
  the payload runs; a `stdout` that is no object with `setEncoding` and
  `on`, or another object on a second read, rejects; and whatever `spawn`,
  a replaced method or a getter throws while the child is started and its
  listeners are installed (a NUL character in the command, a throwing
  `on`) rejects with a fixed message, the thrown value unread.
- **Not promised:** that the values are the child's, that the output is
  UTF-8, or that the promise settles. Other code holding the child may emit
  valid events (resolving with its values while the child prints and exits
  otherwise), substitute a stable stream or replace the child's `on`,
  change the encoding after `setEncoding("utf8")`, or remove the `close`
  listener (the promise stays pending); an `error` emitted after that code
  removed the boundary's `error` listener ends the process. The child is
  not killed on a rejection: its `pid` is a property other code may have
  replaced.
- **Audited against Node 25.2.1's `lib/child_process.js` and
  `lib/internal/child_process.js`:** where no other code holds the child,
  it resolves once the child closes, with the exit code and the signal Node
  passes to `close` and the output decoded as UTF-8, a character split
  across chunks kept whole, and rejects where the child cannot start (a
  missing command, ENOENT; no file descriptors left, EMFILE, where `stdout`
  is absent). `tests/node-runs.mts` runs each case above under Node, each
  in a process of its own whose diagnostics-channel subscriber does what
  other code may, and reports a promise still pending after three seconds
  (2026-10-29).
- **What depends on it:** the worker loop of `unchecked.mts`.
- **Commit:** the introducing commit, `node:url and URL overlay contracts; host boundaries for URL strings and a child's output`.

### Module customization hooks

`files.mts` resolves a specifier as Node does, reads the conditions Node's
resolution enables, and loads a package's module observing every module
the load reads, each through a hook `registerHooks` of `node:module`
installs. A hook runs inside every resolution or load of the process while
it is registered, and other code may register hooks around it: one
registered earlier answers in its place (a forged URL or source, a throw),
and one registered later, by a subscriber of the `module.require` tracing
channel or by the code of a module being loaded, calls it with arguments of
its own (a URL that is no string). No contract a program could hold a hook
at states all of that, so the program holds none.

- **Boundary:** `tools/module-hooks.mts`.
  `resolveWithNode(specifier, parentHref): string | null`,
  `resolutionConditions(): string[]` and
  `loadObserved(path): { reads: ModuleRead[]; outcome: LoadOutcome }`, with
  `ModuleRead = { url: string | null; digest: string | null }` and
  `LoadOutcome = { k: "loaded"; value: unknown; exports: () => ReadonlyMap<string, unknown> | null } | { k: "threw"; thrown: unknown }`.
  The loaded outcome's `exports` operation is described under
  [a loaded module's own exports](#a-loaded-modules-own-exports).
  Each registers its hook and deregisters it before it returns. Node's
  chain of hooks is a chain of continuations built for each resolution or
  load, so a hook registered later may keep the continuation that calls
  the boundary's and call it after the boundary's function returned (after
  throwing, say): each hook is active only until its function returns,
  and afterwards passes the call to the next step and records nothing.
- **What callers get:** strings, arrays of strings, records of them, and a
  loaded module's value or what its load threw at `unknown`; never a hook,
  a context or a `require`. Callers are verified against these signatures,
  which state no effect (`blocker-node-module-hooks`).
  `files.mts#loadModule` observes each read, then throws what the load
  threw, so a load's reads are observed whether it returns or throws; the
  observed-stages check refuses another importer of the boundary, by a
  declaration or by `import(…)`.
- **Contract, what TScert relies on:** each value has its stated type:
  `resolveWithNode` answers the `url` of the resolution's result where it
  is a string and `null` where the resolution throws, its thrown value
  unread; `resolutionConditions` answers a fresh copy of the context's
  `conditions` and throws where they are no array of strings;
  `loadObserved` records, for each call of its load hook whose next step
  returns, the URL where it is a string and the SHA-256 of the result's
  `source` where it is a string (its UTF-8 encoding) or a `Uint8Array` (its
  bytes, hashed when the hook sees them; a `Buffer` may share its memory
  with other views, which may write it later), and `null` otherwise or
  where hashing throws; the reads it returns are a fresh array holding the
  calls made before it returned.
- **Not promised:** that a URL, a condition or a digest is Node's own. A
  hook registered earlier may answer for Node, and one registered later
  may call the boundary's load hook with values of its own; their reads
  are recorded as they come. Loading runs the module's code and every
  hook other code registered, and those may register hooks that outlive
  the call.
- **Audited against Node 25.2.1's
  `lib/internal/modules/customization_hooks.js`:** `registerHooks` pushes
  a frozen `ModuleHooks` onto the process's lists, and `deregister` splices
  it out by its own symbol, both through primordials; the most recently
  registered hook runs first, so each boundary hook is the first at its
  call; a resolve step's result is validated into a fresh null-prototype
  object whose `url` is a string; a load step's result is the hook's own
  object, whose `source` is read once more. `tests/node-runs.mts` runs a
  resolution, the conditions under `--conditions`, a load that throws, a
  load whose module registers a hook calling the boundary's with the URL
  `42`, which an earlier hook answers, a resolution an earlier hook
  forges or throws from, and a load whose module registers a hook that
  keeps its continuation and throws, the continuation called after
  `loadObserved` returned (2026-10-29).
- **What depends on it:** `files.mts#resolveObserved` (through
  `nodeResolve`), `files.mts#runtimeConditions` and
  `files.mts#loadModule`, which family activation uses.
- **Commit:** the introducing commit, `Module customization hooks behind a host boundary; node:os and isBuiltin entries`.

### A loaded module's own exports

The [module customization hooks](#module-customization-hooks) boundary also
holds the operation that copies a loaded module's own enumerable exports.
The object and null tests over `unknown` admit host objects; the model's
copy is stuck on those objects ([host operations](HOST-FAMILIES.md#operations-and-their-obligations)).
Shape tests cannot establish the copy's domain, and the module's exports
may include accessors or a Proxy.

- **Boundary:** `tools/module-hooks.mts#loadObserved` supplies a loaded
  outcome's `exports` function. That function captures only the value
  returned by the module load. `tools/files.mts#loadModule` calls it after
  observing the load's reads, and returns `ReadonlyMap<string, unknown> | null`.
  `family-activation.mts#checkedGuards` holds that map.
- **Contract:** each invocation returns null for null or a value whose
  `typeof` is not `"object"`. Otherwise it evaluates `{ ...value }`, then
  `Object.entries` of that copy, then constructs a fresh `Map` of those
  entries. Own enumerable string keys and their saved values reach the
  map, in entry order; inherited and non-enumerable properties do not.
  Enumerable symbol getters run during the copy, and their values do not
  enter the map. A getter or Proxy trap can mutate shared state, load
  modules, throw any JavaScript value, or fail to return. The signature
  states no preservation effect. Each thrown value propagates unchanged.
- **Behaviour:** the property copy runs after the load hook is deregistered
  and the load's reads are observed, at the same point where activation
  requests the exports. The same spread, `Object.entries` and `Map`
  construction preserve getter order, saved values and value identities.
  Module loads that accessors trigger have the same observation scope as
  accessors in activation's copy. The result map is fresh on each call.
- **Trust:** the boundary's implementation has the stated contract under
  the policy that standard objects and prototypes are not tampered with.
  The contract assumes no shape, data-property guarantee or lack of effects
  for the loaded value. It is an external contract, outside the calculus
  proof. `tests/node-runs.mts` checks the operation under Node, including
  getter effects, symbol getters and a thrown value.
- **Scope:** `blocker-gap-round-unknown-spread` checks the caller's map
  result. `blocker-gap-round-unknown-spread-unchecked` retains the direct
  spread's refusal. General copying of host objects requires semantics for
  their own-property operations and effects.
- **Commit:** the introducing commit.

## Changes for a tool's defect

### A primitive member read's saved witness

`tools/declaration-graph.mts#useProject` tests an optional project's
`configFileName` and `compilerOptions.strict` before calling `check(project)`.
The lowering dispatches on the saved witness of a nested primitive member
read through the existing [path witnesses](HOST-FAMILIES.md#entries).
The branch maps the refined witness and its read links to the next entry.
Reading the primitive field again would refine a different slot while that
entry requires the saved witness's type and link.
A single primitive field of the root is tested through its receiver,
retaining the root's discriminant refinement and its field facts.
An entry whose claims state no refinement of the path's prefix, as in
`tools/fragment-classes.mts#ownClass` after `cls !== gate.selfClass?.name`,
states `unknown` for the witness; the edge covers it by the subtype of the
tested type, the
[tested-slot obligation](PROGRAM-TYPING.md#refinement-under-an-observed-outcome)'s
Boolean case (`nested-witness-optional-receiver`).

`blocker-prep-project-after-check` exercises the compiler project guard.
`invalid-project-after-check-write` checks that a call invalidates a mutable
nested primitive field's narrowing; under Node a callback setting `strict`
to `false` makes the fixture return `false` despite its `true` result
annotation. The forged claims and evidence of `path-witness-controls`
require a primitive field narrowing before its test and after a call;
the existing incoming-edge checks refuse them. This lowering uses the
existing checks and soundness theorems and adds no external assumption.

### A module arrow's result and rest in callback overload selection

`named` in `tools/compiler-channel.mts` is a module constant holding a
one-parameter arrow that deduplicates two paths through a `Set` and
returns `string[]`. Its closure claim includes the signature extended by a
rest of `unknown` at the footprint `{ value: "any", store: "keep" }`, and
`[launcher, directory].flatMap(named)` passes it where `flatMap`'s
callback parameter expects a `sparse readonly string[]` result at each
closed footprint ([prototype contracts](SOURCE-CONTRACTS.md#prototype-contracts)).
The producer's signature plausibility query compares the receiver and
leading parameters contravariantly, extra target parameters against the
source's variadic rest element, and the result covariantly, matching
[function and class coverage](POSITIVE-TYPES.md#function-and-class-coverage),
so call overload selection picks the `flatMap` signature at
`{ value: "any", store: "keep" }`. Lean checks the selected invocation and
the closure's advertised signatures through the existing certificates.
`blocker-prep-flat-map-module-function` exercises the deduplicating module
arrow in `flatMap`, and `invalid-flat-map-module-function` requires a
field written by the arrow to lose its narrowing across `flatMap`.

### Stable compiler children across array bindings

The array binding schedule retains refinements through stable member paths
when reading a position or collecting an array rest. This uses the same
[stable-member mechanism](HOST-FAMILIES.md#stable-members) as ordinary calls:
each member along the path must be stable in every arm of its receiver.
Other field refinements are forgotten. The existing Lean checks validate
the proposed read claims and the read links across the binding operations.

`baseDeclarations` in `tools/declaration-graph.mts#collectDeclarations`
resolves a base identifier, destructures the resulting declarations, then
reads the identifier child's `text` in an error.
`blocker-round-host-member-after-call` exercises that form and child reads
after array and tuple rest. The source uses the compiler API's existing
stable field contract; this producer repair adds no external assumption.

### A named object in a logical operator's result

`tools/shadow-contracts.mts#print` prints a nullable receiver with
`term.receiver && print(term.receiver)` and interpolates the returned
string. The producer uses `truthy_refine` to compute the left operand's
possible result through its named declaration: every object is truthy,
so only `null` from that operand can be a result of `&&` here. A named
union that admits `false` retains that possible result.

This extends the producer's use of its existing declaration-aware
truthiness query to [logical operators](SOURCE-ELABORATION.md#logical-operators).
The existing extraction and certificate checks establish the proposed
expression types. `blocker-gap-round-receiver-template` exercises the
interpolation, and `invalid-gap-round-receiver-template` requires a string
where the logical operator can return `false`.

### A host-node union in a logical operator's result

`tools/computed-types.mts#unionMembers` reads a declaration's parameter
member with `d && params.get(d)`, then finds the first defined result.
The compiler API's `Node` declaration expands to a union of object types.
The producer's declaration-aware truthiness query traverses each union
arm and excludes the declaration from the falsy result only when every
arm is truthy. An intersection's settled operand establishes its
truthiness; conflicting answers remain undecided.
The resulting `Member | undefined` retains the `node`,
`read` and `params` fields required by the recursive call.

This uses the existing [logical-operator checks](SOURCE-ELABORATION.md#logical-operators).
Lean checks the proposed expression claims through the same certificates.
`blocker-round-imported-find-shape` exercises the importing module's
`map`/`get`/`find` chain; `invalid-round-imported-find-shape` retains `false`
in a union with host nodes and returns `false` under Node. The producer
repair takes no external assumption.

### A recursive callback offered narrower parameters

The parent walk `topStatement` in `tools/fragment-parse.mts#lowerFile`
accepts `Node` and is passed to `map` over compiler identifiers. The
callback's longer signature keeps `Node` at its first position and adds
the index and array arguments that the code discards. Its recursive self
entry carries the same signatures. This uses the existing
[closure claims](SOURCE-CLAIMS.md) and checks each signature through the
same body graph; the call checks that the callback admits its arguments.
Keeping the declared leading parameters gives the body the same compiler
node views at each signature. The case `blocker-gap-round-parent-walk`
exercises the recursive walk, and `invalid-gap-round-parent-walk` requires
its written result. Forged leading parameters and results are refused by
evidence production and consumption. This is a producer proposal through
the existing checks and takes no external assumption.

### A callback's signatures and their body claims

An annotated callback passed to `some` on a union of compiler node arrays
has its own signature and a contextual signature taking the additional
arguments `some` passes. The producer states body claims at each signature
([closure claims](SOURCE-CLAIMS.md)). Its call inference retains that claim
when it has per-signature body claims, contains no generic binders, offers
the required arity and meets the callback parameter, keeping each signature
with its body claims. Lean checks every advertised signature and its body.
`blocker-census-annotated-node-union` exercises this support through the
existing closure mechanism; `invalid-census-annotated-node-union` requires
the callback's body to meet its written result type.

### The compiler API's empty-tuple panic

TypeScript 7.0.2's API panics writing a union that holds an empty array
literal's tuple type, a [tool failure](OBLIGATION-DIAGNOSTICS.md#tool-failures)
([the package at run time](COMPILER-API.md#the-package-at-run-time)).
`forInEntryReads` destructured
`ts.isVariableStatement(s) ? s.declarationList.declarations : []`, so every
check including it ended in that tool failure.

- **Change:** read the first declaration by index, forming no empty tuple.
- **Commit:** f704fdb (`tools/fragment-support.mts`).

### A recursive declaration visitor's store contract

The `reads` visitor in `tools/fragment-statements.mts#declarationsOf`
checks an initializer for a reference to the declaration being bound.
Its result states a normal-return `Within` footprint allowing array growth
and preserving existing array positions. The recursive self call and the
compiler API's `forEachChild` use that signature; the existing closure and
call checks establish its body and each call against the footprint.
The surrounding `map` can therefore produce dense `BindingAst[]` storage.

This uses the existing [inferred call effects](SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification)
mechanism with a written recursive signature.
`blocker-compiler-api-declaration-bindings-map` exercises a recursive visitor
that calls a captured preserving callback while mapping compiler nodes to
numbers. `invalid-compiler-api-declaration-bindings-map` gives the recursive
visitor the same annotation while popping the mapped array: two identifiers
produce a result with a hole under Node. The closure body must establish the
written footprint. The annotation changes no runtime return, exception or
effect and adds no external assumption.

### Native probe files at their callback boundary

`tools/type-probe.mts#ProbeProgram` receives `Map<string, string>` from
`makeProbe` and `tools/declaration-graph.mts#compatibilityReviewed`, each
constructed with `new Map`. Its implementations in `withOwnProject` and
`tools/declaration-session.mts#collect` retain that native contract when
iterating the replacements and spreading their keys.

- **Repair:** the parameter retains the native map its callers supply. The
  [native collection contract](SOURCE-CONTRACTS.md#library-globals) gives
  `keys()` its native iterator, checked by array spread.
- **Behaviour:** the annotation is erased. Map identities, lookups,
  iteration order, callbacks, writes, returns and exceptions agree.
- **Avoided form and cost:** a structural `ReadonlyMap` admits arbitrary
  user-written iterators. Checking their protocol effects is unnecessary
  for these constructed maps.
- **Scope:** `blocker-round-probe-file-keys` retains this map boundary.
  This repair adds no rule or external assumption.
- **Commit:** the introducing commit.

### Compiler identity as JSON data

`tools/compiler-channel.mts#identify` constructs a plain compiler identity
record or an explanation string under `unobserved`. Its result combines
that field union with `JsonObject`, retaining the bound on every own string
key that [JSON serialization](SOURCE-CONTRACTS.md#json-and-error) requires.
The constructor uses the existing
[contextual object hints](SOURCE-ELABORATION.md#producing-evidence-from-supplied-claims),
which retain each field and index contract through the intersection.

`current` keeps that full result as `data` for serialization and reads its
fields through an `Identification` view. Both bindings hold the same object;
`identify` executes once, and the serializer receives that original object.
The additional local binding changes no return, exception or heap effect.
This is a repair of an internal data boundary and an explicit record view
for optional-field reads; it adds no external assumption.

`blocker-round-compiler-identity-json` exercises the data boundary through
a generic field union. The overlapping-field, multiple-index and extra-hook
negative cases require all construction constraints. Under Node their
values violate the promised Boolean field or index, or a `toJSON` hook
returns `undefined` where serialization promises a string.

### The brand predicate's normal-return footprint

`tools/compiler-api.mts#hostBrands` and its function and constructor helpers
use `BrandPredicate`: a Boolean callback within
`{ value: "any", store: "grow" }` on normal return. The recursive results
and local `go` closures state the same footprint. The existing
[effect certification](SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification)
checks their bodies before calls consume that guarantee; the native map
contract preserves the readable argument arrays.

The declaration reader's `brandKey` formats string fields and a numeric
span with `join`, and `isBrand` uses the native `Set.has` contract.
Their written footprints and `DeclarationElaborationContext.isBrand` retain
this guarantee at each call to the traversal. The predicate type has one
owner in `compiler-api.mts`. These annotations add no runtime operation,
return, exception or heap effect and take no external assumption.

The failure callback returns `never` and carries its ordinary contract.
It has no normal exit. The traversal's footprint states no guarantee for
an exceptional exit, including one on which that callback mutates a heap
before throwing. Brand directions follow the compiler API's
[declaration reading rules](COMPILER-API.md#reading-rules).

`blocker-round-host-brand-footprint` exercises a known predicate retained
through the shared type and a context. `invalid-round-host-brand-footprint`
shows that storing an unrestricted callback at that type remains an
obligation: a callback popping the outer arguments during recursion leaves
a result hole and causes `TypeError` under Node.

### A record classifier's checked preservation contract

`tools/named-record.mts#NamedRecords` gives classification a normal-return
preservation [footprint](FOOTPRINTS.md). Its definition lookup has a
separate growth footprint, allowing definitions to be settled and cached.
`aliasMeaning` retains its tested expression across classification under
that checked contract.

- **Repair:** `definitionKey` states its checked preservation footprint.
  `Gate.namedRecords` supplies native set membership with that key, and
  `settleDeclarations` retains the native `Set` constructed by its caller.
  The callback passed through `settleDocument` keeps the same preservation
  contract. Each source body has the ordinary qualification check.
- **Behaviour:** these annotations are erased. The classifiers perform the
  same key construction and set lookup; identities, iteration, callbacks,
  returns, exceptions and mutations agree for their native-set callers.
  Preservation applies on normal return.
- **Scope:** a callback with a growth footprint can replace a definition's
  nullable expression. `blocker-prep-alias-expression-after-call` throws a
  `TypeError` under Node for such a callback. The preserving example and the
  false-preservation negative exercise the narrower classification contract.
  Definition lookup retains its growth guarantee.
- **Commit:** the introducing commit.

### A global declaration matcher's array-store footprint

`tools/library-globals.mts#globalEntry` searches the reviewed overlay with
`find`. Its `GlobalSignatureMatcher` takes a signature string and returns a
Boolean within `{ value: "any"; store: "keep" }` on normal return. The lookup
retains the same normal-return footprint. The five providers in
`tools/declaration-graph.mts` compare the argument to a captured declaration
string with strict equality; their bodies establish the matcher contract.

- **Repair:** the matcher contract retains the array-store guarantee of the
  supplied primitive comparisons at the helper's parameter and an owned
  lookup context. The existing callback definition checks certify each
  supplied function before its effect is consumed
  ([certification](SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification)).
- **Find:** the [prototype contract](SOURCE-CONTRACTS.md#prototype-contracts)
  requires `store: "keep"` to pass an element without adding `undefined`.
  The matcher leaves value changes unrestricted.
- **Exceptions:** the guarantee concerns normal return. A throwing matcher
  may change the heap before it throws; the lookup propagates that exception.
- **Behaviour:** the annotations are erased. The same array, field reads,
  strict comparisons, callback arguments, short-circuit order and origin
  default select the same first entry or `undefined`. The callback precondition
  is checked at the source's supplied definitions.
- **Scope:** `blocker-round-global-signature-matcher` checks a known matcher
  retained through an owned context. `invalid-round-global-signature-matcher`
  writes a false preservation promise whose body pops that context's searched
  array; Node throws `TypeError` at the next visit's `global` read. The generic
  find mutation and ordinary-field-effect cases retain their own refusals.

### A mapped identity's null-free array observation

`tools/type-term.mts#expandIdentity` tests whether all mapped field types
are non-null. Its local `settled` function returns a Boolean. Both callers
retain each indexed fallback, `values[i] ?? f.type`, when constructing the
field type. The test observes current contents while
the array keeps its nullable element storage contract.

- **Repair:** the result annotation states the Boolean observation the
  callers consume. A type predicate promising `TypeTerm[]` would require a
  narrower invariant array storage contract; testing present elements does
  not establish that contract
  ([storage contracts](FOOTPRINTS.md#the-fact)).
- **Behaviour:** the annotation is erased. The same `every` calls, null
  comparisons, short-circuit decisions, indexed fallbacks and returned
  records execute in the same order.
- **Scope:** `blocker-next-array-store-promise` exercises the Boolean
  observation. `invalid-next-array-store-promise` retains the unsafe
  mutable-array promise: a nullable alias appends `null` after the test,
  and the narrowed alias calls `toUpperCase` on it. Node throws `TypeError`.
  The [elements fact](FOOTPRINTS.md#the-elements-fact) describes heap
  knowledge subject to preservation; it does not replace a location's
  invariant storage contract.

### The compiler identification failure's absent identity

`tools/compiler-channel.mts#identify` returns a fresh failure object
containing only `unobserved` when the installation is missing, confinement
is unavailable, or an installation digest is missing. Its private
`Identification` failure alternative states `identity?: never`. The
success alternative carries the identity record.

- **Repair:** the result annotation retains the absent identity established
  by all three failure constructors. `current` keeps that fact when it
  builds the failure alternative of `CompilerImplementation`; the existing
  [object-allocation checks](PROGRAM-TYPING.md#objects-and-records) check
  each producer and the returned `Current` record.
- **Scope:** `Identification` is private to the module. Its values come
  from `identify`, called by `current` for its captured identity and again
  by the `changed` callback. The annotation describes these constructors.
  `CompilerImplementation` retains its complete existing contract.
- **Behaviour:** the annotation is erased. The same installation checks,
  digest reads, sandbox profile, failure strings, identities and comparison
  callbacks execute; object keys and serialized JSON agree.
- **Example:** `blocker-next-current-identification` carries the absent key
  through the conditional implementation record.

### A readonly compiler-node list view for accessor filtering

`tools/written-applications.mts#pairOf` reads an object literal's properties
through a `readonly Node[]` local before filtering for matching accessors.
The [compiler node-list contract](COMPILER-API.md#node-lists) supplies the
readonly element view; the existing accessor guards refine each callback
argument before its accessor-specific members are read.

- **Avoidance:** the local annotation gives the callback the general node
  domain admitted by the compiler model. The more specific contextual
  object-element domain requires a callable relation the model does not
  establish for that invocation. Readonly covariance supports the local
  view without changing the element contract of writable storage.
- **Behaviour:** the local holds the same list read at the same point.
  The same filter method, receiver, callback, guards and property reads
  execute in the same order. The binding allocates no array.
- **Example:** `blocker-next-compiler-api-callback-view` exercises the
  readonly view and the accessor-name comparison.

### Module constants read at their annotations beside an omitted step

`tools/fragment-parse.mts` keeps the compiler's overlay texts and open files
in `contents` and `opened`, `tools/unchecked.mts` its comment patterns in
`SUPPRESSION` and `REASON`, and `tools/client-prototype.mts` the answers it
records in `answers`. Each file holds a top-level statement a census omits
as a step of unknown effect: a command's main block (`if` at the top level,
outside the fragment) in the first two, a `WeakSet` no reviewed entry
admits in the third. After it, a module constant that is neither a
function nor a primitive literal is read at its annotation, and without one
is no value ([units](DESIGN.md#function-coverage-and-release-thresholds)).
The five had none ("unbound name contents", `opened`, `SUPPRESSION`,
`REASON`, `answers`).

- **Repair:** `contents: Map<string, string>`, `opened: Set<string>`,
  `SUPPRESSION: RegExp`, `REASON: RegExp` and
  `answers: WeakMap<object, Map<unknown, Map<string, string>>>`, the types of
  the values their initializers build. Read at `RegExp`, a match's group is
  `string | undefined` at each read, so `reasonAt` keeps the group it tests
  (`REASON.exec(…)?.[1]`) and returns that value rather than reading the
  match again.
- **Behaviour:** the annotations are erased; the same maps, sets and
  patterns are built and read. `reasonAt` returns the same group of the
  same match.
- **Scope:** `projectFor`, `openText`, `openFile` and `release` of
  `fragment-parse.mts`; `reasonAt` and `findIn` of `unchecked.mts`;
  `heldSnapshots` and `query` of `client-prototype.mts`.
