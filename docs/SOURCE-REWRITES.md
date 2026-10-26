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
   construct stays refused, with a control case ([constructs
   avoided](#constructs-avoided)).
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
8. **The refusal stays,** and the census reports it, where no route above
   establishes the obligation at acceptable cost. Coverage pressure is
   evidence of value, not permission to weaken safety.

What TScert verifies of its own front end is its source as it stands: code
checked, host boundaries and their contracts, trusted units and refused
functions are reported apart, and a result under a host contract is no proof
of the host's implementation.

## Rewrites

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
refused on principle (`optional-write-refused`).

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
  its value against `undefined`. A promise also carries its JSON object
  contract, so its optional fields cannot introduce non-JSON values.
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

### A readonly JSON check promising writable fields

`isClosedFootprint` and `isCallEffect` (`tools/type-graph.mts`) inspect a
readonly JSON value and promise `ClosedFootprint` and `CallEffect`.
Writable fields in those types claim an invariant storage contract that
checking the current contents does not establish. The same obligation
applies to the nested promise and its parameter.

- **Rewrite:** `ClosedFootprint`, `CallEffect`, and the fields and children
  of `CallPromise` are readonly. Their consumers read the checked views;
  a control forging an effect constructs its replacement as a fresh object.
- **Pattern:** a guard that checks contents promises a readonly view.
  A different writable contract requires fresh storage.
- **Functions:** `isClosedFootprint`, `isCallEffect`, and the two effect
  edits in the filter-guard forged-evidence control.
- **Commit:** the introducing commit, `State the contracts used by the front end's negative patterns`.

### A callback inheriting `any` from object entries

`sameData` (`tools/type-term.mts`) filters `Object.entries(o)` with an
unannotated destructuring callback. The standard library's object overload
supplies `[string, any]`, so the callback's value has no stated contract.
`mergeRefusal` (`tools/array-prototype.mts`) uses the same overload in its
local canonical representation, through both `filter` and `map`.

- **Rewrite:** each callback declares its entry `[string, unknown]`.
  Equality and the recursive reader already accept `unknown`.
- **Pattern:** a callback receiving untyped external data states the
  weakest contract its body needs, checking values before using them.
- **Functions:** `sameData` and `mergeRefusal` (its local `canonical`).
- **Commit:** the introducing commit, `State the contracts used by the front end's negative patterns`.

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

## Constructs avoided

Constructs TScert's code once used, refused because sound support is not
proportionate to their use, and written out of the code by an equivalent
form ([deciding](#deciding-what-a-refusal-of-tscerts-code-calls-for)).

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
- **What callers get:** neither the client, its prototype, a method nor a
  way to answer a request. The channel's `around` (the ledger, the failure
  conversion) is verified against these signatures (`blocker-client-prototype`).
- **Contract, audited against the package** (`dist/api/sync/client.js`,
  `api.js`): the request methods are own data properties of `Client`'s
  prototype; the package catches no error of a request; `apiRequest` returns
  a fresh `JSON.parse` of the reply, or `undefined` for an empty one. Every
  client of the process shares the prototype, so the first call wraps every
  client's requests. A query of a held snapshot asked again is answered by
  reading back the earlier answer's JSON text, which assumes the compiler
  answers it the same each time (query omission, a conjecture).
- **What depends on it:** the functions of `compiler-channel.mts` that check
  or guard the client, and every use of the compiler API in the process:
  every client shares the wrapped prototype, so each answer the package
  returns passes through the wrapper.
- **Commit:** the introducing commit, `Confine Object.getPrototypeOf to a
  host boundary of the compiler channel`.

## Changes for a tool's defect

### The compiler API's empty-tuple panic

TypeScript 7.0.2's API panics writing a union that holds an empty array
literal's tuple type, a tool failure
([the pipeline entry point](DESIGN.md#the-pipeline-entry-point)).
`forInEntryReads` destructured
`ts.isVariableStatement(s) ? s.declarationList.declarations : []`, so every
slice including it ended in that tool failure.

- **Change:** read the first declaration by index, forming no empty tuple.
- **Commit:** f704fdb (`tools/fragment-support.mts`).
