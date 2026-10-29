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

`mergeRefusal` (`tools/array-prototype.mts`) reads `Object.entries(o)` in
its local canonical representation, through `filter` and `map` with
unannotated destructuring callbacks. The standard library's object
overload supplies `[string, any]`, so the callback's value has no stated
contract.

- **Rewrite:** each callback declares its entry `[string, unknown]`.
  The recursive reader already accepts `unknown`.
- **Pattern:** a callback receiving untyped external data states the
  weakest contract its body needs, checking values before using them.
- **Functions:** `mergeRefusal` (its local `canonical`).
- **Commit:** the introducing commit, `State the contracts used by the front end's negative patterns`.

### A promise executor inheriting `any` from its context

The top level of `tools/unchecked.mts` collects each worker's result
through `new Promise<{ files: string[]; found: Found[] }>((done, fail) =>
…)`. TypeScript types the unannotated executor parameters from
`PromiseConstructor`: `done` as `(value: T | PromiseLike<T>) => void` and
`fail` as `(reason?: any) => void`, so `fail` has no stated contract and
its slices (`check`, `findIn`, `decodeResult` in the census of b81675f) are
refused with the reason `blocker-contextual-any` shows.

- **Rewrite:** the executor states its parameters,
  `done: (result: { files: string[]; found: Found[] }) => void` and
  `fail: (reason: unknown) => void`, as `library-new-promise` does. The
  promise's resolving functions accept every argument these types admit,
  so the executor's calls and the promise's settlement are unchanged.
- **Pattern:** a callback whose context types a parameter `any` states the
  weakest contract its body uses.
- **Functions:** the module's top level, read by the slices of `check`,
  `findIn` and `decodeResult`.
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
  `childOf` and `childrenOf` (`tools/syntax.mts`) read nine other child
  fields of any node, which up to 43 kinds carry, and keep `Reflect.get`
  and its refusal.
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
  `stringOfJson` (`tools/family-activation.mts`) converts a member as
  `String` does, by its arms: a primitive by `String`; an array by joining
  its elements' conversions with commas, an element `null` as the empty
  string; an object as `"[object Object]"`, or a `TypeError` with Node's
  message where the object owns `toString`, which JSON data never makes
  callable. Each reader throws where the original threw: `JSON.parse`'s `SyntaxError` of a text that is no
  JSON, in `digestOf`, `checkInventory`, `checkedGuards` and `originOf`;
  `manifestField` catches it and answers undefined, as the original did;
  `decodeResult` answers null where `isResult` answered false. One
  behaviour differs: the conversion of nested arrays recurses on the call
  stack, so the depth at which it exhausts the stack, a `RangeError`,
  differs from Node's own `Array.prototype.join`, as any change of the
  frames would.

  `decodeResult`'s objects hold only the fields its callers read, where the
  original passed on the parsed object with any further members.
- **Pattern:** a value `JSON.parse` returns keeps its JSON type from the
  parse onward, and is read through a decoder of its format.
- **Functions:** `digestOf`, `checkInventory`, `checkedGuards`, `originOf`,
  `manifestField`, `relativeImportTargets`, `isResult`
  (rewritten as `decodeResult`), and their callers; `json-parse-manifest` is the pattern
  as a case.
- **Commit:** the introducing commit, `Parsed manifests and worker results keep their JSON type`.

### A scope's hook read as an optional method

`TermScope` (`tools/type-term.mts`) declared its hooks `record`,
`computed`, `awaited`, `keys`, `modifiers` and `enumerated` as optional
methods, and the readers that pass one on or implement it apart from a
scope typed it by indexed access, `TermScope["record"]` or
`NonNullable<TermScope["computed"]>`. An optional method's function takes
the object it is a member of as its receiver, which the indexed access does
not name, so the type reader refused the type; `typeTerm` passed
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
  (`tools/named-record.mts`); `blocker-indexed-optional-method` and
  `blocker-optional-method-bind` are the refused forms as gap cases.
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
  calling it.
- **Commit:** the introducing commit, `Fields atomText's guards test are read before its callbacks run`.

### A wire document's strings checked at `unknown`

`illFormedString` of `tools/wire-strings.mts`, which finds a string of a
wire document that is not well-formed Unicode, took the document at
`unknown` and read `value.pos` after `"pos" in value` on an open object
("field read on non-object"; the diagnostic census of 5dfb065 reports it in
`illFormedString`, `requireWellFormed` and `wellFormedRefusal`). Its readers
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
- **Commit:** the introducing commit, `Map and Set refusals: the diagnostic
  traversal keeps their bindings, three sites rewritten`.

### A type alias recognised by a guard accepting a JSDoc `@typedef`

The front end recognised a type alias declaration with the compiler's
`ts.isTypeAliasDeclaration(node)` and then read its members
(`node.typeParameters`, `node.name`). The guard also accepts a JavaScript
file's `@typedef` (`JSTypeAliasDeclaration`), and is read by what its code
accepts ([guard recognition](HOST-FAMILIES.md#guard-recognition)), so its
true edge holds both kinds: it reads the members both shapes state
([audited shapes](COMPILER-API.md#audited-shapes)) and gives no
`TypeAliasDeclaration` (the diagnostic census of b81675f reports the
guard's reads in 33 functions, among them `typeTerm`'s callers in
`tools/type-term.mts`, `computedType`, `makeProbe` and `lowerFile`). The
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
through `Object.values`; the diagnostic census of b81675f reports these
refusals in 24 functions, `lowerFile` among them. The value's type had
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
  `blocker-in-unknown-walk` the refused walk. Three sites reading an
  object the compiler provides (`privateClient` of
  `tools/compiler-channel.mts`, `isNode` of `tools/syntax.mts`, `copied` of
  `tools/diagnostic-gate.mts`) have no grammar of TScert's to walk and keep
  their refusal.
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
the generic overload, meets no dictionary. The diagnostic census of
b81675f reports the gate's refusal of the two overloads together
(`blocker-entries-mixed-overloads`) in 23 functions of
`tools/type-term.mts`, each reaching `sameIndex` through `readTypeTerm`.

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

- **Rewrite:** `refusal`, `declarationError` and `ioFailure` register each
  error in a module-private `WeakMap<object, Payload>`. `refusalOf`,
  `declarationSpanOf` and `ioFailureOf` first test for a non-null object,
  then return its registered payload or `undefined`. Lookup preserves the
  entry, so the same error can be handled repeatedly. The tables do not
  keep an otherwise unreachable error alive; collection timing is unspecified.
- **Observable contract:** a gate refusal is an `Error` with the supplied
  message; its registered payload holds the supplied span and message.
  A declaration refusal is an `Error` with the supplied message and optional
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
- **Functions:** `lowerFile`, `diagnosticFragment`, `recoverGate`,
  `collectDeclarations`, `orAbsent` and `io` use these payloads.
  `tests/caught-errors.mts` exercises the real gate and I/O helpers, repeated
  handling and caller attribution; `tests/trusted-inputs.mts` checks repeated
  lookup of a declaration refusal from the actual declaration collector.
- **Pattern:** what a thrown value carries is found by its identity in a
  table its maker fills, rather than read off the caught value.
- **Commit:** the introducing commit, `Caught errors' fields are found in their maker's weak table; WeakMap gets a contract`.

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
admits. The diagnostic census of 6be11ce reports the refusal in 4
functions, 489 statements: `collect` (387), `recordShape`, `settleDocument`
and `settleTerm`. Supporting a replacer would take the serialization of
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
- **Pattern:** a key of data the caller has typed is written from that
  type, field by field.
- **Functions:** `termText` and its helpers, `recordShape`'s `inherit`,
  `instanceOf` and `collect`'s member readings
  (`tools/declaration-graph.mts`), and `collectDeclarations`'s check of
  stated arguments; `typed-tree-text` is the pattern as a case, and
  `invalid-json-stringify-replacer` the refused call.
- **Commit:** the introducing commit, `A type term's text is written kind by kind from its type`.

### A result declared before the block that allocates it

`readDiagnostic` (`tools/diagnostic.mts`) declared `let result` before its
`try`, assigned it `{ ...d }` inside, wrote the decoded parts at keys the
copy may lack (`result.source = …`), and returned it after the `try`. A
write adding a key is typed only on a local's own fresh object, whose
holders are the binding that allocated it and the constants bound to it
since ([key-adding writes](PROGRAM-TYPING.md#key-adding-writes)); an
assignment allocates for no holder, so the five writes are refused (the
diagnostic census of 6be11ce, 107 statements of `readDiagnostic`). The
result is used only inside the `try`, whose `catch` returns `undefined`.

- **Rewrite:** `const result = { ...d }` is declared where it is allocated,
  in the `try`, and returned at the `try`'s end.
- **Pattern:** a local is declared at its allocation, in the block that uses
  it.
- **Functions:** `readDiagnostic`.
- **Commit:** the introducing commit.

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
- **Commit:** the introducing commit.

## Constructs avoided

Constructs TScert's code once used, refused because sound support is not
proportionate to their use, and written out of the code by an equivalent
form ([deciding](#deciding-what-a-refusal-of-tscerts-code-calls-for)).

### An array pattern over a `Set`

`parameterIndex` in `makeProbe` (`tools/type-probe.mts`) collected each
declaration's type parameter position into a `Set` and read its first
element with `const [index] = indexes`. An array pattern over a host
iterable other than an array is refused at its element read
(`diagnostic-set-pattern`); support would step the host's iterator in a
pattern's lowering, for this one site of the census of b81675f.

- **Equivalent form:** the loop keeps the first position and whether every
  later one equals it, and returns that position where they all do and it
  is not negative, as the `Set` of one element did. The loop runs the same
  calls in the same order; positions are integers, which `Set` compares as
  `!==` does.
- **Commit:** the introducing commit, `Map and Set refusals: the diagnostic
  traversal keeps their bindings, three sites rewritten`.

### A `for...of` over a `Map` or an empty array

`collect` in `tools/declaration-graph.mts` iterated
`context.guardPromises.get(marker) ?? []`, a `Map` or an array: the
iteration intrinsic is picked by one host kind, so a union of two kinds has
none (`for-of-map-or-array-refused`), for this one site of the census of
b81675f.

- **Equivalent form:** the loop runs over the `Map` where `get` finds one,
  and is skipped otherwise; the array's loop runs no step, and the standard
  array iterator runs no code ([host assumption](DESIGN.md#trust-surface)).
  The condition and the `get` are evaluated as before.
- **Commit:** the introducing commit, `Map and Set refusals: the diagnostic
  traversal keeps their bindings, three sites rewritten`.

### A method call on the instance under construction

The `Gate` constructor (`tools/fragment-parse.mts`) assigned its field
`scope` from `this.termScope()`, a record of hooks closing over the gate.
A constructor's statement or field assignment reading `this` is refused
(`blocker-constructor-assignment-this`): the instance is allocated at the
constructor's end from one value per field
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
(`invalid-method-effect-overload`). The diagnostic census of 6be11ce
reports the refusal in 8 functions of `tools/`, 804 statements, each
importing `resolutionSlots`; it is the one overloaded function declaration
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

`requestReading` in `tools/compiler-api.mts` gave a request's signature its
effect as `{ ...effect, fresh: … }`, a spread of a local typed `CallEffect`,
whose fields are all readonly. A merge reads only operands whose type
excludes host values, and a record of readonly fields alone excludes none
([excluding host values](HOST-FAMILIES.md#excluding-host-values),
`invalid-compiler-api-node-spread`). Support would track that the local
holds a fresh literal through its annotation, for this one site, which
a8cba50 introduced into a function the census of 6be11ce verified.

- **Equivalent form:** a literal reads `effect`'s five fields in the order
  the spread copies them, with `fresh` at its place, as the spread's later
  field overwrites it. `effect` is a local literal no code writes, owning
  exactly these five data properties, so the copy holds the same values
  under the same keys in the same order, and is fresh as the spread's was.
- **Commit:** the introducing commit, `requestReading builds a request's
  effect field by field`.

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
- **What depends on it:** `files.mts#observeResolution`,
  `files.mts#resolveObserved` and `family-activation.mts`'s module URLs.
- **Commit:** the introducing commit, `node:url and URL overlay contracts; host boundaries for URL strings and a child's output`.

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
  `LoadOutcome = { k: "loaded"; value: unknown } | { k: "threw"; thrown: unknown }`.
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
