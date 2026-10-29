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
this one site of the census of 6be11ce.

- **Equivalent form:** the entry's members are a writable array, and the
  found entry gets the member by `existing.members.push(m)`
  (`array-found-element-update`). Each entry is created in this loop and
  read only by `find`'s test of its name before the loop ends, so keeping
  the first entry and extending its array leaves `own` holding the same
  names, owners and members in the same order as replacing it with a copy;
  the calls of `graph.name` and `graph.fail` run as before.
- **Commit:** the introducing commit, `familyTable gathers a name's members
  without a write at a computed index`.

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
