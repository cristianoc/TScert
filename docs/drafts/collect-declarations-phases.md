# Draft: the phases of the declaration reader

## The existing mechanism this extends

This design restructures the declaration reader around its existing
[one equation per declaration](../SOURCE-CONTRACTS.md#one-equation-per-declaration).
TypeScript resolves names; `type-term.mts` reads their types;
`collect` follows dependencies; `settleDocument` expands mapped types against
the collected definitions. `DeclarationDocument` in `declaration-types.mts`
remains the result. These are the mechanisms for resolution, type reading,
dependency collection and settlement that the four phases below extend.

For TScert's own functions, the existing mechanism is
[source rewrites](../SOURCE-REWRITES.md#deciding-what-a-refusal-of-tscerts-code-calls-for):
give each function explicit inputs, results and effects, and check its slice.
[Footprints](../FOOTPRINTS.md) own facts preserved across calls;
[inferred call effects](../SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification)
own their certification. A `readonly` parameter alone does not establish
preservation through other aliases. Extracted functions use those mechanisms
for their actual effects.

Compiler assumptions belong to the
[compiler API contract](../COMPILER-API.md), an instance of
[host families](../HOST-FAMILIES.md). Library assumptions belong to the
[overlay](../SOURCE-CONTRACTS.md#the-overlay). Compiler lifetime and reuse
belong to [retained declaration sessions](../STAGE-STORE.md#retained-declaration-sessions).
The [general mechanisms](../DESIGN.md#general-mechanisms) therefore cover the
concerns here. The explicit dependency driver is an internal organization of
`collect` and its surrounding loops; it introduces no additional typing or
trust mechanism.

This is a design proposal. Its expected verification and performance gains
are conjectures to measure, rather than proved properties of the proposed
organization. The source locations below refer to `tools/declaration-graph.mts`
at the baseline commit recorded below.

## Phase boundaries and ownership

The public entry remains `collectDeclarations(file, options)` during
extraction. It acquires one compiler session and passes an initialized
context to top-level functions. Mutable state has one owner per table or
queue. Functions receive the data they read and the particular state they
write; a context holding every service and every mutable table would retain
the present coupling.

The phases describe operations, rather than four complete traversals of the
program. Resolve the initial requests, elaborate them, and let dependency
closure resolve and elaborate further requests on demand. Finish only when
that work ends. This preserves collection on use: a dependency of an unused
declaration does not become a root.

| Phase | Inputs | Owned state | Result passed onward |
| --- | --- | --- | --- |
| Resolve declarations and identities | Compiler snapshot, source requests, family selection, library policy | Resolution and identity tables, merged declaration groups (`partners`), alias declarations, brands, symbol identities, diagnostics already observed, family tables and lazy selection state | Resolved roots and uses, declaration identities and groups, ordered diagnostic observations |
| Elaborate into type terms | Resolved declaration or use, binder environment, optional-property mode, explicit owner and external-value context | Temporary term construction, parameter and library-query caches, computed-type probes | Terms and equations, dependencies with source spans, requested instances and contracts, record and statement facts, client answers |
| Dependency closure | Resolved roots, elaboration results and on-demand resolution | Existing per-start queues and shared visited keys, instance identities, guard promises, accumulated definitions and facts | Complete definitions, values, symbols, applications, provenance and validation facts |
| Validate and finalize | Complete graph and facts | Local settlement and result construction; explicit access to lazy selection reporting | `DeclarationDocument`, or the existing located refusal or tool failure |

Proposed internal data names in this draft name TypeScript interfaces, not
new wire formats:

- `DeclarationContext`: the live checker, program, client, root and effective
  optional-property mode. Its lifetime is the compiler snapshot's lifetime.
- `ResolvedDeclaration`: canonical identity, ordered merged parts, origin,
  captured parameters and the source use responsible for collection.
- `ElaborationContext`: binder names and substitutions, current definition
  identity, external-value depth and the narrowly required compiler queries.
- `ElaboratedDeclaration`: equation or existing refused result, ordered
  dependency requests, instance requests and contract requests, plus record,
  program-class and stated-effect facts.
- `CollectedDeclarations`: all document parts and the facts finalization
  consumes, with their source spans. Its construction belongs to closure.

Every boundary states ordinary parameter and return types. Extract the
existing request lists and consumers directly, retaining spans and owners.
A general request union and a general queue are deferred until a specific
invariant requires them.
Existing `Answered<T>` results keep the distinction between an answered
query and a located unsupported query; tool failures retain their causes.

The principal interfaces are `resolveDeclaration(context, resolutionState,
request): ResolvedDeclaration`, `elaborateDeclaration(context, declaration,
elaborationContext, instanceState): ElaboratedDeclaration`,
`closeDeclarations(context, resolutionState, initialRequests):
CollectedDeclarations`, and `finalizeDeclarations(collected, selectionService, observations):
DeclarationDocument`. These are proposed signatures; the narrow query inputs
of each helper replace `context` as each family is extracted. The resolution
state is initialized before closure begins. Closure creates `instanceState`
before calling elaboration. A small allocation operation reserves an instance
identity synchronously, so elaboration can return a reference immediately;
the existing instance sweep consumes the recorded body at its current point.
The allocation operation receives the instance table explicitly and owns its writes. There
is no callback into a partially initialized driver.

### Shared state and dynamic contexts

Each owner exposes narrow operations to the named readers and writers.
A selection query can resolve a family and run diagnostic checks.

| State | Owner and lifetime | Writers and dependencies | Readers and dependencies |
| --- | --- | --- | --- |
| `families` | Resolution's family service, per collection and compiler snapshot | `familyFrom` reads descriptions, resolved roots, bases, files, enums and members; runs existing checks; inserts the constructed family | `familyFrom`, `guardConstants`, `scanSelection` and `familyOf` read tables, members, enums and literals; scanning can call `familyFrom` and extend the table |
| `guardPromises` | Closure's accumulated family facts, per collection | Guard elaboration records named node-guard tag values through an explicit operation after reading the guard entry and `guardConstants`; tag guards keep their direct terms | `collect` reads promises when constructing a family's root equation; the explicit state argument preserves write/read order |
| `scanned` | Resolution's selection service, per collection | `scan` initializes it on first demand using `scanSelection(closure())`; this reads the client import closure, compiler queries, descriptions and `families`, can populate `families`, and runs existing diagnostic checks | `selected` reads it only without a supplied `familySelection` query; final `familySelected` reporting reads `scan()` even with that query supplied |
| `selectionSets` | Resolution's selection service, per collection | `familyOf` resolves the family, then stores the existing set or constructs one from `selected(marker)`, preserving first-use query or scan evaluation | `familyOf` supplies the set to collection and family type reading; later uses retain the cached selection |
| `typesRead` | One contextual type-reading invocation's recursion-path state | `readContextualTerm` adds a type ID on entry to structural reading and removes it in `finally`; recursive readers receive the same explicit path | `readContextualTerm` checks for recursion at the existing point after primitive and literal handling; sibling and later reads see the path after removal |
| `closureBinders` | Contextual parameter elaboration's explicit binder environment | The contextual-closure loop owns `closureBinderNames`, keyed by closure span; each parameter request selects its environment from that table | `contextualTerm`, `readContextualTerm` and recursive signature/member readers receive the environment explicitly for symbol and spelling checks; `renameFree` receives its spelling-to-fresh-name map |

Pass contextual binders and recursion-path state through every recursive
contextual reader and hook with the source span. Other contextual entry
points supply an empty binder environment and a fresh path. Preserve the
add/remove scope, including exceptions: the path records active structural
reads, not completed types. Other traversal-local `seen` sets, such as
`rootOf` and recursive class checks, also receive explicit arguments with
their existing lifetimes. Collection's shared visited keys have a separate
lifetime and purpose.

Selection remains lazy at its existing execution points. Finalization invokes
the selection service only inside `if (options.familySelected)`, after promise
transformations and before document construction and `deferredInDocument`.
That service may build family tables or fail before delivering the callback.
Its inputs include family and selection state, compiler queries and the
diagnostic destination. An eagerly computed observation would change this
execution order.

### Resolve declarations and identities

Extract `resolveDeclarations`, `declarationOf`, `lookup`, `identityOf`,
`aliasOf`, symbol allocation and their supporting queries. Identity retains
the existing module, name and span. Merged groups retain the class-first or
longest-parameter-list choice and the ordered parts. Symbol indices retain
first-use order. Paths through imports and reexports receive the same
clean-declaration checks as their targets.

This phase owns `partners`, `aliasNodes`, `brands`, the symbol index and the
diagnostics table. It can extend them for a newly reached dependency; a caller
receives a resolved result rather than permission to edit the tables.
`clean` reports each diagnostic once per file in its existing order. The
full-file error check used by `checkedClass` remains distinct from `clean`'s
overlap check and ambient-field exception.

Resolution supplies identities to elaboration. It does not call back into
term construction to manufacture them. Requests that need computed types
carry the unresolved computation to elaboration. This breaks the service
cycle between `valueScope`, library recognition, lookup and instances at the
point where a reference can name a dependency without collecting its body.

### Elaborate into type terms

Use the existing `typeTerm`, `computedType`, signature readers and
`TermScope` hooks. Extract one family of scope hooks at a time. Binder lookup,
merged parameters and argument completion have explicit inputs and results;
the part of a hook that discovers dependencies returns or records a request
in state owned by this operation.

In particular, `valueStarts` becomes dependency output rather than an array
unrelated closures append to. `overlayDefinitions`, `primitiveProtos`,
`regexpDefinitions` and `collectionDefinitions` become contract contributions
owned by closure. `statedDefinitions`, `externalTypes`, `programClasses` and
`records` become explicit facts attached to their owning definition or value.
The `collecting` variable becomes the current owner argument. The
`externalReads` counter becomes a nested elaboration context whose child
records the increased depth. Exceptions cannot leave a later operation with
another operation's owner or depth.

Mutually recursive term readers can remain mutually recursive top-level
functions with typed arguments. A scope adapter may expose the existing hook
types to `typeTerm`; each hook receives initialized state and states the
effect it really has. Extracting a cycle as one group is useful engineering,
but its shared census slice gives no coverage gain until that group verifies.
Prefer small independent functions around that group first.

Preserve the whole contract of each admitted declaration, including effects,
own-key bounds, array presence, heritage, parameter bounds and defaults.
An unsupported part retains its refusal. Type reading remains the
[annotation mechanism](../SOURCE-CONTRACTS.md#types-stated-by-annotations).

### Dependency closure to a fixed point

Introduce a top-level `closeDeclarations` operation around the work already
performed by `collectFrom`, `collectInstances` and the `valueStarts` loop.
The fixed point means that processing the pending requests produces no
additional request that requires collection. It concerns reachable
declarations and instances; `settleDocument` continues to own expansion of
deferred mapped types.

Extract `collect`'s per-start traversal directly: an ordered queue initialized
with the start, an indexed cursor and the existing shared `seen` set. Preserve
when each key is marked, each dependency appended, and each equation and
observation produced. The initial instance applies only at cursor zero.
Preserve definition identity keys, `termsText` instance data, instance naming
order and the budget of 256, including the responsible span on failure.
Additional queued, active or completed sets require a specific invariant and
separate justification; they are outside the first extraction.

The first extraction preserves the present scheduling: initial starts,
instances to exhaustion, each newly discovered batch of value starts followed
by instances, then the conditional array-prototype contribution and its value
dependencies. It preserves the current fallback span choices as well as
definition order. Model these as explicit driver stages before considering
one general queue. A change that processes a previously undrained kind of
work after array-prototype discovery is a separate correctness change with
its own case and review; it cannot be hidden in extraction.

The target driver sends every dependency contribution through its owner,
including ones arising while a library contract is read. A result contains
every discovered reachable equation or a located failure. Duplicate work
preserves any required per-use answer and provenance. Prototype contributions
remain demand-driven, and array-prototype rows retain their leading position.

For safety checking, the driver needs explicit queue element types, checked
indexed reads and initialized state, with each transition preserving the
storage contracts of its tables. TScert's function safety theorem does not
prove that this algorithm computes all reachable declarations or terminates.
Those are additional correctness obligations. Ordinary recursive references
are finite by visited identity; growth of computed instances retains the
existing budget refusal. No new claim of termination accompanies extraction.

### Validate and finalize

Extract final assembly with the order visible at the end of the function:
append the selected and demanded definitions; prepend `arrayProto`; run
`settleDocument`; run `externalStatements`; apply `promisedBinders` and
`promisedMethods` to the existing external positions; report family selection;
construct the document; reject `deferredInDocument`.

The inputs state which definitions are records, which are program classes,
which read a stated effect, which values are external, and which instance
identities belong to the client. Finalization reads these facts directly.
It owns its result arrays. Lazy selection reporting calls the resolution
service described above, which owns family-table writes and checks at that
point. Document assembly adds no dependencies. A missing dependency is a
collection error, with no weakening of its annotation. Checks needed to interpret a declaration safely remain
at that read; final validation does not postpone their refusals past other
observable operations.

## Split the options by responsibility

The baseline signature has 90 optional properties. Keep a temporary adapter
at `collectDeclarations` that normalizes absent request lists and exposes the
following coherent interfaces. Each property has one owner.

| Interface | Existing properties |
| --- | --- |
| `DeclarationInput` | `tsconfigPath`, `client` |
| `DeclarationPolicy` | `arrayOverlay`, `familySelection` |
| `RootRequests` | `namespaceMembers`, `locals`, `globals`, `globalValues`, `importMeta`, `ambient`, `root`, `arrays`, `intrinsics` |
| `BindingRequests` | `symbolKeys`, `privateNames`, `staticReads`, `classTests`, `hookTests`, `bindingReads` |
| `OperationRequests` | `iterables`, `spreads`, `restTargets`, `inKeys`, `receiverTargets`, `libraryNames`, `libraryValues`, `elementReads`, `lengthReads`, `openReads`, `regexps`, `dispatchCalls`, `memberReceivers` |
| `TypeRequests` | `staticTypes`, `contextualParams`, `contextualClosures`, `assignCalls`, `computed`, `blockTypes`, `keyTypes`, `mappedTypes`, `symbolNames` |
| `EnumRequests` | `enums`, `constEnumReads` |
| `BindingAnswers` | `symbolKey`, `privateName`, `staticMember`, `inheritedStatic`, `classTest`, `hookTest`, `importedClassTest`, `bindingRead` |
| `OperationAnswers` | `assertionCall`, `globalTest`, `globalIntrinsic`, `globalConstruct`, `iterable`, `restSlice`, `hostIn`, `methodTarget`, `libraryName`, `libraryValue`, `hostElement`, `byteRead`, `openRead`, `regexp`, `dispatch` |
| `TypeAnswers` | `library`, `awaited`, `resolvable`, `awaitable`, `within`, `associatedAlias`, `staticType`, `contextualParam`, `contextualBinders`, `assignTypes`, `computedType`, `blockType`, `completion`, `keyType`, `mappedType`, `symbolName` |
| `EnumAnswers` | `enumMember`, `importedEnum`, `enumMemberRead`, `constEnumRead` |
| `DeclarationObservations` | `record`, `hostGuard`, `seen`, `familySelected` |

`familySelection` is a query whose result affects collection, whereas
`familySelected` reports a result. `completion` also controls whether the
client application sweep runs: the adapter must carry that request explicitly
alongside its answer destination. These two properties cannot be treated as
interchangeable events. Likewise, optional answer callbacks retain any work
selection their presence currently controls.

The target internal results carry typed answer data and ordered observations.
The adapter delivers them to the existing `fragment-parse.mts` callbacks at
their existing execution points, including observations before a refusal.
Each phase receives only its required answer and observation destinations;
`observations` in finalization is its narrow part of `DeclarationObservations`.
First preserve synchronous delivery through small typed answer interfaces;
replace individual callbacks with data only after checking their consumers'
reads, writes, exceptions and order. Buffering every callback until success
would change behavior. The adapter is a migration boundary for callers; the
document wire keeps its single declared shape.

## Compiler compatibility and repeated queries

Put version-sensitive queries in a small internal compatibility module using
the existing compiler API contract and overlay data as its authority. Its
operations cover installed-package and library origin recognition, matching
reviewed declaration text, synthesized mapped-member flags (including the
two `checkFlags & 8` reads), and reading an appended reviewed interface from
a probe snapshot. Return typed answers or the existing failure. Each
operation names the assumption in its contract owner; package changes require
the existing [binding checks](../COMPILER-API.md#binding-the-contract-to-the-implementation).
The module preserves text checks and path recognition. It carries no second
table of library signatures and admits no alternative declaration shape.

Caches belong to the snapshot or collection whose answers they describe.
They hold data rather than closures over the whole collector. Probe nodes
belong to their probe snapshot and cannot enter the base snapshot's cache.
Keys include the declaration group and any binder, arguments, mode, policy or
family selection on which an answer depends. Failed queries preserve their
per-use diagnostic spans and observation behavior.

The review's performance points have these destinations:

- **Compiler per automatic project:** adapt `withOwnProject` through the
  existing session mechanism, retaining strict project discovery, file-read
  observation and snapshot release. Discovery and reuse need separate tests
  for files with different owning projects and changed configurations.
- **Root search per span:** build a per-source-file index with candidate
  nodes in the original traversal order. Separate expression, identifier,
  type-node and computed-node queries preserve each predicate, outermost
  match, `getStart` behavior and excluded `SourceFile` or heritage nodes.
  Build lazily when a request needs it. This replaces repeated searches by
  one walk and lookups, at the cost of retaining the index for that snapshot.
- **Repeated `computedMembers`:** memoize by canonical merged declaration
  group once that group is established, including alias resolution's
  snapshot. A cycle-in-progress entry has a distinct state from a negative
  answer.
- **Repeated `checkedClass`:** retain separate full-file diagnostics and
  class escape results keyed by file and owner; then consider one file walk
  that classifies all relevant owners. A recursive base-class check's
  path-local `seen` is not a globally cached negative result.
- **Repeated `parametersOf` and `library()`:** cache merged parameter data
  and library classification or mapped templates per snapshot and policy.
  Captured-parameter lookup and application completion keep their use-site
  inputs. Diagnostic delivery remains once per observed file.
- **Serialized binder detection:** replace
  `JSON.stringify(term).includes('"k":"binder"')` in `collect` with a
  typed traversal using `visitType`, preserving the exact binder predicate
  and its refusal. Prove preservation of the visited term with the existing
  effect mechanism, or use direct recursion over the term union.
- **One probe per reviewed interface:** first isolate probe construction and
  lifetime. Cache reusable parsed results only with complete snapshot,
  policy and body keys. Batching probes requires checking interface names,
  spans, merging, diagnostics and disposal, so it follows extraction as a
  separate measured change.

These are hypotheses about avoidable work, not measured speedups. A cache
with no parse CPU benefit on the relevant slices does not justify extra state.

## Extraction order and measurements

For every numbered step, record three numbers beside the commit record:

1. **V:** verified statements in `declaration-graph.mts`, from
   `make census FILES=declaration-graph.mts`, with verified/countable totals.
2. **U:** pipeline cases whose actual outcomes and expected refusal reasons
   agree with the previous step, from `make test-cases`, as `U/total`; retain the
   full case results to identify a changed case. The requirement is every
   case unchanged, including gaps and refusals.
3. **P:** parse CPU seconds summed over the census slice invocations, from
   the census record. Report attempted parses, unavailable readings and
   executed/replayed counts alongside it.

Use the same shared heavy lock as the baseline for those runs. This design's
file census is explicitly requested by the owner; the ordinary branch rule
continues to favor targeted before/after slices during iteration. Run the
targeted helper and a caller while extracting, then the file census and suite
at each numbered boundary. Code changes also run the front-end type check,
wire-name check and `make test` according to
[the test tiers](../../AGENTS.md#iterating-run-what-the-change-touches).

Keep extracted top-level function declarations in `declaration-graph.mts`
through these measurements, so V measures verification rather than code
movement. If later file separation is useful, count the destination modules
as well and report the combined total. Retain both the statement denominator
and individual function outcomes: making a refused function smaller is not a
verified-statement gain.

Parse CPU uses the [existing timing measure](../STAGE-STORE.md#timing), user
plus system CPU for Node and the compiler processes attributed to parse.
A replay contributes the producing execution's CPU, not replay lookup time.
Changed tools code changes stage keys. Compare common slices separately from
new extracted slices: additional slices add parse work even if each becomes
cheaper. Report the `collectDeclarations` slice's P separately as a named
comparison whose source changes during extraction. Fixed-source speed tests
are specified below. A first refusal that moves later can
increase parse CPU by reaching more work; interpret P with outcomes and V.

For speed work, retain fixed source files, project configuration, dependencies
and request options from before the change, with their content hashes in the
measurement record. Run both implementations on those same inputs. Keep
separate workloads for repeated span queries, merged parameters and library
queries, repeated computed members, repeated class checks, and reviewed
interface probes. Include repeated collections with automatic project
discovery, covering both the same owning project and different owning
projects: the census supplies an explicit project and cannot measure
`withOwnProject` reuse.

For each workload record at least five executed CPU measurements before and
after, their individual values and median, and peak process memory including
the compiler. Measure cold sessions separately from repeated collections in
a retained session. Record retained index/cache size and memory after each
collection, plus session disposal, so retained state has a visible cost.
Stage replay is not an executed performance sample. Keep installation,
source inputs and limits equal, and report outcomes and document/trace
comparisons with the measurements. V/U/P describe the extraction; acceptance
of a speed change additionally requires these fixed-source measurements.

| Step | Small behavior-preserving boundary | Expected first verification benefit | Performance point addressed | Required numbers |
| --- | --- | --- | --- | --- |
| 1 | Extract the binder-term predicate and other independent term or identity helpers with explicit types; preserve the surrounding callers | Small data-only functions can verify independently of the collector's captured state | Serialized binder detection | V, U/total, P |
| 2 | Extract final assembly in pieces and check its existing helpers: document parts, external statement checks, promise transformations, settlement and final refusal | Typed traversals and result builders have bounded inputs and no resolution cycle; each extracted piece has its own slice | Makes final traversal cost visible; no caching claim | V, U/total, P |
| 3 | Name the option interfaces and add their adapter; pass current owner, external-read context, contextual binders and recursion path explicitly through one hook family at a time | Removes captured bindings and unrelated callback effects from those helpers; adapter gain may be zero | Locates query ownership for later caches | V, U/total, P |
| 4 | Extract resolution and merged-group services; isolate compatibility queries, keeping query order | Independent identity and declaration-part functions precede recursive readers; compiler-dependent slices can retain host-contract refusals | `parametersOf`, `library()`, compiler flag/path/text assumptions | V, U/total, P |
| 5 | Extract elaboration of one declaration or use and its dependency output; move the scope-hook cycle together where necessary | Fully initialized explicit contexts remove forward-captured bindings; small readers are measured separately from the recursive group | `computedMembers` and reviewed-probe ownership | V, U/total, P |
| 6 | Extract the existing closure loops into the explicit staged driver, preserving insertion and refusal order | Queue operations and single-request transitions have small contracts; the whole driver depends on the extracted readers | Repeated instance-map copying becomes visible; no scheduling optimization | V, U/total, P |
| 7 | Add the span index, then merged-parameter, library and computed-member caches, one commit per cache | Checked lookups have independent slices; cache mutations retain explicit storage contracts | Root searches, `parametersOf`, `library()`, `computedMembers` | V, U/total, P per change |
| 8 | Cache full-file class checks and escape answers; adapt automatic-project sessions; finally assess probe reuse, as separate changes | Compiler lifetime and native effects remain explicit; speed work need not increase V | `checkedClass`, `withOwnProject`, reviewed-interface probes | V, U/total, P per change |

Each row is a sequence of small commits when it contains several extractions.
At every numbered boundary and every constituent extraction or cache change,
require temporary before/after comparisons against the preceding implementation
on identical sources and options. Compare the complete declaration document
field by field, preserving array order, identities, symbols, provenance and
spans. Instrument the affected phase boundaries and the public adapter to
compare ordered callback/query traces: destination, arguments, answer or
refusal, return or exception, and position relative to collection operations.
Preserve synchronous delivery and callback-presence work selection.

The required inputs exercise each moved boundary, including merged
declarations, recursive instances, late prototype discovery, contextual
binders and recursive contextual reads, and lazy family selection with and
without supplied queries or report callbacks. Include success and refusal
paths at those boundaries. A refusal compares its exact message, span and
cause, the partial document state available there, and the callback trace
prefix before it; absence of a returned document does not waive comparison.
Include callbacks that throw to check exception order. Retain inputs and
comparison results beside each measurement record; resolve any difference
before treating the step as behavior preserving.

These temporary research checks supplement the required suites. Retire them
once pipeline coverage carries their signal; keep a control only for a
boundary or speed property the pipeline cannot show. Measure V/U/P after
each constituent commit as well as each numbered step.

### Baseline measurement

Measured on 2026-11-01 at commit
`62ce88743b5b3e604054843f56d45d7dcdfbde8e`, branch
`refactor/collect-declarations`, with clean tools and pipeline sources.
The command is `make census FILES=declaration-graph.mts`, run once under
the agents' shared heavy-run lock (`until mkdir … 2>/dev/null; do sleep 20;
done`), with an exit trap to release the lock. It uses the default stage store and the census's 300 s
step limit.

| Measure | Baseline |
| --- | --- |
| V: verified statements | **410 / 4,247 (9.7%)**, 31 / 45 functions verified |
| U: pipeline case baseline | **2,752 / 2,752** cases as expected (`make test-cases`, same sources); comparison starts from these outcomes |
| P: parse CPU | **74.847290 s**, 45 executed parses, 0 replayed, 0 unavailable CPU readings |
| Common collector slice's parse CPU | **13.365444 s** |
| Collector's statements | **0 / 2,941** verified |
| Other refused statements | **896**, across 13 `unverified/search` functions |
| Census wall time | **138.837 s** |

The inventory excludes 11 module statements and 8 statements in 4 other
functions from the counted total. Across all stages there are 494 executed
and 215 replayed invocations. The census record, which that command writes
and whose path it prints, retains the outcomes and producing executions'
measurements; it is not kept in the repository, and the command at that
commit makes it again. `node dev/census.mts refusals <record>` supplies
the sites in the table below.
The baseline is an observation of these sources, installation and stage
policy; it predicts neither additional refusals behind the first one nor a
speedup from extraction.

The suite baseline is also measured on 2026-11-01 under the same lock, by
`make test-cases` at the same commit. The suite reports 3,455 functions verified, 1,458 negative
controls and 210 named gaps. Its case outcomes include those gaps; the
2,752 figure counts agreement with expectations, rather than acceptance of
every source.

### Steps 1–2: syntax and fixed-input measurements

Measured on 2026-11-01 with
[`dev/declaration-metrics.mts`](../../dev/declaration-metrics.mts), comparing
`6e2aa4969397` with `0e853a49dada` on `refactor/collect-declarations`.
The syntax report reads TypeScript's tree. Lines include the function's
signature, option type, comments and body, from its first token through its
closing brace. Each inner function has a name or syntax kind and a source
line and column. A capture is a direct value reference to a binding declared in an
enclosing function inside `collectDeclarations`; references in a nested
function belong to that nested function. Property names and type syntax
are excluded, and lexical scopes distinguish shadowed bindings.

| Syntax measure                                                   |    `6e2aa4969397` |    `0e853a49dada` |
| ---------------------------------------------------------------- | ----------------: | ----------------: |
| `collectDeclarations` lines                                      | 4,094 (526–4,619) | 4,081 (538–4,618) |
| Inner functions                                                  |               564 |               560 |
| Inner function declarations / arrows                             |           1 / 563 |           1 / 559 |
| Inner functions with captures in this scope                      |               360 |               358 |
| Captured mutable local variables                                 |                11 |                11 |
| Captured parameters                                              |                76 |                76 |
| Captured `const` bindings with visible storage mutations         |                41 |                40 |
| Option properties                                                |                90 |                90 |
| File's top-level function declarations with bodies               |                45 |                52 |
| File's top-level functions, including functions held by bindings |                49 |                56 |

Mutable bindings mean `let`, `var` and parameters, whether or not an
assignment occurs. The separate `const` count observes property/element
writes, increment, decrement, deletion and calls of standard Array, Map
and Set mutator names on the binding. It is a syntax measurement: aliases
and effects inside called functions can add mutations it does not count.
The option names, types and optional markers are identical between the
two reports. Each report lists every inner function's captures, every
captured mutable binding's declaring line and capturing functions, every
option property and every top-level function.

The mutable local variables' direct capture counts agree in both sources:

| Binding              | Capturing inner functions |
| -------------------- | ------------------------: |
| `verifierText`       |                         1 |
| `externalReads`      |                         2 |
| `collecting`         |                         3 |
| `scanned`            |                         1 |
| `open`               |                         1 |
| `keysRead`           |                         1 |
| `iteratorSymbol`     |                         2 |
| `stableListed`       |                         1 |
| `found`              |                         1 |
| `closureBinders`     |                         1 |
| `collectedInstances` |                         1 |

The seven additional top-level functions are `hasBinderTerm`, `aliasKey`,
`appendDocumentDefinitions`, `settleDeclarations`, `promisedValues`,
`promisedDefinitions` and `finalizeDeclarations`.

Both file censuses have clean `tools/` and `pipeline/` sources in their
records. Their statement denominators include the collector's inner
functions and the independently extracted helpers.

| File census measure                           |     `6e2aa4969397` |     `0e853a49dada` |
| --------------------------------------------- | -----------------: | -----------------: |
| V: verified / counted statements              | 410 / 4,247 (9.7%) | 421 / 4,257 (9.9%) |
| Verified / counted functions                  |            31 / 45 |            34 / 52 |
| P: parse CPU seconds                          |          77.275100 |          73.862362 |
| Attempted / executed / replayed parses        |        45 / 45 / 0 |        52 / 52 / 0 |
| Unavailable parse CPU readings                |                  0 |                  0 |
| `collectDeclarations` slice parse CPU seconds |          14.271882 |          12.197093 |
| Census wall seconds                           |            131.547 |            147.895 |

These census P totals cover different slice sets. The fixed-input samples
below compare the same slice set.

The fixed parse inputs are all 45 census slices of `declaration-graph.mts`
and all 14 census slices of its direct caller `fragment-parse.mts` at
`6e2aa4969397`. Both implementations read those same 59 files, in sorted
file order, at the same source paths, with the baseline's copied source
dependencies and `tools/tsconfig.json`. Installed packages are the same
physical copies for both implementations. For parse timing, `git archive`
loads each revision's `tools/`, `pipeline/` and `dev/` sources into the same
temporary `measurement/` directory, retaining that directory's copied
dependencies and supplying the same measurement driver. The fixed inputs'
`tools/node_modules` link resolves to this installation, so the implementation
and its inputs recognize the same package paths and runtime enum objects.
`inputs.json` records the slices'
hashes; `sources.json` records every copied source/configuration file's
hash, and each sample checks that manifest before parsing.

```text
inputs.json SHA-256: ef7bbc6312ab5eae25b9879ed46f9cbba01d925c9f109363e392f05164a2c855
sources.json SHA-256: ef0582f9549451fea29b552c174efe19b48a67dc2742f8f3cc9c5a1d174686fd
```

Each sample is a new Node process invoking `parseSource` on the fixed
inputs; parser and declaration-session lifetimes are those of the parse
stage. CPU seconds sum user plus system CPU attributed to the 59 parse
invocations, including their compiler CPU. Samples alternate current and
baseline implementation, five pairs in order. Each sample names a fresh
`TSCERT_STAGE_STORE` directory. Both file censuses and the parse samples
take the session's shared `heavy.lock`, released by an exit trap on failure
as well as success. The censuses use the default store and 300 s stage limit.

| Fixed-input parse CPU seconds            | `6e2aa4969397` | `0e853a49dada` |
| ---------------------------------------- | -------------: | -------------: |
| Sample 1                                 |      83.768107 |      84.454912 |
| Sample 2                                 |      83.720527 |      83.935689 |
| Sample 3                                 |      83.395038 |      83.749236 |
| Sample 4                                 |      83.610453 |      84.212861 |
| Sample 5                                 |      83.925367 |      83.981496 |
| Median                                   |  **83.720527** |  **83.981496** |
| Successful / attempted parses per sample |        59 / 59 |        59 / 59 |
| Executed / replayed parses per sample    |         59 / 0 |         59 / 0 |
| Unavailable CPU readings per sample      |              0 |              0 |

Every sample has identical input hashes and parse outcomes (all successful).
`summary` computes each median from the five retained `report.json` files.

The syntax reports, fixed sources, input manifests, census records and
logs, per-sample reports and invocation logs are not kept in the
repository: the manifests' hashes above identify the fixed inputs, and
`make census` at `6e2aa4969397` and `0e853a49dada` makes the two census
records again.

This fixed-source comparison measures these census slices with an explicit
project. The workloads and automatic project discovery described above
have their own measurement requirements. These measurements compare the
complete revisions, including changes outside `declaration-graph.mts`.

### Refusals and the earliest expected gains

| Function or group | Counted statements | Observed first refusal | Implication for extraction |
| --- | --- | --- | --- |
| `collectDeclarations` | 2,941 | `unsupported: shadowing parameter 1` at proposal | The whole function contributes zero until it verifies; the first observation here is a producer limitation. Extraction gives independent functions their own chances to verify. |
| `withProject`, `useProject`, `withOwnProject`, `clientErrors` | 50 | Incoming edge at `check(project)` | Project helpers share this refusal; compiler-session extraction alone gives no evidence that these slices verify. |
| `promisedBinders`, `promisedMethods` | 5 | Return-contract claim for the conditional binder result | Small existing helpers are near the finalization boundary; inspect the inferred writable result contract and preserve the input's full shape. |
| `namesArray` | 3 | Node-typing claim at `documentHolds(...)` | A small finalization helper is a candidate for an explicit predicate and call contract. |
| `nodeOrigin` | 8 | Closure expression claim at `origins` | Explicitly passing the origin data is an early candidate; the message alone does not establish the cause. |
| `importBindings` | 20 | Closure signature claim outside the source annotation | A named top-level import mapper with its full return type is an early candidate. |
| `externalStatements` | 21 | Node-typing claim at `visitType(...)` | An explicit worklist and a correctly stated visitor effect are candidates; the first refusal does not itself prove an effect is the cause. |
| `overlaidInterface` | 52 | Incoming edge at the local `nameOf` function | Extract the small parameter-name query before the larger overlay reader; inspect the edge claims rather than assuming the helper's syntax is the cause. |
| `selectGlobal` | 355 | Node-typing claim at `forms(overload, key, what, entry)` | The nested readers need their own inputs and call contracts; moving the whole function yields no verification gain. |
| `collect` | 382 | Closure expression claim at `nativeFields` | Explicit state and smaller term readers also apply to the existing dependency collector. |

These observations support beginning with small term functions and the
finalization boundary, then origin, import and parameter helpers around
resolution. Existing `mergedParameters`, the four span-query functions,
`promisedNames`, `mergeMembers` and `mergedClass` already verify in this
census; they give concrete examples of independently checkable functions
near these boundaries. The span index is primarily a performance step,
since its existing query functions already verify.

The owner's reported earlier refusals involving captured closure signatures,
bindings read before set and callback effects motivate explicit contexts and
initialized state. This measurement records the refusals above. It does not
establish those earlier messages as the collector's current first refusal.
Removing `shadowing parameter 1` alone cannot establish that the remaining
2,941 statements verify. More refusals can appear behind it. Locate and
examine that producer failure in its own small step if extraction meets it;
renaming a parameter is justified only by the located cause.

The extraction order is a conjecture about which obligations become small
enough to discharge first. Each step uses its measured refusals to select a
source rewrite within existing contracts. Contract additions or changes,
including external, compiler, library and effect contracts, are excluded from
all numbered steps. Record a verification blocker requiring such work as its
own item in the WORK status table, with the refused obligation and the
contract it would need; any contract proposal belongs to separate work.
Function safety for an extracted helper and faithful annotation interpretation
remain separate obligations.

## Scope

The design covers organization, explicit state and interfaces, compatibility
queries, and measured removal of repeated work. It preserves the admitted
source fragment, the declaration and claims wire formats, library contracts,
family selection, budgets and the successful CLI condition. New typing rules,
new host assumptions, changes to closure effects, wider language support,
different refusal policy and new cache infrastructure belong to separate
designs. Parallel elaboration and new scheduling are outside this extraction;
identity allocation, probes and diagnostics depend on order. Full correctness
or termination proofs of declaration collection are additional work beyond
making its top-level functions verify for safety.
