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
| syntax.mts support (namespace imports in an initialization) | open: `compiler-api.mts`'s initialization reads its namespace import `ts` as a value (`new Map(Object.entries(ts))`), refused as "the namespace import ts is used only through member reads and qualified type names"; the namespace scan reads every statement, the omitted one included, so the refusal refuses every unit of the file (probe census, 2026-11-04) | a namespace object read as a value in an initialization has its contract, and the file's other units are checked |
| Investigation: `compiler-api-guards.mts`'s initialization search memory | open: an investigation, cause unknown: the whole-file search of the module's initialization, a table of compiler-API guards, passed 8.6 GiB resident before an 8 GiB cap stopped it (2026-11-04); under the stage memory cap it is a tool failure | the search runs within the cap, or its cause is established |
| Investigation: a dictionary completed by writes in branches | open: an investigation, cause unknown: `compiler-channel.mts#identify`, a local `{ [field: string]: string \| boolean }` built from a literal and completed by index writes in both arms of an `if`, then returned in a record, is refused at its return with "the edge from node 98 does not establish the claims at this point" (census of `50be2ce8`, 2026-11-05); the form is [avoided](docs/SOURCE-REWRITES.md#a-dictionary-completed-by-writes-in-branches-before-its-return). Which rule fails is not established. | the failing rule is named, and the form supported or its refusal stated |
| Investigation: `files.mts`'s check time | open: an investigation, cause unknown: in the census of `17db34ea` (2026-11-04) the file's check takes 387 s of its 545 s, more than twice its search (151 s), at a peak of 0.2 GB; its 13 functions share one unit with its initialization. Which part of the check grows is not established. | the cause is stated, and the check is repaired or its time explained |
| A census's wall time | open: a census's wall time is about its slowest file's, since a file's stages run in sequence: in the census of `17db34ea` (909 s wall), `declaration-graph.mts` takes 840 s (search 488 s, check 200 s), `fragment-parse.mts` 777 s, `fragment-expressions.mts` 680 s and `fragment-statements.mts` 619 s, each mostly proof search. | a file's units are searched and checked in parallel, and the census's wall time is measured against its slowest unit's |
| Declaration-graph resolution helpers | open: [source rewrites](docs/SOURCE-REWRITES.md#merged-declaration-lists-stored-at-a-readonly-element-contract) and the entries after it, a `throw` and its operand left out of a closure's normal-return footprint, and a write of a cell the unit does not declare proposed as forgetting the other cells, verify 17 of the 26 functions of the cluster (16 of its 17 smallest), 0 → 389 statements, in a targeted census at a 600 s step limit on base `33d5faca` (2026-11-03). `compatibilityReviewed` calls a generic function value (`ProbeProgram`), whose call no rule derives; `collect`, `collectFrom` and `elaborateDeclaration` reach an incoming edge at `callbackResults`' union record; `inDeclarationSession` reaches its descriptor record holding `activeFamilies()`; `closeDeclarations`, `collectInstances`, `selectGlobal` and `collectDeclarations` keep their first refusals | each function verifies or its blocker has its own row |
| Deferred gap candidates | open: six candidates retained from the 13-case round: compiler-enum ordinary-data provenance, error-message narrowing, compiler ancestor cells, AST JSON key bounds, table-classifier preservation and shadow-map provenance. Their private patches and handoffs are preserved; the owner defers their validation to conserve credits. | the selected candidates pass their targeted measurements, suites and independent review |
| Priority-deck refresh | open: the priority deck describes census `9bf8c463`; its revision for the complete `9fb116b8` census is deferred by the owner’s credit constraint. | the deck reflects the measured census and passes source review |
| Loop head separation for a replaced record | open: a `for...of` loop that replaces a binding's record with a fresh one on each pass is refused at the loop's entry edge: the head's knowledge separates the fresh record from the loop's iterator, which the entry does not state (`blocker-for-of-fresh-record`). `template` avoids the form through `reduce` ([SOURCE-REWRITES.md](docs/SOURCE-REWRITES.md#a-loop-replacing-a-bindings-record-on-each-pass)). | `blocker-for-of-fresh-record` verifies |
| Investigation: `blocker-round-binder-entries` near its stage limit | open: the case lowers all of `type-term.mts`, and its four searches share the 60 s case limit. With a fresh store, search CPU is 26.5 s and check CPU 10.7 s at `fba8a506`; under a load average of 85–150 the search exceeds 60 s, and it verifies when rerun by its pattern (2026-11-03). Which part of the search grows with load beyond its CPU is not established. | the case completes within its limit under suite load, or its limit is stated with its reason |
| Investigation: type-term census timeouts | open: at a 600 s stage limit the census of `33d5faca` times out in `type-term.mts`'s slice `someType`, whose own body verifies with its same-file callees as declarations; with `mapTypeParts`' callback contract repaired ([a field's function passed to `map`](docs/SOURCE-REWRITES.md#a-fields-function-passed-to-map)) the slice verifies, search 240.7 s and check 42.2 s, and which part of the earlier search exceeded the limit is not established (2026-11-03). Last measurement: the targeted census at a 1,800 s limit, fresh store, `883614a0` → `fba8a506` (a merge's incoming edges read once all its predecessors are produced, slot value sets computed once), outcomes unchanged: search CPU `quantified` 305.0 → 152.3 s, `patternStmt` 329.4 → 264.5 s; check CPU 57.9 → 41.5 s and 175.7 → 140.5 s (2026-11-03) | controlled comparisons identify the cause and an appropriate search cost or located refusal |
| Investigation: class-statement search timeout | open: `classStmt` reaches its source-expression refusal in the complete `9fb116b8` census at a 300 s stage limit. Its earlier `9bf8c463` census timeout has an unexplained wall-time excess over the isolated saved-input run; investigation of those earlier conditions is deferred under the owner’s credit constraint (2026-11-03). | controlled execution or tracing identifies the earlier timeout conditions |
| Investigation: class-statement resident memory | open: the same saved request reaches peak resident memory 2,117,435,392 → 2,147,663,872 bytes with the context-array and ordered-field implementation. The cause of the resident peak remains unknown (2026-11-03) | allocator accounting distinguishes live retained structures from committed or reserved pages, and identifies the dominant owner |
| Investigation: chain-link type-argument edge | open: the `wrappedMethodCall` and `expr` slices first refuse the incoming edge to the included `chainLink` branch `gate.fail(node, "explicit type arguments are admitted on a method call only")`, at `[50714,50792)`; cause unknown (2026-11-02) | the incoming-edge refusal has an established cause and reproducer |
| Investigation: module catalog proof search | open: `library-modules.mts` retains its readonly effect spreads and their host-exclusion obligation. Migrating its two sites passes the earlier refusal and reaches the 5798-node initializer graph, after 325 expression obligations and 15 closure bodies; the broad rollout times out at 300 s and loses the previously verified `globalNamespace` slice and its 29 statements. Restoring only that file to `8554b30c` restores the dependent verification; the catalog migration is excluded from the scoped rollout (2026-11-02) | the complete catalog initializer has an acceptable proof cost without losing verified dependents |
| Investigation: client diagnostic record allocation | open: the [fresh document-array contract](docs/SOURCE-REWRITES.md#a-probe-requests-fresh-document-array) verifies `withProject` and its `withOwnProject` helper. Fresh 300 s `declaration-graph.mts#withProject,#clientErrors` slices verify 0 of 2 → 1 of 2 functions and 0 of 9 → 4 of 9 statements; `clientErrors` reaches the returned diagnostic-record allocation at `[5385,5579)`, whose cause is unknown. The helper gains 0 of 1 → 1 of 1 functions and 0 of 28 → 29 of 29 statements; accepted `useProject` retains 1 of 1 functions and 13 of 13 statements. No timeouts on base `77814770` (2026-11-03) | the returned record obligation has an established cause and a checked derivation or documented source rewrite |
| Investigation: prototype overlay entry allocation | open: `array-prototype.mts#reviewedEntries` passes the private factory's dense return and reaches the first `forEach` entry allocation, `[5893,6189)`; the `stated` field receives a readable `EffectSignature[]`. The entry's node-typing refusal has an unknown cause. The `prototype` dependent retains its separate type-scope record refusal at `[40649,41175)` (2026-11-03) | the allocation refusals have established causes and checked derivations or documented source rewrites |
| Investigation: queued declaration-value record | open: the targeted `declaration-graph.mts#closeDeclarations` slice reaches the node-typing claim at `({ node, span: at })`, `[6665,6685)`, in the `valueStarts.slice(from, to).map` passed to `collectFrom`; its cause is unknown (2026-11-02) | the record-allocation obligation has an established cause and a checked derivation or documented source rewrite |
| Investigation: renamed-module expression claim | open: the immutable callable-context repair verifies `blocker-next-variadic-context-branch`; fresh 300 s target/dependent slices `fragment-parse.mts#renamedModule,#lowerFile` remain 0 of 2 functions and 0 of 728 statements and first refuse the `mapDocument(module.declarations, { type: term, param, identity, site })` node-typing claim at `[1556,1627)` and `[59305,59376)`, whose cause is unknown. The accepted `hasEarlyBindingReference` helper retains 1 of 1 functions and 42 of 42 statements, with producing cost 7.3 → 6.9 s CPU; no timeouts on base `773d5fc3` (2026-11-02) | the expression obligation has an established cause and a reproducer |
| Investigation: merge scope record | open: the targeted `array-prototype.mts#mergeRefusal` slice on base `7432c670` first refuses its `scopeOf` allocation of the complete `TermScope` record at `[38997,39523)`; cause unknown. The dependent `arrayPrototype` slice retains its earlier `result.expression.fields` refusal (2026-11-02) | the scope-record refusal has an established cause and reproducer |
| Investigation: census batch `8f4c28523e7f`, `blocker-prep-*` gaps | open: `blocker-prep-effect-spread`: spreading the readonly `emptyEffect` while overriding `onThrow` fails its node-typing claim; the explicit nine-field copy verifies the case but makes the searches of `library-modules.mts#moduleEntries,#moduleObjectDefault` and `declaration-graph.mts#globalNamespace,#globalFunction` time out at 300 s, so the spread form is kept (2026-11-02). The batch's other cases ([pipeline cases](pipeline/cases.mts), each source header naming its census functions) verify through their source rewrites and contracts or are negative cases (`blocker-prep-reference-args-map`, `invalid-parameters-qualified-hook`, `blocker-prep-captured-map-records`, `invalid-flat-map-module-function`); the private layout and Node process contracts of the [compiler client and child-process boundary](docs/SOURCE-REWRITES.md#the-compiler-client-and-its-child-process) require owner review | each refusal is explained and answered by the [source-rewrite routes](docs/SOURCE-REWRITES.md#deciding-what-a-refusal-of-tscerts-code-calls-for): support needs a complete contract and checked derivation; a runtime check must establish the property through intervening calls; a repair needs an established defect; avoidance needs equivalent returns, exceptions and effects; a host boundary needs the smallest external operation and its full audited contract; a trusted unit needs owner authorization and explicit dependencies; a proof needs the relevant semantics and stated host assumptions |
| Investigation: computed-type slice expression claim | open: the targeted `computed-types.mts#computedType` slice refuses with `no claimed type for the expression at [17527,17527)` before and after the [returning first-match loop](docs/SOURCE-REWRITES.md#a-first-match-callback-calling-an-imported-type-reader); its cause is unknown. `blocker-prep-host-find-callback` and `inexpressible` verify (base `8f352a6b`, 2026-11-01) | the expression claim has an explained cause and a checked derivation or a documented source rewrite |
| Investigation: receiver-form guard incoming edge | open: targeted slices `fragment-expressions.mts#expr,#binary` reach an incoming-edge refusal at the `.call`/`.bind` receiver-form guard at `[30205,30648)`; its cause is unknown | the incoming-edge obligation has an explained cause and a checked derivation or a documented source rewrite |
| Computed alias passed as a function | open: targeted slices `computed-types.mts#unionMembers,#distributed` pass the missing `node` field through [declaration-aware truthiness](docs/SOURCE-REWRITES.md#a-host-node-union-in-a-logical-operators-result) and reach the refusal of `context.alias` read as a function value for `computedAlias`; its contract declares a method with a receiver; 0 of 2 functions and 0 of 63 statements verify before and after, with no timeouts at a 300 s step limit on bases `1be3678a` before and `3b96f348` after (2026-11-01) | the method passed to `computedAlias` has a checked derivation or a documented equivalent rewrite |
| [Declaration collection phases](docs/drafts/collect-declarations-phases.md) | open: steps 1–6 extract independent helpers, final assembly, resolution and merged declaration groups, compiler compatibility queries, one declaration’s terms and dependency contributions, computed-member detection, synchronous instance allocation and the staged closure driver; named option interfaces and explicit equation owners, external-read depth, contextual binders and recursion paths supply their inputs; the file census verifies 523 of 4386 statements and 47 of 81 functions (2026-11-01); step 6 retains each function’s verified statements and all 2762 case outcomes; declaration documents, ordered callbacks and refusals agree on the compared inputs; steps 7–8 follow the draft | the draft’s phases have explicit inputs and owned state, with unchanged declaration documents, ordered callbacks and case outcomes |
| Investigation: mapped type result record | open: targeted slices `type-term.mts#typeTerm,#constructorForms` pass the optional host-list argument with a [saved list binding](docs/SOURCE-REWRITES.md#an-optional-host-list-tested-through-a-property-receiver) and reach the node-typing claim of `mapped`'s result record; 0 of 2 functions verify before and after, with 0 of 18 → 0 of 19 statements verified and no timeouts at a 300 s step limit on base `b3f431c3` (2026-10-31) | the result record's failed obligation is explained and has a checked derivation or a documented source rewrite |
| Investigation: computed reference result claim | open: targeted slices `type-probe.mts#nodeAt,#makeProbe` verify 0 of 2 → 1 of 2 functions and 0 of 206 → 10 of 208 statements, with no timeouts, on bases `f7de3845` before and `62ce8874` after (2026-11-01); `nodeAt` verifies through the [saved Node view](docs/SOURCE-REWRITES.md#host-member-reads-after-a-generic-guard), and `makeProbe` reaches the node-typing claim of `readReference(name, args, span)` at `[15385,15416)`, whose cause is unknown | the computed reference result claim has an explained cause and a checked derivation or a documented source rewrite |
| Investigation: flow node result record claim | open: targeted slices `source-flow.mts#decodeFlowDocument` and `pipeline/verify-source.mts#checkUnowned` verify 0 of 2 functions before and after the fresh-result repair on base `1be3678a`, with 0 of 186 → 0 of 134 statements verified and no timeouts at a 300 s step limit (2026-11-01); the decoder reaches the constructed node record's node-typing claim at `[23891,24071)`, whose cause is unknown; the caller retains its earlier `Math.round` overlay refusal | the constructed node record's claim has an explained cause and a checked derivation or a documented source rewrite |
| Investigation: refusalStatus completion claim | open: targeted slices `diagnostic.mts#readDiagnostic` and `pipeline/verify-source.mts#refusalStatus` verify 0 of 2 → 1 of 2 functions and 0 of 115 → 149 of 155 statements, with no timeouts, before on `1be3678a` and after on `16956d49` with the decoder repair (2026-11-01); `readDiagnostic` verifies through [fresh typed diagnostic variants](docs/SOURCE-REWRITES.md#a-decoders-result-asserted-through-unknown); `refusalStatus` refuses its completion claim at `[75,88)`, whose cause is unknown | the completion claim has an explained cause and a checked derivation or a documented source rewrite |
| Investigation: shadow signature parameter map claim | open: `blocker-gap-round-receiver-template` verifies through the producer's declaration-aware truthiness query; targeted slices `shadow-contracts.mts#print,#printSignature` advance from the receiver interpolation to the node-typing claim of `params.map((p, i) => …)` at `[4457,4519)` in `printSignature`; 0 of 2 functions and 0 of 78 statements verify before and after, with no timeouts on base `293ad7b1` (2026-10-31) | the parameter map has a checked typing derivation |
| Investigation: unchecked worker file-map closure claim | open: `async-object` verifies with the decoded result's lifetime `then` contract; targeted slice `unchecked.mts#check` advances from async resolution to the closure-expression claim of `[...roots].map((file) => path.relative(".", file))`; 0 of 1 functions and 0 of 42 statements verify before and after, with no timeouts (2026-10-31) | the file-map closure expression has a checked derivation |
| Investigation: decoded finding allocation claim | open: targeted slice `unchecked.mts#decodeResult` advances from async resolution to the node-typing claim of `{ file, line, column, kind, text, reason }`; 0 of 1 functions and 0 of 23 statements verify before and after, with no timeouts (2026-10-31) | the finding allocation has a checked derivation |
| Investigation: file-answer expression claim | open: `blocker-gap-round-cache-answer` verifies with the cache callback's [nullable writable answer contract](docs/SOURCE-REWRITES.md#a-cache-callbacks-nullable-answer-field); targeted slices `files.mts#realOf,#answerOf` advance from 0 of 2 functions and 0 of 14 statements verified to 1 of 2 functions and 7 of 14 statements; `realOf` verifies and `answerOf` reaches the node-typing claim at `[5851,5904)`, with no timeouts (2026-10-31) | the file-answer expression claim has a checked derivation |
| Family activation: record at an index signature | open: `blocker-gap-round-unknown-spread` verifies through the [module export boundary](docs/SOURCE-REWRITES.md#a-loaded-modules-own-exports), with the unrestricted spread retained as a negative case; targeted slices `family-activation.mts#checkedGuards,#activeGuards` advance from the spread's node-typing claim to a record at an index signature, with 0 of 2 functions verified and statement coverage 0 of 174 → 0 of 172, no timeouts (2026-10-31) | the record establishes its index-signature contract |
| Census refusal examples (043267592814) | open: five supplied causes cover 1997 statements in 23 functions. Their case examples verify through contracts and source rewrites ([source rewrites](docs/SOURCE-REWRITES.md#deciding-what-a-refusal-of-tscerts-code-calls-for), [prototype contracts](docs/SOURCE-CONTRACTS.md#prototype-contracts)): `blocker-census-effect-map-result`, `blocker-census-spread-map-records`, `blocker-gap-round-optional-parameter`, `invalid-in-union-read`, `blocker-gap-round-parent-initializer` and its open-node form, `blocker-gap-round-scheme-binder-map`, `blocker-census-annotated-node-union`, `blocker-gap-round-native-method-map` and its inferred form, `blocker-gap-round-locations-map`, `blocker-round-mapped-array-some`, `blocker-round-resolved-overlay-map-result` and `blocker-round-mapped-filter-length`; the unsafe forms are negative cases (`invalid-sparse-join-coercion`, `invalid-spread-map-records`, `blocker-gap-round-optional-parameter-writable`, `invalid-in-union-part`, `invalid-gap-round-scheme-binder-map`, `invalid-some-sparse-callback`, `blocker-round-inferred-map-result`). Last measurement: targeted slices `written-applications.mts#writtenApplications` and `declaration-graph.mts#collectDeclarations` verify 0 of 2 functions and 0 of 3254 statements on base `a92cc758`, the former reaching the callback signature of `t => childParameters(t).length` at `[15098,15128)`, the latter `shadowing parameter 1`; no timeouts (2026-11-01) | each cause has a checked resolution under the source-rewrite routes, including checked receiver contracts and callback signatures for the three isolated mapped-array cases, or documented source rewrites |
| [Investigation: does the model's error lacking `stack` matter](docs/SOURCE-ELABORATION.md#in) | open: an error the program builds owns `stack`, which the model's error does not hold, so `"stack" in e` answers `false` in the model and `true` in JavaScript where `e`'s type leaves `stack` unstated, as every type an error meets does; both answers are checked; no program is known whose result differs (2026-10-27) | a proof that the differing answer changes no checked outcome, or a program it changes |
| Census refusal examples (f502699ca098) | open: the five largest causes after splitting the supplied first refusals cover 5989 statements in 71 functions. `blocker-census-rest-result` verifies by checked result inference for array-rest closures; the Set-copy cause is resolved by retaining the host `Set` type and admitting its union with an array in one constructor form; `blocker-census-options-default`, `blocker-census-import-guard-call`, `blocker-flat-map-narrow-field`, `blocker-gap-round-assign-target`, its length-only form and `blocker-gap-round-early-capture` verify, and `invalid-flat-map-narrow-field` retains the widening refusal. Last measurement: targeted slices `declaration-graph.mts#collectDeclarations` and `fragment-parse.mts#lowerFile` verify 0 of 2 functions and 0 of 3680 statements, the former reaching missing field `text`, the latter its closure-signature body-lowering refusal; no timeouts (2026-10-31) | each cause has a checked resolution under the source-rewrite routes |
| Census refusal examples (pretext `0d102a5c`) | open: the census of pretext's `src/` (chenglou/pretext at `0d102a5c`, its 11 modules but the tests, its `tsconfig.json` with `types: []`) verifies 97 of 209 functions shallow, 625 of 3424 statements, and 62 functions deep, with the typed-array views, `Float64Array`, `Intl.Segmenter` and the DOM's 2D context, canvases, `document`, `navigator` and `getComputedStyle` ([the DOM's canvas, document and navigator](docs/SOURCE-CONTRACTS.md#the-doms-canvas-document-and-navigator)) (2026-11-05). Each reason blocking a function has a case in [pipeline cases](pipeline/cases.mts), its source header naming the pretext functions it stands for: a gap case `blocker-pretext-*`, a negative case where the program is unsafe (`invalid-optional-field-widening`), or an existing case (`invalid-function-constant-value-import`, 3 functions; `blocker-array-index-of-write`, 1). A parameter whose default is a literal states its type ([literal defaults](docs/SOURCE-CONTRACTS.md#literal-defaults), `blocker-pretext-defaulted-parameter`, 15 functions). `String.raw` is read as a template tag ([`String.raw` as a tag](docs/SOURCE-CONTRACTS.md#stringraw-as-a-tag), `blocker-pretext-string-raw`, the initializations of `prepare.ts` and `line-breaks.ts`). The largest open reasons are the unannotated imported regular expression (`blocker-pretext-import-regex-constant`, 6) and non-null assertions of element reads (`blocker-pretext-typed-array-element-assertion`, `blocker-pretext-array-element-assertion`); `new Array<T>(n).fill(v)` is admitted as one fresh dense array (`array-fill`, `blocker-pretext-new-array-fill`); the effect of these on this census is not measured | each cause has a checked resolution under the source-rewrite routes |
| [Coverage of the front end](#the-front-ends-own-functions) | open: the per-unit census of main `ae20a6c6`, v0.94 (2026-11-04, 1800 s and 4 GiB per stage), verifies **643/686 functions shallow (93.7%)** and **10097/17790 statements (56.8%)**; every function the v0.9 census (`1589e590`, 628/684) verifies is among them | every function of `tools/`, `dev/`, `tests/` and `pipeline/` verifies or is refused by a stated restriction |
| [The producer's speed](#the-producers-speed) | entry-environment caching with source-order effect rounds: 77-input corpus user CPU 72.18 → 51.34 → 44.53 s (parent → 749f87a → working tree); every fixed median within 10% of parent; 77 of 77 results identical to parent, 73 of 77 outputs to supplied references; type interning open (2026-10-30) | repeated typing and structural type comparison are reduced, with the producer's output unchanged |
| Investigation: `Examples run under Node` fails within `make test` | open: under a load average of about 14, the suite failed in three runs of `make test` on 2026-10-30 and passed when run alone and on each rerun; the cause is not established | the cause, and the suite passing under load |
| Investigation: a loop update reading a field of a field after a nested discriminant test | open: records `H1 \| H2`, a loop updating `h.n.up` with `h.n.k === "r"` tested inside an `h.k === "one"` branch, is refused at the update even when every implied path witness is kept (2026-10-30); the cause is not established | the cause, and a case showing it |
| [Correctness specifications](docs/drafts/correctness-specs.md) | open: design approved (2026-10-28) | the clamp, binary-search and JSON round-trip cases verify with their contracts, and their negative controls are refused |
| [Canonical heap knowledge](docs/drafts/heap-knowledge-canonical.md) | partial: value sets, links and facts have normal forms proved to hold exactly where the raw knowledge does, idempotent and unique, and separation a compacted form proved to hold exactly where it does, idempotent and bounded; points other than cuts store the normal form, and so do node outputs; nodes and edges read stored knowledge by alias class ([stored knowledge](docs/PROGRAM-TYPING.md#stored-knowledge-and-how-it-is-read)); the evidence writes each value set once. Last measurements: the census of `tools/`, d578dd8 → 8092044, the same 227 of 519 functions verified, search CPU 858.6 → 387.3 s, check CPU 248.0 → 79.4 s, peak memory of one run 10.6 → 1.6 GB; b59096f → the value-set pass, generated workloads at 16 tests, evidence disjunction 319.3 → 3.2 MB, repeated 93.2 → 1.9 MB, guards 1.38 → 0.88 MB, fields 45.8 → 2.4 MB; on 32 repeated tests search CPU 40.2 → 47.5 s (2026-10-28); open: one type context per type rather than per node, the evidence's normal-form validator, the workloads as pipeline cases, disjunction at 32 tests within the step limit, and guards' evidence exponent (2.35 between 16 and 32 tests) | the draft's §9 measurements hold |
| [The type-decision procedure's remaining steps](docs/drafts/subtype-decision.md) | open: the draft's remaining steps, each measured on `moduleFunction`'s sampled time outside input preparation (2.17 s): interning labels 1.11 s, a checker memo 0.31 s, the final check reading search's proved inclusions 0.33 s, a candidate index, hashed kernel lookups and a request-wide demand memo at most 1–5% each; the `Clauses` rule, the completeness theorems of the selected search and discovery, deleting the check's rerun and coverage by assumption carry no measured cost (2026-10-24) | each remaining step lands with its measurement, or is closed as not worth its cost |
| [Decoders' dictionary reads](#decoders-dictionary-reads) | open: in `calculus` 12 of 15 functions verify; `decodeTerm`, `decodeCode` and `termsOf` verify in 10.0 s of evidence search with candidate selection and the answered requests threaded through the document's search, 25.2 s without any reuse (user time, median of 3, 2026-10-19) | the decoders of `calculus`/`control-flow` verify in their modules within the limit |
| [Slices of the value universe](#universe-slices) | partial: a tag test on `unknown` keeps the kinds it does not contradict, proved (`in-unknown-object`); open: the negative `Array.isArray` slice, the meet of a type parameter with `unknown`, and the guards over `unknown` | `typeof v === "object" && v !== null` narrows `unknown`, and the guards over `unknown` promise what their tests establish |
| [A key found on an open object](#key-on-open-object) | partial: the read verifies as an open read, `%Read:k%` at `unknown`, under the open-read restriction, an assumption for the owner's review, on an object no type states the key of (`blocker-in-name-object`) and where a passed `in` test makes the read syntactically eligible on a union with an arm stating no key, at `body` and `type` only on receivers each arm of which states the key or is of the host package (`compiler-api-in-union-read`); open: the read as the model's own, with the lookup invariant proved | `if (typeof v === "object" && v !== null && "k" in v) return v.k` verifies, with the lookup invariant proved |
| [Guard overloads beyond `filter`'s](#guard-overloads) | partial: a guard read as a value meets `filter`'s guard overload and `find`'s at a footprint keeping array stores (`filter-guard-value`, `blocker-compiler-api-filter-guard-element`), and a guard closure meets `find`'s by its promise signature at its body's footprint (`blocker-compiler-api-find-promise`); `every` at a guard promising `string`, `number` or `boolean` gives [the elements fact](docs/FOOTPRINTS.md#the-elements-fact), which `map` relies on within one expression (`blocker-every-promise`, `every-elements-map-join`); open: the predicates excluding null or undefined, and the other natives at the fact; `blocker-round-every-map-narrowing` verifies by [stating the formatting callback parameter at `string \| null`](docs/SOURCE-REWRITES.md#a-formatting-callback-narrowed-by-an-earlier-every-statement), an erased annotation avoiding reliance on the elements fact across a statement; targeted slices `shadow-contracts.mts#print,#printSignature`: 0 → 2 functions and 0 → 78 statements verified, no timeouts (2026-11-01) | `shadow-contracts.mts`'s `print`, which reads its array at `string[]` after `every` answers `true` at a guard, verifies; the formatting callback verifies at its nullable parameter contract |
| [Investigation of generic equality in a condition](#generic-equality-condition) | open: an investigation, cause unknown | `if (left !== right) return 1;` with `left, right: T` verifies, as `return left !== right` does, and the Boolean-return lowering applies to every function's return |
| [Investigation of a negated first read of an element](#negated-first-read) | open: an investigation, cause unknown | `const d = list[0]; if (!d.initializer) return -1;` over a program record verifies |
| [Assigned parameter patterns](#assigned-parameter-patterns) | open | `invalid-parameter-pattern-assigned` and `invalid-parameter-pattern-default-order` become positive cases verifying their Node results |
| [Constructor rests](#constructor-rests) | open | a constructor with a rest parameter is constructed and its variadic construct signature introduced |
| [Class offers across units](#class-offers-across-units) | open | a module class passed by a module function to a variadic construct signature verifies |
| [Generic methods left](#generic-methods-left) | open | bounded class-method binders and members binding different numbers of binders have checked contracts |
| [Contract completeness](#restoring-completeness) | open | effect inference covers the rest wrappers, call forms and nested heap operations it is conservative for |
| [Effects of dispatched calls](#effects-of-dispatched-calls) | open | a method call on a union with a primitive's shape is dispatched and `split-non-empty` verifies |
| [Footprints](#footprints) | open: the seven programs decided (2026-10-17) | every application form has a checked bound |
| Native footprints from their specification steps | open: the [draft](docs/drafts/native-footprints-from-steps.md), awaiting the owner | each modelled array mutator's footprint is derived from its step sequence, the proved lemmas discharging it at a selected call |
| [Exceptional footprints](#exceptional-footprints) | open: handler facts across a throw | a call's footprint on a throw carries an effect through a handler, with `checkUnitJson_safe` concluding it |
| [Class methods' effects](#class-methods-effects) | open: the [draft](docs/drafts/method-effects.md)'s design, accepted by the owner: D1 (a), stated effects, D2–D6 as the draft recommends, D5's rewrite of `Gate`'s four `shift`s into field writes, D7 and D8 (a). Effects are [stated](docs/SOURCE-ELABORATION.md#stated-effects) with `Within<…>` and certified from each definition's code; the compiler API's callback-free node methods state the empty footprint (D4); `forEachChild` is read at each callback footprint (D7); a type guard states its effect at its promise's type (`x is Within<F, T>`); `Gate` states its members `span`, `local`, `hasTypeParam` and `typeParamName`, uncertified while no verified unit lowers `Gate`; 157 of the 167 functions a syntactic scan finds in `expr`'s contract closure state `{value: any, store: grow}` (2026-10-24). Last measurement: `sort` at a comparator whose store changes are at most `grow` is within `{value: any, store: grow}`, and a closure calling a callable object with fields is proposed within its call signature's footprint: census slices at 300 s of `enumStmt` and `enumEntries` (`fragment-classes.mts`), 1ba27599 → that change: verified 0 → 2 (2026-10-30) | callbacks calling a class instance's methods use effects stated with `Within<…>` and certified in each definition's own module |
| [Async and generator code](#async-and-generator-code) | open | an async function's entry and resumption are checked by an asynchronous entry judgment, and `%Await%`, `%AsyncReturn%` and `%AsyncComplete%` leave the trust surface |
| [Iteration left open](#iteration-left-open) | open: `blocker-round-map-keys-spread` verifies with the [native placement Map contract retained](docs/SOURCE-REWRITES.md#a-native-placement-map-widened-to-readonlymap); targeted slices `fragment-statements.mts#markEarly,#hoisting` pass the spread claim and reach the later node-typing claim at `[48517,48535)`, with 0 of 2 functions and 0 of 91 statements verified before and after, and no timeouts (2026-10-31); `blocker-round-map-entries-spread` verifies with the [native merge binder contract retained](docs/SOURCE-REWRITES.md#native-merge-binders-widened-to-readonlymap); targeted slices `array-prototype.mts#mergeRefusal,#prototype` retain 0 of 2 functions and 0 of 215 statements verified, with no timeouts: `mergeRefusal`’s first refusal moves from the entry spread to `Object.entries(value)`, while `prototype` retains its optional dictionary key-read refusal (2026-11-01) | the iteration forms listed there are lowered; both map-iterator spreads have checked result contracts or documented source rewrites |
| [Keys known only at run time](#keys-known-only-at-run-time) | open | the writes listed there are typed |
| [Remaining source forms](#remaining-source-forms) | open | the forms listed there are admitted |
| [Model limits of one form each](#model-limits-of-one-form-each) | open | each limit listed there has its model support |
| [Regular expressions left](#regular-expressions-left) | open | replacement callbacks of a regex of the conservative shape, a native regex from `new RegExp`, a regex's properties and structural match iterators are admitted, and `SetIterator` and `MapIterator` loops require the native mark |
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
| [Selection rules the data names](#union-shapes-candidates) | open | open target arms and shared literals each have a rule with its lemma, or a measurement shows it unneeded |
| [Observed stages beyond macOS](#observed-stages-beyond-macos) | open: the parse and TypeScript's diagnostics replay on macOS only | the compiler's reads are confined and observed on Linux, and the stages replay there |
| [Certificate size](docs/drafts/certificate-sharing.md) | open: stages 1 to 4 landed (node headers and the wire-text scan, read summaries, the evidence document's tables, separation facts). Last measurement, stage 4, census slices on executed stages, median of 3 serial runs, before (ec59551) → after: evidence `moduleFunction` 5.82→5.17, `inertRead` 5.31→5.31, `resolve` 2.69→2.69, `collect` 77.50→4.35 and `closeStatements` 51.50→3.87 MB; search CPU 29.3→28.4, 21.1→20.5, 20.5→19.8, 8.6→1.6 and 5.0→1.1 s; check CPU 5.0→4.8, 3.6→3.5, 3.4→3.3, 4.5→1.0 and 3.0→0.7 s; all five verified before and after (2026-10-23). Stage 1's structural decoder awaits the owner's choice of a reference: the decoder it must equal is built from the derived codecs and `sameJson`, partial definitions without defining equations a proof can use, so a proof needs total reference codecs, audited against them; the re-encode and comparison are 36% of `collect`'s check samples; stage 5 waits on residual cost | the five stages land, each with its proofs and controls, and `moduleFunction`, `inertRead`, `resolve`, `collect` and `closeStatements` verify with their search and check CPU measured before and after |

## Open work

<a id="next-steps"></a>

### Coverage of the front end

<a id="the-front-ends-own-functions"></a>
**The front end's own functions.** The goal is every function of the
repository's own TypeScript verified: `tools/`, `pipeline/`, `tests/` and
`dev/` (the sources under `pipeline/examples/` are the cases' inputs, many
refused by design). Verification states safety, each function's annotated
contract at every call, not that the parser reads TypeScript correctly. The
census checks each module unit by unit over one front per file and records
each unit's own refusal
([measuring coverage](AGENTS.md#measuring-coverage-once-on-main),
[function coverage](docs/DESIGN.md#function-coverage-and-release-thresholds),
[statement coverage](docs/DESIGN.md#statement-coverage)); its record groups
the refused units by the blocker each names
([choosing the gap cases](AGENTS.md#choosing-the-gap-cases-to-work-on)).

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
generic assertion function meets too.

`readFragmentFile` and `readClaimsFile` in `pipeline/verify-source.mts` read
back a document the run wrote, for a test to forge, and assert its type with
`as` (reason at the assertion) rather than decode it: no TypeScript decoder
of the Fragment or the claims document exists, and the tests reach about 100
fields deep in them. The two stay outside the goal by decision; what they
read is decoded again by Lean before anything is checked.

Gap cases standing for census refusals, each header naming its census
functions, are worked in the gap round's order: `blocker-prep-api-constructor`,
`blocker-node-create-require`, `blocker-contextual-default-argument`,
`blocker-compiler-api-generic-meet-field`,
`blocker-compiler-api-contextual-host-shape` and `blocker-in-unknown-walk`.

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

### The compiler API's contract

[COMPILER-API](docs/COMPILER-API.md) specifies the native assumptions,
restricted views and independent checks used by the front end.
[Modeling a library](docs/SOURCE-CONTRACTS.md#modeling-a-library) gives the
method for choosing supported project operations and measuring their cost.

### Guards and narrowing

<a id="universe-slices"></a>
**Slices of the value universe.** A tag test on a value at `unknown`
keeps the kinds of a JavaScript value it does not contradict
([the rule](docs/SOURCE-MODEL.md#slices-of-the-value-universe-by-tag-tests)).
Two slices remain, the negative `Array.isArray` answer and a type
parameter's meet with `unknown` (`T ∩ unknown`, whose meet row the rule
does not read):

```math
\frac{\Gamma\vdash x:J_{\mathrm{ref}}\qquad \mathsf{Array.isArray}(x)\ \text{answers}\ \mathsf{false}}
     {\Gamma\vdash x:J_{\mathrm{ref}}\setminus\mathsf{arrays}}\ \textsf{slice-non-array}
```

$`J_{\mathrm{ref}}\setminus\mathsf{arrays}`$ is $`J_{\mathrm{ref}}`$ with an
own-key bound excluding the store key.

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
`claim-text.mts`, `claim.mts`, `type-graph.mts` and `diagnostic-view.mts`,
6 of them refused at their promise in the census of 2026-10-19, verify in
their own units in the census of `17db34ea`.

<a id="key-on-open-object"></a>
**A key found on an open object.** A value that `typeof v === "object"`,
`v !== null` and `"k" in v` admit holds an object of an open record clause
$`c`$ stating no key $`k`$. The read `v.k` is an
[open read](docs/SOURCE-CONTRACTS.md#open-reads), the intrinsic
$`\%\mathsf{Read}{:}k\%:(\{\})\Rightarrow_{\emptyset}\mathtt{unknown}`$,
whose signature rests on the open-read restriction. Reading it as the
model's own read, a rule

```math
\frac{\Gamma\vdash v:c\quad c\ \text{an open record clause}\quad k\ \text{a string key}\notin\mathrm{objectProtoKeys}\quad c\ \text{excludes host values}}
     {\Gamma\vdash v.k:\top}\ \textsf{read-unstated}
```

needs a lookup invariant in the premise on inputs and preserved by every
step: every object's field locations are valid heap locations and its
prototype links lead through such objects, so a lookup of any key steps to
a value. The record meaning (`recT`) constrains the named fields only, so
under the current premises an unnamed key may hold a location outside the
heap and an unconstrained `[[proto]]` can leave the lookup without a result,
and a host object's property may be a getter its family does not state.


<a id="guard-overloads"></a>
**Guard overloads beyond `filter`'s.** TypeScript's `every<S>` narrows the
array to `readonly S[]` where it answers `true` at a guard, and `find<S>`
returns `S | undefined`. Neither is a contract of the native at the top
footprint ([prototype contracts](docs/SOURCE-CONTRACTS.md#prototype-contracts)): a
callback may append untested elements or replace tested ones before `every`
answers, and `find` passes `undefined` at positions a callback removed. Both
hold at a callback keeping array stores. A guard read as a value, whose
slot or entry states its promise signature extended by a rest, meets
`find`'s at its own footprint, and a guard closure by its promise signature
at the footprint its body proposes, its code checked at both
([prototype contracts](docs/SOURCE-CONTRACTS.md#prototype-contracts)).

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

<a id="assigned-parameter-patterns"></a>
**Assigned parameter patterns.** A parameter pattern one of whose bindings
the function assigns is refused at the gate, as is an assigned parameter
with a default and no annotation
([patterns](docs/SOURCE-ELABORATION.md#patterns)). Supporting them needs
each binding's contract derived from the parameter's annotation (or
context) at the position it reads, and each name bound where the pattern
reaches it, before a later default of the same pattern reads it: in
`function f({ a = 1, b = a }: { a?: number; b?: number }) { a = 2; return b; }`,
`f({})` is 1.

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
spell for the closure. Members of
two declarations, or of two instances of one, binding as many binders relate
up to renaming ([generic methods](docs/SOURCE-CONTRACTS.md#generic-methods)); two
binding different numbers of binders (`m<U, V>` at `m<W>`), which TypeScript
relates by instantiating the source at the target's binders, need an instance
table naming each source signature's image at the target's binders, inside
the family entry's table; `invalid-tag-inherited-declaration`, a control of the
native promise's tag, stops at that relation before its obligation. A binder a member's result accumulates
(`catch`'s `Promise<T | TResult>`) grows its family by one binder per call:
each is an application of the one equation, unfolded only when read
([RECURSIVE-EQUATIONS](docs/RECURSIVE-EQUATIONS.md)), never truncated.

<a id="restoring-completeness"></a>
**Contract completeness.** Array presence, callback effects and conversion
contracts impose separate obligations. Their current designs are stated under
[arrays](docs/SOURCE-MODEL.md#arrays), [native contracts](docs/SOURCE-MODEL.md#exact-contracts-and-native-effects) and
[effect certification](docs/SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification).
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
`checkUnitJson_safe` ([the design](docs/SOURCE-ELABORATION.md#exceptional-footprints)).
Left: handlers receive no current-content facts across a throw, and a node
with a handler is outside the node-by-node bound, so `map` over a callback
popping a fresh array inside `try` takes its signature with holes
(`map-fresh-handler-refused`).

- a semantic extension: `SafePost` states no postcondition on a throw, so
  `checkUnitJson_safe` needs an exceptional conclusion tied to the exact CLI
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
the subclass. The owner's decisions (2026-10-24): D7, `forEachChild` given one
signature per callback effect, and D8 (a), the checker's requests stated as
an audited host contract (a T6 extension); continue `expr`'s contract
closure and D5.

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
([CALLABLES](docs/CALLABLES.md)). Four promise controls stop before their
obligations: `invalid-native-promise-catch-record-explicit` at the
recognition of `catch`'s method instance, `invalid-generic-promise-ambient-open-record`
and `invalid-generic-promise-invariant-result` at `Awaited`'s
resolution-qualified scope, and `invalid-generic-promise-unknown-output`
at the modeled `await`'s input.


### Source forms and the model

<a id="iteration-left-open"></a>
**Iteration left open.** An array pattern over a host
non-array iterable needs the pattern's reads as steps of `%Iterate:K%`, or of
the protocol. A spread of a program's iterable where the statement evaluates
code before it, and a default or nested pattern in an array pattern over one,
need the protocol's steps interleaved with that code, in the expression, not
before the statement (`pattern-program-iterable-default-refused`). A spread
of a `ReadonlyMap`'s `values()` needs the view's iteration, which a program's
object meeting it need not give as the host's collection does
(`spread-readonly-map-values-refused`). One in a conditional's branch needs the steps after
the test, in that branch alone (`blocker-spread-in-conditional`): a
declaration whose value is the conditional lowered into one branch per
outcome of its test, each with the test's narrowing. A generator needs a state-machine lowering, as
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
identity to its keys, which it does not (`invalid-object-growth-passed`; a
local annotated by a record of optional fields alone may hold a host object,
`growth-optional-accumulator-refused`). The design for it is a stable
location per object holding its extensible shape: the fields fixed at
allocation as a prefix, and a tail of added keys in the heap. Every
reference shares one invariant on the keys the tail may gain and the values
they may hold, and a write or a call invalidates each observation that a key
is absent. A constructor that calls a method on its instance before adding
its remaining fields needs the same. A key added to a class instance
whose prototype holds methods is copied with the prototype, but the copy is
typed as the record `mergeResult` gives, which states no method: it needs a
merge result at the instance's row. A write to an array at a key typed
`number` (`blocker-array-index-of-write`) needs the key related to the
array's length: a write at a key that is no array index (`indexOf`'s -1)
adds a property outside the array's store, and one past the length leaves
holes below it. Where the elements admit `undefined` (the ReScript
runtime's marker cache, `markers[depth] = m`), the holes are admitted, but
a write at a key that is no array index remains: the key it adds changes
the object's keys, which the calculus fixes at allocation (a fresh array's
own-key bound excludes it), and the property it overwrites may have a
narrower contract than the elements', which `numericOwn` bounds from above
only, so another reference may hold it at that contract
(`{ "-1": number }` beside `(number | string | undefined)[]`). Admitting it
needs the writable numeric index `Array<T>` declares, `[n: number]: T`,
read as a writable index is: every numeric property at the element
contract, and no own-key bound excluding numeric keys.

<a id="remaining-source-forms"></a>
**Remaining source forms.** A method call on a union of primitives,
which needs one callee contract its receiver meets. A plain write to a
member of a value whose type admits `undefined`, which needs the guard
reads, calls and updates have (`nullish-member-write-refused`). A contextual
closure parameter at an object literal's type with a method, which needs an
object contract stating the method (`closure-contextual-method-refused`). An
indexed access at an optional method an interface inherits, which needs
the method's receiver to be the type it is read from
(`computed-index-inherited-method-refused`). An imported constant
initialized by an array literal `as const`, which needs the declaration
reader to read its readonly tuple
(`literal-const-array-constant-value-import`). A source binder used both
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
other native errors, `hasOwnProperty("message")` and `Object.getPrototypeOf`. `JSON.stringify` of such an instance with a replacer naming `message`
needs it, since the parameter is a JSON value and an instance holding a
prototype is none (`error-subclass-json-replacer`). A promise about objects
decided by tests of an `unknown` needs the tests' object, which may be a
class instance or a host object, related to `Record<string, unknown>`
(`type-guard-object-refused`). A function type met with a record of
readonly fields needs a clause stating a callable with readonly fields
(`intersection-callable-readonly-refused`). `keyof T` and `T[K]` over a function's own binder need a row whose
meaning fixes a key set, which a value set does not. `o.m?.()` needs the receiver saved
across the test. `key in o` at a key the built-in prototypes hold needs those
prototypes' keys in the model.

<a id="regular-expressions-left"></a>
**Regular expressions left.** A
literal, `exec`, `test` and the string methods dispatching to a regex are
admitted ([regular expressions](docs/SOURCE-CONTRACTS.md#regular-expressions)).
Left: a replacement callback of a regex of the conservative shape or of a
`RegExp` annotation, whose argument count the shape does not fix, and of a
literal held in a binding, which needs the binding shown unshared until the
call (code holding the regex may change its pattern through `lastIndex`); a native regex of the conservative
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
  registration is refused (`collections-process`).

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
value itself passed on keeps `undefined`,
as in `xs[0] !== undefined && known.has(xs[0])`, which
needs a current-content fact about an element location, kept from the test
to the second read, as a field path would need one (`o.a !== undefined &&
f(o.a)` is refused the same way). A `flatMap` callback returning a
primitive or an array of primitives
needs a second signature quantifying a binder bounded by the primitives,
which the first does not use: neither the producer's instance of a member
read nor Lean's search for one assigns a binder no parameter of the
selected signature names. The design question is per-signature binders, or
bounds, in a prototype member's scheme. A closure passed to `map` over an array literal of
records with different members is read
at TypeScript's contextual records, `{ a: number; b?: undefined } |
{ a?: undefined; b: number }`; the producer claims it at the literals'
records `{ a: number } | { b: number }`, which state no absence of the
other's member and so are outside the parameter's records. A closure parameter at a generic declaration's anonymous record at an
instance with an optional member at a binder
(`{ v?: T }` of
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
`afterRelation` and `textWord`, and `docs.mts`'s `numbered`), and a `flatMap`
callback returning a string (`record-render.mts`'s `card`).

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
[Certified imports](docs/SOURCE-CONTRACTS.md#certified-imports) check an
imported function's code in the importer's run, at its effect-qualified
signature. `checkUnitJson_safe` keeps its statement.
Combining a certified import's conclusion with the importer's is left to
this theorem, plus the review obligation that the import binds the certified
unit's closure ([the linking obligation](docs/SOURCE-CONTRACTS.md#certified-imports)).

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
selection rules R1–R7: the structural engine's candidate selection is R1–R5,
and R6 and R7 are the [tag sets](docs/HOST-FAMILIES.md#tag-sets).

<a id="union-shapes-lemmas"></a>
**The lemmas in the repository.** The lemmas UNION-SHAPES states of its
rules (`str_excluded`, `str_included`, `views_exclude`,
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
it. The engine does not represent those dependencies: `demandPairsIn`
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
**Selection rules the data names.** Two candidates have no rule yet, ranked
with evidence sharing by what remains of `statementsOnPath`'s run: open
target arms, a record source
whose literal keys a target arm leaves open, which needs a fact that the
arm cannot hold the source's literal (an own-key bound excluding the key);
and shared literals, arms sharing a literal, which a second discriminant
key read by R3 may separate.

### The producer's speed

The producer is untrusted: its speed changes no verified outcome, only how
long a census and the suites take. [Where `lowerFile`'s time
goes](docs/deep-dives/lowerfile-time) measures the stages and names the
avoidable work.

**Entry environments.** A statement's evaluation records each
sub-expression's entry environment in a table. Environments are persistent
lists: an entry retains a pointer. Each entry also retains the queries read
before its observation, including claims used by refinement and callee
instances. A lookup reuses the environment while those dependencies and
the rigid bounds agree; a changed dependency causes another evaluation.
Each unchanged set of dependencies needs one evaluation. Explanation runs retain
full evaluation to preserve their observations.

**Effect rounds.** Functions are typed in source order. Each round raises
footprint assumptions and withdraws unsupported on-throw assumptions until
the module functions and recursive closures reach a fixpoint. A refusal
stops the round before later functions are typed. Entry-environment caches
belong to individual typing passes.

User CPU seconds on the saved 77-input corpus, measured 2026-10-30.
The parent is `adb122b4`, HEAD is `749f87a6`, and the working tree uses
source-order effect rounds with entry-environment caching. Each producer
is built separately; the parent and HEAD copies live under `.speed-corpus/`.
Measurements are serial, with rotating executable order and medians of
three runs; inputs below 0.1 s use fifteen runs. Qualified imports are
supplied only when the array in `qualified.json` is nonempty.

| Input | Parent | HEAD | Working tree |
| --- | ---: | ---: | ---: |
| `c101` | 29.138 | 13.617 | 14.316 |
| `c102` | 3.656 | 1.970 | 1.971 |
| `c103` | 3.059 | 2.369 | 2.675 |
| `c104` | 3.971 | 1.788 | 2.322 |
| `c105` | 0.384 | 0.243 | 0.239 |
| `m2` | 7.146 | 3.818 | 5.113 |
| `m3` | 0.299 | 0.471 | 0.296 |
| `m5` | 1.939 | 11.566 | 1.930 |
| `m8` | 0.190 | 0.300 | 0.174 |
| `m10` | 0.245 | 1.631 | 0.156 |
| `m12` | 2.285 | 0.444 | 0.738 |
| `m13` | 5.568 | 1.456 | 2.798 |
| `m17` | 0.195 | 0.278 | 0.150 |
| **Whole corpus (77 inputs)** | **72.176** | **51.336** | **44.535** |

Every working-tree median is within 10% of its parent median; the largest
increase is `c12`, 0.008378 → 0.009204 s (9.86%). The working tree matches
the parent's stdout, stderr and exit status on all 77 inputs. Parent,
HEAD and working tree each match 73 supplied `claims.json` references:
`c101`–`c103` contain pipeline-added module records, whereas the producer
emits an empty `modules` array. In `c104`, the reference's `typeParts`
entry at point `1333:1342:12`, start 1545, has no current path facts for
`term`; all three producers emit a refinement of its `k` path, with
corresponding type-table differences. References are unchanged. These
measurements cover direct producer invocations on saved inputs, including
empty stdout on refusals (2026-10-30).

Instrumented runs count entry-cache misses (cold misses plus invalidations),
invalidations and SCC rounds below. HEAD's counts include its source-order
fallback; the working tree uses one source-order round and zero SCC rounds
on each of these five refused inputs (2026-10-30).

| Input | HEAD misses | Working-tree misses | HEAD invalidations | Working-tree invalidations | HEAD SCC rounds |
| --- | ---: | ---: | ---: | ---: | ---: |
| `m5` | 9,117 | 424 | 1,831 | 85 | 53 |
| `m10` | 1,750 | 196 | 399 | 89 | 10 |
| `m3` | 379 | 214 | 56 | 31 | 8 |
| `m8` | 280 | 129 | 101 | 50 | 4 |
| `m17` | 702 | 271 | 125 | 43 | 21 |

In these measurements, SCC scheduling types later functions before
reaching a refusal, then repeats source-order inference to recover the
first refusal. Source-order rounds limit that work to the prefix ending
at the refusal. Successful inputs retain the entry-cache savings; their
timings also show the cost of whole-module effect rounds.

**Shared, numbered types.** The producer builds equal types separately and
compares them part by part: the deep dive measures 12.2 million union
comparisons on the `lowerFile` slice (2026-10-30). Interning types would give
each distinct type an identity; its gain is unmeasured.

Import planning drops one refused import per round: the deep dive measures
16 plans and 6 repeated module proposals, about 14.5 s (2026-10-30).
Reporting every refused import at once keeps the outcome only when no
refusal depends on another import being dropped, which that change has to
show.

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
