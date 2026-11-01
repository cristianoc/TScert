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
| Computed alias passed as a function | open: targeted slices `computed-types.mts#unionMembers,#distributed` pass the missing `node` field through [declaration-aware truthiness](docs/SOURCE-REWRITES.md#a-host-node-union-in-a-logical-operators-result) and reach the refusal of `context.alias` read as a function value for `computedAlias`; its contract declares a method with a receiver; 0 of 2 functions and 0 of 63 statements verify before and after, with no timeouts at a 300 s step limit on bases `1be3678a` before and `3b96f348` after (2026-11-01) | the method passed to `computedAlias` has a checked derivation or a documented equivalent rewrite |
| [Declaration collection phases](docs/drafts/collect-declarations-phases.md) | open: steps 1–4 extract independent term and identity helpers, final assembly, resolution and merged declaration groups, and compiler compatibility queries; named option interfaces and explicit equation owners, external-read depth, contextual binders and recursion paths supply their inputs; the file census verifies 506 of 4376 statements and 46 of 75 functions (2026-11-01); step 4 retains each function’s verified statements and all 2762 case outcomes; 70 source/option, 12 diagnostic and 18 compiler compatibility comparisons agree; steps 5–8 follow the draft | the draft’s phases have explicit inputs and owned state, with unchanged declaration documents, ordered callbacks and case outcomes |
| Stable host child reads across array bindings | closed: `blocker-round-host-member-after-call` verifies declaration resolution and array or tuple rest through the existing stable-member checks; the producer retains stable paths across array binding operations ([mechanism](docs/SOURCE-REWRITES.md#stable-compiler-children-across-array-bindings)); targeted slices `declaration-graph.mts#collectDeclarations` and `fragment-parse.mts#lowerFile` verify 0 of 2 functions and 0 of 3683 statements before and after on `1b29b7d8`: the former advances from missing `text` to `shadowing parameter 1`, while the latter retains its closure-expression claim at `[117316,117323)`; no timeouts (2026-11-01) | — |
| Investigation: mapped type result record | open: targeted slices `type-term.mts#typeTerm,#constructorForms` pass the optional host-list argument with a [saved list binding](docs/SOURCE-REWRITES.md#an-optional-host-list-tested-through-a-property-receiver) and reach the node-typing claim of `mapped`'s result record; 0 of 2 functions verify before and after, with 0 of 18 → 0 of 19 statements verified and no timeouts at a 300 s step limit on base `b3f431c3` (2026-10-31) | the result record's failed obligation is explained and has a checked derivation or a documented source rewrite |
| Investigation: computed reference result claim | open: targeted slices `type-probe.mts#nodeAt,#makeProbe` verify 0 of 2 → 1 of 2 functions and 0 of 206 → 10 of 208 statements, with no timeouts, on bases `f7de3845` before and `62ce8874` after (2026-11-01); `nodeAt` verifies through the [saved Node view](docs/SOURCE-REWRITES.md#host-member-reads-after-a-generic-guard), and `makeProbe` reaches the node-typing claim of `readReference(name, args, span)` at `[15385,15416)`, whose cause is unknown | the computed reference result claim has an explained cause and a checked derivation or a documented source rewrite |
| Decoder value widened to unknown | closed: `blocker-round-decoder-erased-assertion` verifies through [typed fresh decoder results](docs/SOURCE-REWRITES.md#a-flow-document-assembled-from-decoded-values); `source-flow.mts#decodeFlowDocument` constructs its result from decoded fields and returns its typed document | — |
| Investigation: flow node result record claim | open: targeted slices `source-flow.mts#decodeFlowDocument` and `pipeline/verify-source.mts#checkUnowned` verify 0 of 2 functions before and after the fresh-result repair on base `1be3678a`, with 0 of 186 → 0 of 134 statements verified and no timeouts at a 300 s step limit (2026-11-01); the decoder reaches the constructed node record's node-typing claim at `[23891,24071)`, whose cause is unknown; the caller retains its earlier `Math.round` overlay refusal | the constructed node record's claim has an explained cause and a checked derivation or a documented source rewrite |
| Investigation: refusalStatus completion claim | open: targeted slices `diagnostic.mts#readDiagnostic` and `pipeline/verify-source.mts#refusalStatus` verify 0 of 2 → 1 of 2 functions and 0 of 115 → 149 of 155 statements, with no timeouts, before on `1be3678a` and after on `16956d49` with the decoder repair (2026-11-01); `readDiagnostic` verifies through [fresh typed diagnostic variants](docs/SOURCE-REWRITES.md#a-decoders-result-asserted-through-unknown); `refusalStatus` refuses its completion claim at `[75,88)`, whose cause is unknown | the completion claim has an explained cause and a checked derivation or a documented source rewrite |
| Investigation: shadow signature parameter map claim | open: `blocker-gap-round-receiver-template` verifies through the producer's declaration-aware truthiness query; targeted slices `shadow-contracts.mts#print,#printSignature` advance from the receiver interpolation to the node-typing claim of `params.map((p, i) => …)` at `[4457,4519)` in `printSignature`; 0 of 2 functions and 0 of 78 statements verify before and after, with no timeouts on base `293ad7b1` (2026-10-31) | the parameter map has a checked typing derivation |
| Investigation: unchecked worker file-map closure claim | open: `invalid-async-object` verifies with the decoded result's lifetime `then` contract; targeted slice `unchecked.mts#check` advances from async resolution to the closure-expression claim of `[...roots].map((file) => path.relative(".", file))`; 0 of 1 functions and 0 of 42 statements verify before and after, with no timeouts (2026-10-31) | the file-map closure expression has a checked derivation |
| Investigation: decoded finding allocation claim | open: targeted slice `unchecked.mts#decodeResult` advances from async resolution to the node-typing claim of `{ file, line, column, kind, text, reason }`; 0 of 1 functions and 0 of 23 statements verify before and after, with no timeouts (2026-10-31) | the finding allocation has a checked derivation |
| Investigation: file-answer expression claim | open: `blocker-gap-round-cache-answer` verifies with the cache callback's [nullable writable answer contract](docs/SOURCE-REWRITES.md#a-cache-callbacks-nullable-answer-field); targeted slices `files.mts#realOf,#answerOf` advance from 0 of 2 functions and 0 of 14 statements verified to 1 of 2 functions and 7 of 14 statements; `realOf` verifies and `answerOf` reaches the node-typing claim at `[5851,5904)`, with no timeouts (2026-10-31) | the file-answer expression claim has a checked derivation |
| JSON serialization of mapped arrays | closed: `blocker-round-mapped-json` verifies with the [recursive JSON array contract](docs/SOURCE-CONTRACTS.md#json-and-error), which admits holes and `undefined` array elements; on base `62ce8874`, targeted slices `files.mts#direntsRead,#direntsOf` advance from 0 of 2 functions and 0 of 15 statements verified to 2 of 2 functions and 15 of 15 statements, with no timeouts (2026-11-01); root `undefined` and nested callable `toJSON` remain refused | — |
| Claim printer conversion domains | open: `blocker-round-unknown-string` verifies through [explicit primitive checks](docs/SOURCE-REWRITES.md#a-negative-object-guard-before-primitive-conversion); on base `8002b625`, targeted slices `claim-text.mts#bareAtomText,#atomText` advance from `String(atom)` at `[2122,2134)` to `String(atom.v)` at `[4112,4126)` in numeric-literal printing; 0 of 2 functions verify before and after, with 0 of 78 → 0 of 80 statements verified and no timeouts (2026-11-01). The finite-number test does not establish that the JSON field is primitive | object-valued literal conversion has checked effects or an equivalent source rewrite |
| Investigation: family-table closure expression claim | open: `blocker-gap-round-graph-find` verifies with the graph lookup's empty footprint retained at its field and supplied definition; targeted slices `host-families.mts#familyTable` and `declaration-graph.mts#collectDeclarations` verify 0 of 2 functions and 0 of 3238 statements before and after at `3bd318a3`, and 0 of 2 functions and 0 of 3241 statements on rebased `935f152d`, with no timeouts; `familyTable` passes the `find` callback's annotation obligation and reaches the closure-expression claim of `result` at `[25362,25368)`, while `collectDeclarations` retains missing field `text` (2026-10-31); isolated case `blocker-round-mapped-array-push` refuses the mapped result as a `push` receiver | the family-table closure expression claim has a checked derivation; the isolated mapped receiver has a checked derivation or a documented source rewrite |
| Investigation: claim printer primitive conversion | open: `blocker-gap-round-key-stringify` verifies through the [explicit missing-key text](docs/SOURCE-REWRITES.md#a-missing-field-key-printed-explicitly), with its original possibly absent serialization retained as a negative case; targeted slices `claim-text.mts#bareAtomText,#atomText` pass the `JSON.stringify(key)` obligation and reach the node-typing claim of `String(atom)`, with 0 of 2 functions and 0 of 78 statements verified; `liftLabels` retains its mapped callback’s [store-preserving contract](docs/SOURCE-REWRITES.md#mapped-arms-with-a-store-preserving-callback), and `blocker-gap-round-captured-arms-reduction-preserving` verifies while the unrestricted original is a negative case; targeted slices `claim-text.mts#liftLabels,#liftType` advance from the reduction’s `arms` read at `[22255,22259)` to `String(atom)` at `[2428,2440)`, with 0 of 2 functions verified and statement coverage 0 of 57 → 0 of 58; neither measurement has timeouts (2026-10-31); isolated case `blocker-round-unknown-string` refuses `String(value)` at `unknown` | the primitive conversion has a checked derivation; the isolated conversion is answered under the source-rewrite routes, including the effects of conversion hooks |
| Investigation: synthetic member array receiver | open: `blocker-round-mapped-array-push` verifies through an [explicit loop over a private snapshot](docs/SOURCE-REWRITES.md#mapping-a-private-snapshot-before-appending-to-its-result); `invalid-round-mapped-array-push` retains the shared-receiver refusal and its shrinking-callback counterexample under Node. Targeted slices `host-families.mts#familyTable` and `declaration-graph.mts#collectDeclarations` verify 0 of 2 functions before and after on base `5a9e8f70`, with statement coverage 0 of 3241 → 0 of 3242 and no timeouts at a 300 s step limit. `familyTable` advances from the mapped result at `[25362,25368)` to `per` in the synthetic member map at `[22904,22907)`; `collectDeclarations` retains `unsupported: shadowing parameter 1` (2026-11-01) | the synthetic member map receiver has a checked derivation or a documented source rewrite |
| Family activation: record at an index signature | open: `blocker-gap-round-unknown-spread` verifies through the [module export boundary](docs/SOURCE-REWRITES.md#a-loaded-modules-own-exports), with the unrestricted spread retained as a negative case; targeted slices `family-activation.mts#checkedGuards,#activeGuards` advance from the spread's node-typing claim to a record at an index signature, with 0 of 2 functions verified and statement coverage 0 of 174 → 0 of 172, no timeouts (2026-10-31) | the record establishes its index-signature contract |
| Named records serialized as JSON | done: `named-implicit-index` verifies with the [complete key contracts retained](docs/SOURCE-REWRITES.md#a-named-record-widened-to-a-json-dictionary); the unsafe open-record conversion is `invalid-named-implicit-index`, whose extra string-valued key is observed under Node; targeted slices `files.mts#entriesRead,#entriesOf` and `family-activation.mts#checkedGuards,#activeGuards` verify 0 → 4 of 4 functions and 0 → 198 of 198 statements, with no timeouts (2026-11-01) | the constructed records retain their index-signature contracts through serialization |
| Array presence at the module filtering loop exit | open: targeted slices `fragment-parse.mts#lowerFile,#parseFile` advance from the conditional mapped array’s `filter` receiver to the later `lowered.map`; its claimed receiver retains the initial sparse alternative; 0 of 2 functions and 0 of 747 statements verify before and after, with no timeouts (2026-10-31–2026-11-01) | the final projection has a checked receiver through a loop-exit fact or an equivalent source rewrite |
| Investigation: mixed compiler-node and record method invocation | open: `blocker-every-mixed-closure` reaches the node-typing claim of `node.getSourceFile()` with its named callback's declared leading parameter types; the parameter admits a compiler node or a record holding the method as a field (2026-10-31) | the mixed method invocation has a checked typing derivation |
| Census refusal examples (043267592814) | open: five supplied causes cover 1997 statements in 23 functions; `blocker-census-effect-map-result` verifies through the [sparse receiver of native `join`](docs/SOURCE-CONTRACTS.md#prototype-contracts), with `invalid-sparse-join-coercion` retaining the conversion-bound refusal; targeted slices `claim-text.mts#atomText,#bareAtomText` advance from `atom.args.map((t) => typeText(t, state))` to the node-typing claim of `JSON.stringify(key)`, with 0 of 2 functions and 0 of 78 statements verified before and after; the full nested-spread example verifies with its input records stated as JSON data and fresh mapped records allocated at their full writable contract; the narrower inferred allocation stays a negative case; `blocker-census-spread-map-records` verifies through a checked readonly array view, and `invalid-spread-map-records` refuses a shrinking callback; `blocker-gap-round-optional-parameter` verifies with the [readonly field contract of `firstOptional`](docs/SOURCE-REWRITES.md#readonly-fields-in-the-optional-parameter-helper), and `blocker-gap-round-optional-parameter-writable` retains the writable-field refusal; targeted slices `fragment-classes.mts#classBody,#classStmt` advance from `firstOptional(all)` to an incoming-edge obligation in the `baseProto` record expression, with 0 of 2 slices and 0 of 393 statements verified before and after, no timeouts (2026-10-31); `invalid-in-union-read` verifies with the named part's absent spread value stated, and `invalid-in-union-part` retains the original missing-field refusal; targeted slices `fragment-parts.mts#mapExprParts,#deepPartMap` advance from missing `spread` to a source-expression typing obligation, with 0 of 2 functions and 0 of 46 statements verified before and after; `blocker-gap-round-parent-initializer` verifies through the [compiler initializer kinds](docs/SOURCE-REWRITES.md#a-compiler-nodes-initializer-read-through-its-parent), and `blocker-gap-round-parent-initializer-open-node` verifies through the same kind tests, with the open-node `in` form recorded under [constructs avoided](docs/SOURCE-REWRITES.md#an-initializer-read-after-an-in-test-on-an-open-compiler-node); targeted slices `written-applications.mts#isInitializer,#writtenApplications` verify 1 of 2 functions and 2 of 315 statements before and after: `isInitializer` verifies, while `writtenApplications` retains a closure signature outside its source annotation at `[25842,25863)`; no timeouts (2026-10-31); targeted slices `written-applications.mts#writtenApplications` and `declaration-graph.mts#collectDeclarations` verify 0 of 2 functions and 0 of 3251 statements before and after: the former advances from missing `initializer` to a closure signature outside its source annotation in `level => level.length`, while the latter retains missing `text`; no timeout in either measurement (2026-10-31); targeted slices `declaration-graph.mts#selectGlobal,#collectDeclarations` verify 0 of 2 functions and 0 of 3290 statements before and after: `selectGlobal` passes the nested-spread callback parameter and reaches the return contract of a scheme-binder allocation, while `collectDeclarations` retains its `capturedAt` initialization refusal; no timeout in either measurement (2026-10-31); `blocker-gap-round-scheme-binder-map` verifies through the existing allocation checks with complete field hints from record intersections; `invalid-gap-round-scheme-binder-map` retains the refusal to widen an already allocated binder; targeted slices `declaration-graph.mts#selectGlobal,#collectDeclarations` verify 0 of 2 functions and 0 of 3290 statements before and after: `selectGlobal` advances from the scheme-binder return contract at `[28522,28588)` to the node-typing claim of `forms(overload, key, what, entry)` at `[28645,28678)`, while `collectDeclarations` retains missing field `text` at `[57387,57407)`; no timeout in either measurement (2026-10-31); `blocker-census-annotated-node-union` verifies through the existing closure checks, with the producer retaining a sufficient callback claim and its per-signature body claims; its negative result-contract case and forged-claim controls guard the boundary; targeted slices `declaration-graph.mts#collect,#collectDeclarations` verify 0 of 2 functions and 0 of 3317 statements before and after: `collect` advances past the per-arrow body-claim mismatch to a closure signature outside its annotation in `nativeFields.map`, while `collectDeclarations` retains its possible read of `capturedAt` before initialization (2026-10-31); `blocker-gap-round-native-method-map` verifies through [writable field annotations](docs/SOURCE-REWRITES.md#native-method-maps-with-writable-field-contracts); `blocker-gap-round-native-method-map-inferred` verifies the same explicit form, with [inferred writable fields avoided](docs/SOURCE-REWRITES.md#inferred-writable-fields-in-native-method-maps) and no remaining supplied census sites; targeted slices `declaration-graph.mts#collect,#collectDeclarations` verify 0 of 2 functions before and after, with statement coverage 0 of 3317 → 0 of 3320 on base `ee67919f`; `collect` advances from the native method map’s closure signature to a closure-expression claim at `[33912,33916)`, while `collectDeclarations` retains missing field `text`; no timeouts (2026-10-31); `blocker-gap-round-locations-map` verifies through the [JSON location result contract](docs/SOURCE-REWRITES.md#declaration-locations-retained-as-json-data), with its unknown-result negative and unrestricted-callback gap retained; targeted slices `type-probe.mts#makeProbe` and `declaration-graph.mts#collectDeclarations` verify 0 of 2 functions and 0 of 3138 statements before and after: `makeProbe` advances from the declaration-map closure claim to the node-typing claim of `n.end` in `nodeAt`, while `collectDeclarations` retains missing field `text`; no timeouts (2026-10-31); `blocker-round-mapped-array-some` verifies through the [sparse receiver contract of native `some`](docs/SOURCE-CONTRACTS.md#prototype-contracts), with `invalid-some-sparse-callback` refusing an unchecked read through its sparse third callback argument (TypeError under Node); targeted slices `declaration-graph.mts#collect,#collectDeclarations` verify 0 of 2 functions and 0 of 3323 statements before and after on base `d6675e26`: `collect` advances from `read.some` at `[33912,33916)` to `nativeFields.map` at `[46984,46996)`, while `collectDeclarations` advances from missing field `text` at `[57387,57407)` to `shadowing parameter 1`; no timeouts (2026-11-01); `blocker-round-inferred-map-result` is a negative case: a shrinking callback leaves a hole in its `Form[]` result, demonstrated under Node (2026-11-01; [unsafe inferred map result](docs/SOURCE-REWRITES.md#an-inferred-map-result-with-an-unrestricted-callback)); `blocker-round-resolved-overlay-map-result` verifies with the [consumed overlay fields](docs/SOURCE-REWRITES.md#overlay-fields-consumed-by-the-signature-helper) of the signature helper in `selectGlobal`; targeted slices `declaration-graph.mts#selectGlobal,#collectDeclarations` verify 0 of 2 functions and 0 of 3296 statements before and after on `a92cc758`: `selectGlobal` changes its first refusal from the helper call at `[28693,28726)` to the allocation of a scheme record at `[28518,28665)`, while `collectDeclarations` retains `shadowing parameter 1`; no timeouts (2026-11-01); `blocker-round-mapped-filter-length` verifies with the [mapped binder records’ writable contract](docs/SOURCE-REWRITES.md#mapped-binder-records-with-their-writable-contract); targeted slices `written-applications.mts#writtenApplications` and `declaration-graph.mts#collectDeclarations` verify 0 of 2 functions and 0 of 3254 statements before and after on base `a92cc758`: the former passes the mapped-record filter and reaches the callback signature of `t => childParameters(t).length` at `[15098,15128)`, while the latter retains `shadowing parameter 1`; no timeouts (2026-11-01) | each cause has a checked resolution under the source-rewrite routes, including checked receiver contracts and callback signatures for the three isolated mapped-array cases, or documented source rewrites |
| [Investigation: does the model's error lacking `stack` matter](docs/SOURCE-ELABORATION.md#in) | open: an error the program builds owns `stack`, which the model's error does not hold, so `"stack" in e` answers `false` in the model and `true` in JavaScript where `e`'s type leaves `stack` unstated, as every type an error meets does; both answers are checked; no program is known whose result differs (2026-10-27) | a proof that the differing answer changes no checked outcome, or a program it changes |
| Census refusal examples (f502699ca098) | open: the five largest causes after splitting the supplied first refusals cover 5989 statements in 71 functions; `blocker-census-rest-result` verifies by checked result inference for array-rest closures; the Set-copy cause is resolved by retaining the host `Set` type and admitting its union with an array in one constructor form; `blocker-census-options-default` verifies through the existing record and binding checks; targeted slices `declaration-graph.mts#collectDeclarations` and `fragment-parse.mts#lowerFile` verify 0 of 2 functions and 0 of 3680 statements before and after: the former advances past `tsconfigPath` to a possible read of `capturedAt` before initialization, the latter retains its refusal of a closure collecting a rest array without a result annotation; `blocker-census-import-guard-call` verifies with the [exact-kind import guard](docs/SOURCE-REWRITES.md#a-type-node-or-an-import-recognised-by-a-guard-accepting-another-kind); targeted slices `fragment-statements.mts#readScope,#readCannotThrow` advance from the import call to the `for-of-iterator` claim of `for (const f of mentions[i] ?? [])` in `functionPlacement`, with 0 of 2 slices and 0 of 42 statements verified before and after; `blocker-flat-map-narrow-field` verifies with the fresh array's writable element contract stated at allocation, and `invalid-flat-map-narrow-field` retains the original widening refusal; targeted slices `fragment-expressions.mts#expr,#binary` advance from array widening to the node-typing claim of `gate.expr(target)` in the `Object.assign` branch, with 0 of 2 slices and 0 of 459 statements verified before and after (2026-10-31); `blocker-gap-round-assign-target` verifies through a [direct check of the destructured target](docs/SOURCE-REWRITES.md#an-array-patterns-first-element-after-a-length-test); `blocker-gap-round-assign-target-length-only` verifies in the [equivalent checked form](docs/SOURCE-REWRITES.md#an-array-target-justified-only-by-length), with targeted slices `fragment-expressions.mts#expr,#binary` retaining the callable-return node-typing refusal at `[27877,28021)` and 0 of 2 functions and 0 of 461 statements verified before and after, no timeouts (2026-10-31); targeted slices `fragment-expressions.mts#expr,#binary` advance past `gate.expr(target)` to the callable branch’s `withValue` return object at `[27877,28021)`, with 0 of 2 slices verified and statement coverage 0 of 459 → 0 of 461, no timeouts (2026-10-31); `blocker-gap-round-early-capture` verifies with the outer arrow’s returned-function type stated; targeted slices `declaration-graph.mts#collectDeclarations` and `fragment-parse.mts#lowerFile` verify 0 of 2 functions and 0 of 3680 statements before and after: the former advances from `capturedAt` initialization to missing field `text`, while the latter retains its closure-signature body-lowering refusal; neither measurement times out (2026-10-31) | each cause has a checked resolution under the source-rewrite routes |
| [Coverage of the front end](#the-front-ends-own-functions) | open: `blocker-gap-round-visitor-effect` verifies with the [forward helper’s store-preserving contract](docs/SOURCE-REWRITES.md#a-forward-visitor-helper-with-a-store-preserving-contract); targeted slices `fragment-expressions.mts#letWrites,#localValues` verify 0 → 2 of 2 functions and 0 → 59 of 59 statements, with no timeouts; `blocker-gap-round-visitor-effect-unstated` verifies with the same written contract, whose erased runtime code is identical to the unstated form ([construct avoided](docs/SOURCE-REWRITES.md#a-forward-captured-helper-without-a-stated-effect)); targeted slices `fragment-expressions.mts#letWrites,#localValues` retain 2 of 2 functions and 59 of 59 statements verified before and after, with no timeouts, on bases `287c9361` → `1e58e428` (2026-10-31); `blocker-gap-round-nested-filter` verifies with the [primitive dictionary and interface Map contracts retained](docs/SOURCE-REWRITES.md#a-primitive-overlay-enumerated-through-an-open-record); targeted slices `array-prototype.mts#reviewedEntries,#mergeRefusal` advance past the closure-signature refusal and interface-map spread to node-typing claims of the `footprintEffect` object in module initialization and `...binders.entries()`, respectively; 0 of 2 functions and 0 of 120 statements verify before and after, with no timeouts (2026-10-31); targeted slices `fragment-statements.mts#functionPlacement,#hoisting` verify 0 → 1 of 2 functions and 0 → 35 of 58 statements with nullish fallbacks selecting the existing union iteration contract; `functionPlacement` verifies, and `hoisting` reaches the node-typing claim of `...placed.keys()` (2026-10-31); targeted slices `computed-types.mts#parameterMembers` and `unchecked.mts#unstated,#boundary` verify 0 → 3 of 3 functions and 0 → 39 of 39 statements with the producer retaining spread operands whose elements fit and preserving non-array iterator contracts (2026-10-31); the census of `tools/` at a 300 s step limit on main commits `8ec44f16ba8d` → `b644972daee6` verifies 382 → 380 of 637 functions and 3754 of 15205 → 3965 of 15224 statements (24.7% → 26.0%), with 0 → 0 stage timeouts (2026-10-31 → 2026-11-01); seven functions gain verification: `diagnostic.mts#diagnosticOutcome,#span,#sourceMap,#directJudgment,#diagnosticNode,#readDiagnostic` and `type-probe.mts#nodeAt`; nine functions lose verification at source-effect refusals: `named-record.mts#termText,#termsText,#optionalTermText,#fieldText,#indexText,#staticText,#binderText,#effectText,#kindsText`; targeted slices of those nine functions on base `d6e14138` verify 0 → 9 functions and 0 → 28 statements with declaration-aware array presence comparison, with no timeouts (2026-11-01); the slice of `lowerFile` alone on an empty stage store, refused at a closure's signature: 239 s at ee0ed0e5, 108 s with the producer's joins indexed by name and sorted unions merged, the producer's CPU 184.9 → 64.1 s; [where its time goes](docs/deep-dives/lowerfile-time) (2026-10-30); 24 of 24 functions of `dev/`, 9 of 13 of `tests/` and 3 of 37 of `pipeline/` (2026-10-19, 60 s step limit); the [negative-pattern audit](cases-report.md#negatives-in-tools) records source-contract repairs and their slice outcomes ; targeted compiler-API slices at 300 s: nine missing-member gates advance to further refusals, with 0 of 10 selected slices verified before and after and no timeout (2026-10-25); targeted slices `type-term.mts#readTypeTerm,#typeTerm` report their first refusal at the node-typing claim of `quantified(scope, node.typeParameters, node.parameters, node.type, node, span)` in place of the alias-scope binding annotation, with 0 of 2 functions and 0 of 150 statements verified before and after and no timeout (2026-10-31) | every function of `tools/`, `dev/`, `tests/` and `pipeline/` verifies or is refused by a stated restriction |
| [The producer's speed](#the-producers-speed) | entry-environment caching with source-order effect rounds: 77-input corpus user CPU 72.18 → 51.34 → 44.53 s (parent → 749f87a → working tree); every fixed median within 10% of parent; 77 of 77 results identical to parent, 73 of 77 outputs to supplied references; type interning open (2026-10-30) | repeated typing and structural type comparison are reduced, with the producer's output unchanged |
| Investigation: `Examples run under Node` fails within `make test` | open: under a load average of about 14, the suite failed in three runs of `make test` on 2026-10-30 and passed when run alone and on each rerun; the cause is not established | the cause, and the suite passing under load |
| Investigation: a loop update reading a field of a field after a nested discriminant test | open: records `H1 \| H2`, a loop updating `h.n.up` with `h.n.k === "r"` tested inside an `h.k === "one"` branch, is refused at the update even when every implied path witness is kept (2026-10-30); the cause is not established | the cause, and a case showing it |
| [Correctness specifications](docs/drafts/correctness-specs.md) | open: design approved (2026-10-28) | the clamp, binary-search and JSON round-trip cases verify with their contracts, and their negative controls are refused |
| [Canonical heap knowledge](docs/drafts/heap-knowledge-canonical.md) | partial: value sets, links and facts have normal forms proved to hold exactly where the raw knowledge does, idempotent and unique, and separation a compacted form proved to hold exactly where it does, idempotent and bounded; points other than cuts store the normal form, and so do node outputs; nodes and edges read stored knowledge by alias class; the census of `tools/`, d578dd8 → 8092044, the same 227 of 519 functions verified, search CPU 858.6 → 387.3 s, check CPU 248.0 → 79.4 s, peak memory of one run 10.6 → 1.6 GB (2026-10-28) ([stored knowledge](docs/PROGRAM-TYPING.md#stored-knowledge-and-how-it-is-read)); the evidence writes each value set once; b59096f → this pass, generated workloads at 16 tests, evidence disjunction 319.3 → 3.2 MB, repeated 93.2 → 1.9 MB, guards 1.38 → 0.88 MB, fields 45.8 → 2.4 MB, and census slices `moduleFunction`, `resolve`, `inertRead`, `confined`, `collect` and `closeStatements` together, search CPU 269 → 72 s, check CPU 54 → 11 s, `moduleFunction` evidence 300.7 → 3.8 MB; search CPU on `collect` 1.55 → 1.89 s and `closeStatements` 1.13 → 1.59 s, and on 32 repeated tests 40.2 → 47.5 s (2026-10-28); open: one type context per type rather than per node, the evidence's normal-form validator, the workloads as pipeline cases, disjunction at 32 tests within the step limit, and guards' evidence exponent (2.35 between 16 and 32 tests) | the draft's §9 measurements hold |
| [The type-decision procedure](docs/drafts/subtype-decision.md) | done: the census of 6a3a864, every stage's producing execution, 4d29662 → 6a3a864, search CPU 5,385.9 → 778.7 s and check CPU 70.5 → 52.2 s, the slowest search 247 → 26.0 s (`fragment-statements.mts#abrupt`), no function lost (2026-10-24); design reviewed (2026-10-23); census slices on executed stages, median of 3 serial runs, before (c71c404) → after step 1, instantiation by inclusion: search CPU `forOfPattern` 115.0→34.7 s, `pattern` 15.1→7.5, `moduleFunction` 29.1→26.1, `inertRead` 21.1→20.8, `resolve` 20.4→20.0, `patternDefaults` 0.8→0.6, `collect` 1.7→1.6, `closeStatements` 1.2→1.2; check CPU 5.0→4.6, 3.6→3.6, 3.4→3.3, 0.4→0.4, 1.0→1.0, 0.7→0.7; evidence `moduleFunction` 5.2→5.1 MB, the others unchanged; outcomes unchanged; synthetic `Node` widths 5/30/50/87/136, elapsed 0.88/7.55/18.6/54.6/137.6→0.64/2.32/4.89/12.24/28.76 s (2026-10-23); step 2, narrowing's candidates unfolded once and search's slice memo: search CPU `moduleFunction` 26.1→20.1 s, `inertRead` 20.8→15.2, `resolve` 20.0→14.6, `forOfPattern` 34.7→30.6, `pattern` 7.5→6.7, the other three unchanged; check CPU 4.6→4.3, 3.6→3.2, 3.3→3.0; evidence and outcomes unchanged; the width series unchanged (2026-10-23); step 3, the synthesized type first among the pool's: search CPU `moduleFunction` 20.1→18.7 s, `inertRead` 15.2→13.9, `resolve` 14.6→13.3, `forOfPattern` 30.6→30.2, `pattern` 6.7→6.6, the other three unchanged; check CPU 4.3→4.2, 3.2→3.2, 3.0→2.9; evidence, outcomes and the width series unchanged (2026-10-23); step 4, a source clause the target holds covered as it is (`Same`), label containment linear, renamed-member pairs once: search CPU `moduleFunction` 18.7→12.9 s, `inertRead` 13.9→10.0, `resolve` 13.3→9.4, `forOfPattern` 30.2→16.1, `pattern` 6.6→5.0, the other three unchanged; check CPU 4.2→3.2, 3.2→2.7, 2.9→2.5, `collect` 1.0→0.9; evidence and outcomes unchanged; widths 5/30/50/87/136 0.61/2.26/4.84/12.12/28.38→0.59/1.30/2.13/4.51/8.97 s (2026-10-23); step 5, search's candidate types deduplicated by hash: search CPU `moduleFunction` 12.9→10.1 s, `inertRead` 10.0→7.6, `resolve` 9.4→7.0, `forOfPattern` 16.1→11.6, `pattern` 5.0→3.7, the other three unchanged; check CPU, evidence, outcomes and the width series unchanged (2026-10-23); step 6, search checks a rule's parts before comparing its result with the claim, and finds a source clause among the target's by bucket: search CPU `moduleFunction` 10.1→9.9 s, `inertRead` 7.6→7.3, `resolve` 7.0→6.8, `forOfPattern` 11.6→9.6, `pattern` 3.7→3.4, the other three unchanged; check CPU, evidence and outcomes unchanged; widths 5/30/50/87/136 0.57/1.26/2.10/4.45/8.93→0.56/1.10/1.66/3.26/6.36 s (2026-10-23); step 7, a member test's arm reads only the candidates of its key: search CPU `moduleFunction` 9.9→9.0 s, `inertRead` 7.3→6.6, `resolve` 6.8→6.0, `forOfPattern` 9.6→9.0, `pattern` 3.4→3.3; check CPU 3.2→2.9, 2.7→2.5, 2.5→2.3; the other three, evidence, outcomes and the width series unchanged (2026-10-23); after the review's repairs (unspecialized index definitions, a variadic call's rest arguments before its result), against step 7: search CPU `moduleFunction` 9.0→9.1 s, `inertRead` 6.6→6.6, `resolve` 6.0→6.1, `forOfPattern` 9.0→9.2, `pattern` 3.3→3.4; check CPU 2.9→3.0, 2.5→2.6, 2.3→2.3, `collect` 0.9→1.0; widths 5/30/50/87/136 0.56/1.08/1.65/3.24/6.31→0.57/1.10/1.69/3.33/6.46 s; evidence and outcomes unchanged (2026-10-24); step 8, no table grown from or expanded at a pair no valid family covers: search CPU `moduleFunction` 9.1→8.5 s, `inertRead` 6.6→5.9, `resolve` 6.1→5.4, `forOfPattern` 9.2→8.3, `pattern` 3.4→3.3, the other three unchanged; check CPU unchanged within 0.1 s; evidence and outcomes unchanged; widths 0.57/1.10/1.69/3.33/6.46→0.56/1.05/1.44/2.71/5.32 s; sampled time outside the front end (reading the fragment and the claims, lowering and freezing them) and the evidence write, median of 3, at widths 5/30/87/136 0.11/0.26/1.03/2.35 s; of 1,214 reruns without selection over the seven slices and the width-136 input none established a comparison (2026-10-24); step 9, clause membership by an index under the label hash, in search and in the validator, which reads a pair's target clauses once, as opaque rows do: search CPU `moduleFunction` 8.5→8.4 s, `inertRead` 5.9→6.0, `resolve` 5.4→5.5, `forOfPattern` 8.3→7.0, `pattern` 3.3→3.2, the other three unchanged; check CPU `moduleFunction` 3.1→2.8, `inertRead` 2.6→2.5, `resolve` 2.4→2.3, the others unchanged; evidence bytes and outcomes unchanged; widths 5/30/50/87/136 0.56/1.05/1.44/2.71/5.32→0.53/0.94/1.26/2.14/3.53 s; sampled time outside the front end and the evidence write at widths 5/30/87/136 0.11/0.26/1.03/2.35→0.12/0.22/0.65/1.17 s, within the width criterion (2026-10-24); step 10, the row-matched instance computed when the engine reaches it and reading no row where a target signature has no scheme signature of its effect and arity: search CPU `moduleFunction` 8.4→6.9 s, `inertRead` 6.0→5.5, `resolve` 5.5→5.0, `forOfPattern` 7.0→5.7, `pattern` 3.2→2.9, `patternDefaults` 0.6→0.5, the other two unchanged; check CPU unchanged within 0.1 s; evidence bytes and outcomes unchanged; widths 0.53/0.94/1.26/2.14/3.53→0.56/0.94/1.29/2.08/3.41 s; outside the front end and the evidence write 0.12/0.22/0.65/1.17→0.11/0.21/0.60/1.04 s (2026-10-24); step 11, search's checks of its graphs and codes answer the inclusions it established from their proofs: search CPU `moduleFunction` 6.9→6.5 s, `inertRead` 5.5→5.4, `resolve` 5.0→4.9, `forOfPattern` 5.7→5.4, `pattern` 2.9→2.8, the other three unchanged; check CPU, evidence bytes and outcomes unchanged; widths 0.56/0.94/1.29/2.08/3.41→0.53/0.93/1.25/1.99/3.20 s; outside the front end and the evidence write 0.11/0.21/0.60/1.04→0.10/0.18/0.54/0.89 s (2026-10-24); step 12, a node's known derivation found by a key of its claim: search CPU `moduleFunction` 6.5→6.1 s, `inertRead` 5.4→5.0, `resolve` 4.9→4.5, `forOfPattern` 5.4→5.0, `pattern` 2.8→2.5, `collect` 1.6→1.5, `closeStatements` 1.2→1.1, `patternDefaults` unchanged; check CPU, evidence bytes and outcomes unchanged; widths 0.53/0.93/1.25/1.99/3.20→0.51/0.90/1.18/2.00/3.22 s; outside the front end and the evidence write 0.10/0.18/0.54/0.89→0.10/0.18/0.53/0.87 s (2026-10-24); step 13, discovery computes a row's demand once and reads each row's target clauses with their index once: search CPU `moduleFunction` 6.1→6.0 s, `inertRead` 5.0→4.9, `resolve` 4.5→4.4, `forOfPattern` 5.0→4.8, the other four unchanged within 0.1 s; check CPU, evidence bytes and outcomes unchanged; widths 0.51/0.90/1.18/2.00/3.22→0.52/0.92/1.17/1.85/2.88 s; outside the front end and the evidence write 0.10/0.18/0.53/0.87→0.10/0.16/0.41/0.61 s (2026-10-24); step 14, search's comparisons not redone without selection, every check keeping the rerun: search CPU `moduleFunction` 6.0→5.8 s, `inertRead` 4.9→4.8, `resolve` 4.4→4.3, `forOfPattern` 4.8→4.5, `pattern` 2.5→2.4, the other three unchanged; check CPU, evidence bytes and outcomes unchanged, every pipeline case as expected; widths 0.52/0.92/1.17/1.85/2.88→0.52/0.86/1.06/1.63/2.49 s; outside the front end and the evidence write 0.10/0.16/0.41/0.61→0.08/0.11/0.21/0.27 s (2026-10-24); step 15, an edge's unsatisfiable context decided reading each slot's labels until one has a clause: search CPU `moduleFunction` 5.8→5.3 s, `inertRead` 4.8→4.4, `resolve` 4.3→3.9, `forOfPattern` 4.5→4.3, `pattern` 2.4→2.3, `collect` 1.6→1.5, `closeStatements` 1.2→1.1, `patternDefaults` unchanged; check CPU `moduleFunction` 2.9→2.7, `inertRead` 2.5→2.4, `resolve` 2.3→2.2, the others unchanged; evidence bytes and outcomes unchanged; widths 0.52/0.86/1.06/1.63/2.49→0.52/0.85/1.04/1.62/2.46 s; outside the front end and the evidence write unchanged (2026-10-24); step 16, a graph check computes each member-test field slice its yields read once: search CPU `moduleFunction` 5.3→4.8 s, `inertRead` 4.4→3.9, `resolve` 3.9→3.5, `forOfPattern` 4.3→4.1, the other four unchanged; check CPU `moduleFunction` 2.7→2.6, `inertRead` 2.4→2.2, `resolve` 2.2→2.0, the others unchanged; evidence bytes and outcomes unchanged; widths 0.52/0.85/1.04/1.62/2.46→0.50/0.85/1.08/1.58/2.46 s; outside the front end and the evidence write 0.08/0.11/0.21/0.27→0.08/0.11/0.21/0.28 s (2026-10-24) | the eight slices and the width series meet the design's expected costs, each step measured |
| [The type-decision procedure's remaining steps](docs/drafts/subtype-decision.md) | open: the draft's remaining steps, each measured on `moduleFunction`'s sampled time outside input preparation (2.17 s): interning labels 1.11 s, a checker memo 0.31 s, the final check reading search's proved inclusions 0.33 s, a candidate index, hashed kernel lookups and a request-wide demand memo at most 1–5% each; the `Clauses` rule, the completeness theorems of the selected search and discovery, deleting the check's rerun and coverage by assumption carry no measured cost (2026-10-24) | each remaining step lands with its measurement, or is closed as not worth its cost |
| [Decoders' dictionary reads](#decoders-dictionary-reads) | open: in `calculus` 12 of 15 functions verify; `decodeTerm`, `decodeCode` and `termsOf` verify in 10.0 s of evidence search with candidate selection and the answered requests threaded through the document's search, 25.2 s without any reuse (user time, median of 3, 2026-10-19) | the decoders of `calculus`/`control-flow` verify in their modules within the limit |
| [The search of `protocolPattern`](#fragment-statements-search-meets) | done: in the census of 6a3a864 the slice `protocolPattern` and `patternStmt` share searches in 25.7 s of CPU, `abrupt`'s in 26.0 s (2026-10-24); 73 s of CPU alone on dca7c93's artifacts; in the census of both slices at a 600 s limit each search takes 73 s (2026-10-22); in the census of 4d29662 the search of `patternStmt`'s and `abrupt`'s slices takes 247 s of CPU each and of `forOfPattern`'s 123 s, together 52% of the census's executed search CPU, each ending in the refusal of a source expression obligation (2026-10-23) | `fragment-statements.mts#protocolPattern` and `#patternStmt` finish their search within 30 s alone |
| [The sync API's checking wrapper](#sync-api-checking-wrapper) | open | `make suite` runs the front end's sync-API calls through the wrapper C5 describes |
| [The compiler API's full shape check](#compiler-api-shape-check) | open | C3 checks every member and child kind over the corpus it names, the absent required members exactly the corrections |
| [Slices of the value universe](#universe-slices) | partial: a tag test on `unknown` keeps the kinds it does not contradict, proved (`in-unknown-object`); open: the negative `Array.isArray` slice, the meet of a type parameter with `unknown`, and the guards over `unknown` | `typeof v === "object" && v !== null` narrows `unknown`, and the guards over `unknown` promise what their tests establish |
| [A key found on an open object](#key-on-open-object) | partial: the read verifies as an open read, `%Read:k%` at `unknown`, under the open-read restriction, an assumption for the owner's review, on an object no type states the key of (`blocker-in-name-object`) and where a passed `in` test makes the read syntactically eligible on a union with an arm stating no key, at `body` and `type` only on receivers each arm of which states the key or is of the host package (`compiler-api-in-union-read`); open: the read as the model's own, with the lookup invariant proved | `if (typeof v === "object" && v !== null && "k" in v) return v.k` verifies, with the lookup invariant proved |
| [Guard overloads beyond `filter`'s](#guard-overloads) | partial: a guard read as a value meets `filter`'s guard overload and `find`'s at a footprint keeping array stores (`filter-guard-value`, `blocker-compiler-api-filter-guard-element`), and a guard closure meets `find`'s by its promise signature at its body's footprint (`blocker-compiler-api-find-promise`); `every` at a guard promising `string`, `number` or `boolean` gives [the elements fact](docs/FOOTPRINTS.md#the-elements-fact), which `map` relies on within one expression (`blocker-every-promise`, `every-elements-map-join`); open: the predicates excluding null or undefined, and the other natives at the fact; `blocker-round-every-map-narrowing` verifies by [stating the formatting callback parameter at `string | null`](docs/SOURCE-REWRITES.md#a-formatting-callback-narrowed-by-an-earlier-every-statement), an erased annotation avoiding reliance on the elements fact across a statement; targeted slices `shadow-contracts.mts#print,#printSignature`: 0 → 2 functions and 0 → 78 statements verified, no timeouts (2026-11-01) | `shadow-contracts.mts`'s `print`, which reads its array at `string[]` after `every` answers `true` at a guard, verifies; the formatting callback verifies at its nullable parameter contract |
| Investigation: the elements fact past a statement | cause unknown: the atom `every` adds reaches the branch on its result but not the `map` after it where the test is a statement (`every-elements-saved`, a constant; `every-elements-negated`, `if (!…) return`) | both cases verify |
| [A conditional's join past an arm's read](#conditional-optional-field) | closed by avoidance: `blocker-round-conditional-record-join` verifies with the [explicit receiver test](docs/SOURCE-REWRITES.md#an-optional-chain-result-tested-before-a-conditional-record) and the existing preservation contract of `Gate.span`; `invalid-round-conditional-record-call` refuses a callback that clears the field, shown under Node; targeted slices `fragment-classes.mts#classBody,#classStmt` advance from the incoming-edge refusal to the prototype-binding allocation's node-typing claim, with 0 of 2 functions and 0 of 393 statements verified before and after, no timeouts (2026-11-01) | the equivalent receiver test answers the supplied census expression without a new rule or trust assumption |
| [Investigation of the search's cost on the parser's slices](#search-cost-parser-slices) | done: the cost of filtering a fact by the slot's type, decided with each shared label's overlap computed once; `moduleFunction` 39.8 s → 5.3 s, `confined` past 300 s → 21.8 s; the search's elapsed time over the census 1036 s at d5c2754, 298 s at 963ffa4 (2026-10-24) | the cause is established of the search's elapsed time over the census rising from 224 s at 38ed032 to 1036 s at d5c2754, with `fragment-expressions.mts`'s `moduleFunction` from 5 s to 55 s and `confined` from 8 s to the 300 s limit |
| [Investigation of generic equality in a condition](#generic-equality-condition) | open: an investigation, cause unknown | `if (left !== right) return 1;` with `left, right: T` verifies, as `return left !== right` does, and the Boolean-return lowering applies to every function's return |
| [Investigation of a negated first read of an element](#negated-first-read) | open: an investigation, cause unknown | `const d = list[0]; if (!d.initializer) return -1;` over a program record verifies |
| [Investigation of a literal guard over `JsonValue \| undefined`](#literal-guard-json-read) | open: an investigation, cause unknown | `guard-literal-json-read-refused` verifies |
| [A re-tested operand of a negated guard's disjunction](#retested-disjunction-operand) | open: cause established (2026-10-30) | `blocker-compiler-api-optional-path-join` verifies |
| [Investigation of a field written before a spread of a literal arm](#field-before-literal-arm) | open: an investigation, cause unknown | the cause of `object-spread-field-before-literal`'s refusal is established, with a reproducer and a concrete repair obligation |
| [Investigation of an alias of function types met with a record](#callable-alias-meet) | open: an investigation, cause unknown | `spread-intersection-callable-alias` verifies |
| [Investigation of a member two intersection operands state](#meet-member-disagreement) | open: an investigation, cause unknown | the cause of `path-test-intersection-disagree`'s refusal is established, with a reproducer and a concrete repair obligation |
| [Investigation of a recursive visitor on a node's arms](#for-each-child-union-visitor) | done: on fea595c, with the producer proposing a dispatched call in an expression as the lowering makes it (8ae33c5) (2026-10-24) | `compiler-api-visitor-union` verifies |
| [Investigation of `forEachChild`'s list visitor](#for-each-child-list-visitor) | open: an investigation, cause unknown | `compiler-api-visitor-list-gap` verifies |
| [Assigned parameter patterns](#assigned-parameter-patterns) | open | `invalid-parameter-pattern-assigned` and `invalid-parameter-pattern-default-order` become positive cases verifying their Node results |
| [Constructor rests](#constructor-rests) | open | a constructor with a rest parameter is constructed and its variadic construct signature introduced |
| [Class offers across units](#class-offers-across-units) | open | a module class passed by a module function to a variadic construct signature verifies |
| [Generic methods left](#generic-methods-left) | open | `class-generic-method-bounded-refused` verifies, and members binding different numbers of binders relate |
| [Contract completeness](#restoring-completeness) | open | effect inference covers the rest wrappers, call forms and nested heap operations it is conservative for |
| [Effects of dispatched calls](#effects-of-dispatched-calls) | open | a method call on a union with a primitive's shape is dispatched and `split-non-empty` verifies |
| [Footprints](#footprints) | open: the seven programs decided (2026-10-17) | every application form has a checked bound |
| [Exceptional footprints](#exceptional-footprints) | open: handler facts across a throw | a call's footprint on a throw carries an effect through a handler, with `checkJson_safe` concluding it |
| [Class methods' effects](#class-methods-effects) | open: the draft's design accepted by the owner (2026-10-23): D1 (a), stated effects, and D2–D6 as the draft recommends; D5's rewrite of `Gate`'s four `shift`s into field writes is approved within step 3 as an exception to the no-rewrite rule (2026-10-23); step 1 (`no-return` with the async refusal L6) verifies `enumMembers` and `enumOpen` (slices of `fragment-classes.mts`, 300 s, 2026-10-24); step 3's [statements](docs/SOURCE-ELABORATION.md#stated-effects) are read and certified from each definition's code, and the compiler API's callback-free node methods state the empty footprint (D4); `Gate` states its members `span`, `local`, `hasTypeParam` and `typeParamName` (uncertified: no verified slice lowers `Gate`) and the method fields' functions `patternDefaults`, `inert` and `steppedPattern`, certified in their slices; census slices at 300 s, 16 functions of `fragment-{statements,expressions,classes}.mts`: verified 9 → 9, none gained or lost (2026-10-24); `pattern`'s array-pattern `map` passes, and `pattern`, `forOfPattern`, `protocolPattern`, `patternStmt` and `abrupt` stop at its object-pattern `map`, whose callback calls `gate.expr`: `expr`'s contract closure, with D7 and D8 (a) approved (2026-10-24) and D5's rewrite, is designed in the draft's §12; `forEachChild` is read at each callback footprint (D7), and a `map` callback calling it with a visitor within a stable footprint gives a dense result; 157 of the 167 functions a syntactic scan finds in `expr`'s contract closure, `expr` and `pattern` among them, state `{value: any, store: grow}` (of the others, 6 state a smaller footprint, 2 return `never` and 2 are type predicates) (`Gate`'s stacks popped by field writes, D5), and census slices at 300 s, 84 functions of 15 files of `tools/`: verified 76 → 78, `pattern` and `forOfPattern` gained, none lost (2026-10-24); census slices at 300 s on fea595c, 158 functions of 17 files of `tools/`, the 84 above among them: verified 78 → 76, `enumMembersTerm` and `enumIntrinsic` lost (`enumMembersTerm` states `{value: any, store: grow}`, which a `TermScope` member calling it needs, and its slice does not establish it at its `sort` of the array `filter` returns), none gained; `refers` verifies, and `patternStmt`, `protocolPattern`, `abrupt` and `neverAssigned` stop at an incoming-edge obligation in `markEarly`'s recursive closure `names` (2026-10-24); census slices at 300 s of the 18 functions of `fragment-statements.mts` sharing that obligation, `neverAssigned` among them, on 0e159b5 → on 3726ae4 (a guard's membership test decided by its binding, a fact filtered by its slot's type): each passes `markEarly`'s obligation and stops at a node-typing obligation of `protocolPattern`'s `rest`, `elements.at(-1)`; verified 0 → 0; the slowest search 38.5 → 24.3 s of CPU (2026-10-24); the same 18 on 8d9b1cb → with a condition's derived expressions unmarked by a source span ([residuals](docs/SOURCE-ELABORATION.md#residuals)): each passes `rest`'s obligation and its search exceeds 300 s; verified 0 → 0; with clause disjointness decided pair by pair, the search takes 68.7 s of CPU and stops at a node-typing obligation of `hoisting`'s write `gate.hoisted = []`; verified 0 → 0 (2026-10-24); [the inventory](docs/drafts/method-effects-inventory.md) gives each of the 183 functions `expr` and the gate's `TermScope` reach its statement and basis, 61 certified; a type guard states its effect at its promise's type (`x is Within<F, T>`), and `isTypeAlias` of `syntax.mts` states the empty footprint: census slices at 300 s of `resolve`, `moduleFunction`, `inertRead` and `typeStatement`, c105173 → this change: verified 0 → 4 (2026-10-28); `sort` at a comparator whose store changes are at most `grow` is within `{value: any, store: grow}`, and a closure calling a callable object with fields (`Number`, read as `Number.isFinite` too) is proposed within its call signature's footprint: census slices at 300 s of `enumStmt` and `enumEntries` (`fragment-classes.mts`), 1ba27599 → this change: verified 0 → 2 (2026-10-30) | callbacks calling a class instance's methods use effects stated with `Within<…>` and certified in each definition's own module |
| [Async and generator code](#async-and-generator-code) | open | an async function's entry and resumption are checked by an asynchronous entry judgment, and `%Await%`, `%AsyncReturn%` and `%AsyncComplete%` leave the trust surface |
| [Function declarations in bodies](docs/SOURCE-ELABORATION.md#function-declarations-in-a-body) | done: `function-declarations-in-body` and `function-declaration-before-initialization` verify | a function declared in a body is bound where it may first be read, and a call of it before the block's bindings are initialized reaches their checked accesses |
| [Iteration left open](#iteration-left-open) | open: `blocker-round-map-keys-spread` verifies with the [native placement Map contract retained](docs/SOURCE-REWRITES.md#a-native-placement-map-widened-to-readonlymap); targeted slices `fragment-statements.mts#markEarly,#hoisting` pass the spread claim and reach the later node-typing claim at `[48517,48535)`, with 0 of 2 functions and 0 of 91 statements verified before and after, and no timeouts (2026-10-31); `blocker-round-map-entries-spread` verifies with the [native merge binder contract retained](docs/SOURCE-REWRITES.md#native-merge-binders-widened-to-readonlymap); targeted slices `array-prototype.mts#mergeRefusal,#prototype` retain 0 of 2 functions and 0 of 215 statements verified, with no timeouts: `mergeRefusal`’s first refusal moves from the entry spread to `Object.entries(value)`, while `prototype` retains its optional dictionary key-read refusal (2026-11-01) | the iteration forms listed there are lowered; both map-iterator spreads have checked result contracts or documented source rewrites |
| [Keys known only at run time](#keys-known-only-at-run-time) | open | the writes listed there are typed |
| [Remaining source forms](#remaining-source-forms) | open | the forms listed there are admitted |
| Optional prototype bound lookup | closed by repair: `blocker-round-optional-dictionary-read` verifies the [native Map bound lookup](docs/SOURCE-REWRITES.md#optional-prototype-bounds-looked-up-by-binder-name); `invalid-round-optional-dictionary-read` refuses the inherited-function result shown under Node; targeted slices `array-prototype.mts#prototype,#primitivePrototype` verify 0 of 2 functions and 0 of 107 statements before and after on base `e59a1274`, with no timeouts; the first refusals advance from inherited-key reads to `Object.entries(value)` and `nonEmptySplit(separators)`, respectively (2026-11-01) | — |
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
| [Selection rules the data names](#union-shapes-candidates) | open | R6, R7, open target arms and shared literals each have a rule with its lemma, or a measurement shows it unneeded |
| [Observed stages beyond macOS](#observed-stages-beyond-macos) | open: the parse and TypeScript's diagnostics replay on macOS only | the compiler's reads are confined and observed on Linux, and the stages replay there |
| [Certificate size](docs/drafts/certificate-sharing.md) | open: design approved (2026-10-23); stage 1's node header and wire-text scan landed: check CPU, median of 3 interleaved runs on saved inputs (each range within 0.2 s), `moduleFunction` 15.8→9.7 s, `resolve` 12.7→7.4 s, `collect` 19.9→14.7 s, `closeStatements` 12.7→9.5 s; check peak RSS 9.4→4.2, 8.0→3.7, 18.3→7.8 and 11.5→5.1 GB; evidence 154→86, 133→71, 411→410 and 266→265 MB (2026-10-23; `inertRead` unmeasured); stage 2's read summaries landed: census slices on executed stages, median of 3 serial runs [range], before→after, search CPU `moduleFunction` 45.1 [44.7–47.1]→30.2 [29.6–30.3] s, `inertRead` 36.0 [35.9–38.0]→21.8 [21.4–21.9] s, `resolve` 35.3 [35.2–37.3]→21.0 [20.5–21.1] s, `collect` 16.2 [15.6–16.3]→16.0 [16.0–16.2] s, `closeStatements` 9.8 [9.5–9.8]→9.7 [9.7–9.8] s; check CPU 10.7 [9.9–10.7]→6.3 [6.1–6.3], 9.3 [8.9–9.5]→4.6 [4.6–4.6], 8.3 [8.2–8.5]→4.0 [4.0–4.1], 16.0 [15.0–16.1]→15.5 [15.3–16.0] and 10.2 [10.0–10.3]→10.2 [10.1–10.2] s; wall time within 0.7 s of CPU; evidence 85.5→25.9, 79.2→22.9, 70.9→16.2, 410.1→410.1 and 265.3→265.3 MB; check peak RSS 4.2→1.0, 3.8→1.0, 3.6→0.7, 7.8→7.8 and 5.1→5.1 GB; counted in the evidence documents, the derivation nodes the main check path validates (each step's proof, an ordinary derivation where a node has no step, each obligation; footprint and promise re-checks not counted) of `moduleFunction`, `resolve` and `inertRead` 22,943→5,025, 17,495→2,753 and 21,956→5,688, beside 27, 19 and 22 summaries of 1,454, 1,143 and 1,470 arms; their subtype validations (`sub` nodes, arms with a comparison, edge entries) 41,660→37,142, 26,729→22,958 and 29,322→25,333, those citing an instance 185, 72 and 72 before and after; per request, every request reading a union's view reads through summaries (83, 63 and 68 uses), one union read each left per arm; `collect` and `closeStatements` read no union and are unchanged (1,726 and 945 nodes; 27,782 and 24,181 subtype validations); all five verified before and after (2026-10-23); stage 3's evidence document, tables with backward references: census slices on executed stages, median of 3 serial runs (every range within 0.1 s and 0.01 GB), before (stage 2's medians) → after, evidence `moduleFunction` 25.9→5.8, `inertRead` 22.9→5.3, `resolve` 16.2→2.7, `collect` 410.1→77.5 and `closeStatements` 265.3→51.5 MB; search CPU 30.2→29.2, 21.8→21.0, 21.0→20.3, 16.0→8.3 and 9.7→4.7 s; check CPU 6.3→5.2, 4.6→3.6, 4.0→3.3, 15.5→4.5 and 10.2→3.0 s; check peak RSS 1.0→0.34, 1.0→0.33, 0.7→0.30, 7.8→1.70 and 5.1→1.05 GB; all five verified (2026-10-23); checking proper, no longer reading and decoding, is most of `moduleFunction`'s check; stage 4's [separation facts](docs/drafts/heap-freshness.md), one per allocation, addressed by level: census slices on executed stages, median of 3 serial runs (every range within 0.5 s and 0.01 GB), before (at ec59551) → after, evidence `moduleFunction` 5.82→5.17, `inertRead` 5.31→5.31, `resolve` 2.69→2.69, `collect` 77.50→4.35 and `closeStatements` 51.50→3.87 MB; search CPU 29.3→28.4, 21.1→20.5, 20.5→19.8, 8.6→1.6 and 5.0→1.1 s; check CPU 5.0→4.8, 3.6→3.5, 3.4→3.3, 4.5→1.0 and 3.0→0.7 s; check peak RSS 0.34→0.34, 0.33→0.33, 0.30→0.30, 1.70→0.13 and 1.05→0.12 GB; all five verified before and after; `collect`'s 2,798,774 distinct-link references are 3,940 references to 402 separation facts (1.24 MB) (2026-10-23); stage 1's structural decoder awaits the owner's choice of a reference: the decoder it must equal is built from the derived codecs and `sameJson`, partial definitions without defining equations a proof can use, so a proof needs total reference codecs, audited against them; the re-encode and comparison are 36% of `collect`'s check samples | the five stages land, each with its proofs and controls, and `moduleFunction`, `inertRead`, `resolve`, `collect` and `closeStatements` verify with their search and check CPU measured before and after |
| Fresh literals in field and index writes | done: the producer supplies the target storage contract; fresh literals verify and aliased mutable storage retains its invariant contract; census slices `hoisting` and `statements` (300 s, 2026-10-25) pass both literal writes and stop at `forInStmt`’s call `gate.local(d.name)`, verified 0 → 0 | field and index literals meet their storage contracts |
| Closed computed class and interface members | done: the type reader evaluates members at closed applications; class constructor types are refused by a shared instance check in computed results and contextual closure, static-field and Object.assign contracts; nested generic results and recursive member reads verify; the `API` default-argument case verifies; census slices `declaration-session.mts#close` and `discard` (300 s, 2026-10-25), verified 0 → 2 | the full admitted contract is read at each closed application, with open arguments refused |

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
  them ([stated type guards](docs/COMPILER-API.md#stated-type-guards); 16); a mapped type over
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
  assignment to a binding that is no mutable local (an assigned parameter
  with a default; 6); a guard's promise not met at a return (5); `Number`, a callable with
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
calls of TypeScript's compiler API are verified under. Two of its pieces
are designs no code implements.

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
`claim-text.mts`, `claim.mts`, `type-graph.mts` and `diagnostic-view.mts`
(6 slices refused at their promise, 3 more behind them) wait on the slices
and on their own promises.

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

<a id="conditional-optional-field"></a>
**A conditional's join past an arm's read.**
The existing conditional checks admit both field-reading forms:

```typescript
type Opt = { v?: string | null };
export function defined(o: Opt): string | null {
  return o.v !== undefined ? o.v : null;
}
export function loose(o: Opt): string {
  return o.v != null ? o.v : "";
}
```

The census expression uses the [explicit receiver test](docs/SOURCE-REWRITES.md#an-optional-chain-result-tested-before-a-conditional-record).
Its call to `Gate.span` has a store-preserving contract. An ordinary
callback may clear the tested field; `invalid-round-conditional-record-call`
checks that separate obligation.

### Investigations

Each is a refusal whose cause is not established.

<a id="search-cost-parser-slices"></a>
**The search's cost on the parser's slices.** Between the censuses of
38ed032 and d5c2754 (300 s step limit, 2026-10-24) the search's elapsed
time over all slices rises from 224 s to 1036 s. The rise follows 3726ae4,
which filters a fact's type by the slot's type
([refinement by a fact](docs/PROGRAM-TYPING.md#refinement-by-a-fact)):
there, the slices of `moduleFunction` and `confined` go from 4.1 s and
5.7 s to past 300 s. Most filters read a fact type and a slot type of about
109 node types sharing their labels, and each shared label was compared
with the slot type's clauses in turn, its own among them, at every one of
about 40 000 filters of a slice. A label of the slot's type whose own
clauses overlap is kept without that comparison, from a hint computed once
per label, with the same filtered list; two field types are found disjoint
label pair by label pair. With both, the two slices' search takes 5.3 s and
21.8 s, `confined` refused at a later obligation, and the search's elapsed
time over the census of 963ffa4 is 298 s.

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

<a id="retested-disjunction-operand"></a>
**A re-tested operand of a negated guard's disjunction.** In
`if (!ts.isMethodSignatureDeclaration(m) || m.typeParameters?.length ||
m.postfixToken) throw …`, the negated guard is a test, so
`ExpressionPlan.logicalTruth` lowers the regrouped `!g(m) || (b || c)` as a
value and the `if` tests it. Where `b`, a number, passed its truthy test, the
value is `b`'s and is tested again; the truthy slice of `number` is `number`,
so the re-test's failing edge, which the run never takes, reaches the next
statement without the fact `m.postfixToken` undefined that its entry claims.
The same condition verifies with a Boolean in place of the guard, without
the negation, or without `b` (2026-10-30). A repair either dispatches such a
disjunction on its operands' truth, the producer claiming the negation's
literal wherever the lowering evaluates it, or states the passed test as a
fact of the value that makes the re-test's failing edge vacuous.

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

<a id="for-each-child-union-visitor"></a>
**A recursive visitor on a node's arms.** A closure passing itself to
`n.forEachChild` in an expression, where the flow reads `n` at several arms
of its family (`ts.isIdentifier(n) && names.has(n.text) ? n :
n.forEachChild(refers)`), verifies at the footprint its body shows
(`compiler-api-visitor-union`): the producer proposes the call dispatched
on the union in one node, as the lowering makes it
(`Type_queries.dispatches_call`).

<a id="for-each-child-list-visitor"></a>
**`forEachChild`'s list visitor.** A call of `forEachChild` passing a
second visitor, `n.forEachChild(() => { k++; }, () => { k++; })`, has no
derivation of its node typing in search, inside a callback or not, at the
declared signature as at the per-footprint ones
(`compiler-api-visitor-list-gap`); the same call with one visitor verifies.
The declaration reader reads the second parameter as an optional function of
a readonly dense array of nodes. Which step refuses the second argument is
not established.

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
`checkJson_safe` ([the design](docs/SOURCE-ELABORATION.md#exceptional-footprints)).
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
([CALLABLES](docs/CALLABLES.md)).


### Source forms and the model

<a id="iteration-left-open"></a>
**Iteration left open.** An array pattern over a host
non-array iterable needs the pattern's reads as steps of `%Iterate:K%`, or of
the protocol. A spread of a program's iterable where the statement evaluates
code before it, and a default or nested pattern in an array pattern over one,
need the protocol's steps interleaved with that code, in the expression, not
before the statement. One in a conditional's branch needs the steps after
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
identity to its keys, which it does not. The design for it is a stable
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
holes below it.

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
[Certified imports](docs/SOURCE-CONTRACTS.md#certified-imports) check an
imported function's code in the importer's run, at its effect-qualified
signature. `checkJson_safe` keeps its statement.
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
