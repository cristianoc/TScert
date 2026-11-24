# Verification work

The work ledger of the independent verifier: every open item in one line,
then the designs behind the items.
[DESIGN](docs/DESIGN.md) states the architecture and decisions;
[the source boundary](docs/SOURCE-FRAGMENT.md) owns the supported-fragment
restrictions.

<a id="next-steps"></a>

## Status

Progress is recorded here and nowhere else. Each row is one open item: what
is open with its next action, and when it closes. A commit that moves an
item updates its row, and a closed item's row and prose are deleted: the
commit record keeps what it did. The prose under [open work](#open-work)
describes an item's design and evidence, not its progress.

| Item | State | Closed when |
| --- | --- | --- |
| Pretext's walkers across their visitors | `walkPreparedLinesRaw` and `walkPreparedComplexLines` (`src/line-break.ts`), `walkLineRanges` and `layoutWithLines` (`src/layout.ts`), and `walkRichInlineLineRanges` (`src/rich-inline.ts`) all verify under the paper-rules prototype: all 78/78 functions across `line-break.ts` (18), `layout.ts` (19), `rich-inline.ts` (23), and `prepare.ts` (18, ordinary `verified`) are accepted (`dev/paper-rules/pretext/expected.json`). The visitor's effect is written as a bounded effect variable ([the effect language](docs/drafts/effect-languages.md), [the paper-rules skill](.claude/skills/paper-rules/SKILL.md)); module-private caches (`cachedEngineProfile`, `graphemeEndCaches`, `graphemeRules`, `breakRules`, `classRuns`, `classRemaps`) are framed via confined module state `"@state"` (`Effects<P, T>`, `Join<E, P>`, rule `ConfinedRule` proved in `Verification.Paper.EffectLanguage.{Rules,Model}` from `Confinement.ClosedOut` with local module confinement checks in `dev/paper-annotations.mts`), and `normalizePreparedLineStart` / `stepPreparedSimpleLineGeometry` state the exact cursor fields `"cursor.segmentIndex"` and `"cursor.graphemeIndex"`. `walkPreparedComplexLines` states `"cursor.segmentIndex": "keep"` and `"cursor.graphemeIndex": "keep"` in its callback bound (discharged at `walkPreparedLinesRaw`'s forwarding call via `Anch` + `Meet` over its fresh `const cursor`, and framed across `onLine?.(...)` with alias-aware bound coverage), and its `getEngineProfile()` call is framed via `Confined` so destructured `prepared.*` read links survive into the line loop; `SinglePass.nearStep` filters non-linear index atoms so merge entailment retains `0 <= lineEndSegmentIndex` across `decided:`. The public line streams check their caller's `start` cursor where they copy it (`stepNextLine`, `layoutNextRichInlineLineRange`), throwing a `RangeError` where its segment index is no safe non-negative integer. The steppers state contracts over the cursor: `normalizePreparedLineStart`, `stepPreparedSimpleLineGeometry`, `walkPreparedComplexLines` and `stepPreparedLineGeometryFromStart` require `safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex`, all but the first `cursor.segmentIndex < prepared.widths.length` too, and ensure the first; `normalizePreparedLineStart` also ensures `result === false || cursor.segmentIndex < prepared.widths.length`, which a loop invariant over its `segmentIndex` proves, and the raw walker's scan past what a line can't start with keeps one over `startSegmentIndex`. Where the source does not establish them, unsafe assumes state the facts over a local copy: the cursor's grapheme index, safe and non-negative at the complex walker's line start and, in the simple stepper, below its start segment's advances, which no clause bounds by the length of its segment's list (#365, 3, `dev/paper-rules/repro-365.ts`). The complex walker's loops state invariants: the outer over its cursor and the handle's lengths, the inner over `i`, its line start, `hangEndSegmentIndex` and `pendingBreakSegmentIndex` (at most `segmentCount`), `hasContent === false || lineStartSegmentIndex < i`, `lineStartSegmentIndex <= lineEndSegmentIndex` (in its grapheme loop too), `endSegmentIndex === -1`, `fitBreakSegmentIndex` a safe integer, and each nullable or item list read by index, `x === null || segmentCount <= x.length` (`hyphenRooms`, one entry longer, `<`); the simple stepper's loops state the same over `lineEndTrims`. At a step other than a call of a slot, the prototype's layer keeps the ordinary checker's normal effect, so the step keeps the facts it does not name as in the ordinary pass. All 56 guarded reads of the walkers and the steppers they call between visits are restored (`// PAPER: guard removed`), judged on the prototype pass's own verdict: `normalizePreparedLineStart` 1, `walkPreparedLinesRaw` 1, `stepPreparedSimpleLineGeometry` 17, `walkPreparedComplexLines` 37. `PreparedLineData` states `@invariant this.segmentFlags.length === this.widths.length`. `measureAnalysis` (`prepare.ts`) returns a `MeasuredSegments`, the handle's fields with no invariant: for a rich-inline item it returns the paragraph's `segmentFlags`, made for every segment the paragraph can have, beside the `widths` filled so far. Where the source does not establish the invariant, 38 unsafe assumes name #356 (`line-break.ts` 13, `layout.ts` 10, `rich-inline.ts` 15): where a handle is built from a text's `MeasuredSegments` (`prepareInternal`, a paragraph of one text item, an atomic item's own text), whose fact `measureAnalysis` cannot state, as a clause's guard tests a path null and none tests it not null; at the paragraph's handle, whose `segmentFlags` is `flags.subarray(0, widths.length)`, of which the pass knows no length, and which needs `widths.length <= flags.length`, a count over the items the source does not state; at `prepareWithSegments`'s result, a spread, which carries no fact of its fields; in `layoutWithLines`'s visitor, over the handle it captures; after a call from another module of a function relying on a unit its module refuses, of which the caller gains no contract, the type invariant over the handle it passes included (`layout.ts` 7, `materializeRichInlineLineRange` 2); at each handle a walker gets from `flow.data` (6), which the paragraph's type can state (`@invariant this.data.segmentFlags.length === this.data.widths.length` is read through the field), each function receiving the paragraph then establishing it at its returns; in `setEmptyObjectFacts` (3) and `createLine` (1), where the pass loses it inside a loop, the cause not established; and, for each nullable or item list the steppers read by index, `segmentCount <= x.length` under `x !== null` at the top of the complex walker's line loop and at the simple stepper's start (10), with a breakable segment's per-grapheme lists at their reads (3); two loop invariants of `setEmptyObjectFacts` and `isSoftHyphenSegment`'s `Modifies<{}, boolean>` carry it through that function's loops. Left out of the invariant: `breakableFitAdvances.length === widths.length`, which no guarded read needs and which, assumed beside it, leaves `prepareRichInline` and `createLine` refused at calls the assume stands right before; each nullable list's null-guarded clause, which the walkers' loop invariants state over their local copies instead; and the lists of the optional `items`, from a condition over which, an `if`'s included, the pass learns no fact. Next: discharge the remaining unsafe assumes (#356, #365) — establish a text's handle invariant in `measureAnalysis` and the paragraph's in `prepareRichInline`, and state it over `flow.data`. | The walkers verify with all 51 bound sites in upstream form. |

### Frames and facts across calls

| Item | State | Closed when |
| --- | --- | --- |
| Shrinking owned arrays | The [private representation](docs/drafts/private-representation.md) draft refuses a class whose member pops an owned array or overwrites a reference in it. Next: prove the protocol rigid for an owned array holding no storage. | Such a class is admitted, with the rigidity proved. |
| [Abstract confined regions](docs/drafts/abstract-confined-regions.md) | User-defined heap abstractions (`FastMap`, `LruCache`, `Arena`) and module caches mutate internal arrays whose spines and element cells carry no property key, so key-disjointness cannot separate them from caller arrays (`prepared.widths`). The module half (`M.@state`, `ModuleRegion`, `closedOut_region_disjoint`, `closedOut_reach_disjoint`, generalized `Anchored`, and `ConfinedRule`) is proved in `Verification.Paper.EffectLanguage.{Rules,Model}` and exercised in the paper-rules prototype (unblocking all 5 refused Pretext functions). Open: class-instance `@rep` regions, full calculus proofs in `SinglePass`, and `mode8Accepted_sound` integration. | Abstract confined regions (`m.@rep`, `M.@state`) and their disjointness theorem are proved in Lean (`mode8Accepted_sound` unchanged), unifying built-in `Map`/`Set`/`WeakMap`, user-defined `FastMap`, and module caches with zero collection-specific rules. |
| Cross-field null implications in clauses | A clause states a null test only as a leading guard, so `a !== null \|\| (b === null && c === null)`, a clause of the paragraph handle's invariant, is refused. Next: admit `P === null` and `P !== null` as atoms. | Such a clause elaborates and is used at boundaries, with a case. |
| [Keeping contract facts across calls](docs/drafts/keeping-contract-facts-across-calls.md) | A `??=` cache, a `Set`'s and a `Map`'s mutators and calls keeping objects keep their facts. Next: frame measurement helpers' writes, callbacks (pretext's `onLine`) and defaulted parameters' preconditions. | Each frame the draft names is certified, and pretext's walkers keep their handle's facts across their calls. |
| [Stated effects](docs/drafts/stated-effects.md) | `Modifies<P, T>` is read and certified for parameter spine regions, fresh spines and slots. Open: its other location keys are parsed and refused, and an array literal is no `Fresh<T>` source. | The draft's §10 cases verify, location keys included. |
| [Tolerant frames](docs/drafts/tolerant-frames.md) | The draft's three conjectures name Lean statements not proved as one. Next: state transformer soundness as one theorem. | That theorem has the footprint and index-fact mechanisms as instances. |
| [Implementation rules and paper rules](docs/drafts/implementation-and-paper-rules.md) | The paper rules in Lean (B) are `lean/Verification/Paper/TolerantFrames`, matched to the paper item by item in [B against the paper](docs/drafts/b-against-the-paper.md). | Each rule acceptance applies is matched to its paper rule, or their difference is stated. |
| Native footprints read by name in proposals | The front's proposals recognise natives by method name (`HeadInference.lean`'s `resized`, `touched` and `Ctx.pushed`; `Synthesis.lean`'s freshness, `generalArrayUse` and evolving writes). Next: read each from the callee's contract. | No list of method names remains. |
| Library rules keyed by method names | `ArithmeticRules.lean` matches a call by method names and states its trust as lists of contract names. Next: match the callee's contract. | A rule matches the contract and its trust names the contract's row. |
| Built-in prototype keys as one table | The built-ins' keys are listed in `Fragment.lean` (`functionKeys`, `typedArrayKeys`, `inKeyRefusal`) and `SourceTypes.prototypeNames`. Next: state one table. | The contracts and the refusals read that table. |
| Mechanical front end (no front-end inference) | Unverified front-end passes hold non-mechanical inference in four pockets: `Lowering/Types.lean`, `Lowering/Flow.lean`, `Lowering/Observations.lean`, and `Lowering/Compact.lean` (used by the proved verifier), `tools/declaration-graph.mts`, and `dev/paper-annotations.mts` (prototype only, isolated by `tests/prototype-isolation.mts`). Future stages: (1) prove or drop `Compact.lean` and ban new AST-side inference of unannotated postconditions; (2) move `Lowering/Flow.lean` and `Observations.lean` onto the lowered CFG in `SinglePass`/`HeadInference.lean`; (3) replace `dev/paper-annotations.mts` with mechanical annotation parsing plus proved CFG checks at unification; (4) slim `tools/declaration-graph.mts` to mechanical declaration translation. | The TS front end and AST lowering perform mechanical syntax and declaration translation alone, with all semantic deduction over lowered CFGs in proved Lean. |
| Native footprints from their specification steps | The [draft](docs/drafts/native-footprints-from-steps.md) awaits the owner's decision. | Each modelled array mutator's footprint is derived from its step sequence. |
| [Footprints](#footprints) | A variadic construction, a call of a callable object and a packed call consume no footprint, so a bounded body refuses them. Next: give each a checked bound. | Every application form has a checked bound. |
| [Exceptional footprints](#exceptional-footprints) | A handler receives no fact across a throw, and a node with a handler is outside the node-by-node bound (`map-fresh-handler-refused`). | A call's footprint on a throw is carried through a handler, with `mode8Accepted_sound` concluding it. |
| [Class methods' effects](#class-methods-effects) | The [draft](docs/drafts/method-effects.md)'s design is accepted by the owner. Next: continue `expr`'s contract closure and `Gate`'s `shift` rewrites (D5); `Gate`'s stated members are uncertified while no verified unit lowers `Gate`. | Callbacks calling a class instance's methods use effects stated with `Modifies<…>`, certified in each definition's module. |
| [Contract completeness](#restoring-completeness) | Effect inference is conservative for some rest wrappers, call forms and nested heap operations. | Inference covers them, the source targets and their negative controls kept. |
| [Effects of dispatched calls](#effects-of-dispatched-calls) | A method call on a union receiver with a primitive's shape is not dispatched, so its effect is not established. Next: lower the dispatch into branch nodes, or check effects compositionally. | Such a call is dispatched and its effect established. |

### Pretext's bounds

| Item | State | Closed when |
| --- | --- | --- |
| Pretext bounds chain 1 | 7 of the chain's 67 rewrites are restored and 210 of 210 functions verify (pretext `chain1`, `86a93c0`). Left: `measureAnalysis` (33) and its helpers (26) need a frame naming the array `readScriptRuns` splices, a nested region the regional check does not certify; `mapSourceLineBreaks` (11) needs length contracts of `replace` and `slice`, awaiting the owner; `normalized[i]!` (2) needs a rule for a string's element read. | Every rewrite of the chain is restored and 210 of 210 functions verify. |
| Native length facts for pretext | Lengths from `push`, literals, filled allocations, `indexOf` and footprint-qualified `map` verify. Open: sparse allocation, `fill` aliasing, `map`'s captured length, loop invariants over a cell, bounds on an existing nullable array. | Each open form has a checked rule or a stated refusal. |
| [Quantified clause extensions](docs/drafts/quantified-every-extensions.md) | #396 is closed by the interval route: quantified facts take interval bounds and element-tag bodies, and `quantified-suffix-null` verifies. Open: #397 (shifted parallel indexing) and #398 (bitmask-guarded bodies), each by the draft's route, a rewrite of Pretext's source with its equivalence audit; the draft awaits the owner's decision on them. | The chosen route of each issue lands: its gap case verifies, or Pretext's rewrite verifies with its audit and distinguishing fixture. |
| String method bounds in pretext | `charCodeAt`, `slice`, the searches and string addition have bounded contracts. Next: state a checked non-empty-match condition for a regex `split`. | Pretext's consumers establish their bounds with checked annotations. |
| Generated-table bounds in pretext | Fixed-stride arithmetic uses linear clauses. Open: bitwise result ranges, products of variable terms and quantified typed-array elements. | The decoder and the table readers establish their annotated bounds. |
| [Typed-array prefixes](docs/ARITHMETIC.md#quantified-clauses) | Prefix bounds, vacuous prefixes, exact-write extension and `xs[n++] = v` have checked rules. Next: restore pretext's prefix builders and consumers. | They verify with their stated bounds. |
| [Integer types](docs/drafts/integer-types.md) | `SafeInt` and the clause `int` are read wherever a type is. Open: a loop counter starting at a `SafeInt` merged with a `number` (`safe-int-loop-start-gap`), a path's integrality from its type alone, a literal union read at `int`. | The gap case verifies and pretext's `measureAnalysis` and `getTrailingCollapsibleStart` drop `safeInteger(...)`. |
| [Type invariants over field paths](docs/drafts/field-paths-and-record-invariants.md#2-record-invariants) | A path precondition no caller's fact establishes is refused (pretext's `layoutNextRichInlineLineRange`). Next: a cursor invariant or a validated entry. | `field-path-precondition-unestablished` verifies. |
| [Shared clause forms](docs/ARITHMETIC.md#quantified-clauses) | Linear alternatives, Boolean postconditions, quantified element paths and guarded adjacent-element ordering have source cases. Next: check the pretext functions that motivated them. | Those functions verify under their written clauses. |
| [Quantified clauses](docs/ARITHMETIC.md#quantified-clauses) and [loop invariants](docs/ARITHMETIC.md#loop-invariants) | Deferred: a write into an ordinary array that no region fact keeps apart keeps no quantified fact over it. Pretext needs none. | Such a write keeps the facts its index allows, or the owner drops the item. |
| [Function-boundary bounds](docs/ARITHMETIC.md#preconditions) | Open: a clause relating a parameter to captured storage, and one naming a defaulted argument. | `bounds-captured-precondition-gap` and `bounds-default-precondition-gap` verify. |
| [String lengths as terms](docs/drafts/string-lengths.md) | Open in pretext's upstream form (2026-11-08): `removeSkippableSegmentBreaks` (an `indexOf` result no contract bounds), `needsComplexTextPath` (a bound kept by parity), `readScriptRuns` (a path bound across array writes), `getScriptFacts` (a table read at `getClass`'s result). | Each verifies, or its refusal is stated. |
| [Written postconditions](docs/ARITHMETIC.md#postconditions) | `@ensures` with `old(…)` composes at calls. Open: `measureAnalysis`'s post is not composed onto the local `widths` at `prepareRichInline`'s call (31 rewrites), and `written-ensures-old-refused`. | Pretext's `zeros` push loop establishes its length without a runtime check. |

### The front end's own code

| Item | State | Closed when |
| --- | --- | --- |
| [Coverage of the front end](#the-front-ends-own-functions) | Census of main `ae20a6c6` (2026-11-04): 643/686 functions shallow, 10097/17790 statements. Next: rank the refusals of the `single-pass` census and work them in gap rounds. | Every function of `tools/`, `dev/`, `tests/` and `pipeline/` verifies or is refused by a stated restriction. |
| Priority-deck refresh | The deck describes census `9bf8c463` (2026-11-02). Next: rebuild it from the `single-pass` census. | The deck reflects the measured census and passes source review. |
| Deferred gap candidates | Six candidates of the 13-case round wait, their validation deferred by the owner: compiler-enum provenance, error-message narrowing, compiler ancestor cells, AST JSON key bounds, table-classifier preservation, shadow-map provenance. | The selected candidates pass their measurements, suites and review. |
| Compiler client contracts (census batch `8f4c28523e7f`) | The batch's cases verify or are negative cases. Open: the private layout and Node process contracts of the [compiler client](docs/SOURCE-REWRITES.md#the-compiler-client-and-its-child-process) await the owner's review. | The owner has reviewed them. |
| syntax.mts support (namespace imports in an initialization) | `compiler-api.mts` reads its namespace import as a value (`new Map(Object.entries(ts))`), which refuses every unit of the file. Next: give a namespace object read as a value its contract. | The file's other units are checked. |
| [Module constants at an entry](docs/drafts/module-constant-entries.md) | An imported guard is read at its entry. Open: `type-guard-value-import` (its library's plans refused), and a constant holding an arrow function has no entry. Next: lay the arrow out as a module function. | `blocker-compiler-api-token-subtype` verifies. |
| [Declaration collection phases](docs/drafts/collect-declarations-phases.md) | Steps 1–6 are done. Next: steps 7–8 of the draft. | The phases have explicit inputs and owned state, with unchanged declaration documents and case outcomes. |
| Declaration-graph resolution helpers | 17 of the cluster's 26 functions verified on the claims route (2026-11-03). Next: read the others (`compatibilityReviewed`, `collect`, `collectFrom`, `elaborateDeclaration`, `closeDeclarations`, `collectInstances`, `selectGlobal`, `collectDeclarations`) in the `single-pass` census. | Each verifies or its blocker has its own row. |
| [Decoders' dictionary reads](#decoders-dictionary-reads) | 12 of `calculus.mts`'s 15 functions verified on the claims route (2026-10-19). Next: measure the decoders in the `single-pass` census. | The decoders of `calculus.mts` and `control-flow.mts` verify within the limit. |
| Computed alias passed as a function | `computed-types.mts`'s `unionMembers` and `distributed` pass `context.alias`, a method with a receiver, as a function value. Next: derive it, or rewrite to an equivalent. | The method passed to `computedAlias` has a checked derivation or a documented rewrite. |
| Family activation: record at an index signature | `family-activation.mts`'s `checkedGuards` and `activeGuards` are refused at a record meeting an index signature. | The record establishes its index-signature contract. |
| Regression coverage for refusal-index rows | 42 rows of [the refusal index](docs/SOURCE-FRAGMENT.md#fragment-boundary) name no case (2026-11-05). Next: add or name a case for each. | Each enforced boundary of the index has a case reaching its refusal. |
| [The any check over external declarations](#the-any-check-over-external-declarations) | A stated limit: relations `any` satisfied in an outside declaration are not re-established (447 errors in the shadowed declarations, 2026-10-18). | A check re-establishes them and `tests/unchecked-project/gaps.mts` is refused. |
| [Computed types evaluated through helper declarations](#computed-types-evaluated-through-helper-declarations) | A stopgap. Next: replace the helper declarations by a checker endpoint, or check the computation by an elaborator in Lean. | One of the two is in place. |

### Investigations

Each is a refusal or a failure whose cause is not established. Those of a
function of `tools/` were measured on the claims route; a targeted census
of `single-pass` at a 60 s limit (2026-11-21) refuses those it reached
(`print`, `printSignature`, `checkedGuards`, `activeGuards`,
`decodeFlowDocument`, `moduleEntries`, `moduleObjectDefault`). Their next
action is the same: read the function's refusal in the `single-pass` census
and name the failing rule.

| Item | State | Closed when |
| --- | --- | --- |
| A concrete subclass of an identity generic subclass | `class Mid<T> extends Box<T> {}; class Leaf extends Mid<number> {}` is refused at the middle class's base call, for every kind of type argument. | The cause is established, or the shape verifies with a case. |
| A dictionary completed by writes in branches | A local `{ [field: string]: string \| boolean }` completed by index writes in both arms of an `if` and returned in a record is refused at the join's edge; `compiler-channel.mts#identify` [avoids the form](docs/SOURCE-REWRITES.md#a-dictionary-completed-by-writes-in-branches-before-its-return). | The failing rule is named, and the form supported or its refusal stated. |
| A loop update reading a field of a field after a nested discriminant test | Over records `H1 \| H2`, a loop updating `h.n.up` with `h.n.k === "r"` tested inside an `h.k === "one"` branch is refused at the update (2026-10-30). Next: write the reproducer as a case. | The cause, and a case showing it. |
| [Does the model's error lacking `stack` matter](docs/SOURCE-ELABORATION.md#in) | `"stack" in e` answers `false` in the model and `true` in JavaScript; no program is known whose result differs. | A proof that no checked outcome changes, or a program it changes. |
| The fast checks and controls | `make test-checks` takes about 5 minutes in CI and has hung twice (81 minutes in CI, 40 minutes locally, a file worker's verifier gone and its controller waiting). Next: find the hang's cause. | The hang is fixed, each check's cost and purpose are recorded, and the scripts fail within a budget near their healthy duration. |
| `Examples run under Node` fails within `make test-checks` | Under a load average of about 14 the suite failed in three runs and passed alone (2026-10-30). | The cause, and the suite passing under load. |
| Type-term census timeouts | `type-term.mts#someType` timed out at 600 s; with `mapTypeParts`' contract repaired it verified in 283 s (2026-11-03). | The cause of the cost is identified, with an acceptable cost or a located refusal. |
| [The cost of a walk](docs/drafts/walk-cost.md) | `typeTerm` peaks at 4.75 GiB (2026-11-24): an enum comparison lowers to a per-member chain, temporaries keep their facts, and stores are copied per node. A field's read takes the name its read link gives (§2): the draft's 128-member comparison holds 213,446 facts in its closure's walk (2026-11-24). Next: §2's liveness, then §1. | The four changes land, each measured; `typeTerm` runs under the census's 4 GiB. |
| Module catalog proof search | Migrating `library-modules.mts`'s two readonly effect spreads timed out at 300 s and lost `globalNamespace`, so the file keeps the spreads (2026-11-02). | The catalog's initializer has an acceptable proof cost without losing verified dependents. |
| Chain-link type-argument edge | `fragment-expressions.mts`'s `wrappedMethodCall` and `expr` are refused at the edge into `chainLink`'s `gate.fail` branch. | The edge's refusal has a cause and a reproducer. |
| Receiver-form guard incoming edge | `fragment-expressions.mts`'s `expr` and `binary` are refused at the edge into the `.call`/`.bind` receiver-form guard. | The edge has a cause and a derivation or a documented rewrite. |
| Client diagnostic record allocation | `declaration-graph.mts#clientErrors` is refused at its returned diagnostic record. | The record has a cause and a derivation or a documented rewrite. |
| Queued declaration-value record | `declaration-graph.mts#closeDeclarations` is refused at `({ node, span: at })` in the `map` passed to `collectFrom`. | The record has a cause and a derivation or a documented rewrite. |
| Prototype overlay entry allocation | `array-prototype.mts#reviewedEntries` is refused at its first `forEach` entry record; `prototype` at its type-scope record. | Both have causes and derivations or documented rewrites. |
| Merge scope record | `array-prototype.mts#mergeRefusal` is refused at `scopeOf`'s `TermScope` record. | The refusal has a cause and a reproducer. |
| Renamed-module expression claim | `fragment-parse.mts`'s `renamedModule` and `lowerFile` are refused at `mapDocument(module.declarations, …)`. | The expression has a cause and a reproducer. |
| Computed-type slice expression claim | `computed-types.mts#computedType` is refused with no type for one expression. | The expression has a cause and a derivation or a documented rewrite. |
| Mapped type result record | `type-term.mts`'s `typeTerm` and `constructorForms` are refused at `mapped`'s result record. | The record has a cause and a derivation or a documented rewrite. |
| Computed reference result claim | `type-probe.mts#makeProbe` is refused at `readReference(name, args, span)`. | The call has a cause and a derivation or a documented rewrite. |
| Flow node result record claim | `source-flow.mts#decodeFlowDocument` is refused at its constructed node record; its caller `checkUnowned` at a `Math.round` overlay. | The record has a cause and a derivation or a documented rewrite. |
| refusalStatus completion claim | `pipeline/verify-source.mts#refusalStatus` is refused at its completion. | The completion has a cause and a derivation or a documented rewrite. |
| Shadow signature parameter map claim | `shadow-contracts.mts#printSignature` is refused at `params.map((p, i) => …)`. | The map has a checked derivation. |
| Unchecked worker file-map closure claim | `unchecked.mts#check` is refused at `[...roots].map((file) => path.relative(".", file))`. | The closure has a checked derivation. |
| Decoded finding allocation claim | `unchecked.mts#decodeResult` is refused at its finding record. | The record has a checked derivation. |
| Early-marking after a map-keys spread | `fragment-statements.mts`'s `markEarly` and `hoisting` are refused at an expression after their `Map` keys spread. | The expression has a cause and a derivation or a documented rewrite. |
| File-answer expression claim | `files.mts#answerOf` is refused at one expression. | The expression has a checked derivation. |

### Source forms

| Item | State | Closed when |
| --- | --- | --- |
| [Slices of the value universe](#universe-slices) | A tag test on `unknown` keeps the kinds it does not contradict. Open: the negative `Array.isArray` slice, a type parameter's meet with `unknown`, and guards over `unknown`. | `typeof v === "object" && v !== null` narrows `unknown`, and the guards promise what their tests establish. |
| [A key found on an open object](#key-on-open-object) | The read verifies as an open read under the open-read restriction, an assumption for the owner's review. Next: prove the lookup invariant and read it as the model's own. | `if (typeof v === "object" && v !== null && "k" in v) return v.k` verifies, with the invariant proved. |
| [Guard overloads beyond `filter`'s](#guard-overloads) | `find` and `every` are read at a guard keeping array spines. Open: predicates excluding null or undefined, and the other natives at [the elements fact](docs/FOOTPRINTS.md#the-elements-fact). | `shadow-contracts.mts#print`, reading its array at `string[]` after `every`, verifies. |
| [A Boolean return lowered as a condition](#generic-equality-condition) | The lowering is scoped to type guards and assertion functions. Next: apply it to every return and check that `loose-equality` and `generic-unknown-arguments` keep their outcomes. | The lowering applies to every function's return. |
| Spreading a pack into a callback in a generic base constructor | A base constructor calling `cb(...values)`, extended at a concrete tuple, is refused. Next: state `callPacked`'s relationship ([packed binders](docs/PROGRAM-TYPING.md#packed-binders)) at the construction. | The shape verifies, with a case and an unsafe counterpart refused. |
| [Assigned parameter patterns](#assigned-parameter-patterns) | Refused at the gate. Next: derive each binding's contract from the annotation at the position it reads. | `invalid-parameter-pattern-assigned` and `invalid-parameter-pattern-default-order` verify their Node results. |
| [Constructor rests](#constructor-rests) | A constructor's rest parameter is refused. Next: a construction allocating the rest spine. | Such a constructor is constructed and its variadic construct signature introduced. |
| [Class offers across units](#class-offers-across-units) | A module function passing a module class to a variadic construct signature is refused. | That call verifies. |
| [Generic methods left](#generic-methods-left) | Open: bounded class-method binders, and members binding different numbers of binders. | Both have checked contracts. |
| [Async and generator code](#async-and-generator-code) | `%Await%`, `%AsyncReturn%` and `%AsyncComplete%` are trusted intrinsics. Next: an asynchronous entry judgment. | An async function's entry and resumption are checked and the three leave the trust surface. |
| [Iteration left open](#iteration-left-open) | Open: array patterns over host iterables, spreads of a program's iterable beside other code or in a branch, a `ReadonlyMap`'s `values()`, generators. | The forms listed there are lowered. |
| [Keys known only at run time](#keys-known-only-at-run-time) | Open: writes at a run-time string or symbol key, to a shared object, or to an array at a `number` key. | The writes listed there are typed. |
| [Remaining source forms](#remaining-source-forms) | Open, one form each. | The forms listed there are admitted. |
| [Model limits of one form each](#model-limits-of-one-form-each) | Open, one limit each. | Each limit listed there has its model support. |
| [Regular expressions left](#regular-expressions-left) | Open: replacement callbacks, a native shape for `new RegExp`, a regex's properties, structural match iterators. | Those are admitted, and `SetIterator` and `MapIterator` loops require the native mark. |
| [JSON records by their fields](#json-records-by-their-fields) | A record typed by its fields is no `JsonValue`. Next: a bound on all its own string keys, kept through mutation and calls. | Such a record meets `JsonValue`. |
| [Node's process](#nodes-process) | Open: the write `process.env[k] = s` (`node-process-env-write`), and events known only as strings. | The write goes through a host setter preserving every alias's view, and iterated signal names are proven admitted. |
| [Fixed location kinds](docs/drafts/location-kinds.md) | Kinded worlds are the active model. Open: a world for the pipeline's actual built-in objects, which Lean does not enumerate. | The built-ins' declared contracts have a compatible initial world. |

### Proofs and trust

| Item | State | Closed when |
| --- | --- | --- |
| [The claims-free route](docs/SINGLE-PASS.md#8-the-claims-free-front) | The single pass is the only route. About 13,000 Lean declarations that only the claims route used remain (the claims decoder, the certificate producer's search, RequestJson's requests). Next: delete them. | Every such definition is deleted. |
| Check a declared contract's scope at its callable's arity | No reader checks a declared, native, library, claimed or interface-row contract's positions against its callable's arity. Next: one validation phase shared by every admission ([design](docs/drafts/effects-of-commands.md#what-the-decoder-establishes-and-what-consumers-check)). | Every stated contract is admitted only within its callable's scope, with forged-document controls. |
| Prove that decoding the writing of any effect returns that effect | Proved for serializable effects (`EffectCodec.decode_encode`), argued for the others. | The theorem holds for every effect, in the axiom check. |
| [Module composition](#module-composition) | Certified imports are checked; composing the units is reviewed, not proved. | A Lean theorem composes units certified against each other's signatures. |
| [Precision](#precision) | Open, one fact each. | The facts listed there are derivable. |
| [Correctness specifications](docs/drafts/correctness-specs.md) | The design is approved (2026-10-28). Next: build it. | The clamp, binary-search and JSON round-trip cases verify, their negative controls refused. |
| [Canonical heap knowledge](docs/drafts/heap-knowledge-canonical.md) | Normal forms are proved and stored. Open: one type context per type rather than per node, and the draft's §9 measurements, last taken on the claims route (2026-10-28). | The draft's §9 measurements hold. |
| [The type-decision procedure's remaining steps](docs/drafts/subtype-decision.md) | The draft's remaining steps (interned labels, a checker memo, a candidate index) were measured on the claims route (2026-10-24). Next: measure them on the single pass. | Each step lands with its measurement, or is closed as not worth its cost. |
| [Structure-directed comparison's lemmas](#union-shapes-lemmas) | Proved outside the repository against `84b326a`. Next: add them as modules. | They are modules of `lean/Verification/Types/` the build checks. |
| [Selected discovery and the rerun](#union-shapes-discovery) | Open: the engine has no single dependency representation. | The selected search is proved to find every certificate the full search finds, and the rerun removed where that applies. |
| [Selection rules the data names](#union-shapes-candidates) | Open: open target arms and shared literals have no rule. | Each has a rule with its lemma, or a measurement shows it unneeded. |
| [A semantics of the Fragment](#a-semantics-of-the-fragment) | Open. | Lowering is proved a simulation of a Lean interpreter of the Fragment. |
| [A connection to ECMA-262](#a-connection-to-ecma-262) | Open. | The host's stated types are lemmas of a mechanized specification. |

### Speed and infrastructure

| Item | State | Closed when |
| --- | --- | --- |
| Single pass cost with nothing supplied | Cause known. `prepareRichInline` takes 16.5 s of verifier CPU (2026-11-16, [the measurement](docs/drafts/on-demand-processing.md#interface-demand-in-a-prepared-worker)); `measureAnalysis`, refused, keeps inference for its written effect contract. | `prepareRichInline` takes at most a first run, a diagnosing walk and its final run. |
| [Facts computed forward, supplied facts as candidates](docs/drafts/forward-facts.md) | Step 1 is done: a loop head's proposed fact is a candidate. Next: step 2. | The draft's five steps land, each measured on the cases and pretext. |
| Class-statement resident memory | A saved request peaks at 2.1 GB resident, cause unknown (2026-11-03). Next: reproduce on the single pass. | Allocator accounting names the dominant owner. |
| [Observed stages beyond macOS](#observed-stages-beyond-macos) | The parse and TypeScript's diagnostics replay on macOS only. Next: a confinement on Linux. | The stages replay on Linux. |

## Open work

### Coverage of the front end

<a id="the-front-ends-own-functions"></a>
**The front end's own functions.** The goal is every function of the
repository's own TypeScript verified: `tools/`, `pipeline/`, `tests/` and
`dev/` (the sources under `pipeline/examples/` are the cases' inputs, many
refused by design). Verification states safety, each function's annotated
contract at every call, not that the parser reads TypeScript correctly. The
census checks each module unit by unit over one front per file and records
each unit's own refusal
([measuring coverage](AGENTS.md#measuring-coverage-on-main-and-single-pass),
[function coverage](docs/DESIGN.md#function-coverage-and-release-thresholds),
[statement coverage](docs/DESIGN.md#statement-coverage)); its record groups
the refused units by the blocker each names
([the gap policy](.claude/skills/gap-round/SKILL.md#the-policy)).

Of `pipeline/*.mts` and `tests/` (2026-10-19, 60 s step limit), the first
blockers are Node's `Buffer` through `readFileSync` and `spawnSync` without
an encoding, the worker's socket (`Duplex`, a member the checker
synthesises), a member read after `assert` narrowed a union, and key-adding
writes to `process.env`. `node:assert/strict`'s `equal` promises its actual
is the expected value only in its declaration: the promise is generic, and
no generic promise signature is encoded, which a program's own generic
assertion function meets too.

`readFragmentFile` in `pipeline/verify-source.mts` reads back a document the
run wrote, for a test to forge, and asserts its type with `as` (reason at
the assertion): no TypeScript decoder of the Fragment exists. It stays
outside the goal by decision; what it reads is decoded again by Lean before
anything is checked.

Gap cases standing for census refusals, each header naming its census
functions, are worked in the gap round's order: `blocker-prep-api-constructor`,
`blocker-node-create-require`, `blocker-contextual-default-argument`,
`blocker-compiler-api-generic-meet-field`,
`blocker-compiler-api-contextual-host-shape`, `blocker-in-unknown-walk`,
`blocker-next-compiler-api-ancestor-cell`, `blocker-api-indexed-method` and
`blocker-optional-method-bind`.

<a id="decoders-dictionary-reads"></a>
**Decoders' dictionary reads.** The decoders of `calculus.mts`,
`control-flow.mts` and `diagnostic.mts` read the wire as `Json`, what
`JSON.parse` returns without a reviver
([the contract](docs/SOURCE-CONTRACTS.md#library-globals)): a parsed object
is a dictionary of parsed data, read by key as the index's value or
`undefined`, and a key it may inherit from `Object.prototype` is refused
(`invalid-json-parse-inherited`). A constructor object's one key and its
value are `Object.entries`' pair, so no read at a key known only at run
time is needed.
`dev/lowering-dump.mts` decodes the verifier's output with
`decodeUnits`, which calls `fields` and `nat` in `map` callbacks: imported
functions, whose effect no certificate states
([module composition](#module-composition)).

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
own-key bound excluding the spine key.

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
loses the slice its body tested.

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
hold at a callback keeping array spines. A guard read as a value, whose
slot or entry states its promise signature extended by a rest, meets
`find`'s at its own footprint, and a guard closure by its promise signature
at the footprint its body proposes, its code checked at both
([prototype contracts](docs/SOURCE-CONTRACTS.md#prototype-contracts)).

<a id="generic-equality-condition"></a>
**A Boolean return lowered as a condition.** The
[Boolean-return lowering](docs/SOURCE-ELABORATION.md#a-guards-boolean-return),
which turns a return into a condition, is scoped to type guards and
assertion functions: applied to every return (2026-10-19), it refused
`loose-equality` and `generic-unknown-arguments`, at a comparison of two
values of a type parameter in a condition. That comparison verifies
(`if (left !== right) return 1;` with `left, right: T`, 2026-11-21).

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
collecting one needs a construction that allocates the rest spine from the
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
spines the body allocated, through fresh results ([footprint
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
dispatched call's effect is not established. Either the dispatch
lowers into branch nodes whose callees are evaluated values, or effects are
checked compositionally for these terms.

<a id="footprints"></a>
**Footprints.** [FOOTPRINTS](docs/FOOTPRINTS.md) states the mechanism: a
construct's fact, the operations proved to keep it, stated as closed
footprints, and Lean's node-by-node check that a callback, with what it
calls, stays within one. The checked forms are inspections, typed writes of
fields holding values, and fixed calls, variadic calls and constructions at
a selected signature, `pop`, `shift` and `reverse` at a spine the body
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
`mode8Accepted_sound` ([the design](docs/SOURCE-ELABORATION.md#exceptional-footprints)).
Left: handlers receive no current-content facts across a throw, and a node
with a handler is outside the node-by-node bound, so `map` over a callback
popping a fresh array inside `try` takes its signature with holes
(`map-fresh-handler-refused`).

- a semantic extension: `SafePost` states no postcondition on a throw, so
  `mode8Accepted_sound` needs an exceptional conclusion tied to the exact CLI
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
`Modifies<P, T>`, read by declaration identity and
certified from each definition's body in its own module. The owner's
decisions (2026-10-23): D1 (a), stated effects; D2 the `Modifies<…>`
spelling; D3 `no-return` as an independent first step; D4 T3's extension to
the callback-free node methods' footprints, `forEachChild` excluded; D5
reachability deferred, `Gate`'s `shift` stacks rewritten instead, and the
node-list stable spine its own host-family item; D6 an override whose effect exceeds its base's statement refused at
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
adds a property outside the array's spine, and one past the length leaves
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
entry collects the fresh spine at it and a spread of its value gives a list in the pack. Explicit type arguments on an element call,
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
  primitive string key and value, its footprint `{value: any, spine: keep}`
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
(`Ref null ∧ Ref bool ≤ Ref (null ∨ bool)`) is true and not derivable. An element read keeps no
heap fact: it reads the heap only, but the value it finds is a value only
where the spine's contract says so, which the frame rule would have to take
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
which the first does not use: no instance of a member read assigns a binder
no parameter of the selected signature names. The design question is per-signature binders, or
bounds, in a prototype member's scheme. A closure parameter at a generic declaration's anonymous record at an
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

<a id="module-composition"></a>
**Module composition** as a Lean theorem: the step-indexed argument that
units certified against each other's signatures compose.
[Certified imports](docs/SOURCE-CONTRACTS.md#certified-imports) check an
imported function's code in the importer's run, at its effect-qualified
signature.
Combining a certified import's conclusion with the importer's is left to
this theorem, plus the review obligation that the import binds the certified
unit's closure ([the linking obligation](docs/SOURCE-CONTRACTS.md#certified-imports)).
It also discharges each unit's entry separation, its module cells two apart
([module cells](docs/SOURCE-ELABORATION.md#module-cells)), from the
initialization's allocation of each cell.

<a id="a-semantics-of-the-fragment"></a>
**A semantics of the Fragment.** The parser's rewrites and lowering rest
on review. The Fragment moves close to source JavaScript, the rewrites move
into lowering, and the Fragment gets a direct semantics in Lean: an
executable interpreter that reads it as JavaScript does, with types erased.
Lowering is proved a simulation of it. The interpreter's faithfulness to
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
