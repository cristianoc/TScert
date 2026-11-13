# Draft: the single pass's controls

The single-pass route (`TSCERT_ROUTE=single-pass`, [the single
pass](single-pass.md#9-the-claims-free-front)) has boundaries no proof
covers: what the parser writes, what the type computation proposes, what the
interface stages publish, and how the trusted contracts read. This draft
lists each, the controls that guard it, and the gaps left with what each
needs.

**Evidence labels.** **Measured** gives the command, the commit and the
date. **Cited** names inspected code. **Conjectured** marks a claim not
checked.

## The existing mechanism this extends

The controls of `pipeline/test.mts` ([controls](../STAGE-STORE.md#controls)):
each feeds the verifier an input no case makes (a forged document, a forced
proposal, a mutation of the checker) and requires its refusal; each
registers with `control(…)`, runs in a pool of control processes, and every
operation it runs replays from the stage store. The single pass's controls
are the same mechanism over the route: `tests/single-pass-controls.mts`,
run by `test-all.sh` as the suite "Single-pass controls". A control checks
its case on the route, then runs the pass over the case's fragment under a
forced proposal (`TSCERT_FORCE`), over a forged fragment, or with a
mutation verifier of the pass (`tests/single-pass-mutations.mts`, built as
`pipeline/evidence-mutations.mts` builds the old checker's). The forced
proposals are one list, `tests/single-pass-control-inputs.mts`, which
`dev/single-pass-agreement.mts` reads too.

One kind of entry keeps a control's meaning where the route cannot show it
yet. A forged input
the route accepts where the old route refuses it is a stop: registered with
`stop(…)`, kept as written, run only with `TSCERT_SINGLE_PASS_STOPS=1`, and
named by every run.

## Coverage

Measured: `node tests/single-pass-controls.mts`, engine-cleanup at the
merge of engine-front, 2026-11-12: 163 controls (2 stops not run), every
one passing, 19 s.

| Boundary | Controls | Gap and what it needs |
| --- | --- | --- |
| The parser's fragment: its shape | Malformed bodies, graph labels, claim-shaped annotations, unexamined fields at the root and on nodes, overload units at another function's code, unbound names, deferred mapped types, a regex shape no declaration lists, a family guard's call without its domain: each refused by the fragment's decoder or the front, by the old control's refusal text. | An assignment to an unbound name is refused with no span. |
| The parser's fragment: its contracts (`requires`, `ensures`, loop invariants, statements, store regions) | False postconditions (3), a removed quantified precondition, a false loop-cell invariant, a closure's removed precondition, fresh results, moved, rebased and path regions, an old array at a slot's join, a generic closure's statement, a method's dropped statement, a callee's store separation removed: each refused at its unit. | none |
| The parser's fragment: its declarations | The Promise tag (renamed, dropped, on another prototype, a base or a callable one, PromiseLike in `then`, an allocation keyed by it, the native contract without it), a generic member's result, a union host's member effects, an array's `toJSON`, stable keys and stable links, written applications' arguments, scopes and references, binder roles, an unguarded alias, guard domains, a guard's promise: each refused. | none: the old route's form of this boundary is obsolete (below, "Declarations by identity"); its form on the route has its control ("forged declarations: another import closure"). |
| The parser's fragment: reserved names | Each write form renamed to `stack` refused at the write's span; a member renamed `stack` accepted, the reservation the parser's alone. | none |
| The type computation's proposals | 62 forced proposals over the forces of the Lean front (`TSCERT_FORCE`), each a positive unit accepted unforced and refused forced, or a negative one refused both ways; `elements` on native-length-literal `order@440`; `array-spreads` on two negatives (no positive unit exists: the force skips a check compatible operands pass); `objects` and `optional-reads` on blocker-census-options-default `config@148`; `annotations` on four units, each parameter proposed at `undefined`. | none |
| Loop-head facts | `head-entry` (loop-head-contents `continued@413`); the given facts are an input the pass checks on every edge into the head. | The route reads no given facts: 78 cases need one (the predecessor's case run). |
| The start's entry | `start-facts` (returntype-guard `isName@125`); the mutation `sp-entry` accepts it, so this control catches a pass without its entry check. | none |
| The pass's checks (mutations) | `sp-entry` caught by the `start-facts` control; `sp-footprint` caught by three negative cases. | `sp-edge-evidence` flips no unit of the cases probed. The edge evidence is the pass's own (below, "The pass's own evidence"), so no force of it is kept. `checkedEdge`, `checkedStep` and `returnCheck` have no mutation: their results carry the pass's answers, and a mutation must build that structure. |
| Module interfaces and the stage store | A module's document leaving out a function an import reaches (the imported function, or one its code calls): each unit reading the import refused at its read, `unbound name <name> in <module>, read through the import '<local>'`, on the interface path and the one-process path; a forged interface row refused by the store-map check; a forged stored interface recomputed; an interface stale for an edited module refused; forced and selected requests keyed apart; own-file and reordered requests reach the same keys; an importer's forced execution prints one payload; a timed-out or failed component unpublished; cold and warm runs agree, the interface stages replay warm, an importer's edit executes its stages and replays the module's interface, to a cold run's outcome; the pass's exit without a complete refusal, injected into the verifier `VERIFIER` names, a tool failure. | none |
| Native and host contracts | Every negative case `tests/node-runs.mts` runs under Node (365, its Node half there) refused on the route, but one reviewed acceptance (invalid-native-promise-invariant-result); the stand-in host's reading rules, a declared-optional method, the string-tagged family, the compiler enums through an audited and a mismatched installation, nested installations. | The route refuses a unit where the old producer refused the file (status `unverified` for `unsupported`); `exhausted` at a written obligation is reported `unsupported` (`pipeline/verify-source.mts`, `singlePass`). |
| The lowering | The malformed bodies above; the front's refusal of a form it does not handle is a refusal (two `jsDoc` forms). | 996 refusals of the cases name a node and a Lean term, no span (`expression at node N`); a ported control matches the node where the old one matched a span (four controls). |

## Declarations by identity

The old route's control of another import closure (`values`' code over
`collections-json-uninherited-key`'s declarations) refused the claims,
which name declarations by their position in the document. The route reads
no claims: the code names each declaration it reads by its identity (its
module, name and span, the `target` of a reference), and the front reads
the definition of that identity. So a tampered declaration list changes
what the route accepts for a unit only through the identities the unit
reads:

- An identity the document has no definition of: the unit is refused at
  its annotation (`the declarations required by this unit cannot be
  interpreted: reference has no declaration equation`), the control's
  first half. A unit reading no declaration (`identity`) has a verdict
  independent of the list, the control's second half.
- A position: the route reads none.
- A definition's content under its own identity: the document is the front's
  statement of what TypeScript resolved, and it carries no hash (CLAUDE.md,
  "Wire formats"); neither route can check content against anything but
  the code that reads it. Content the code contradicts is refused by the
  controls of the declarations above (a generic member's result, member
  effects, the Promise tag); content no code contradicts is the trusted
  front's, a review obligation on both routes.

## The old route's controls with no counterpart

The predecessor's classification of `pipeline/test.mts` (engine-switch at
4ecb0149) names 53 controls guarding a boundary nothing on the route guards.
By group:

- **Numeric facts (22): obsolete.** Each forged a fact in the claims at a
  statement entry (a length, an element bound, a quantified or region fact,
  a fact across a write) and required the search to leave it out. The route
  takes no such claim: a fact at an ordinary node is the pass's own transfer
  along its edges (`Programs/SinglePass.lean`, the trusted side its theorem is
  about, [order of work](single-pass.md#order-of-work)), a loop head's is a
  given fact checked on every edge into it (`head-entry`), the start's is
  checked against the request's entry facts (`start-facts`). Until the
  theorem holds, the referee (mode 9) and the negative cases on the route
  guard the transfer.
- **Native and host contracts (about 18): the boundary stands.** The route
  reads the same declarations and native contracts, and the type
  computation proposes the instance at each call. Guarded by the Node
  counterexamples control and the `instances`, `iteration-values`,
  `copy-exclusions`, `elements` and `array-spreads` forces, and per control by
  the negative cases below ("The native and host controls, one by one"): 11
  of 25 covered, 13 in part, 1 not.
- **Contracts and annotations (8): the boundary stands for the proposals.**
  A claim at a point narrower than its annotation (a result bound after a
  call, a type invariant at a call's entry, a guarded fact, a void
  parameter, an unconstrained generic's bound, a dictionary's named view, a
  keyof's unique symbol, a prototype's read type) is, on the route, a
  proposal of the type computation the pass checks at the point. The forces
  `early-contracts`, `objects`, `instances` and `schemes` are the nearest;
  none states a parameter or result narrower than its annotation.
- **Control flow (2): obsolete.** A labelled continue's join and a do-while's
  first entry are the pass's own merge and loop head; the loop head's entry is
  `head-entry`'s control.
- **Mutations (the old suite's mutation controls): replaced in part.** The
  pass's mutations above; the old mutations of `HeapLinks`, `HeapSeparation`,
  `KnowledgeExpand` and `PointClaims` are of modules the pass also calls
  (cited: `SinglePass.edgeEvidenceChecked` calls `PointClaims.checkMappedUsing`),
  but their specializations into the file plans are not mutated.

## The native and host controls, one by one

Each old control of a native or host contract with no guard on the route,
against the negative cases on the route: covered where a negative case runs
the same contract with the same wrong reading and the route refuses its unit
for that reason. Measured: the route's verdicts of the full agreement run at
25aae967 (fr-3), 2026-11-12; the controls read in `pipeline/test.mts` (lines
of the classification at engine-switch 4ecb0149).

| Old control | On the route |
| --- | --- |
| native lengths (189) | covered: the five invalid-native-length cases, each refused at the read past the length |
| splice insertion (332) | in part: the erased receiver-store exception (invalid-splice-insert-map-density); a widened inserted rest has no case, TypeScript rejecting the insertion |
| import.meta (2323) | covered: invalid-import-meta-url, -dirname, -resolve |
| instanceof Map and Set (2343) | in part: the writable Map (invalid-instanceof-map-write); a Set at a Map's view has no case |
| an erased generic contract (2464) | in part: invalid-generic-contract-erasure is refused before the pass, so the pass's own refusal is not shown |
| a function and a class given a signature (2493) | covered |
| thenable instances (2873) | in part: `await`, an async return, `Promise.resolve` and `new Promise` at a callable `then`; an allocation read as a promise has no case |
| an async literal's own keys (2921) | covered, at the return |
| `Reflect.apply` (3069, its claim half) | in part: the argument and receiver negatives; a nullable argument list has no case |
| constructed errors' own keys (3134) | in part: writes and copies of `message`, `stack`, `name`; a construction read as owning them has no case |
| prototype contracts (4075) | in part: invalid-generic-prototype-instanceof, refused at an argument; an invented prototype read type has no case |
| a function's `toString` (4103) | in part: the related cases are refused before the pass; its result read at `number` has no case |
| `Number`, a callable object (5122) | in part: its member and call contracts; the forged results have no case |
| an array given `toJSON` by a write (5669) | covered |
| an inherited `constructor` read (5826) | in part: the writes (invalid-native-promise-constructor-write, -alias); the read at `undefined` has no case |
| a sparse receiver (6098) | covered |
| `split`'s separator (6132) and its tuple (6155) | covered |
| a global regex's replacement (6382) | in part: replacer callbacks that pop; a string replacement has no case |
| host-admitting operands (7791) | in part: other host-admitting spreads (invalid-spread-readonly-array, invalid-spread-empty-record); the readonly record only in gap cases |
| enum claims (8346), frozen literals (8363) | covered |
| enum reverse keys (8383) | in part: the ambient enum (invalid-ambient-enum-reverse); invalid-enum-reverse-number is not handled on the route |
| a corrected compiler-API method (8420) | covered: the control "a compiler-API method a correction makes absent" (each call refused at its read under the corrected description, each verified under the plain one) |
| compiler-API corrections (8875) | covered |

The part of each "in part" row no case shows is a forged reading of a
native at a call or a read, which no source states, since TypeScript
rejects the program. On the route such a reading is a proposal of the type
computation, and the pass checks every proposal at its node: the per-unit
theorem (`passUnitVerdict_safe`, cited: branch engine-proof-unit-wt, its
hypotheses `RunSound` and `RunKeepsSummaries`) is about those checks, and
the forces (`instances`, `guards`, `elements`, `objects`, `optional-reads`)
show each check is reached. What stays trusted is the native's declaration
itself, which the negative cases above and the Node counterexamples guard.
So that part goes with the claims; no control is kept for it.

## The pass's own evidence

The edge search's evidence, the step's derivations and the facts at a
point are computed by the pass and checked by it; no input states them.
Whatever they are, a unit mode 8 accepts is safe
(`SourceClaimJson.PassUnit.passUnitVerdict_safe`). So the old controls that
forged a fact at a call's entry or an edge (written ensures, type
invariants, guarded facts) have no input to forge on the route: their source
half is the negative case each names, refused on the route, and the forged
half goes with the claims.

## Every old control

Each of the 281 registrations of `pipeline/test.mts` (lines at engine-switch
4ecb0149, classes of the predecessor's classification), on the route.
*Covered* names the new control, force or case; *gone* names the mechanism
it goes with (*proposal*: a forged reading is a proposal the pass checks,
above); Counts: covered 158, covered in part with the rest gone 54, gone 68,
new 1.

| Line | Old control | On the route |
| --- | --- | --- |
| 100 | loop cells: the strict invariant is checked independently of proposed facts | covered by forced head-entry, cells |
| 123 | ordered arrays: a forged adjacent-element clause is refused | gone with the claims: a fact at a point is the pass's own transfer |
| 139 | element paths: a strict length bound forged from an inclusive clause left out at its entry, the read needing i | gone with the claims: a fact at a point is the pass's own transfer |
| 157 | Boolean postconditions: a false bound under a true return is refused | covered by "forged fragment: a false bound in a Boolean postcondition" |
| 171 | linear disjunction: a strict bound forged from an inclusive arm left out at its entry, the read needing it ref | gone with the claims: a fact at a point is the pass's own transfer |
| 189 | native lengths: a length fact each native contract withholds, forged at the return, left out and the unit veri | covered: invalid-native-length-* (5 cases) |
| 219 | Each consumer's whole precondition forged at its call's entry, so the call itself would hold there, is left ou | gone with the claims: a fact at a point is the pass's own transfer |
| 274 | forged claims over bounds-quantified-invariant | covered by "forged fragment: a quantified precondition removed" |
| 289 | forged claims over bounds-cell-invariant | covered by "forged fragment: a false loop-cell invariant" |
| 310 | The closure claim's precondition must follow from its written one, both while producing evidence and while con | covered by "forged fragment: a closure's written precondition removed" |
| 332 | splice insertion: widened rest and erased receiver-store exception refused in search and checking | covered in part (erased store exception: invalid-splice-insert-map-density); rest gone: proposal |
| 370 | checked index writes: a bound claimed past the mask alone, another array's comparison or no guard left out and | gone with the claims: a fact at a point is the pass's own transfer |
| 446 | bounded element reads: the read past the end and the read after a pop, claimed at the element type with and wi | gone with the claims: a fact at a point is the pass's own transfer |
| 477 | length terms: an equality of two lengths claimed where no test stated it, left out at its entry, the call need | gone with the claims: a fact at a point is the pass's own transfer |
| 498 | typed-array lengths: a read below a typed array's length claimed where no test stated it, at the length and be | gone with the claims: a fact at a point is the pass's own transfer |
| 532 | string lengths: a code point read below a string's length claimed where no test stated it, at the length and b | gone with the claims: a fact at a point is the pass's own transfer |
| 564 | written ensures: a result bound absent from the call's signature, forged after the call, left out and the read | in part: the case invalid-written-ensures-unstated refused; the forged fact gone with the claims ("The pass's own evidence") |
| 586 | type invariants: an invariant claimed of a cast record at a call's entry, left out there, the call refused | in part: the case invalid-type-invariant-cast refused; the forged fact gone with the claims ("The pass's own evidence") |
| 606 | guarded facts: an invariant's body claimed with its guard removed, and guarded by another field's test, each l | in part: the case invalid-guarded-invariant-other-field refused; the forged fact gone with the claims ("The pass's own evidence") |
| 652 | loop invariants: a back edge breaking one refused at the loop's head with no fact the producer proposes | covered by forced head-entry |
| 679 | quantified facts: a strict element bound claimed over an inclusive precondition and after direct and field ali | gone with the claims: a fact at a point is the pass's own transfer |
| 728 | Advancing the claimed prefix over an unwritten cell must fail independently of the producer's choice to drop t | gone with the claims: a fact at a point is the pass's own transfer |
| 756 | region facts: aliases claimed apart before a write through one left out at the entry claiming it, the read ref | gone with the claims: a fact at a point is the pass's own transfer |
| 790 | every-empty: negative elements forged over [0,1] left out, verified in search and checking | gone with a left-out candidate, a search notion; mode 8 computes facts itself |
| 809 | quantified facts: the strict element bound claimed extended across a push of the length and a push into a poss | covered in part by forced head-entry; rest gone: proposal |
| 841 | typed-array quantified facts: a strict element bound claimed over an inclusive precondition and after a subarr | gone with the claims: a fact at a point is the pass's own transfer |
| 877 | sealed handles: a handle's invariant claimed at a call's entry after a resize, left out there, the call refuse | gone with the claims: a fact at a point is the pass's own transfer |
| 898 | typed arrays: a construction's precondition claimed of a fraction at its entry, left out there, the postcondit | gone with the claims: a fact at a point is the pass's own transfer |
| 919 | forged fresh result: an identity function's statement forged to promise a fresh result, refused at its unit in | covered by "forged fragment: a fresh result stated of an identity function" |
| 941 | forged fresh field: a unit whose region on a fresh field rebases to none, claimed to keep the store it grows,  | covered by forced callees, fresh |
| 962 | ${file}: drain's forged mutable-field freshness refused by transport in search and checking; the same evidence | gone with the old checker's mutation verifier (pipeline/evidence-mutations.mts); the pass's own: sp-entry, sp-footprint |
| 1006 | forged store regions: a region moved to another parameter, refused at the unit's regional check in search and  | covered by "forged fragment: store regions moved" |
| 1037 | forged path regions: a path region moved to its record's own store, refused at the unit's regional check, and  | covered by "forged fragment: path regions moved" |
| 1070 | forged rebasing: a caller's region moved from the field's array to its record, its call's rebased frame refuse | covered by "forged fragment: rebased regions" |
| 1108 | forged fresh store: a fresh result forged onto a function returning its parameter, whose result a regional bod | covered by "forged fragment: a fresh result whose store a caller pops" |
| 1132 | forged slots: a captured binding claimed as a slot, a read after a nested write claimed at the slot's old valu | covered by forced captures, cells |
| 1191 | forged slot join: an old array on the nullish path of acc ??= …, refused in search and in checking | covered by "forged fragment: an old array at a slot's join" |
| 1223 | forged store separations: a separation forged at the caller's entry, and a fact forged across a frame that may | in part: covered by "forged fragment: a store separation removed"; the separation claim half gone: proposal |
| 1259 | forged guarded separation: a separation guarded by another binding than the region position's keeps no length  | gone with the claims: a fact at a point is the pass's own transfer |
| 1287 | unknown store guard tag: refused by the TypeScript and Lean claims decoders | gone with claims decoder (wire deleted |
| 1309 | type invariants: a postcondition forged into the document, refused at the return | covered by "forged fragment: a false postcondition" |
| 1329 | type invariants: a parameter's fact at the returns forged into the document, refused at a return | covered by "forged fragment: a false parameter fact at the returns" |
| 1349 | facts across writes: a bound a field write, an aliased write, a pop or a for...of body's pop takes away, forge | gone with the claims: a fact at a point is the pass's own transfer |
| 1383 | field paths: a read claimed below another root's or another field's length, and a path fact forged at its entr | covered in part by forced paths; rest gone: proposal |
| 1419 | sibling field: a narrowing kept past an aliased write of its key refused in search and checking | covered by forced field-writes, paths |
| 1443 | object destructuring assignment: a target's read at another storage, and a stale narrowing after it, refused | covered by forced cells, stale |
| 1510 | module cache: a read claimed defined, a write's value claimed undefined, and a dropped contract, refused | covered by forced cells, early-contracts |
| 1556 | module cache: escapes in omitted code keep the cache's write refused | covered by "omitted units: escapes in omitted code" |
| 1570 | labels: a claim holding only if continue outer stayed in the inner loop is refused | gone: the pass's own merge (a labelled continue's join) |
| 1589 | do...while: the test's narrowing claimed before the body's first run is refused | gone: the pass's own loop head; forced head-entry |
| 1615 | a closure forged at a longer visitor signature its parameter does not take is refused | covered by forced offers |
| 1646 | an arm's invented callable signature is refused at its incoming edge; the original evidence is refused | covered by forced arms |
| 1673 | array rests: unrestricted intrinsic, omitted default and forged own iterator alias refused | in part: covered by "forged fragment: the rest intrinsic's effect widened"; the omitted default gone with the claims; the iterator alias covered in part by forced offers |
| 1723 | forged claims over | stays (route-independent): runExample of invalid-string-object-hook under Node |
| 1766 | forged intersection binder: null claimed as string at a field initializer, refused in search and checking | covered in part by forced objects; rest gone: proposal |
| 1782 | compiler enum binding, ${reexport ? re-exported : direct}: all ${hostEnums.length} enums, ${mismatched ? misma | covered by "compiler enum binding (4 controls)" |
| 1823 | forged claims over stateful-source/arithmetic | covered by "forged fragment: malformed bodies" |
| 2241 | units: each unit listed with its dependencies; one unit's evidence no evidence of another; a unit claimed narr | in part: covered by "units: each listed with its dependencies, a names list selecting"; one unit's evidence for another gone with the evidence; the narrowed-claim half gone: proposal |
| 2298 | grouped array length claim: refused at the member access in search and check | gone with the claims: a fact at a point is the pass's own transfer |
| 2323 | import.meta's url, dirname and resolve result claimed at string: refused at the read | covered: invalid-import-meta-url, -dirname, -resolve |
| 2343 | instanceof Map and Set claimed beyond their promised views: refused at the iterable | covered in part (invalid-instanceof-map-write); rest gone: proposal |
| 2382 | a deferred mapped type in a forged parser document, at a parameter and at a definition: refused | covered by "forged fragment: a deferred mapped type" |
| 2405 | a graph label, a claim-shaped annotation and an unexamined field in the parser's document, at its root or on a | covered by "forged fragment: graph labels, claim-shaped annotations, unexamined fields" |
| 2464 | Bypass the producer's refusal: manufacture its old proposal by erasing the method in a copy of the AST. Both v | gone with the producer: the route reads the original contract, refused before the pass |
| 2493 | a call through function and a construction through class, forged at a signature: refused | covered: invalid-function-wildcard-call, invalid-class-wildcard-construct |
| 2529 | overload units forged at another function's code: refused | covered by "forged fragment: overload units at another function's code" |
| 2547 | a read of a name its document does not bind, a call's, a spread operand's and an assignment target's: the prod | covered by "forged fragment: unbound names" |
| 2606 | an imported module's functions reading a function left out: left out with it, transitively; a module whose top | stays (route-independent): parser: which imported functions the fragment keeps |
| 2630 | A generic method's argument pack `P` beside a nested generic method binding its own `P` is a pack: the inner ` | covered by "forged fragment: binder roles, an unguarded alias, written applications" |
| 2757 | forged tag documents: the tag renamed, dropped, stated of another prototype or a base's, PromiseLike in the na | covered by "forged declarations: the Promise tag" |
| 2873 | forged thenable instances: await, async return, Promise.resolve and new Promise at a callable then, and an all | covered in part (await, async return, Promise.resolve, new Promise at a callable then); rest gone: proposal |
| 2921 | forged async literal: a returned literal with a callable then claimed as owning no key, refused at the allocat | covered: invalid-async-return-literal-thenable |
| 2946 | forged filled array: its instance claimed at a type other than its explicit type argument, refused in search a | covered by "forged fragment: explicit type arguments widened; forced instances" |
| 3007 | forged tag key: a key-adding write claimed at a symbol key refused | covered in part by forced keys; rest gone: proposal |
| 3027 | forged computed key: a key's read claimed at another literal, a field renamed or spelled otherwise than its nu | covered by forced keys |
| 3069 | Reflect.apply: argument and receiver counterexamples executed; required list checked in evidence production an | covered in part (invalid-reflect-apply-arguments, -receiver); rest gone: proposal; c half open (port: requiredList forged) |
| 3101 | Error copy: freshness, preservation, ordinary objects and copied field claims checked independently | covered in part by forced copy-exclusions; rest gone: proposal |
| 3134 | forged error instances: an own message and a stack claimed of a constructed error, refused | covered in part (writes and copies of message, stack, name); rest gone: proposal |
| 3162 | forged for-of patterns: the element's read and the step's value claimed at a string, refused | covered by forced iteration-values |
| 3192 | forged indexed iteration: the element claimed at a number, refused | covered by forced iteration-values |
| 3222 | forged unknown slices: a read claimed at fewer kinds than the tests leave, refused | covered in part by forced guards; rest gone: proposal |
| 3257 | forged stack member: accepted by Lean, the reservation enforced by the parser alone | covered by "forged fragment: a reserved member name" |
| 3277 | forged reserved writes: each write form renamed to stack, refused at the write in search and check | covered by "forged fragment: writes renamed to a reserved key" |
| 3303 | forged optional method call in an arrow: the saved receiver claimed at undefined refused | covered by forced chains |
| 3323 | forged meet member: the method's object claimed at undefined refused | covered by forced meets |
| 3342 | forged optional method call: either read of the saved object claimed at undefined refused | covered by forced chains |
| 3366 | forged wrapped member call: either read of the saved object claimed at undefined refused | covered by forced chains |
| 3390 | forged chain test: the receiver read again claimed at the tested arm refused | covered by forced chains |
| 3418 | forged present slice: an arm the test admits dropped, and an arm dropped past a test undefined passes, refused | covered in part by forced reads; rest gone: proposal |
| 3452 | forged operand entry: a parameter read claimed narrower than its test refused | covered in part by forced implications; rest gone: proposal |
| 3475 | forged chain entry: a chain's first read claimed as if later operands had answered refused | covered by forced chains |
| 3503 | forged never call: a call of a function that returns claimed at the empty type refused | covered by forced never |
| 3527 | guard binding: a closure's write keeps the guard an ordinary call, another binding's does not | stays (route-independent): parser: the guard's lowering in the fragment |
| 3540 | forged guard branch: a branch a guard that can hold leaves reachable is checked | covered by forced guards |
| 3558 | forged contextual records: a closure claimed outside its record (Box<never> at Box<undefined> included) refuse | covered by forced offers |
| 3632 | early captured aliases: extraction refuses growth before consuming evidence, in and outside loops | covered by the negative case on the route |
| 3650 | forged early bindings: a dropped or narrowed contract, a literal's contract unlike its annotations and a narro | covered by forced early, early-contracts |
| 3850 | forged disjunction: an object read claimed at one arm where another object's test holds refused | covered in part by forced implications; rest gone: proposal |
| 3875 | spread of an intersection: a copy claimed at a field no operand's field gives refused at the merge, in search  | covered by forced spreads |
| 3902 | spread of an intersection: a copy claimed with a key one operand states as a method refused, in search and in  | covered by forced spreads |
| 3934 | forged spread absence: an optional never key the source may own refused in search and in checking | covered by forced spreads |
| 3959 | A contextual readonly view must be derived from the mapped records. | covered in part by forced spreads; rest gone: proposal |
| 3981 | Array literals and ordinary calls use the same checked spread copy. A forged operand claim must be refused in  | covered by forced array-spreads |
| 4009 | A source cannot make the planner emit a malformed flow document. | gone with the flow document decoder (the producer's input |
| 4034 | forged claims over constructor-tuple-spread | covered in part by forced array-spreads; rest gone: proposal |
| 4075 | prototype contracts: invented read types and unbound parameters refused in both modes | covered in part (invalid-generic-prototype-instanceof); rest gone: proposal |
| 4103 | function toString: the call and the proposed signatures forged at number refused | covered in part (the related cases, refused before the pass); rest gone: proposal |
| 4127 | forged declarations: an erased contract, binder roles, an unguarded alias and an uncovered member refused by t | covered by "forged declarations: a generic member's result; forged fragment: binder roles, an unguarded alias, written applications" |
| 4166 | forged import closure: refused | covered by "forged declarations: another import closure" |
| 4202 | label trees other than the one spelling, and a binder as a producer row: refused | gone with label-tree spelling of claims |
| 4233 | The named view remains part of a mixed dictionary's source contract: an index-only replacement must not certif | covered by forced annotations: index-signature-uninherited-key preserveMixed@877 |
| 4246 | a keyof's unique symbol claimed as another symbol or every symbol: refused | covered by forced annotations: keyof-unique-symbol nameOf@901 |
| 4270 | mapEntry's arrow, or AddIndex's construct signature: its last parameter. | covered in part by forced offers; rest gone: proposal |
| 4286 | A closure is created at a variadic signature only when the signature's fixed parameters cover the ones its cod | covered by forced offers |
| 4300 | claims wider than their annotations: refused | gone with claim wider than its annotation |
| 4336 | forged inferred rest result: refused in search and checking | covered in part by forced offers; rest gone: proposal |
| 4361 | Point identities bind claims to executions of the shared graph. Source provenance alone cannot authorize a cla | gone with claim point identities |
| 4400 | evolving use contract: a forged contract refused at the write | covered by forced evolving |
| 4426 | bound next of a union of hosts: one host's result claimed alone refused | covered by forced binds |
| 4457 | unequal bound member effects: refused by the producer's union signature comparison | covered by "forged declarations: unequal bound member effects" |
| 4495 | a guard whose ${signature} signature may change its receiver's store: the field reread refused in search, the  | covered by forced steps, callees |
| 4521 | a comparison of a field's value saved before a callback: the reread after it refused | covered in part by forced callbacks; rest gone: proposal |
| 4561 | a guard's narrowing claimed past a conjunction inside a disjunction: refused | covered by forced implications |
| 4624 | an assertion on a field, then a call claimed to change everything: the reread refused | covered by the negative case on the route |
| 4633 | a guard on a field, then a middle disjunct claimed to change everything: the reread refused | covered by the negative case on the route |
| 4643 | a test, a guard on a field, then a disjunct claimed to change everything: the reread refused | covered by the negative case on the route |
| 4653 | an intersection's discriminant another arm's tag set meets: that arm's missing field refused in search and che | covered in part by forced arms; rest gone: proposal |
| 4714 | a guard's answer held past a reassignment of the answer or the guarded binding: the use refused | covered by the negative case on the route |
| 4725 | a call excepting its receiver's own locations, with no receiver slot: the field reread refused in search, the  | covered by forced steps |
| 4748 | a field's narrowing across a for...of loop: refused without the iterator's fresh object or own-state step | covered by forced loops, steps |
| 4782 | the elements fact: refused without every's elements promise, at another predicate, on graph code claiming eith | covered by forced elements |
| 4824 | an unrestricted call between a guard and the field's reread: the reread refused in search, the forged callee o | covered by forced callees |
| 4847 | a native's call at an unrestricted callback between a guard and the field's reread: refused in search and in c | covered by forced callbacks |
| 4880 | bound next effect of ${name}: excess preservation refused in search and checking at the binding | covered by forced binds |
| 4919 | bound receiver-store effect of ${name}: excess preservation refused in search and checking at the binding | covered by forced binds |
| 4993 | A deferred closure body owns execution points separate from creation. | gone with claim execution points |
| 5008 | A copied finalizer's source site belongs to each actual finalizer action. | gone with claim execution points |
| 5026 | A condition of a Boolean literal type takes one arm (`ifKnown`): claimed at that arm alone, `ready // zs[0]` i | covered by forced decided |
| 5051 | On `cell-union-capture`, whose captured cell is of a union of a `null / boolean` arm and a `null` arm, a conte | covered by forced cells, captures |
| 5110 | The result of a call through a captured union of functions is not narrowed to one alternative's: claimed `true | covered by forced arms |
| 5122 | `Number`, a callable object with methods: a member read is the method its clause states, invoked on `Number`,  | covered in part (Number's member and call cases); rest gone: proposal |
| 5152 | A bound method's variadic signature is covered by the member's when the claimed rest is within the member's (` | covered in part by forced offers; rest gone: proposal |
| 5168 | Explicit type arguments, written as another type than the one the claimed instance fits: on a method call, `re | covered by "forged fragment: explicit type arguments widened" |
| 5200 | A writable index is never met through an own-key bound: a callee holding the object as a writable dictionary m | covered in part by forced keys; rest gone: proposal |
| 5248 | A generic body is a graph request over its binders' parameter rows. Reusing valid evidence must not let an inf | covered in part by forced schemes; rest gone: proposal |
| 5261 | A captured cell keeps the contract its declaration states. Retyping it in the entry claim changes what the clo | covered by forced captures |
| 5274 | A module function is reached at its own annotated signature, which Lean reads from the source; a producer cann | gone with a producer retyping a callee (Lean reads the signature |
| 5287 | Only a module function without a rest parameter has its signature extended by a rest of `unknown` in its slot: | covered in part by forced offers; rest gone: proposal |
| 5300 | The initialization unit's claims are checked like a function's: claiming the constant's initializer at another | covered in part by forced early-contracts; rest gone: proposal |
| 5311 | A call's substitution is the elimination it proposes, so evidence produced for the checked substitutions canno | covered by forced instances |
| 5350 | A graph certificate for the checked Boolean instance cannot validate a different quantified contract. The sche | covered by forced schemes |
| 5362 | A call of a generic closure is claimed at the instance its type arguments name, also where the scheme spells t | covered by forced instances |
| 5435 | A nested closure's claim is checked at the scheme's binder: a ground `() => boolean` claim fits every observed | covered by forced schemes |
| 5465 | Each run reaches a field that is null or absent and throws there: where the source verifies, the nested read's | gone: proposal |
| 5505 | The undefined branch cannot establish a number-valued read observation. | gone: proposal |
| 5524 | A void parameter admits numbers and objects as well as undefined. A forged singleton claim must fail at the pa | covered by forced annotations: void-source-values compareArguments@169 |
| 5540 | An unconstrained source generic admits unknown, but its independently extracted bound excludes calculus top an | gone: proposal (a type argument proposed at top); forced instances is the check's wiring |
| 5559 | annotated union callback: missing signature claims and forged body types refused by both entry points | covered by forced callbacks |
| 5579 | recursive callback: forged leading parameter and result refused in search and checking | covered by forced callbacks |
| 5610 | forged claims at each kind of point: read and checked there | gone with claims at each kind of point |
| 5623 | forged claims over blocker-census-options-default | covered by "forced objects: blocker-census-options-default config@148" |
| 5648 | an array owning toJSON, forged past the parser and the producer: refused by search and check | covered by "forged fragment: an array owning toJSON" |
| 5669 | an array given toJSON by a write, on borrowed claims and evidence: refused at the write, directly and through  | covered: invalid-array-tojson-write, -view |
| 5739 | Borrow successful claims and evidence from a contract accepting the narrow listener / extra argument; consume  | covered in part by forced offers; rest gone: proposal |
| 5783 | a number listener at a signal, on borrowed claims and evidence: refused at the call and in checking | covered in part by forced callbacks, offers; rest gone: proposal |
| 5826 | Own-key exclusion preserves the inherited constructor read. A forged undefined claim must fail both search and | covered in part (invalid-native-promise-constructor-write, -alias); rest gone: proposal |
| 5899 | Widening a generic wrapper's result preserves its input qualification. Forging an unbounded target must fail s | covered by forced instances |
| 5921 | Scheme matching must keep both the native receiver bound and finally's fixed cleanup result contract. These fo | covered by forced schemes |
| 5953 | A qualified instance's input is classified by its certificate: forging Promise.resolve's input to the promise' | covered in part by forced instances; rest gone: proposal |
| 6007 | callback footprint claim {${footprint.value}, ${footprint.store}}, ${file}: ${accepted ? certified : consumed  | covered in part by forced callbacks, literals; rest gone: proposal |
| 6098 | ${method}: a sparse receiver forged readable refused in search and in checking | covered: invalid-flat-map-sparse-callback, invalid-filter-sparse-callback |
| 6132 | forged split separator: a separator claimed at string refused in search and in checking | covered: invalid-split-string-separator |
| 6155 | forged split tuple: shrunk, aliased and annotated results claimed non-empty refused in search and in checking | covered: invalid-split-alias-shrink, -element-write |
| 6182 | forged nullish receiver: a receiver claimed without undefined refused in search and in checking | covered in part by forced chains; rest gone: proposal |
| 6205 | forged fresh result: code returning its parameter refused in search and in checking | covered by forced fresh |
| 6231 | construct footprint claim {keep, keep}, class-constructor-effect: refused at the cell write | covered in part by forced callees; rest gone: proposal |
| 6266 | forged construct form: a string's set claimed at Set<number> refused in search and in checking | covered by forced instances |
| 6288 | forged view form: a Set<number>'s copy claimed at Set<string> refused in search and in checking | covered by forced instances |
| 6310 | forged union form: a string set's copy claimed at Set<number> refused in search and in checking | covered by forced instances |
| 6329 | forged dead optional body: refused where the receiver may be present | covered in part by forced chains; rest gone: proposal |
| 6349 | forged constant extension: refused where the arrow is created | gone with the claims: a fact at a point is the pass's own transfer |
| 6382 | forged dispatch effect: a global regex's replacement refused in search and in checking | covered in part (invalid-regexp-replace-callback-*); rest gone: proposal |
| 6415 | forged replacement callback: a preserving dispatch and a string capture refused in search and in checking | covered by forced callbacks |
| 6464 | forged declaration footprints: each not covering the body's refused in its loop, in search and in checking | covered by forced loops, callees |
| 6494 | forged returned-closure footprints: refused at the return type and at the closure's pop, in search and in chec | covered by forced results |
| 6534 | forged claims over invalid-range-text-argument-write | covered in part by forced callees; rest gone: proposal |
| 6549 | forged claims over call-keeps-view-path | covered by forced paths |
| 6562 | forged initializing write: a cell written whatever it holds, claimed at init, refused at the write in search a | covered by forced cells |
| 6590 | forged throw footprints: a caller of Math.max claimed on a throw, and a handler around a call claimed without, | covered by forced throws |
| 6623 | forged rethrow footprint: an exceptional guarantee refused in production and checking | covered by forced throws |
| 6639 | forged no-return node: a call returning Promise<never> claimed at never refused in search at its typing | covered by forced no-return |
| 6666 | forged no-return node at a non-empty type: gate.fail typed string in a callback claimed at {keep, keep} refuse | gone with the old checker's mutation verifier (pipeline/evidence-mutations.mts); the pass's own: sp-entry, sp-footprint |
| 6691 | forged async footprints: an async function, an async arrow and an async recursive constant reaching no complet | gone with the old checker's mutation verifier (pipeline/evidence-mutations.mts); the pass's own: sp-entry, sp-footprint |
| 6747 | forged stated declaration: a claim above its statement refused in search and in checking, certified only witho | gone with the old checker's mutation verifier (pipeline/evidence-mutations.mts); the pass's own: sp-entry, sp-footprint |
| 6768 | forged stated guard: a guard's claim wider than the statement at its predicate's type refused in search and in | gone with the old checker's mutation verifier (pipeline/evidence-mutations.mts); the pass's own: sp-entry, sp-footprint |
| 6789 | forged stated closures: a weaker effect refused in search and in checking, certified only without the full-dom | gone with the old checker's mutation verifier (pipeline/evidence-mutations.mts); the pass's own: sp-entry, sp-footprint |
| 6830 | stated generic closure: a statement written into the Fragment refused in search | covered by "forged fragment: a generic closure's statement" |
| 6850 | unstated method of a stated member: the class's construction refused in search, the Fragment's statement dropp | covered by "forged fragment: a method's statement dropped" |
| 6882 | stated import: the importer verified relative to the import assumption, the exporting module's run refused | covered by "stated import: the exporting module refused" |
| 6895 | forged field contents: an arm excluded before its field failed every value, a string's or a number's, refused  | covered in part by forced field-writes; rest gone: proposal |
| 6935 | forged field tag facts, of a record's field and of a dictionary's entry: claimed before the test, past an alia | covered by forced field-writes, paths |
| 6987 | forged typed cells: a fact of a field narrower than an entering arm's field type, refused in search and in che | covered by forced cells |
| 7010 | forged field equality fact: claimed before the test refused in search and in checking | covered by forced paths |
| 7034 | forged guard effects: a guard claimed within the empty footprint refused at the declaration, in search and in  | covered in part by forced guards; rest gone: proposal |
| 7054 | forged certified imports: a narrowed unit, dropped qualified reads, stale module claims, a cycle of qualified  | covered in part by forced imports; rest gone: proposal |
| 7223 | element writes: keep at a required position certified in search and checking, keep at an optional one and the  | covered in part by forced callees; rest gone: proposal |
| 7254 | negated guard dispatch: a narrowed claim where the guard answered false refused in search and in checking | covered by forced guards |
| 7285 | known Boolean: an entry claimed past what only a pruned arm carries, and a known Boolean's entry claimed at a  | covered by forced decided |
| 7315 | guard Boolean return: the true return claimed false, the false one claimed true and an arrow's true one claime | covered in part by forced start-facts; rest gone: proposal |
| 7359 | guard closure callback: a claim without the promise, a longer row at an unjustified result and rows short of t | covered by forced guards, callbacks |
| 7421 | filter guard closure: its longer promise signature without the promise, at an unestablished promise, a paramet | covered by forced guards, callbacks |
| 7473 | guard value callback: its claim without the promise, at a promise the guard does not state, and a plain functi | covered by forced guards |
| 7522 | find guard value: a guard popping the searched array forged as preserving stores refused at its declaration in | covered by forced guards |
| 7538 | find guard closure: its longer promise signature at the top footprint and at an unestablished promise refused  | covered by forced guards |
| 7580 | Object.entries's mixed overloads: the dictionary's call at the plain overload and the interface's at the dicti | covered by forced instances |
| 7615 | exhausted footprint check: reported as exhausted in search and in checking | covered by "exhausted footprint check" |
| 7634 | footprints and effects other than the one spelling: refused | gone with claims spelling |
| 7656 | forged import footprints: an imported function's call refused each footprint narrower than everything | covered by forced imports |
| 7709 | Parameters callback effect: forged claims refused in evidence production and consumption | covered by forced callbacks |
| 7725 | unlisted sync guard: forged narrowing claims refused against the parsed declaration in evidence production and | covered by forced guards |
| 7743 | this predicates' index: forged claims narrowing by the omitted index refused against the parsed views in evide | covered by forced guards |
| 7791 | forged host-admitting operands: an argument and a spread operand claimed at readonly fields refused at the cal | covered in part (invalid-spread-readonly-array, -empty-record); rest gone: proposal |
| 7802 | forged recursive closures: a self type at a result and at a footprint the body does not establish refused in s | covered in part by forced schemes; rest gone: proposal |
| 7847 | host reading on a stand-in host: every read of jsDoc refused, also with claims made over a document stating it | covered by "host reading on a stand-in host" |
| 7926 | forged view narrowing: the other arm on the true edge refused | covered by forced guards |
| 7946 | forged guard promise: refused at the guard's body | covered by forced guards |
| 7968 | unpromised guard call: its qualified read refused | covered by "forged fragment: a guard's promise removed" |
| 7991 | guard closure claimed without its promise: refused | covered by forced guards |
| 8015 | guard closure's promise claimed over a narrower parameter: refused | covered by forced guards |
| 8036 | forged regex shape: a literal naming a shape no declaration lists refused | covered by "forged fragment: a regex shape no declaration lists" |
| 8054 | forged tag sets: unsorted, duplicated and single-element sets refused | gone with claims tag-set spelling |
| 8083 | forged residual claims: the node a kind test's false edge leaves claimed at the excluded shape, refused | covered by forced guards |
| 8105 | forged family claims: the excluded arm on a kind test's and on a guard's false edge, a guard value's promise a | covered by forced guards |
| 8208 | forged guard evidence: a membership test's false edge at its true edge's slice, and a guard value's promise ex | gone with guard evidence (evidence gone |
| 8249 | forged guard domains: a domain the argument is not within, with the entry's tags and with none, in a condition | covered by "forged fragment: guard domains" |
| 8322 | nested installations: a copy of the audited package in the client's node_modules is no guard | covered by "nested installations (2 controls)" |
| 8346 | forged enum claims: the tag enum read at a writable record, refused at the read | covered: invalid-compiler-api-enum-field-write |
| 8363 | forged freeze claims: a frozen literal's call at its writable fields, refused at the call | covered: invalid-object-freeze-writable-* |
| 8383 | forged enum reverse claims: a key at number, and an ambient enum's reverse key, refused | covered: invalid-ambient-enum-reverse, invalid-enum-reverse-outside, -number (refused, unlocated) |
| 8420 | corrected method: a method a correction makes absent at a tag is optional in that tag's shape, a generic decla | new: "a compiler-API method a correction makes absent"; the claims half gone with the claims |
| 8492 | declared-optional method: each shape's own optional member, the required one shared, its call refused | covered by "declared-optional method on a stand-in family" |
| 8520 | string-tagged family, activated by its description beside the compiler API's: its guards' calls are membership | covered by "a string-tagged family" |
| 8728 | guards on undefined, over the stand-in family: a node guard's false edge holds a unit, a tag guard's true edge | covered: the stand-in family cases on the route (fr3-1); the forged claims half gone: proposal |
| 8785 | guards on undefined, forged claims: parent present in the throw's handler, refused at its read, and a string o | in part: covered by "forged fragment: a guard's undefined behaviour"; the claims half covered in part by forced guards |
| 8875 | corrections: each of the ${compilerApiFamily.corrections.length} verifies uncorrected, and its claims and evid | covered: invalid-compiler-api-corrected-* (10 cases); the claims half gone with the claims |
| 8929 | tag selection: one per run, the importer's and its module's family readings equal; the module's own run select | stays (route-independent): parser: one tag selection per run in the fragment |
| 8962 | string sets: ordered by code point in the producer, Lean and TypeScript | gone with string sets ordered in producer, Lean and TS |
| 8986 | wire strings: lone surrogates and invalid UTF-8 refused by the producer, Lean and TypeScript | in part: covered by "forged fragment: a lone surrogate and bytes that are no UTF-8"; the claims half gone with the claims wire |
| 9039 | node headers: a referenced proof written out, a proof-less step's sequent stated alone and an ordinary derivat | gone with evidence node headers |
| 9120 | evidence references: a reference past its table, an entry of another kind and a premise at or after its deriva | gone with evidence references |
| 9229 | read summaries: 8 units read through summaries (two qualified bodies', a closure's code's and a typed read's a | gone with evidence read summaries |
| 9420 | evidence spellings: key order, whitespace, key escapes, an exponent and a negative zero read as the parsed val | gone with evidence spellings |
| 9460 | step failures: an exit without a complete refusal, and a failed --explain, are tool failures | in part: covered by "step failures: the pass's exit without a complete refusal is a tool failure"; the producer's `--explain` gone with the producer |
| 9520 | read narrowing: a receiver claimed narrowed past no completed read is refused at the edge, in 10 negatives | covered by forced reads |
| 9551 | negated disjunction: a re-read in a condition claimed past the first test's answer, and a negation as a value  | covered by forced implications |
| 9588 | ordinary read witness: unsupported own-key strengthening refused by the checker; the same exact document check | gone with the old checker's mutation verifier (pipeline/evidence-mutations.mts); the pass's own: sp-entry, sp-footprint |
| 9623 | path witnesses: exact forged evidence refused at incoming edges; wrong receiver/field isolate links, false pre | gone with the old checker's mutation verifier (pipeline/evidence-mutations.mts); the pass's own: sp-entry, sp-footprint |
| 9763 | separation: an argument stated fresh, a level at its depth and a stale depth isolate the separation check; wit | gone with the old checker's mutation verifier (pipeline/evidence-mutations.mts); the pass's own: sp-entry, sp-footprint |
| 9839 | path chains: the honest document accepted; a forged predecessor refused by type coverage, a chain past a call  | gone with the old checker's mutation verifier (pipeline/evidence-mutations.mts); the pass's own: sp-entry, sp-footprint |
| 9932 | A guard's false edge over tag-set arms (PROGRAM-TYPING.md, "A membership test", member-split). Over `Node`, wh | gone with the old checker's mutation verifier (pipeline/evidence-mutations.mts); the pass's own: sp-entry, sp-footprint |
| 10003 | stable keys: a writable (optional and required), an absent and an unmarked optional or writable stable key ref | covered by "forged declarations: stable keys" |
| 10081 | guard after kind tests: a fact of kind at a receiver with an arm lacking kind refused by the claims decoder in | gone with claims decoder |
| 10117 | guard after kind tests: the observed read's present link withheld, the honest evidence refused at the guard an | gone with the old checker's mutation verifier (pipeline/evidence-mutations.mts); the pass's own: sp-entry, sp-footprint |
| 10151 | stable links: the document without the tested member's stable key refused in search and in checking, the hones | covered by "forged declarations: a stable link's key dropped" |
| 10187 | stable optional members: the document without the optional members' stable keys refused in search and in check | covered by "forged declarations: stable optional members' keys dropped" |
| 10223 | stable-link negatives: honest pre-test claims and evidence; mixed, record and let isolate the call, catch isol | gone with the old checker's mutation verifier (pipeline/evidence-mutations.mts); the pass's own: sp-entry, sp-footprint |
| 10324 | A long-lived caller retains only explicitly requested runs, including replayed results and results whose consu | stays (route-independent): run retention of checkSource and checkApart |
| 10435 | replay: cold and warm workers with different request histories agree on outcomes, documents and logs; the warm | covered by "store: cold and warm runs, an importer's edit, over the interface stages; module interfaces: the store boundary" |
| 10647 | evidence reuse: ${units} units' evidence found by one verifier identity accepted by another's + check, no sear | gone with evidence reuse |
| 10683 | evidence reuse fallback: ${variants.map(([n]) => n).join(, )}: a miss, then the search; + reused and searched  | gone with evidence reuse |
| 10724 | evidence reuse in module runs: refused reused evidence searched again before any withdrawal | gone with evidence reuse |
| 10751 | evidence reuse after a whole-check failure: every reused unit searched again, then one check | gone with evidence reuse |
| 10778 | evidence reuse after ${failure}: every reused unit searched and checked again | gone with evidence reuse |
| 10811 | evidence reuse: duplicate evidence lines trigger search | gone with evidence reuse |
| 10831 | evidence reuse ${mode}: complete searched verdicts within the check bound | gone with evidence reuse |
| 10880 | evidence reuse divergence: earlier evidence accepted where the current search refuses; with reuse off the refu | gone with evidence reuse |
| 10906 | edit replay: an edit of an importer replays its module run's search and check, and an edit of one function rep | covered by "store: cold and warm runs, an importer's edit, over the interface stages" |
| 10986 | unit replay: an edit of one function executes its unit's stages and those of the units reading a changed inter | covered by "store: cold and warm runs, an importer's edit, over the interface stages" |
| 11080 | type graph: a callable type's methods decode to themselves | gone with claims type graph decoder |
| 11105 | slice translation: honest evidence accepted across differing stores; forged claims, evidence and anchors refus | gone with slice translation of evidence |
| 11152 | controls: ${controls.length} in ${((performance.now() - started) / 1000).toFixed(1)} s on ${width} + lanes (${ | gone: the old suite's summary line |
