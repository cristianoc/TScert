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

Two kinds of entry keep a control's meaning where the route cannot show it
yet. A unit the route refuses unforced for want of a loop-head fact
(`lostBaselines`, five units) is required refused, so the control fails once
the unit verifies and its honest baseline is to be required. A forged input
the route accepts where the old route refuses it is a stop: registered with
`stop(…)`, kept as written, run only with `TSCERT_SINGLE_PASS_STOPS=1`, and
named by every run.

## Coverage

Measured: `node tests/single-pass-controls.mts`, engine-controls at
801908b6, 2026-11-12: 126 controls (2 stops not run), every one passing.

| Boundary | Controls | Gap and what it needs |
| --- | --- | --- |
| The parser's fragment: its shape | Malformed bodies, graph labels, claim-shaped annotations, unexamined fields at the root and on nodes, overload units at another function's code, unbound names, deferred mapped types, a regex shape no declaration lists, a family guard's call without its domain: each refused by the fragment's decoder or the front, by the old control's refusal text. | An assignment to an unbound name is refused with no span. |
| The parser's fragment: its contracts (`requires`, `ensures`, loop invariants, statements, store regions) | False postconditions (3), a removed quantified precondition, a false loop-cell invariant, a closure's removed precondition, fresh results, moved, rebased and path regions, an old array at a slot's join, a generic closure's statement, a method's dropped statement: each refused at its unit. | Five of these units are refused unforced on the route (`lostBaselines`): their forged refusal shows nothing until a loop-head fact is supplied. |
| The parser's fragment: its declarations | The Promise tag (renamed, dropped, on another prototype, a base or a callable one, PromiseLike in `then`, an allocation keyed by it, the native contract without it), a generic member's result, a union host's member effects, an array's `toJSON`, stable keys and stable links, written applications' arguments, scopes and references, binder roles, an unguarded alias, guard domains, a guard's promise: each refused. | none: the old route's form of this boundary is obsolete (below, "Declarations by identity"); its form on the route has its control ("forged declarations: another import closure"). |
| The parser's fragment: reserved names | Each write form renamed to `stack` refused at the write's span; a member renamed `stack` accepted, the reservation the parser's alone. | none |
| The type computation's proposals | 62 forced proposals over the forces of the Lean front (`TSCERT_FORCE`), each a positive unit accepted unforced and refused forced, or a negative one refused both ways; `elements` on native-length-literal `order@440`; `array-spreads` on two negatives (no positive unit exists: the force skips a check compatible operands pass); `objects` on blocker-census-options-default `config@148`. | An optional field's read proposed without `undefined` has no force (below, `optional-reads`). |
| Loop-head facts | `head-entry` (loop-head-contents `continued@413`); the given facts are an input the pass checks on every edge into the head. | The route reads no given facts: 78 cases need one (the predecessor's case run). |
| The start's entry | `start-facts` (returntype-guard `isName@125`); the mutation `sp-entry` accepts it, so this control catches a pass without its entry check. | none |
| The pass's checks (mutations) | `sp-entry` caught by the `start-facts` control; `sp-footprint` caught by three negative cases. | `sp-edge-evidence` flips no unit of the cases probed: it needs a forced proposal whose edge evidence the check refuses (below, `edge-evidence`). `checkedEdge`, `checkedStep` and `returnCheck` have no mutation: their results carry the pass's answers, and a mutation must build that structure. |
| Module interfaces and the stage store | A module's document leaving out a function an import reaches (the imported function, or one its code calls): each unit reading the import refused at its read, `unbound name <name> in <module>, read through the import '<local>'`, on the interface path and the one-process path; a forged interface row refused by the store-map check; a forged stored interface recomputed; an interface stale for an edited module refused; forced and selected requests keyed apart; own-file and reordered requests reach the same keys; an importer's forced execution prints one payload; a timed-out or failed component unpublished; cold and warm runs agree, the interface stages replay warm, an importer's edit executes its stages and replays the module's interface, to a cold run's outcome. | Injected tool failures of the route's stages need the route to run the verifier `VERIFIER` names (`pipeline/module-interfaces.mts` calls `verifierBuild`). |
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
| a corrected compiler-API method (8420) | not covered: no negative case; the correction exists only as the control's family override |
| compiler-API corrections (8875) | covered |

Most of the gaps are forged readings of a native that no source states,
since TypeScript rejects the program: a negative case cannot carry them,
and each needs a force or a forged fragment on the route.

## Forces the Lean lanes would add

| Force | States | Unit | Expected |
| --- | --- | --- | --- |
| `optional-reads` | a read `o.f` of an optional field at the field's type without `undefined` | blocker-census-options-default `config@148`, accepted unforced | refused at the read (`expression at node N: Tm.readAt`) |
| `edge-evidence` | the edge search's evidence (`CertificateProducer.edgeUsing`) covering no slot, at every edge whose target needs a subtype answer | loop-head-contents `continued@413`, accepted unforced | refused at its edge (`edge from node l to node t`); with it, `sp-edge-evidence` is caught |
| `annotations` | a parameter's or a result's proposed type narrower than its written annotation, at every read of it | type-guards `describe@1103`, accepted unforced | refused at the read or the return |

`optional-reads` and `annotations` are written for `Lowering/Synthesis.lean`
(the read site's field type and `walkUnit`'s parameters) and probed on
those units with the expected refusals; their entries in
`tests/single-pass-control-inputs.mts` land with that file's change.
