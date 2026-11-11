# Draft: the single forward pass

A design written against TScert `engine-search` at ee789e26. It is an
experiment: one forward pass over a unit's graph that gives the unit's
verdict, fast by construction. The pass is untrusted; its verdict is
compared with the existing search and check, which stay unchanged.

**Evidence labels.** **Measured** gives the command, the commit and the date.
**Cited** names inspected code. **Conjectured** marks a design claim or an
estimate.

## The existing mechanism this extends

What holds at a program point is a
[heap state assertion](../PROGRAM-TYPING.md#heap-state-and-assertions),
checked on every incoming edge, and a statement entry (a cut) holds exactly
its required assertion and the facts the claims supply there
(`CertificateProducer.produceRawUsing`, cited). The steps' rules are the
proved checker `HeapExpressionRules.Checker.ordinary` (cited); the search
selects a step with `CertificateProducer.expressionEffectUsing` and an
edge's slot evidence with `CertificateProducer.edgeUsing` (cited). The pass
keeps all of these: the same assertions at the same points, the same rules,
the same type comparisons. It changes how the state between them is held
and in which order nodes are visited.

## 1. Stable names

A binding is named once, where it is introduced: an input slot, a step's
result, a fresh name at a cut, or at a merge whose predecessors give one slot
different names. A read of a slot (`var i`) gives that slot's value, and its
result keeps the slot's name (the copy rule, `HeapExpressionRules.copy`,
states exactly this equality). An edge's slot map renames no fact: the
target's slot `i` holds the name of the source slot the map reads. A node's
table from names to slots is built only for the names its step reads.

## 2. One state

A state is the name at each slot and one store of facts over names
(cells, values, links, elements, index facts, separation facts), indexed by
the names each fact mentions. A step produces a delta: the facts its rule's
output adds, and the facts of its input the output lost. A fact over a name
no slot holds stays true (a binding never changes); where a step reads it,
its linear facts are first restated through read links and eliminated
(`HeapKnowledge.restateReads`, `eliminateIndices`, as an edge's projection
does today). A linear fact a delta adds over a name a read link gives is
also stated over the read's path (`restateReads`): a later step that drops
the read's name keeps the path's fact.

Beside the store, a state carries the implications its edges establish
(`PromiseCalls.Implication`: where the test holds `true`, the target has
the type), over names: a step's conditional yields, at a pushed edge, state
them of its result; a read of a tested name yields them again at every slot
holding the target; a step's yields are searched with the implications at
its slots (`nodeYields`); a merge keeps those the search's merge keeps
(`CertificateProducer.meetImplications`, over each edge's context as the
source's yields refine it).

## 3. Order

The graph without the edges into cuts is acyclic (every cycle passes through
a cut, `produceRawUsing`'s invariant, cited). The pass visits its nodes once,
in a topological order. A node with one predecessor takes that edge's state;
a merge takes the facts every predecessor holds, a slot whose predecessors
give it different names named afresh, each predecessor's facts renamed to it.
Slots whose predecessors give them the same names in every predecessor take
one fresh name; a name a predecessor holds at slots taking different fresh
names has its facts restated under each, and those fresh names are equal
there. A fact is stored in one form: an unconditional fact reads no
condition's polarity.

## 4. Loop heads

A loop head is the target of a retreating edge of a depth-first walk from
the start, handlers' edges included. A statement entry that is no loop head
is an ordinary node: its state is its predecessor's, or the meet of its
predecessors' at a merge; a written assertion there is an obligation on
that state. A merge works on what differs between its predecessors: the
first's store less each fact another lacks, found where the stores'
persistent maps are not one object (`Store.diff`), and each predecessor's
own differences at the merge's names; the rules below that query a
predecessor's facts run over those differences alone, and the implications
join runs where an edge carries an implication or a slot an edge's type
differs at is a test some edge answers `false`. A name a predecessor
renames that no slot of the merge holds leaves the store there. At a merge, a linear bound every predecessor states of one form
under one condition is kept at the weakest of their bounds; a name a slot
keeps that another slot's fresh name renames in some predecessor is stated
equal to it there; a linear bound over the merge's names one predecessor
states and every other entails over its linear facts near the bound's names
(`HeapKnowledge.entailsKnown`) is kept; the guarded facts the search's join
keeps (`CertificateProducer.joinGuarded`) are kept, each predecessor's guards
first also lowered once through its read links (`lowerGuards`); and a fact
one predecessor states of a slot another holds `null` or `undefined` in is
kept guarded by that tag where every predecessor's facts entail it
(`indicesCheckWith`), as the join guards a store separation. Everywhere, one linear bound
is kept per normalized form and condition, the strongest, and a length atom
is also stated as the linear facts it means (`HeapKnowledge.atomLinear`).


A loop head's state is exactly its given invariant: its written assertion
(`@invariant`, required assertions) and the facts the claims document
records there. Every edge into a cut, a back edge included, carries the
obligation that its state entails that invariant; the cut is visited once,
from its invariant. The pass computes no invariant, guesses none and
retries nothing. Where a unit that verifies today needs a fact at a cut
that neither source gives, that fact is supplied as an input of the pass
and listed.

A cut's given invariant may also state implications (where a test holds
`true`, a slot has a type): supplied as an input of the pass, for the
experiment from the implications the existing search's certificate holds at
the cut, written once per unit to a file of given facts
(`dev/single-pass-given.mts`, `verifier --verify-units 6`) the pass reads
(`TSCERT_GIVEN`), never computed by the pass. Every edge
into the cut carries the obligation that its own implications state each
of them, at a type within the given one.

Likewise a cut's given invariant may state which of its slots hold the
input a promise goal is about (the certificate's `arguments` at the cut):
those slots keep the input's name, and every edge into the cut carries the
obligation that its slots mapped there hold that name. A return under a
promise goal is checked as `ControlFlow.checkReturnResult` checks it: the
answer's type, and the argument, as the step's yields refine it, within the
promise at a slot holding the input's name.

A return under a postcondition (`@ensures`) is checked as
`GraphCode.returnOk` checks it: the output's facts over the result and the
inputs' entry values, each the name the start gave its input, entail it
(`returnEntails`). A cut's given invariant may state which of its slots hold
an input's entry value (`GraphCode.trackTable`'s pairs), those slots
keeping the input's name, each an obligation on every edge into it.

## 5. Steps and obligations

A step's rule is applied to the facts over the names its expression reads,
closed through alias links, read links and linear facts (the facts an
entailment over those names may chain through), at the slots the node's
table gives. A step whose effect may write (`ordinary`, `written`,
`boundedWrite`) reads every fact, since its output states which heap facts
survive. Obligations (a required assertion, an edge into a cut) are
entailment queries against the facts over the names they mention, closed
the same way. A step's facts relate every slot holding one of their names
by an alias link. An edge observing a test releases the alternatives it
contradicts (`HeapKnowledge.withElements`). An edge whose context, refined
by the step's yields, its target does not admit is checked again with each
slot the target does not admit at its refined type read at its unrefined
type; both are types of its value.

### A call of a slot

A call whose callee is a slot is read off the callee's signatures, in the
order `CertificateProducer.expressionWithUsing` tries them, each operand by
identity or a subtype proof, each stated precondition decided once per call over the index facts connected to the
call's slots through shared slots, alias links and read links.
The step is `ordinary` at that derivation, and its output is the proved
layers' (`Checker.ordinary`'s `select`). Where those layers keep every heap
fact the call does not name (`elementsCall`, `requiresCall` at a heap-keeping
effect, `freshCall`, `keepsCall` without `ownCall`), the output over the
named facts is the step's delta and every other fact stays where it is;
otherwise the layers read every fact.

### A footprint

A unit stating a footprint is bounded node by node in the walk, as
`GraphCode.compositionalChecked` checks it (`nodeChecked`): a node's throw
is within the bound where the unit states the bound on a throw or a handler
outside the region with no normal return catches it (`deadHandler`), so an
effect without `onThrow` admits no such handler; a state also carries the names
holding a store the run allocated (`inferFresh`'s facts, over names: a copy
of such a name, or a call at a signature stating a fresh result; a merge
keeps the names every predecessor holds; a cut holds none, its given
invariant stating none); the region from which no normal return is possible
is `GraphCode.deadIterate` over the claims' result types, computed once; at
each node outside it, the node's step is within the bound
(`ExpressionEffects.check`, `writeWithin`, `initWriteWithin`,
`selectedWithinAt` with the receiver's freshness, an empty type), its throw
too where the unit states the bound on a throw, and a return under a fresh
result returns a fresh name; inside it, `deadNode`. A graph the bound
refuses may still be within it by its store regions (`regionalChecked`),
which the pass does not decide: that unit is not handled.

### A step's derivation

Every step's derivation is checked as the checker's `run` checks it
(`ProgramCertificates.checkTreeUsing`, or `PromiseCalls.requiresTree` for a
call at a precondition the step's facts establish): the search's `select`
takes a derivation as given, and a derivation it selects may be one the
check refuses. The read summaries the derivations read are checked once
for the unit, as a response's are (`validSummary`,
`checkReadSummariesResult`), and the unit's expression claims are checked
over them.

### A handler

A node's handler is an edge carrying the thrown value in a fresh name, at
a type admitting every value (its target's landing slot's, or the pool's),
under the facts a throw keeps (`ControlFlow.handlerFacts`, the base step's
`ordinaryOutput`: values, alias links, separation and the index facts
reading no heap), from the node's entry state.

## 6. Where the rules read more than a step's names

- A construction reads every fact: its result's facts (a typed array's view
  length) follow from facts the names of its operands do not reach.

- A step that may write (a call's `ordinary` step, `written`, `boundedWrite`)
  states which heap facts survive it: its derivation is searched over the
  facts its expression names, and its output selected once over every fact
  (`Checker.select`, HeapExpressionRules.lean `Checker` structure).
- An allocation states its object apart from every object slot of the
  context (`HeapExpressionRules.allocLinked`, the separation at the output's
  depth): its output names slots no fact it read names, mapped back through
  the node's names.
- A request's checks over its whole certificate (its footprint,
  `GraphCode.compositionalCheckedResult`; its postcondition, `ensuresResult`;
  its store regions, `regionalChecked`) are made in the walk, node by node.

### Store regions

A unit's store regions, and a footprint the walk refuses node by node for a
result that is not fresh (`effectResult`'s regional fallback, with no
regions), are checked in the walk as `ArgumentRegionGraph.checkNode` checks
each node. A label's regional facts (the slots holding an entry argument
path, the fresh values and cells, the fresh fields) are, at the start, the
regions' input slots; at a loop head, given (from the existing search's
tables, `SourceExtraction.regionTable` and `freshTables`, with the field
names fresh fields range over); elsewhere what every edge into it
establishes. At each node: the cells it keeps (`cellsKept`), the fields its
types keep stable, its origins and fresh outputs (`nodeOrigins`,
`freshOut`, `cellOut`, `fieldOut`), and on each edge what it establishes at
the target; `checkNode` decides the node over those facts and the node's
evidence (its derivation, its step, its facts on entry), each loop head's
given facts the obligation on an edge into it. The entry's conditions
(`checkEntryFields`, a unit neither async nor promising a fresh result)
are checked before the walk.

### Qualified bodies

A qualified body (`SourceRequest.checker`) is walked over the request's own
graph and image check at its checker and aliases. Its checker's `select` is
its `run`, so a step's derivation is checked by the step's own check. Its
request-level conditions are those `effectResult`, `regionalResult` and
`ensuresResult` state of a qualified body.

## 7. Output and scope

The output is the verdict, with the first refused obligation located; a
construct the pass does not handle is an explicit `not handled` result,
never an acceptance. Not handled: a qualified body with code requests.

`verifier --verify-units 3 <fragment> <claims> <file-key> <depth> <name>`
runs the pass; `TSCERT_COMPARE=1` checks, at every node, that the state
entails the knowledge the existing search's certificate holds there.
`verifier --verify-units 8 <fragment> <file-key> <depth> <name>` runs it
over the fragment alone (section 9).

### Observing

`TSCERT_OBSERVE` runs the pass again and stops at one point; the walk keeps
nothing extra otherwise. `node:L` or `offset:K` (the innermost node whose
source span holds `K`) gives that node's state on entry, after its step,
and at a merge each predecessor's state at the merge's slots with the names
each gives every slot. `refusal` keeps each node's states and a merge's
renamings, and at the unit's refusal gives its obligation, the facts over
the names it mentions and those connected, each fact it lacks, and each
fact over those names an earlier state held that its state lacks; for each,
going back from the refusal, where it was last present and what removed
it: a step, an edge, a merge (with the predecessors lacking it, followed in
turn), or a loop head's given invariant. A refusal in a code request (a
closure's, a constructor's or a method's own graph) gives its obligation,
the facts over its names and each fact it lacks, at the code's nodes.
`dev/single-pass-state.mts` runs
it over a kept pipeline run and prints these over source names, with the
bindings' types.

### Counts

`TSCERT_COUNTS` prints, per member, the pass's counts as a JSON line
(`counts: <name> {…}`): the graph's nodes and edges, the nodes reached and
visited, rule applications and those reading the whole store, entailment
queries and the facts they read, merges and the facts their predecessors
state that the met store lacks, the facts per state (sum and largest), the
facts given at loop heads (written, from the claims, supplied); and once per
process the bytes of the files read (`counts-read:`).

### The performance gate

`node dev/perf-gate.mts <pretext checkout at ba09794f>` runs the pass over a
fixed set of units: pretext's `measureAnalysis`, `prepareRichInline` and
`buildEngineProfile`, also from the fragment alone (section 9), and ten
pipeline case units of different shapes. Each
unit's fragment and claims are captured through the pipeline, its given facts
written by `--verify-units 6`, and the pass run three times. Each unit is
compared with `dev/perf-baseline.json`:

- its verdict equals the baseline's;
- each count is at most the baseline's, and the nodes visited equal the nodes
  reached;
- the CPU time of the verifier process (user and system, the best of three)
  is at most the baseline's by the baseline's `tolerance` (a fraction, 0.3)
  or its `slackMs` (20), whichever is larger. Wall time is printed, not
  compared.

The gate prints one table, each value beside its baseline, and exits 1
naming each regression. The counts do not depend on the machine's load and
are the gate's primary measure. The baseline changes only by
`node dev/perf-gate.mts <checkout> --update`, which writes the measured
values; a lower count or time is kept by that command, run on purpose. The
correctness half is `dev/single-pass-agreement.mts`, which exits 0 exactly
when no unit disagrees with the pipeline, none is not handled and every case
ran; a unit whose pipeline check did not finish is counted apart.

## 8. What the pass reads from the claims document

Measured 2026-11-10 on the lowered graphs with no-op nodes left out
(measureAnalysis 1473 nodes, prepareRichInline 3189). Bytes are of each
class in the unit's own claims, the document's other parts listed apart.

| Class | measureAnalysis | prepareRichInline | Source |
| --- | --- | --- | --- |
| (a) entry binding types | 10198, 338 KB | 23609, 861 KB | declared or derivable, flow types inferred |
| (a) expression types | 1341, 73 KB | 2617, 141 KB | derivable by the step rules, but literals and generic calls |
| (b) `current` fields | 17, 0.7 KB | 53, 1.5 KB | inferred |
| (b) `instantiate` | 26, 1.2 KB | 63, 3.0 KB | inferred (type arguments) |
| (c) signature, footprints, storage contracts | 26, 2.2 KB | 52, 3.2 KB | given by the source, relayed |
| (d) entry facts, bounds, quantified, apart, stores apart | 6091, 736 KB | 9032, 1029 KB | written invariants given; the rest inferred |
| (e) type rows | 241, 47 KB | 194, 48 KB | the producer's encoding of declared types |
| (e) other functions' claims | 16, 223 KB | 20, 767 KB | their signatures given; bodies unread |
| (e) imported module runs | 5, 2.0 MB | 10, 8.3 MB | signatures given; bodies unread |

The whole document is 3.77 MB for measureAnalysis (fragment 2.11 MB) and
11.9 MB for prepareRichInline (fragment 4.26 MB). Read and lowered:
measureAnalysis 469 ms (JSON 89 ms, `planImports` 58, `fileFront` 103,
`extractAll` 136, groups 52, the rest 31), prepareRichInline 991 ms (JSON
248 ms, `extractAll` 382, `fileFront` 198). The claims' share of the JSON
read in bytes is 64% and 74%; their share inside `fileFront` and
`extractAll` (decoding labels into the store, relabelling contexts) is not
separated by these timers.

(a) Of measureAnalysis's 78 bindings, 56 hold one type at every entry; 22
(2998 occurrences) change type between entries: a test's narrowing, an
assignment's, a loop's widening. A forward walk computes a narrowing from
the test's rule and an assignment's type from its value's; at a merge and
at a loop head it needs the binding's declared type (TypeScript's type of
the `let` or the parameter), since the join of a literal `0` and an
increment is the declared `number`, not a type a rule synthesizes. Of 31
parameters and storage contracts, 15 keep their declared type throughout.

(b) `current` fields change one verdict in 56 units of loop-heavy cases
(`blocker-compiler-api-grandparent-loop`) and none in 162 sampled units
or the three units. `instantiate` names a generic call's type arguments,
which the pass would infer at the call.

(d) The pass reads entry facts at loop heads only (measureAnalysis: 132
claims facts and 27 written ones at 6 heads, of 6091 entries' facts).
Withheld, measureAnalysis and prepareRichInline are refused at a call's
precondition, buildEngineProfile is accepted, and 10 of 43 accepted units
of loop-heavy cases are refused; none of 162 sampled units changes.

### The referee

A node no path from the start reaches is checked by the proved layer at its
own context; the pass does not decide one whose context some environment
meets (`not handled`). The walk states the bindings where the unit's body
completes, each at the empty type where it never does, at the unit's
completion node.

`verifier --verify-units 9 <fragment> <file-key> <depth> <name>` runs the
search and the proved check (`FilePlans.verifyGroup`) over mode 8's plans:
the same computed types, stand-ins and given facts, every statement entry's
facts the given file states as candidates (`entryFacts`, written by mode 6
with `TSCERT_GIVEN_FACTS=all`), and the search's cuts the loop heads and the
start (`FilePlans.headCuts`), so that it carries facts through every other
statement entry as the pass does. A unit mode 8 accepts and mode 9 refuses
is a hole in the pass until shown otherwise; `dev/single-pass-agreement.mts`
with `TSCERT_REFEREE` prints each as `hole:`. `TSCERT_FORCE` forces
adversarial proposals into the walk, comma-separated: `literals` (every
function literal at keep/keep), `callees` (every function of the file without
a written footprint at keep/keep), `elements` (every element read without
`undefined`), `objects` (every object literal at its expected type),
`spreads` (every spread with every key its operand's type states, optional
ones as present). Under a forced proposal, a forced footprint is one the
function's own unit establishes, and a unit whose dependency of the file is
refused counts as refused where both modes are compared with the pipeline.
The script's controls run with their forced proposal
whatever the patterns, each expected refused by mode 8:
`invalid-method-effect-stated-throw-caught` `wrong` and
`invalid-node-assert-catch-continue` `rows`, under `literals`.

## 9. The claims-free front

### End state

The design's target: no OCaml producer; no claims document, hence no wire
format for it, no decoder of it and no check of its field names across
languages; one forward pass; given facts at loop heads only; every type
computed by TScert in Lean.

`verifier --verify-units 8` reads the fragment and the given file, and no
claims document (`SourceClaimJson.fragmentPlans`, `Claims/FragmentFront.lean`).

- **Store and signatures.** The store is the fragment's declarations and
  annotations, lowered with a type table of the primitives alone
  (`fragmentClaims`). Each function's parameters and result are its
  annotations' types; its footprint is the one its declaration writes
  (`Modifies<…>`, with its `@requires` and `@ensures`), else the ordinary
  effect. Another function, and an import, is read at that signature; an
  import at its declared type. A function literal whose body the walk sees
  change nothing states the footprint keeping values and stores.
- **Types.** Every expression's and statement entry's type and every
  `let`'s storage contract is the walk's (`Synthesis.retypeUnit`), at each
  execution point of the unit's flow graphs (`SourceFlow.pointId`), each
  point holding its node's sites' expressions and its statement's bindings.
  A module constant is read at its initializer's type in the
  initialization's walk with its annotation, a module cell at that walk's
  storage contract (`Front.withInitTypes`). A call of a generic module value,
  a generic class's construction and a `for...of`'s iteration intrinsic are
  instantiated at the binders' types the walk gives them
  (`instancesFromWalk`). A binder a resolution qualifies (`%Await%`,
  `%AsyncReturn%`, `%PromiseResolve%`, an `Awaited<T>`-resolved one) is
  instantiated at its input's type with the certificate that type's form
  gives (`Scheme.resolutionCertificate`: a binder of the unit's own scheme
  or its observation that binder's, a native promise its payload's where
  the binder is resolvable, else observed whatever its payload, a union each
  label's, any other label stable), its observation and result the ones the
  checked certificate establishes (`Scheme.resolutionInstance`); written
  type arguments name its binders but the observations and results. A
  binder's type is read off an actual by matching its parameter's type one
  level at a time (`Synthesis.matchBinder`): the binder itself; in a union,
  the one member naming it at the actual less what the other members admit,
  else each label of the actual at the first member it matches; one type
  constructor's arguments at the actual's of the same constructor; an
  array's elements, a record's fields and methods' results, a callable's
  result at the actual's. Of a call's signatures the first each walked
  actual is within at the binders so read is selected, else the first the
  actuals' count admits. A slice rest of an array pattern is the call of its
  `%RestFrom:k%` at the value, any other rest the tuple of the positions
  after it. A declaration of a statement declaring several holds the
  bindings before it.
- **Function literals.** A function literal passed as an actual is stated
  at its parameter's signature taking the most parameters; any other at its
  written parameters and receiver (a method's `this`). Its effect is the one
  it writes (`Modifies<…>`); else the footprint keeping values and stores
  where the walk sees no write, assignment or call changing the heap, else
  the closed footprint of the classes of contents its writes and calls
  change (an assignment of a binding it does not declare or a field write
  the values; an element write the values and a store's growth; an array's
  `length`, and a call changing a receiver's store or elements, both; a
  call changing its receiver's own locations the values and its store's
  change; any other call its instance's footprint); and it bounds a throw
  (`onThrow`) where none of its calls states a throw left unbounded. A
  callback is stated at that effect where its parameter's effect covers it
  (`Effect.covers`; without `onThrow` where the parameter states none), else
  at the parameter's. Of a call's several signatures, each callback is
  walked first at the first one's parameter, and the signature chosen is
  the first whose parameters admit the walked actuals and callbacks and
  cover each callback's effect, with every binder bound; the binders a
  callback's result would give are first read off the type expected of the
  call's value, where that instance admits the actuals. A written type
  guard or assertion is stated with its promise, its result the guarded
  type, and also at its own parameters. A constant holding a function
  literal that reads it is walked with the constant at its written type,
  else at its written signature keeping values and stores and bounding its
  throws, raised to the type the walk gives the literal until the two
  agree, at most four rounds (the producer's rounds over a recursive
  constant). Its own check decides it (section 5, "A footprint").
- **Early bindings.** Each early binding of a statement list (the flow
  graph's `.early` node) is bound from the list's entry on at its written
  contract: its annotation, else its function literal's written receiver,
  parameters (a defaulted one admitting `undefined`) and result at its
  written effect, else the ordinary one; that is its storage contract. A
  `return`'s value holds the statement's bindings at its own position,
  where a finalizer holds the return.
- **Regions.** A function whose statement states store regions is
  proposed at `top`; the regional check of its own regions certifies the
  statement.
- **Classes and literals.** A class value is the construct signature of its
  constructor's written parameters and instance (its written result), or
  of the fresh constructor it is bound to, with its static fields, each at
  the class binding's annotation's type where it states one. An object
  literal states its own keys exactly (`HasTyUsing.alloc`'s bound); where a
  record is expected, it is that record's form with each field at the
  expected one, else at the value's own type, as written where that is
  within the expected record, else stating its own keys exactly.
- **Loop heads.** A loop head's facts beyond its written assertion are the
  given file's `headFacts` (and `headFactsOfCodes` for each code request),
  each at the statement entries that start where the given one does and hold
  as many slots (a `for`'s head and its declarations' entry share a start); mode 6
  writes them with `TSCERT_GIVEN_FACTS=1`, for the experiment from the
  claims' facts at the loop heads and the start (`SinglePass.loopHeads`).
- **Written-footprint stand-ins.** For a measurement, `TSCERT_STANDINS`
  names a file of footprints the file's functions and imports would write
  (`{"functions": […], "imports": […]}`, each a name, footprint, on-throw
  flag and result footprint), read apart from the source; the bytes read
  count it. A stand-in, as a written footprint, is what the function's
  callers read and what its own unit establishes. `dev/single-pass-standins.mts` writes one from a claims
  document, the producer's proposals standing in for the annotations.

Measured 2026-11-10 at the commit adding this section (perf gate, CPU of
the verifier process, best of 3; read+lower and pass from `TSCERT_PROFILE`
stamps):

| Unit | Mode 3: bytes, CPU | Mode 8: bytes, CPU | Mode 8: read+lower (walk), pass |
| --- | --- | --- | --- |
| measureAnalysis | 5.88 MB, 1044 ms | 2.13 MB, 822 ms | 272 ms (42), 517 ms |
| prepareRichInline | 16.1 MB, 2284 ms | 4.30 MB, 1991 ms | 601 ms (87), 1306 ms |
| buildEngineProfile | 3.12 MB, 252 ms | 1.32 MB, 127 ms | 84 ms (7), 34 ms |

The stand-ins each unit needs, each a function its unit calls whose
footprint the unit's verdict reads (removing any one refuses the unit):
`measureAnalysis` 9 of its file's functions (`countRenderedSpacingGraphemes`,
`addInternalLetterSpacing`, `needsComplexTextPath`, `isSpaceKind`,
`mayHoldCursive`, `getFollowingSpaceTail`, `getTailKerning`,
`getJoinedNarrowing`, `getTextSegmentWidth`) and 16 imports
(`getHanKerningTrims`, `textMayHanKern`, `lazyRegExp`, `getEmojiCorrection`,
`getExtraSpacings`, `getFollowingSpaceMetrics`, `getFontMeasurement`,
`getFontSpaceKerning`, `getHyphenText`, `getSegmentFit`, `getSegmentMetrics`,
`getSpaceKerning`, `getSpaceWidth`, `getTextWidth`, `textMayContainEmoji`,
`zeros`); `prepareRichInline` 4 functions (`getHyphenRooms`,
`setEmptyObjectFacts`, `zeroList`, `getOpeningFit`) and 2 imports
(`isCollapsibleSpaceCode`, `readLetterSpacing`); `buildEngineProfile` none.

Agreement with the pipeline over the 3,303 pipeline cases (mode 8 with the
given files, `TSCERT_REFEREE`), measured 2026-11-11: 6,296 units, 4,682
agree, 830 disagree, 784 not handled. A file the pipeline refuses before any
unit's check is run from its fragment too: the unit holding the refusal's
position is compared with the refusal (91 units), the others are undecided
(85; the pass accepts 24, none the unit an unsafe program's refusal names).
Referee: 10 units mode 8 accepts and mode 9 refuses (all pipeline-verified),
18 the other way: 9 at a node no path from the start reaches, which mode 8
does not handle, and 9 refused (`blocker-import-meta`, `import-meta` ×2,
`null-equality-slices`, `field-write-refinement`,
`equality-several-singletons`, `type-parameter-typeof-family` ×2,
`try-catch` `describe`). Both modes accept seven
units the pipeline refuses: `blocker-pretext-equality-conjunction` `runs@923`,
a gap case (a safe program the pipeline does not verify), and six, each a
valid instance the producer did not propose: `invalid-bounds-callback-footprint` `visit@88`,
`invalid-generic-literal-widening` `use@206`,
`invalid-native-promise-invariant-result` `widen@89` (`make<unknown>` at
the expected result `Box<unknown>`), `blocker-gap-round-cache-answer-inferred`
`real@605` (the callback's literals at the cache's record
`{ answer: string | null }`), and `invalid-spread-intersection-disjoint-literals`
and `invalid-spread-intersection-optional-narrowing` `copied` (each copy is
within the written result; the producer refuses the file at its proposal
heuristic).
