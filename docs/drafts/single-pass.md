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
result returns a fresh name; inside it, `deadNode`. A code request of an
async definition has the footprint `top` (`RequestJson.asyncEffects`, as
`RequestJson.codeTableResult` requires of every code): its call returns
normally where its body throws, so no bound its body meets is the call's.
A call whose result is the empty type is within the bound on normal
return; its throw, caught by a live handler, is within it only at a
signature bounding its throws. A graph the bound
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
  (`Checker.select`, HeapExpressionRules.lean `Checker` structure). A heap
  fact over a name no slot holds is outside what the step reads, so the
  step drops it (cells, elements, read links and index facts reading the
  heap, as a handler's edge drops them); a heap-free fact stays. Measured
  2026-11-12 over the pipeline cases: no step reached such a fact.
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

A node no path from the start reaches never runs: the pass follows every
normal and exceptional edge from the start (`loopHeads`' `reached`), so the
nodes it reaches include every node a run can be at, and it decides
nothing of the others (a finalizer's copy for a throw no step raises, a
handler no throw reaches). The proved layer checks such a node at its own
context all the same, which the referee does. The walk states the bindings where the unit's body
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
ones as present, the copy at its own keys exactly), `stale` (a binding a function literal assigns kept
narrowed across a call), `guards` (each guard's and family guard's true
answer stated on its false edge too), `reads` (a member read's receiver
held without `null` and `undefined` at every later statement), `paths`
(each narrowed member path kept narrowed at every later statement), `loops`
(each path narrowed before a loop kept at its head, its body and its exit,
whatever ends it), `decided` (every test's `false` answer unreached),
`finally` (a finalizer's shared entry its statement's normal completion
alone), `never` (every call's statement completing at no value), `meets`
(a type parameter's value dropped from `a ?? b`'s left operand),
`implications` (every constant's initializer narrowing every other
binding where the constant is tested `true`), `arms` (a call of a union of
callables at its first arm's signature). Under
a forced proposal, a forced footprint is one the
function's own unit establishes, and a unit whose dependency of the file is
refused counts as refused where both modes are compared with the pipeline.
The script's controls run with their forced proposal
whatever the patterns, the proposal deciding the control's unit and the
units it depends on (the file's other units compared unforced), each
expected refused by mode 8:
`invalid-method-effect-stated-throw-caught` `wrong` and
`invalid-node-assert-catch-continue` `rows`, under `literals`, and
`invalid-cell-truthiness-narrowing` `kept`, under `stale`, and
`invalid-exceptional-handler-fact` `wrong`, under `throws` (every function
at keep/keep bounding its throws), `invalid-declaration-pop-callback`
`dropped`, under `callees`, `invalid-certified-write-value-import` `zeros`
and the positive `certified-value-import` `tallies`, under `imports` (every
imported function a module establishes keeping values and stores and
bounding its throws), `invalid-compiler-api-guard-loop-partial`
`names`, under `guards`, `invalid-read-narrows-write` and
`invalid-read-narrows-closure` `wrong`, under `reads`, and
`invalid-slot-path-call` `keyText` and `invalid-path-witness-alias`
`wrong`, under `paths`, `invalid-object-spread-two-sources` `count`, under
`spreads`, `invalid-keyed-read` `pick`, under `keys` (a keyed read of an
object at the first name its key may spell alone),
`invalid-closure-offer-narrower-mutation` `wrong`, under `offers`,
`invalid-field-narrowing-for-of-callback` and `-closure` `count`, under
`loops`, `invalid-unassigned-let` `readBeforeAssignment`, under
`decided`, `invalid-map-fresh-alias` `drained`, under `callbacks`,
`invalid-map-fresh-reassigned` `drained`, under `fresh`,
`for-of-program-iterable` `sum` and `bind-union-host` `total`, under
`binds` (each member bound by `o.m.bind(o)` keeping values and stores;
accepted unforced, refused at the bind, its member's effect changing the
heap), `union-callee` `renderEither`, under `arms` (accepted unforced,
refused at the call, the second arm's result outside the first's),
`invalid-closure-default-effect` `stale`, under `defaults` (each
function literal's defaults' changes left out of its effect),
`invalid-generic-closure-effect` `stale`, under `schemes`
(every generic closure claimed keeping values and stores and bounding its
throws, its body's effect unchecked against that claim),
`invalid-compiler-api-guard-loop-finally` `names`, under `finally`, and
`invalid-closure-graph-captured-cell` `counter`, under `never`,
`invalid-type-parameter-meet-narrowing` `present`, under `meets`, and
`invalid-negated-disjunction-saved` `wrong`, under `implications`, and
`invalid-closure-cell-capture-narrowed` `wrong`, under `captures` (every
captured binding at its type where the literal is made), and
`invalid-object-spread-width-replaced` `wrong`, under `objects`, and
`invalid-class-static-inherited-rest` `rest`, under `spreads`, and
`invalid-native-promise-invariant-result` `widen`, under `instances` (a
call's instance kept at the one its actuals give where the type expected of
its value does not admit that instance's result: `make<number>` returned at
`Box<unknown>`, whose field is written at its contract). A control's
`invalid-async-throw-only-arrow`, `-expression` and `-object-method`
`wrong` (refused at the async code's footprint) and
`invalid-method-effect-throw-caught` `wrong` (refused at the caught call's
throw), under `no-return` (a never-returning call changing nothing under a
handler and in an async body too), and `map-stable-set` `distinct`, under
`steps` (accepted unforced, refused at its callback's iterator step), and
`loop-head-contents` `continued`, under `head-entry` (accepted unforced,
refused at an edge into its loop's head). A control's
acceptance counts only with every unit
it `depends` on accepted: a run with named units checks only those, a
dependency's footprint among its proposals, so its reader follows
`depends`.

## 9. The claims-free front

### End state

The design's target: no OCaml producer; no claims document, hence no wire
format for it, no decoder of it and no check of its field names across
languages; one forward pass; given facts at loop heads only; every type
computed by TScert in Lean.

The single pass carries its own Lean soundness theorem: a unit the pass
accepts is safe. With that theorem the existing search and the proved
checker are retired with their code, so the end state has one checker;
this happens once the pass has no gap left against the pipeline over the
cases. Until the theorem exists, the existing checker is the referee
(mode 9). The proof's organising statements are the transfer of knowledge
along each exit edge of a node (a fact is kept where the node's effect
preserves it; new facts follow from the node's exact post) and the check of
every edge against its target's knowledge, loop heads included.

### Order of work

The work has two sides. The trusted side is the pass
(`Programs/SinglePass.lean`): its verdict is what the theorem is about. The
untrusted side is the type computation (the walk and the front), the
module interfaces and the tooling that writes given facts: each of its
results is a proposal the pass checks.

1. The pass is frozen once it reads the given facts its remaining units
   need (a fresh slot and a binding's type at a loop head, each an
   obligation on every edge into the head) and bounds a never-returning
   call's footprint where its throw is caught. A later change of the pass
   states its reason against the proof.
2. The proof's model side depends on no code of the pass and proceeds
   beside every other item: admissible transitions over the step-indexed
   model, the modality indexed by an effect, its laws, the atom axioms.
3. The pass's theorem is proved against the frozen pass, the referee
   deciding soundness until it holds.
4. Work on the untrusted side proceeds beside the proof: the remaining
   rules of the walk, the module interfaces, the units' costs. Its measure
   is agreement with the pipeline over the cases, unit by unit, by a
   complete run before each integration.
5. The existing search and proved checker, the producer and the claims
   wire format are deleted when the theorem holds and no unit disagrees
   with the pipeline, a unit both the pass and the referee accept beyond
   the pipeline counting as reviewed, not as a disagreement.

`verifier --verify-units 8` reads the fragment and the given file, and no
claims document (`SourceClaimJson.fragmentPlans`, `Claims/FragmentFront.lean`).

What mode 8 still takes in the claims wire format, the list the format's
removal works through:

- **An internal carrier.** `fragmentClaims` builds a document in the claims
  wire format (each function's name, name position, parameters and result
  marked unavailable, its footprint, `onThrow` and result footprint; the
  primitives' type rows; empty entries and expressions) and `fileFront`
  decodes it into the front once; the footprints `declarationEffects`
  finds are then written into the front's claims and slots
  (`Front.withStandIns`).
- **The walk's types as claim rows.** `Synthesis.retypeUnitWith` and
  `retypeFromFragment` state the walk's types as a `SourceClaims.Function`:
  expressions, statement entries, storage contracts, entry contents
  (`entryCurrent`) and the execution points' rows; `instancesFromWalk`
  states each generic call's instance and resolution certificates there.
- **Given loop-head facts.** The given file mode 6 writes from the existing
  search's certificate over the producer's claims: each unit's `headFacts`
  and `headFactsOfCodes`, each cut's `graph` row (`arguments`, `implies`,
  `inputs`) and the regional tables' heads (`footprintRegional`).
- **Stand-ins.** `TSCERT_STANDINS`, written by
  `dev/single-pass-standins.mts` from a claims document: the footprints the
  file's functions and imports would write (`qualified` carries the
  imports'), each taking the place of the walk's proposal or of the
  module's established footprint.
- **Module units' loop-head facts.** The given file's lines of the module
  units checked for imports (`module:<location>#<unit>`), which mode 6
  writes from the module runs the claims plan.

- **Store and signatures.** The store is the fragment's declarations and
  annotations, lowered with a type table of the primitives alone
  (`fragmentClaims`). Each function's parameters and result are its
  annotations' types; its footprint is the one its declaration writes
  (`Modifies<…>`, with its `@requires` and `@ensures`), else the ordinary
  effect. Another function, and an import, is read at that signature; an
  import at its declared type, at the footprint its module establishes
  where one does ("Imports" below). A function literal whose body the walk sees
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
  (`instancesFromWalk`); a loop's element is its intrinsic's one binder,
  else (a union's iteration) the `value` its stepper yields. An async
  literal with an expression body is at the promise its `%AsyncReturn%`
  call gives. A binder a resolution qualifies (`%Await%`,
  `%AsyncReturn%`, `%PromiseResolve%`, an `Awaited<T>`-resolved one) is
  instantiated at its input's type with the certificate that type's form
  gives (`Scheme.resolutionCertificate`: a binder of the unit's own scheme
  or its observation that binder's, a native promise its payload's where
  the binder is resolvable, else observed whatever its payload, a union each
  label's, any other label stable), its observation and result the ones the
  checked certificate establishes (`Scheme.resolutionInstance`); written
  type arguments name its binders but the observations and results. A
  binder's type is read off an actual by matching its parameter's type one
  level at a time (`Synthesis.matchBinder`), at what the receiver gives
  it, else at the join of what the actuals give it (the producer's join of
  lower bounds); a bound `U extends T` propagates U's lower candidates
  to T until the finite sets settle (inference.ml:540-556). A binder the signature reads only at its callbacks'
  parameters at the candidate within every other (the producer's meet of
  an upper-only binder's candidates, inference.ml:557-569),
  a primitive's members read off its prototype: the binder itself; in a
  union, the one member naming it at the actual less what the other members
  admit and less the labels another binder of the call reads off one of
  them (a union iteration's parts, each kind's binders apart), else each
  label of the actual, a single one included, at the first member it
  matches, the bare binder last (`TResult1 | PromiseLike<TResult1>` at
  `string` is `string`: the producer's arm of a part's own kind, else the
  bare binder, inference.ml:425-503); one type
  constructor's arguments at the actual's of the same constructor; an
  array's elements (a tuple's positions separately), a record's fields and
  methods' results, a constructor's first signature's result and parameters,
  a callable's result at the actual's, then its parameters
  where the result supplies no candidate, of a callable stating several
  signatures (a guard's plain row beside its promise row) the first naming
  the binder (a written guard's promised type, the producer's `promised`). A binder no actual gives is at what
  the type expected of the call's value gives it, whether or not that
  instance admits the actuals (the call's step decides), else at a
  scheme's declared default read at the binders so far (`then`'s `TResult2
  = never`; the producer's `default`, inference.ml:637-647), a proposal the
  call's instance check decides, else at its bound
  read at the binders so far, else at `unknown` (the producer's upper
  candidates and `top`, inference.ml:584-636). Fresh array literals at generic
  tuple positions keep those positions recursively, each value widened.
  An actual that is a call, at a parameter placing the call's unbounded
  binders at tuple positions (through at most four arrays; of a
  construction's signatures, the first placing them so), is walked at that
  parameter with those binders as holes: a type naming a hole guides an
  array literal (a tuple of the positions it states, a position holding a
  hole at its element's own type) and a call, whose instance is read off its
  actuals and whose callback is walked at its parameter read at the binders
  the call's result gives there, where that names holes in its result alone
  (the producer's `contextual_actual` and `result_bound`: `new
  Map(xs.map((x) => [x.k, x]))` is a `Map` of the pairs' types).
  A source function's unbounded binder inferred directly from its actuals
  widens primitive literal candidates when its result does not return that
  binder bare, within the other actuals' and expected result's constraints
  (inference.ml:608-630). Written bounds, explicit seeds and callback-only
  candidates retain their types. The instance precedes result allocation;
  each existing argument keeps its store contract.
  An ordinary generic constructor supplies its construct signatures at fresh
  binders; its actuals supply their instance as for a function call.
  A packed generic class's construction reads written callback parameters
  before choosing its tuple instance; the tuple parameter's actual supplies
  that instance, whose argument lists the existing lowering derives.
  A generic method's binder its annotations read as packed (a class
  binder at its declaration's packed parameter) is packed in the method's
  scheme, its argument lists its own row (the producer's `T#pack`,
  claims.ml:490-499). A callee of one signature whose rest is a packed
  binder's argument lists takes one last spread of a value of that binder
  at its own type (expression_calls.ml:607-616); the lowering's
  `callPacked` checks the operand (Atoms.lean:220-224).
  A finite record gives a dictionary parameter no index candidate; an
  otherwise unconstrained, unbounded binder there defaults to `unknown`,
  as inference.ml:301-308, 631-632. Its named fields do not constrain other
  own values. Explicit method type arguments seed the instance. An expected union's
  unique application of the result's declaration supplies its contextual
  type arguments. Of a call's signatures the first each walked actual is
  within at the binders so read, satisfying their bounds, is selected, else
  the first the actuals' count admits; a call may omit each trailing parameter whose
  contract admits `undefined` (`T | undefined` included), a variadic
  signature's fixed ones too, passing no rest (the producer's `callable`).
  Of one signature, a fresh literal at a parameter that is a bounded binder
  is made at the bound where the bound names a dictionary (an object
  literal) or a tuple (an array literal), and the binder read off it (the
  producer's `dictionary_bound` and `tuple_bound`); a fresh array literal at
  a parameter whose binders are bounded by literal types is made at the
  parameter read at those bounds, where that leaves it no binder (the
  producer's `literal_bounds`: `pick<K extends 0 | 1>(e: Array<[K,
  number]>)` at `[[0, 1]]`). Of several signatures, an object or array
  literal at a parameter they state differently is made at the first one's
  parameter it fits (the producer's `shared_actuals`). A rest that is a binder's
  argument lists (`...args: T`) binds it at the actuals past the fixed ones,
  widened: an argument pack where only the rest uses the binder, else the
  tuple of them, whose argument lists the rest's are; an occurrence solely
  as a constructor or callback's argument pack supplies no value type (the producer's pack
  rest). A spread actual of a tuple of required positions
  stands for those positions; a spread of any other array for one actual of
  its elements, which only a variadic signature taking no more fixed
  parameters than the actuals before it admits; into an ordinary call of no
  variadic signature, no actual after the first spread runs code. Constructors
  admit later actuals that run code, with tuple spreads saved by their
  execution plan. A slice rest of an array pattern is the call of its
  `%RestFrom:k%` at the value, its binder the union of the value's elements
  from position `k` on, an optional one's with `undefined` (the producer's
  `slice_element`), any other rest the
  tuple of the positions after it. An object pattern's rest is a fresh
  object of the value's one record's fields but the named keys, at their
  types; of any other value, the copies it gives as a spread's operand but
  the named keys. An assignment pattern's rest is a pattern's. A nested pattern's value is stated at its span (a parameter's
  pattern is a destructuring of the parameter), and a defaulted part that
  is a name is read at the field's type at its span. A declaration of a statement declaring several holds the
  bindings before it.
- **Function literals.** A body has no type; an expression body the parser
  writes as statements (a guard's Boolean return, `booleanReturn`) shares
  its expression's span, which keeps the expression's type. A function literal
  passed as an actual takes its unwritten parameters' types from its
  parameter's signature taking the most parameters; any other literal is at
  its written parameters and receiver (a method's `this`). Its body reads each binding
  it captures that a slot holds (`cellLocals`: the unit's or an enclosing
  literal's) at its type where the literal is made, one a cell holds at its
  declared type (the producer's `forget`); `TSCERT_FORCE=captures` reads a
  cell's at its type there too, the adversarial proposal. A literal of no
  rest that is not a guard is stated at its own parameters' row and, beside
  it, at each signature the expected callable states binding more
  parameters whose leading ones are within its own (variadic: at least as
  many), each at its own result and effect, as the producer's
  `from_context` offers them, each offered row at the offered signature's
  result where the body's is within it (`{s with call_effect}`), a use's
  offer at the literal's own leading parameters (`discarded_signature`);
  where the expected signature's leading
  parameters differ from its own in representation (the producer then
  states its interior per row), at that signature alone. A constant holding
  a literal of no type parameters and no rest, unannotated or annotated at
  one signature, read where one fixed signature binding more parameters
  whose leading ones are within the literal's is expected (an argument, an
  annotated binding, a return), offers the literal that signature
  (`closure_offer`). A module constant, unannotated, holding a literal of
  no type parameters, rest, defaults or guard whose result is written, is
  also at its signature extended by a rest of `unknown`, its code
  discarding the further actuals, as a module function's slot is. Where a unit's walk finds such an offer, the unit is
  walked once more with each offered row stated at its literal, the walk's
  one retry, at most one walk beyond the first (the producer's second round).
  `TSCERT_FORCE=offers` offers every longer signature whatever its leading
  parameters, the adversarial proposal. A defaulted parameter is offered
  with `undefined`, bound in the body at its type less `undefined` joined
  with its default's (a parameter of `unknown` at `unknown`), its default
  made at that type at the literal's entry, before the body, its effect the literal's
  (`TSCERT_FORCE=defaults` leaves it out, the adversarial proposal). A
  literal with an array rest is stated at its rest arrow, the pack of the
  rest's element, at its written effect else the ordinary one
  (`ClosureSetup`'s own signature of an array rest); a rest of a tuple of
  required positions is one fixed parameter per position. Its effect is the one
  it writes (`Modifies<…>`); else the footprint keeping values and stores
  where the walk sees no write, assignment or call changing the heap, else
  the closed footprint of the classes of contents its writes and calls
  change (an assignment of a binding it does not declare or a field write
  the values, `x ??= v` of such a binding whose `v` changes nothing its
  initialization, `init`; an element write the values and a store's growth;
  a `for...of` what each step of its stepper's first signature does, the
  values and its store's change where the step changes its receiver's own
  locations (a native iterator's position), else the step's footprint
  (`TSCERT_FORCE=steps` leaves the steps out, the adversarial proposal); an array's
  `length`, and a call changing a receiver's store or elements, both,
  but a call changing the store of a constant holding a store the run
  allocated (one initialized by a call whose instance states a fresh
  result, or by such a constant), which is its instance's footprint (the
  producer's `receiver_fresh`); a call changing its receiver's own
  locations the values and its store's change; any other call its
  instance's footprint); it bounds a throw (`onThrow`) where none of its
  calls states a throw left unbounded; and an expression body that is a
  call whose instance states a fresh result states one (the producer's
  `fresh_result`). `TSCERT_FORCE=fresh` takes every named receiver as
  such a constant, the adversarial proposal. A
  generic function literal (one writing type parameters, a class's generic
  method included) is claimed at the scheme its annotations state, before
  its unit's walk: its binders its own, each bound its written one; its
  receiver its written `this`, an arrow's every value; its parameters and
  result as written, a defaulted parameter with `undefined`, an array rest
  its element; its effect its written one, else, for an expression body
  that with its defaults calls nothing (`Synthesis.mayCall`), keeping values
  and stores and bounding its throws, else the ordinary effect (the
  producer's scheme claim, claims.ml:546-564). Its scheme row and binder
  rows are `Scheme.closureRows`', so its annotations, and its body's walk,
  read each binder as a rigid row; the walk states it at that scheme where
  its body's effect is within the scheme's, and states a call of a local
  holding a scheme with its callee at the call's instance (`closureRows`'
  instances): a binder's row that is a meet (a bounded binder, `T extends
  U` reading `T ⊓ U`) at the one clause row holding the meet of its
  binders' types' clauses with the row's own (`SchemeInstances.meetOk`), and
  elsewhere a meet naming several binders at the type every other's labels
  include; a scheme's rest is stated at the argument pack of its positions
  read at the binders, a binder's meet row there at the binder's type
  itself, the labels a spread's store must hold (`SpreadsInto`). An unwritten result whose parameters contain no nested scheme is
  proposed by a preliminary body walk
  (expression_closures.ml:266-272), then checked at the scheme’s rigid
  rows with the body. A result that this walk cannot determine supplies no
  scheme. Any generic literal a walk meets before the scheme rows are made (a
  declaration's footprint, the initialization's walk), is walked at its own
  parameters as any other literal. A
  callback is stated at that effect on every row it offers, never at its
  parameter's (without `onThrow` where the parameter states none; the
  producer's footprint at each row it claims). Of a call's several
  signatures, each callback is walked first at the first one's parameter
  under the binders its receiver and other actuals give, and the signature
  chosen is the first whose parameters admit the walked actuals and whose
  callback parameter each callback's type is within (the checker's
  subtyping of arrows, which bounds the callback's effect by the
  parameter's), in the store after those walks, with every binder it
  mentions bound (the producer's `matches_actuals`); where none admits a
  callback, the first stating each callback's promise, else the first
  admitting the other actuals, the callback at its own effect, which the
  pass then refuses. A binder the chosen signature does not mention is at
  the empty type. `TSCERT_FORCE=callbacks` chooses the first signature and
  states each callback at its parameter's effect, the adversarial
  proposal. A callback whose parameter is a binder another actual's
  parameter takes at a position of one of its methods is walked at the
  callable the actual's method of that key takes there: of its signatures
  of that arity taking a callable there, the last whose effect covers the
  parameter's method's, else the first (a string's `replace` dispatching to
  a native regex's `[Symbol.replace]`, the producer's `from_actuals`); the
  binder is then read off the walked callback. The binders a
  callback's result would give are first read off the type expected of the
  call's value, where that instance admits the actuals. An empty array
  literal in a callback's body is made at no expected array naming a binder
  of the call that no actual has given a type yet: it keeps its own type,
  an array of no element (the producer's `never[]`), and the binder is read
  off the callback's other returns. A written type
  guard or assertion is stated with its promise, its result the guarded
  type, and also at its own parameters. A constant holding a function
  literal that reads it is walked with the constant at its written type,
  else at its written signature keeping values and stores and bounding its
  throws, raised to the type the walk gives the literal until the two
  agree, at most four rounds (the producer's rounds over a recursive
  constant). Its self reads offer the literal longer signatures as any read
  of a constant holding a literal does (`closure_offer`); where the walk
  states offered rows at the literal, the constant is read at the type the
  walk gives the literal, those rows included, written or not. Its own check decides it (section 5, "A footprint").
  A field of an object literal at a key the expected record states as a
  method is walked at the callable a read of that method bound to the
  record is, its signatures the method's (the producer's `f.read`,
  expression_objects.ml:25-36): a literal there is stated at each of them
  binding more parameters, an iterator's `next` at `(value) => …` beside
  its own row. A generic function literal at a key the expected record
  states as a scheme is allocated at that scheme, the store's contract the
  annotation's (the producer's field built at its contract's type,
  expression_objects.ml:51-52); the allocation's typing checks the
  literal's own scheme within it.
  A constant holding such a literal, read where one variadic signature of
  an element rest binding at least as many fixed parameters is expected,
  offers the literal that signature at its own leading parameters
  (`closure_offer`, closure_offers.ml:54-56). A literal walked with no
  expected type (a field of an argument's object literal) is stated,
  beside its own row, at the rows the parameter's callable offers it once
  the call's instance is chosen (`fit`, `contextRows`).
  A constant holding a class value whose constructor's body returns an
  allocation last, read where a constructor type is expected (a
  dictionary's field at its index's value, less the `undefined` of an
  absent read), is offered: each method of its
  prototype chain a constant of a literal holds, the signature the
  expected instance's member states binding more parameters, at the
  class's instance as receiver; and the class value, the construct
  signature giving that instance, at that signature's parameters where it
  binds more than the constructor, else at the constructor's; a variadic
  construct signature of an element rest as it is (the producer's
  `offer_class`, closure_offers.ml:62-95). A class value is held at its
  own construct signatures, the offered ones among them, as a callable is;
  the constructor's code is checked at each (ClosureSetup.lean:211-224).
  A member stating its signatures at several receivers (an array's methods
  at a dense and at a sparse array) is called at those whose receiver
  admits the walked receiver, each callback walked first at the first of
  them, and its type at the call states those rows.
  A call whose instance's result is the empty type, under no handler and
  in no async body, changes nothing on a normal return, for a literal's
  effect and for a declaration's footprint (the producer's `no_return`,
  source.ml:1031-1035); its throw is its signature's. Under a handler or
  in an async body its throw is caught and the heap it leaves is a normal
  return's: the call changes what its instance's footprint states.
  `TSCERT_FORCE=no-return` reads it as changing nothing there too, the
  adversarial proposal.
  A synchronous throw operand outside a handler or finalizer contributes
  only its exceptional effect, since it has no normal exit
  (source.ml:1140-1144). A finalizer’s body and handler retain those effects:
  the finalizer may replace a throw with a normal return.
- **Declarations.** Each function a wanted unit reaches, callees first,
  is walked as its unit is, each callee read at the footprint found for it
  (`declarationEffects`). A walk proposes the join, by class of location,
  of the changes its writes and its calls' instances make (the grades a
  function literal's effect is found with, the producer's
  `footprint_stmts`): keep/keep where it changes nothing, and nothing where
  the join is the ordinary effect. It bounds its throws where nothing in it
  leaves a throw unbounded. For this reading the grades are the
  producer's (`footprint_expr`, `footprint_stmts`, source.ml:1016-1170): an
  assignment of a binding held in a cell or of one it does not declare, and
  an early binding's declaration, change the values; `x ??= v` of such a
  binding whose `v` changes nothing initializes it (`init`, the producer's
  `NullishAssign`); a field write, update or logical assignment changes the
  values, a `length`'s the stores too; an element write or update the values
  and a store's growth; a call, at its instance and, for a call of a local
  binding, at each signature of its declared type, changes its signature's
  footprint, the values too where it changes its receiver's own locations,
  and everything where it changes its receiver's store and the receiver is
  no constant holding a store the run allocated (`effects_footprint`); a
  typed array's element write (`elementWrite`) is within its footprint; a
  `for...of` changes what its intrinsic's call states and, of each signature
  of the stepper it gives, the values where the step changes its receiver's
  own locations, the iterator, else the step's footprint
  (`iteration_footprint`), everything where the walk determines no stepper;
  a call of an unknown callee (a
  function's `toString` among them: its lowered call tests the receiver and
  calls a value's own `toString` where it is no function) and a call without
  `onThrow` a handler catches change everything; a call without `onThrow`, an iteration and a finalizer leave a throw
  unbounded. A function passed to a call changes what its own signatures'
  effects state; where the call's instance is a generic module function's,
  or the passed function has no known type,
  it changes everything, and so does a generic function literal the
  declaration creates, which this walk reads with no scheme. A
  self-recursive function is walked with itself at keep/keep bounding its
  throws, then at the join of that and what the walk found, until a walk
  finds no more than it assumed, three walks at most. A function whose
  result annotation can state a returned function's footprint
  (`resultWithFootprint`: one function type of fixed signatures stating no
  effect, throw bound or promise), and whose returns each hold a function
  of fixed and variadic signatures, is proposed,
  beside its footprint, the join of those signatures' footprints as the
  footprint of the function it returns (the producer's `returned_footprint`,
  proposal.ml:164-174); its callers read it, its returns establish it
  (`resultWithFootprint`); `TSCERT_FORCE=results` proposes it keeping values
  and stores, the adversarial proposal (the controls
  `returned-closure-footprint` `countLetters`, accepted unforced, and
  `invalid-returned-closure-footprint` `lastRead`). Where the initialization
  calls a function so proposed, the walks run once more, the
  initialization's walk typing the module values at the proposals. A guard or an
  assertion function is proposed like any other, its promise kept. An
  async, generic or rest function, or one with a written effect or a
  stand-in, keeps its footprint. Each proposal is a stand-in: its callers
  read it and its own unit establishes it; the front states it at the
  function's claim and slot (`Front.withStandIns`).
- **Imports that never return.** An import of one fixed signature whose
  declared result is the empty type, stating no promise, is read at the
  footprint keeping values and stores (`Front.withNeverImports`): it has no
  normal return, so its normal return meets every footprint; its throws
  stay unbounded. The reading rests on the declared result, as every read
  of the import does. An intrinsic (`%…%`) keeps its reviewed contract.
  Pretext's `x ?? missing()` is the case: with it the functions calling
  `missing` are proposed their own footprints.
- **Cells.** A binding held in a cell (a module binding the unit assigns,
  one a closure shares, every `let` of a module's initialization) is
  narrowed by its own assignment and by tests, as a slot is, until a
  statement changes a value location other than by assigning that binding:
  from the next statement on it is at its declared type, whether or not
  the walk has met an assignment of it (the producer's `forget` at a step
  that may write cells, execution_analysis.ml:243). What a cell currently holds is a current-content fact,
- **Imports.** An import is read at the footprint its module establishes
  where the fragment alone resolves it to a unit of a module the fragment
  lists (`importNeeds`, `Claims/Imports.lean`), by the checks a qualified
  read of the claims passes ([certified imports](../SOURCE-CONTRACTS.md#certified-imports),
  `eligibleRead`): its declaration identity names that module, and the unit
  is the module's function of the declaration's name whose name lies within
  the declaration's span (a default import's declaration names the
  function, a re-export's the module declaring it; a function the parser
  leaves out, `absent`, is no unit); the unit has no binders, rest,
  receiver or guard, and no code of its module writes its binding; the
  import is one fixed call signature of no rest, receiver, binders or
  promise, stating the unit's precondition and postcondition; the two
  readings of the signature agree (`sameReading`); and no other import binds
  its local name. Only the reads the code the selected units reach mentions
  are resolved, a module's top-level code counted where its functions read a
  name it binds (`reachMentions`); a module's own imports are resolved the
  same way, recursively. The modules are planned callees first, each from
  its own fragment (`fragmentPlansWithModules`): its imports at what the
  modules planned before establish, a module on a cycle with its reads of
  the modules not yet planned at the ordinary effect; each function read
  proposed its walk's footprint (`declarationEffects`) or the one it writes.
  Of the importer's functions reached, one read at a footprint the walk does
  not propose (a stand-in's, or the one an async, generic, rest or
  written-effect function keeps) adds no names: its body is neither walked
  nor checked for the selected units. A stand-in for an import takes its
  place: its module is not planned for it. Before the modules are planned,
  the reads are resolved from the importer down, a round at a time, each
  module's front built once and kept for its plans (`Front.withQualified`):
  a function read whose walk with every import at the least footprint
  (keeping values and stores, bounding its throws) proposes the ordinary
  effect is at the ordinary effect, and its module is planned for it no
  further, nor are the modules only its code reads (first its own walk with
  every module value at that footprint, `Front.changesEverything`, then the
  walks of what it reaches, `declarationWalks` with `least`, each function
  returned at the least footprint too); nothing is so decided in a module
  whose initialization calls a function returning one, whose values hold
  the returned functions at the ordinary effect there. That its walk
  at any established footprints proposes the ordinary effect too rests on
  the walk's grades being monotone in its callees' footprints, conjectured;
  where it fails, the read is at the ordinary effect, which needs no check.
  The groups of the functions proposed more than the ordinary effect, and
  every group they reach, are checked in the same invocation by the same
  mode (mode 8's pass, mode 9's search and check), each verdict on its own
  line as the unit `module:<location>#<unit>`, its loop heads' facts the
  given file's lines of that name, which mode 6 writes from the module runs
  the claims plan (`ModuleRun.givenLines`) and mode 8 reads only for a module
  whose groups it checks. A read is at its proposal where
  the function's group and every group it depends on, of its module and of
  the modules it reads, was accepted there; the importer's units that
  mention the read list that group in `depends`. Every other import, one
  of no module fragment (a declaration file, a package), one the fragment
  does not resolve, one of a module whose plans fail, and one whose
  proposal is the ordinary effect or is not established, is at its declared
  type with the ordinary effect (but the reading of an import that never
  returns). The declared type is what the importer reads in every case;
  only the effect rests on the module's check. A stand-in names an import's
  footprint in place of its module's. `TSCERT_FORCE=imports` proposes
  every function read keeping values and stores and bounding its throws,
  the adversarial proposal: the controls `certified-value-import`
  `tallies` (accepted unforced) and `invalid-certified-write-value-import`
  `zeros` are refused under it, each at its module's refusal of `tally`
  and `drop`, which change the heap.
- **Cells.** A binding the unit assigns and holds in no slot (a module
  binding, one a closure shares) is narrowed by its own assignment and by
  tests, as a slot is, until a statement changes a value location other
  than by assigning that binding: from the next statement on it is at its
  declared type. What a cell currently holds is a current-content fact,
  which no step keeps across a write without a separation
  ([no general frame rule](../PROGRAM-TYPING.md#no-general-frame-rule));
  the producer's entries widen the binding there too. A handler's entry
  and a finalizer's entry on a throw's route state each cell at its
  declared type, and so does a return's route through a finalizer where
  evaluating the returned value changes a value location: a throw keeps no
  current-content fact (`ControlFlow.handlerFacts`; the producer's handler
  edge, proposal_flow.ml:556). `TSCERT_FORCE=cells` keeps the narrowing,
  the controls
  `module-cache-keeps-lengths` `count` and
  `module-cache-before-initialization` `rhs` (its initialization's `let`
  across the call of a function that writes it), `fresh-separation`
  `handlerCell` (a shared `let` at a handler's entry) and
  `module-cells-written-in-turn` `aside` (two module cells at a finalizer's
  entry, on the throw's route and the return's).
- **Early bindings.** Each early binding of a statement list (the flow
  graph's `.early` node) is bound from the list's entry on at its written
  contract: its annotation, else its function literal's written receiver,
  parameters (a defaulted one admitting `undefined`) and result at its
  written effect, else the ordinary one; that is its storage contract. It
  stays at that contract after its declaration, which writes its cell, every
  later read checking the cell's contents against it (the producer's early
  declaration, proposal_flow.ml:317-327); `TSCERT_FORCE=early` holds it at
  its initializer's type, the control `early-bindings` `count`. A
  `return`'s value holds the statement's bindings at its own position,
  where a finalizer holds the return.
- **Finalizers.** The flow graph copies a `finally` block per route that
  leaves the `try` (`SourceFlow.sequence`). The copies of the normal
  completion, the throw and each `break` or `continue` share one entry per
  statement: the join of the statement's normal completion, the bindings a
  throw of its body or handler leaves (each binding they assign at its
  declared type) and each such jump's. A return's copy is walked from the
  return's bindings, its statements' entries read by that copy's points
  (a point whose scope holds `%return@p%`). A loop's close (the
  iterator's `return` that a `for...of` over a program's iterable calls
  when a `return` leaves it) is such a finalizer: each return's copy is
  walked from the return's bindings, and the return's held value holds that
  copy's completion. After the finalizer, its
  bindings hold at the statement's start (the rethrow), at each return's
  held value (that return's copy's), and for each jump; where a copy never
  completes, these are at the empty type.
- **Regions.** A function whose statement states store regions is
  proposed at `top`; the regional check of its own regions certifies the
  statement.
- **Classes.** A class value is the construct signature of its
  constructor's written parameters and instance (its written result), with
  its static fields, each at the class binding's annotation's type where it
  states one. A fresh constructor (a class binding `C.[[class]]`) has first
  the signature giving the instance its body allocates, its tail
  allocations stating their own keys exactly; a class value whose code is
  a constructor an earlier class value of its declaration was walked at
  has that one's signatures. An allocation holding a prototype link states
  its own keys exactly, the link at its walked type and each other key at
  the expected record's field. A copy (`{ ...o }`) whose sources each state
  their own keys exactly, with no optional field, states its own keys
  exactly. Where a type is expected, each copy an object literal with spreads gives
  is made at the first member of it whose field at each named key the part
  is within, its named fields at that member's, where the copy is within
  the member (`TSCERT_FORCE=objects` states the expected type itself).
  A copy (`{ ...o }`, `Object.assign`) is the union of the
  copies its parts give: a named field set in each, a spread merged into
  each once per label of its operand (a record's fields but its prototype
  link and a key it also states as a method, a key two operands of an
  intersection state at the field within the other's; a class value's
  static fields; nothing from a primitive; no stated key from a string or a
  function of no fields; a function's fields, open; a dictionary's string
  fields, its string index the type of every other own string key and its
  symbol index every symbol key's, two indexes of one key class, an
  intersection's, not handled), a key the source surely has at its type,
  one it may have at the union of both, or at a side's index, one either
  may hold at an unknown type dropped; where a side states an index and
  each says what it gives under every key of its class, the copy states
  the index at the union of both sides' and that class's fields', and
  each such field at it (`object_spread.ml`, `merge_alternative`).
  The initialization's generic closures, a generic class's methods among
  them (each quantifying the class's binders, `C."m"#classI`), are claimed
  at the schemes their annotations state, as scheme rows, before its walk
  types the values holding them. A read off a generic class's name (a
  static field) reads the class at an instance, each binder at its bound
  (`unknown` where it states none), recorded as the read's type arguments;
  a bound reading another binder is not handled there.
  A fresh call bound to an unannotated constant and followed by an alias
  or a mutating member use selects a matching overload whose result has no
  required array positions, where one exists (source.ml:1453-1482,
  expression_calls.ml:1079-1087). The call creates that store contract;
  later uses retain it. Other uses retain their existing result proposal.
  A member `o.m` of a union of objects each stating it at the same signatures
  (a host family's node kinds, each its own receiver) is that member with
  every member's receivers and schemes; each stating it at one signature of
  no promise, binders or rest, all taking the same parameters at the same
  effect, it is that signature returning the union of their results (the
  producer's `bound_union`). Any other member of a union is read arm by arm,
  each arm's member at that arm's receiver (its own or its prototype's) or
  its field, the union of them: a union of callables.
  A call of a union of callables, each arm of one fixed signature and no
  binders, is each arm's call: every arm's count admits the actuals, each
  actual is made at the parameter every arm states at its position, else at
  its own type (the producer's `shared_actuals`), and the value is the union
  of the arms' results; for a declaration's footprint it is a call of no one
  instance, changing anything and leaving a throw unbounded (the producer's
  `callable`). `TSCERT_FORCE=arms` states the first arm's signature alone,
  the adversarial proposal. A bounded binder's value is called at its bound.
  An array arm's `length` is a number beside the other arms' reads.
  A keyed read `o[k]` is an array's or a string's element, an object's
  field at each name the key may spell (its string literals, its numbers
  that are array indices: an enum's reverse map, a record at a
  literal-union key), else its index (a dictionary's, with `undefined`).
  A member of a receiver typed by a bounded binder is read through the
  bound (`Plans.boundOf`). A function's `toString` is `Function.prototype`'s. A member read the
  read rule refuses at the walked receiver's type (a member no contract of
  it states, a key no index constrains, a primitive's prototype stating
  none: `readCell`) is the unit's refusal at that read, a call of one
  callable none of whose signatures admits the actuals' count (the
  lowering's `selectSignature`; a construction of a class of no binders, a
  value of no call signature such as `Function`, and a variadic signature
  whose argument lists are the empty type admitting none) the unit's
  refusal at that call, and so is a call of a union of callables an arm of
  which does not admit the count, a call of a union an arm of which states
  no call signature (the lowering's split names an arrow at every arm), a
  spread of an intersection of two operands with index signatures the
  unit's refusal at that spread (the producer's `meet_records`), and
  an expression a part of which is; any other type the walk does not
  determine is a construct the pass does not handle.
  Each expression's type is read at its own statement's point,
  where two statements' expressions share a span (a construction's parts).
- **Function forms.** `Object.assign(f, { … })` at its two annotations is
  the callable object of the record annotation's fields at the function
  annotation's signatures (its variadic ones where `f` has a rest
  parameter), `f` walked at the function annotation and the literal at the
  record's. `f.bind(o, a…)` of a target other than a member of `o` is, of
  the target's fixed signatures (else its one variadic one), the first
  stating no promise, keeping what binding keeps (`Effect.keeps`) and
  taking the prefix within its first parameters: at any receiver, the
  parameters left, its result and its effect past the prefix
  (`Effect.drop`), with each further signature of the same parameters
  promising about a parameter past the prefix. `o.m.bind(o)` (a
  `for...of` over a program's iterable binds its iterator's `next` so) is
  the member at any receiver at the effect binding keeps, of several
  signatures its first of no promise binding keeps (`next(...[value]: [] |
  [TNext])` at its zero-argument row) with each further one of its
  parameters promising (the producer's `Bind`); of a union of hosts whose
  members differ (`%iterator.next.bind(%iterator)` over a union of
  iterables), the member read arm by arm, and bound, of each arm's member
  its first signature of no promise binding keeps, where all take the same
  parameters at the same effect, at any receiver taking them at the effect
  binding keeps, returning the union of their results (the producer's
  `bound_union`; the lowering splits the host's slot, `unionVar`, and binds
  each arm's member, `bindMember`); `TSCERT_FORCE=binds`
  states it keeping values and stores, the adversarial proposal.
  `f.apply(o, list)` and
  `Reflect.apply(f, o, list)` are the target's one signature's result, the
  call at its effect, for a list that is null, undefined or a tuple of
  required positions, or, for a target taking only a rest, an array of any
  length. A method at a computed key of one string literal is that member; at an
  index key of an array, the array's element there, called at the array.
- **Collected values.** A spread of a program's iterable and an array
  pattern over one collect the values its protocol's steps yield
  (`collect`, `protocolPattern`, tools/fragment-statements.mts): the
  collected array (`%items`, `%rest`, an unannotated `[]` the steps push
  onto) is made at the array of the values a step not done yields, an
  element binding (`let %vI = undefined`) at `undefined` or those values,
  the producer's evolving bindings (statement_analysis.ml:222-240); the
  step's type is the protocol's bound `next` of the statement's other
  bindings, or of the next statement, walked ahead.
  A `for...of`'s iteration intrinsic of no binders (a string's,
  `%Iterate:string%`) is called at the iterable as a generic one is, its
  stepper held at the loop's head and its `value` the element.
- **Expected types.** A store's contract is fixed where the store is made;
  a read is a copy, an upcast of an immutable value, or an upcast of a store
  to a readonly view of it. An annotated declaration holds an object it is
  initialized with at the members of its declared type the object is
  within (a primitive, nullish or callable value as an assignment narrows
  it; an early binding at its written contract), never at the exact type of
  the store it was made from; an object literal assigned to a binding a
  slot holds likewise (the producer's `slot_holds`). So a value is made at the type its position
  expects: a return's, an annotated declaration's, an assignment's (also
  `??=`, `||=`, `&&=`), a field write's field, an element write's contents,
  a cast's target, a function literal's result; and from there a
  conditional's arms, the right operand of `&&`, `||`, `??` and `,`, an
  object literal's fields (the union of the fields the expected members
  state at the key) and an array literal's positions. By form: an object
  literal states its own keys exactly (`HasTyUsing.alloc`'s bound), where
  nothing is expected each field a literal's widened type, a name's, a
  read's or a const assertion's (`true as const`) as it is (the producer's
  `fresh`); at a
  dictionary with a writable index it is allocated at that dictionary with
  each of its keys a field (at the dictionary's named field, else its
  index), the optional fields it leaves out absent; at a record, it is that
  record's form with each key a field the allocation writes (a stable key
  the record states as a view stays a view), at the expected field, else at
  the value's own type, as written where that is within the expected
  record, else stating its own keys exactly. An array literal is made at the
  one array member whose positions admit its elements, each element made at
  its position; at an iterable other than an array, at the readonly array
  of what it yields (its `[Symbol.iterator]`'s `next` results' `value`),
  presence `readable`; where nothing is expected, at an array of its
  elements' widened union, presence `readable`. `[…] as const` and `{…} as
  const` make the operand at the const type. A function literal writing no
  parameter's type is walked at the expected signature taking the most
  parameters. A call's binders are read off the receiver and the actuals
  first, those still unbound off the expected type; where the instance so
  read has a result the expected type does not admit, the expected type's
  instance where it binds every binder and admits the actuals. A call whose
  signature states a fresh result is made at the first expected array whose
  elements admit the result's.
  An uncontextualized object literal nested directly in a fresh field is
  made at its own open record, unless its own keys are required exact or
  it carries a prototype (expression_objects.ml:46-54, 83-97).
  A spread nested inside a fresh call actual receives the expected record
  fields recursively; each spread operand that is a literal receives the
  optional fields of that context, and each resulting copy is checked
  within an expected arm (expression_objects.ml:135-218).
- **Narrowing.** A tag test narrows a binding or path by the tag slice;
  `unknown` (a `source` label) becomes the kinds of value the test does not
  contradict where it contradicts some (`BranchRefinement.sourceSlice`); a
  type parameter's value (its meet with its bound), where a test naming one
  primitive family holds, becomes that family, as `unknown` does, and stays
  where it fails; under any other test, a meet row becomes the meets of its
  parts with each clause of it the test does not contradict, none where it
  contradicts every one (`T ⊓ (number | null)` less `null` and `undefined`
  is `T ⊓ number`, the lowering's `observedSlice`). Where a constant holding
  a condition's value (a guard's call, a test, a conjunction of them,
  `implicationForm`) is tested `true`, each constant and each parameter no
  cell holds is at what the condition narrows where it holds
  (`constantImplications`). A test that cannot give an answer (its value's slice for
  it is empty, `!e` where `e` cannot give the other, `a || b` not `false`
  where either operand is never falsy, not `true` where neither is ever
  truthy, `a && b` dually) leaves the arm of that answer unreached, walked
  for its entries; a loop whose test cannot answer `false` is left by its
  breaks alone; a statement whose value has no type (a call of a function
  returning `never`) does not complete, what follows it walked for its
  entries, unreached, each binding at the empty type (the producer's
  `unreachable`); an unreached expression whose type the walk does not determine is at
  the empty type. `typeof x` is a `string`. A
  call of a type guard, on its true arm, and a statement calling an
  assertion function, after it, narrow the binding the promise names to
  its members within the guarded type, else to that type; a method's
  promise is read at the member's type. A family guard testing its
  operand's field (`ts.isIdentifier(n)`) narrows the binding to the arms
  whose field can answer so, `undefined` answering no `true` and, where
  the guard throws on it, no `false` (`PromiseCalls.memberFieldSlice`). A
  member read of a receiver that may be `null` or `undefined` reads the
  others (it throws on those, `nullishSplit`), and past it the receiver,
  where a slot of the unit holds it, is without them (`readNarrowing`);
  an assignment, a join and a loop head end that as any narrowing. A destructuring
  default is added where the part may be `undefined`, made at the part's
  type less `undefined` (a parameter's default at its annotation's); a
  function the default makes within a callable part's type is held at that
  type (a parameter's type is what the body reads), an object literal
  default at that type's members it is within. Strict equality with
  a literal holding narrows the operand, where it may hold the literal
  (`unknown` included), to the literal (but `0`, which `-0` equals too);
  a comma expression tested is its last operand's test, where the test
  assigns no binding; equality with an operand holding one of
  several singletons (each member of its type one, `equalitySplit`)
  narrows each operand to the union of its slices at the
  singletons the other may hold. `k in x` holding states a record's optional
  `k` present (a field where the record states one, else a view) and a
  dictionary not naming `k` with `k` a view of its index. `Array.isArray`
  holding keeps the labels the edge's observation keeps
  (`arrayRefine`, `BranchRefinement.arraySlice`). A discriminant test no
  member of a binding can answer so leaves the binding no value; an arm a
  test leaves a binding or path no value is walked for its entries, and
  where it completes or returns is unreached.
  A member read whose receiver supplies no cell contract is a located
  refusal, as `Plans.readCell` (Plans.lean:518), including a binder meet
  whose bound supplies no readable row. A primitive member whose prototype
  is absent from the unit is likewise a located read refusal
  (`Plans.primitiveArms`, Plans.lean:646-648).
- **Field contents.** A statement entry states the member paths a test
  narrowed (its `current` contents, an execution point's `entryCurrent`),
  each a member of an object other than `length`: a test of the path, a
  guard or a family guard whose actual it is (a guard's only where its call
  changes no value of the heap), and a discriminant test of a member of it
  (`o.key.kind` narrows `o.key` to the arms whose `kind` can answer so),
  where some read of the unit's walk reads the path, or a longer path of its
  root, at its narrowed type. A
  path's narrowing ends at a write of its field, at an assignment of its
  root (a destructuring assignment's from its first target on), after a
  call whose instance may change a value of the heap (or whose callee is
  unknown) but where each member of the path is a key every arm of its
  receiver states stable (the producer's `stable_path`), and, but such
  stable paths, after the left operand of `&&` or `||` whose right operand's
  walk ends a path; a guard's call narrows its actual's path only where its
  own call ends none. A method call reads its member path at its narrowed type before walking
  its actuals, as any other read (expression_properties.ml:32-35); the
  receiver remains the object holding the member. A path's prefix is read at its narrowed type; a
  write of an element at a key naming no one field or number, and
  `Object.assign`, end every path; after `o.f ??= v` (and `||=`, `&&=`)
  the path `o.f` holds the assignment's value, and after `o.f = v`, of an
  immutable binding's object every record arm of which states `f`, its
  contract less the nullish values `v` does not admit (the producer's
  `written_field`); a handler states none. An array literal assigned to an array pattern of as many names or
  members (`[o.f] = …`, at the field's type), none defaulted, is made at
  the tuple of their declared types. A path narrowed
  before a loop is stated at its head, at each statement entry of its body
  and past its exit where nothing in its test, body and update ends it (a
  write of a field the path reads, an assignment of its root, a call that
  may change a value of the heap) and its root is no binding the loop
  declares; over a `for...of`, also only where the iterable is an array,
  the root holds no allocation (an object or array literal) and each member
  of the path is a required field every record arm of its receiver states,
  none a `length` (the producer's `separated_path`: the locations an
  iterator's step keeps).
  Over a `for` or `while` loop, a path whose root the loop neither
  declares nor assigns is held from its head on, through the test and the
  body, where nothing in the loop calls or writes (an increment or an
  assignment of a binding aside) or each member of the path is stable.
  After such a call, each binding a function literal walked so far assigns
  (one it captures, held in a cell) is at its declared type again.
- **Named guard offers.** A longer signature collected for a named guard
  retains the guard's written promise and proposed body effect when the
  requested promise matches (expression_closures.ml:396-399,433-450).
  Its leading parameters supply that row's interior; the body's result
  remains Boolean. The code check establishes the promise separately at
  every advertised row, including the original signature.
- **Constructor result offers.** When an offered constructor's result
  widens one of the class's method signatures, a fixed argument pack offers
  that result at the constructor's own parameters
  (closure_offers.ml:62-95). An element-rest offer keeps the existing
  variadic rule. The constructor body and every method row establish the
  proposed result; fixed storage contracts remain unchanged.
- **Iterator bind control.** The program-defined iterable's sum accepts
  unforced in modes 8 and 9 and refuses the forced bind proposal. The
  agreement tool treats it as a positive control: unforced closed acceptance
  is required, and forced refusal satisfies the control
  (dev/single-pass-agreement.mts, the positive-control comparison).
- **Async literal results.** A generic module value retains which binders
  have no written bound, through equation lowering and preparation. Direct
  primitive candidates of those binders use inference.ml:608-630's widening
  before resolution and fresh allocation; explicit arguments and declared
  bounds retain their constraints. A literal's contextual result guides
  async return calls before allocation (expression_closures.ml:263-268).
  A widened candidate's observation and resolution result are instantiated
  by its resolution certificate before comparison with the expected result;
  a failed resolution retains the original candidate. Thus the expected
  resolution result bounds widening (inference.ml:220-229,248-250,620-628).
  An async block's result is the union of its walked return calls, as for
  an expression body
  (expression_closures.ml:263-291). The resolution instance and each code
  body's return are checked; no existing promise store changes contract.
- **Implemented overload interiors.** A literal with no binders, rest or
  defaults, expected at several fixed signatures of its own arity, proposes
  that callable and walks its body once at each signature's parameters and
  result (expression_closures.ml:455-473). Each row supplies its expression,
  entry and local storage proposals through the existing closure overlay.
  Captured cells keep their declared contracts. The front places each
  overlay at the body's execution points; ClosureSetup.lean:322 checks its
  row count, and Claims/Json.lean:993-1056 checks every code body.
- **Annotated recursive constants.** A non-early constant’s annotation supplies
  its recursive signature; the self-effect starts at keep/keep with a bound
  on throws (statement_analysis.ml:294-317). The existing four-round
  self proposal checks agreement with the walked body (proposal.ml:224-240);
  the annotation supplies contextual parameter types. Each code body must
  establish its proposed signature and footprint.
- **Annotated module callables.** An immutable annotated callable retains a
  separately inferred keep/keep effect on the same receiver, parameters and
  result, including its bound on throws (semantic.ml:231-241). The default
  receiver admits source values; the literal’s internal `top` receiver
  also admits them. The declaration keeps its signature and every other
  component. The initialization’s code body and each use check this proposal.
- **Write footprints.** A compound write at a numeric literal index proposes
  value `any`, store `grow` (source.ml:1086-1087). A logical
  write to a required writable field of source values proposes value `any`,
  store `keep` (source.ml:1111-1113; type_queries.ml:1009-1027); the receiver
  is a binding or a path with known contents. `ExpressionEffects.sourceField`
  checks the principal invariant operand. Each proposal is checked against
  the body at SinglePass.lean:1351-1380.
- **Growth and assignment.** A write of a key a constant's records may lack
  is at the contract it adds the key at (the optional field's, else the
  value's type, a literal's widened), the constant's records owning it
  after. `Object.assign`'s value is the target's fields and then each
  source's, a later key replacing an earlier one.
- **Loop head types.** At the head of a `while` or `for` loop, a binding
  the loop assigns is at its declared type, but a source binding a slot
  holds (no cell) that enters narrower than its declared type, with no
  literal that widens within the declared type (`let i = 0` at `number`
  widens at the head, as TypeScript widens a mutable binding's literals):
  that one is at the join of
  its entry type and its types on the edges back to the head, the loop's
  test, body and update walked again from that join until the edges add
  nothing, at most three walks, the walk's state restored after each; kept
  where the join settles strictly within the declared type, else at the
  declared type (the producer's fixpoint, flow.ml:104-139). The head's
  types are its point claims, so the pass checks every edge into the head
  against them, the entry and each back edge (section 5).
  `TSCERT_FORCE=head-entry` states such a binding at its entry type,
  unwalked, the adversarial proposal: `loop-head-contents` `continued`,
  accepted unforced, is refused at an edge into its loop's head.
- **First use through a module function.** A use of an unannotated
  constant's fresh array as an actual of a module function reads the
  function at its one written signature, its slot's extension by a rest of
  `unknown` aside (statement_analysis.ml:122-124): `joined([...a, ...xs])`
  of `joined(terms: Term[])` builds `xs = forms.map(…)` at `Term[]`. The
  pass checks the allocation at that contract and every use against it.
- **Expected instance with a receiver.** Where the instance the actuals give
  has a result the expected type does not admit, the expected type's
  instance binds the receiver's binders from the receiver first, an input as
  the actuals are (inference.ml:518-529): `calls.map(name)` expected at
  `(string | undefined)[]` is the call at `U` of `string | undefined`. The
  instance must still admit every actual; the pass checks the call at it.
- **Rethrowing handlers.** A `try` with no finalizer whose handler has no
  normal exit (it completes only by a throw, the producer's
  `throw_only_stmts`, source.ml:975-993) contributes its body's changes
  alone to a normal return's footprint, the body's calls graded as outside
  any handler; the handler's changes leave a throw unbounded where they
  exceed the body's (source.ml:1168-1169). The function's own unit checks
  the proposal (SinglePass.lean:1351-1380, a dead handler region bounding
  throws alone).
- **Captured cells' contents.** No member path whose root a cell holds (a
  `let` a closure shares, a captured binding of a function literal) is
  narrowed: the producer states a field's contents of an immutable binding's
  object alone (refinement.ml:312-314). A test that changes a value location
  ends a cell's narrowed contents in both its arms, at the step
  (execution_analysis.ml:243-246); and a cell whose contract names a type
  parameter keeps its contract under a test, as `observed_contents` keeps a
  contract that is no union of atoms (environment.ml:73-83). A member of a
  union of objects is read at every object clause of each arm, a bounded
  binder's meet row at its bound's clauses (`Synthesis.memberFor`).
- **Dispatched callbacks.** For a declaration's footprint, a callback walked
  at the callable an actual's method takes (a string's `replace` at a
  regex's `[Symbol.replace]`) changes what that method's signature and the
  callback's own signatures state, as the producer reads the call's member
  at its claimed row (proposal.ml:84-91); any other function passed to a
  generic module function's call changes everything. The function's own unit
  checks the proposal; `TSCERT_FORCE=callbacks` still refuses
  `invalid-map-fresh-alias` `drained`.
- **Casts through `unknown`.** `x as unknown` is at `x`'s type
  (expression_values.ml:483-486), so the outer cast of `x as unknown as H`
  is the obligation that `x` meets `H` (a sealed handle's representation and
  invariant); the cast's own claim is checked against its annotation
  (`Atoms.lean`'s `cast-annotation`).
- **Loop heads.** A loop head's facts beyond its written assertion are the
  given file's `headFacts` (and `headFactsOfCodes` for each code request),
  each at the statement entries that start where the given one does and hold
  as many slots (a `for`'s head and its declarations' entry share a start); mode 6
  writes them with `TSCERT_GIVEN_FACTS=1`, for the experiment from the
  claims' facts at the loop heads and the start (`SinglePass.loopHeads`).
  A callback's code request uses its own indexed `codes` row (implications,
  promise arguments and input identities) and `headFactsOfCodes` row
  (source start, context width and index atoms).
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
footprint the unit's verdict reads, measured 2026-11-11 with the imports'
footprints their modules establish (removing any one refuses the unit; the
given file with the module units' lines): `measureAnalysis` 3 imports and
none of its file's functions: `getHanKerningTrims`, whose module unit the
pass refuses (a closure's loop head lacks a fact of `widthTrims`);
`getSegmentFit`, resting on `getFontKanaKerning`, which the pass refuses;
and `getFontMeasurement`, proposed the ordinary effect, through
`getCanvasFont`, whose callback to a generic native method's instance the
walk reads at the ordinary effect. `prepareRichInline` and
`buildEngineProfile` need none and are verified with none. Of the 81
functions the walk proposes for `measureAnalysis` (its file's and its
imports' modules'), 79 are proposed the producer's claim (footprint,
on-throw flag and returned footprint), 28 before the grades above; of
`prepareRichInline`'s 169, 165 (75 before); `buildEngineProfile`'s 2 of 2.

Imports' cost (perf gate, CPU of the verifier process, best of 3, measured
2026-11-11 beside the verifier of f894d34a, which plans no module, in
parentheses): with the gate's stand-ins, `measureAnalysis` 1287 ms (934),
`prepareRichInline` 7146 ms (2188), `buildEngineProfile` 142 ms (143); with
none, 2900 ms, refused (430), and 7270 ms, verified (920, refused). For
`prepareRichInline` with the stand-ins, the modules' least fronts take
0.23 s, their least walks 0.77 s, their plans 1.73 s and the 115 module
groups checked 2.24 s, every invocation again; the footprints established
keep more facts (`mergeDiffs` 1,826 for 1,823, `stateFactsSum` 132,919 for
132,540), and the given lines of the modules checked add 206,985 bytes read
(`measureAnalysis` 49,549). [Module interfaces](module-interfaces.md)
designs the store of each module's established footprints that removes
the repetition.

Agreement with the pipeline over the 3,303 pipeline cases (mode 8 with the
given files, `TSCERT_REFEREE`), measured 2026-11-11: 6,296 units, 4,974
agree, 584 disagree, 738 not handled. A file the pipeline refuses before any
unit's check is run from its fragment too: the unit holding the refusal's
position is compared with the refusal (91 units), the others are undecided
(85; the pass accepts 24, none the unit an unsafe program's refusal names).
Referee: 6 units mode 8 accepts and mode 9 refuses (all pipeline-verified),
12 the other way. Both modes accept eight
units the pipeline refuses: `blocker-pretext-equality-conjunction` `runs@923`
and `growth-optional-accumulator-refused` `optionalAnnotated@290`, gap
cases (safe programs the pipeline does not verify; the second's object is
the fresh literal, allocated at its own exact keys, which no host object
is, so the key-adding write is a write of a plain object), and six, each a
valid instance the producer did not propose: `invalid-bounds-callback-footprint` `visit@88`,
`invalid-generic-literal-widening` `use@206`,
`invalid-native-promise-invariant-result` `widen@89` (`make<unknown>` at
the expected result `Box<unknown>`), `blocker-gap-round-cache-answer-inferred`
`real@605` (the callback's literals at the cache's record
`{ answer: string | null }`), and `invalid-spread-intersection-disjoint-literals`
and `invalid-spread-intersection-optional-narrowing` `copied` (each copy is
within the written result; the producer refuses the file at its proposal
heuristic).
