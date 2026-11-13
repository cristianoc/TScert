# The single pass

TScert's check: one forward pass over each unit's graph, which computes the
types and facts at every program point and checks every step, edge and
return against the calculus's proved rules; a unit it accepts is safe
(`mode8Accepted_sound`, [the theorems](#9-the-theorems)). The pass reads a
file's fragment and the module interfaces its imports read: every type is
computed by its front ([the claims-free front](#8-the-claims-free-front))
and every proposal checked where it is used.

This document is the root of the single pass's documentation, approved by
the owner as a root on 2026-11-12. It owns what the pass checks, its walk,
loop heads' proposals and the diagnosing walk, and its theorems by level,
and it owns the documents beside it:

- [the walk's rules](SINGLE-PASS-FRONT.md): the types, footprints and
  narrowings the front proposes;
- [the unit theorem](SINGLE-PASS-THEOREM.md): from the pass's verdict to
  every function's safety, the file and cross-module theorems, the
  hypotheses' statements and the boundaries that stay trusted;
- [the graph proof](SINGLE-PASS-PROOF.md): the graph theorem
  `run_sound_single_pass` in the indexed model, tolerant frames and the
  driver's walk;
- [the controls](SINGLE-PASS-CONTROLS.md): each boundary no proof covers
  and the controls that guard it.

**Evidence labels.** **Proved** names the Lean theorem. **Measured** gives
the command or count and the date. **Cited** names inspected code.
**Conjectured** marks a design claim not checked.

## The rules it applies

What holds at a program point is a
[heap state assertion](PROGRAM-TYPING.md#heap-state-and-assertions),
checked on every incoming edge, and a statement entry that is a loop head
(a cut) holds exactly its given invariant ([loop heads](#4-loop-heads)).
The steps' rules are the proved checker
`HeapExpressionRules.Checker.ordinary` (cited); the pass selects a step
with `CertificateProducer.expressionEffectUsing` and an edge's slot
evidence with `CertificateProducer.edgeUsing` (cited), and checks what each
selects. Between program points the pass holds the state as facts over
names, and it visits each node once.

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
the names each fact mentions (`SinglePass.Store`: the live facts a
`Std.HashSet`, and by each name a `Std.HashMap` list holding each live fact
mentioning it once). A step produces a delta: the facts its rule's
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
its slots (`nodeYields`); a merge keeps those
`CertificateProducer.meetImplications` keeps (over each edge's context as the
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

`SinglePass.runWalk` drives the walk by structural recursion on a fuel of
the nodes and one (`drive`, one node per step from the queue, a fuel that
runs out a refusal) and returns its record (`Walk`): per label whether it
was visited, its entry state and implications (a written assertion's facts
added), its state after its step and at a merge its context and the fresh
counter the merge started from; the states and implications each edge
carried into it and the edges into a merge as the merge reads them; per
processed edge its source, target and mapping, whether it pushes, the
implications it carries and whether some environment may meet its
context. `SinglePass.run`'s verdict is a function of that record
(`Walk.outcome`). Each node is visited over pure functions of its state:
a loop head's entry (`headEntry`), a merge (`mergeState`), a node's step
(`checkedStep`, its counts beside it as `StepStats`), an edge's store
(`edgeStoreOf`) and what an edge into an ordinary node carries
(`edgeTransfer`); `materialize` selects its facts by rounds
(`selectRound`, `selectFrom`, structural on a fuel of the store's size).

## 4. Loop heads

A loop head is the target of a retreating edge of a depth-first walk from
the start, handlers' edges included. A statement entry that is no loop head
is an ordinary node: its state is its predecessor's, or the meet of its
predecessors' at a merge; a written assertion there is an obligation on
that state. A merge works on what differs between its predecessors: the
first's store less each fact another lacks (`Store.diff`), and each predecessor's
own differences at the merge's names; the rules below that query a
predecessor's facts run over those differences alone, and the implications
join runs where an edge carries an implication or a slot an edge's type
differs at is a test some edge answers `false`. Each joined implication is kept
where every incoming edge establishes it (`PromiseCalls.impliesCheck` over
the edge's refined context, its implications at slots and its mapping). A name a predecessor
renames that no slot of the merge holds leaves the store there. At a merge, a linear bound every predecessor states of one form
under one condition is kept at the weakest of their bounds; a name a slot
keeps that another slot's fresh name renames in some predecessor is stated
equal to it there (an alias link; the two linear facts of their numbers'
equality only where that predecessor's unconditional facts make the name an
integer, `Store.integral`); a linear bound over the merge's names one predecessor
states and every other entails over its linear facts near the bound's names
(`HeapKnowledge.entailsKnown`) is kept, where in every
predecessor's view the bound is a fact or each of its terms is defined by
the facts near its names (`entailDefinedCheck`, `HeapKnowledge.termDefined`); the guarded facts
`CertificateProducer.joinGuarded` keeps are kept, each predecessor's guards
first also lowered once through its read links (`lowerGuards`); and a fact
one predecessor states of a slot another holds `null` or `undefined` in is
kept guarded by that tag where every predecessor's facts entail it
(`indicesCheckWith`), as the join guards a store separation. Everywhere, one linear bound
is kept per normalized form and condition, the strongest, and a length atom
is also stated as the linear facts it means (`HeapKnowledge.atomLinear`).

A unit states at most one written assertion per label; a request
with two at one label is refused.

A loop head's state is exactly its given invariant: its written assertion
(`@invariant`, required assertions) and the facts the front proposes there
([loop heads' proposals](#loop-heads-proposals)). Every edge into a cut, a
back edge included, carries the obligation that its state entails that
invariant; the cut is visited once, from its invariant. A refused proposal
is left out between runs ([the diagnosing walk](#the-diagnosing-walk)); a
run itself computes no invariant and retries nothing.

A cut's given invariant may also state implications (where a test holds
`true`, a slot has a type, [implications at statement
entries](#implications-at-statement-entries)). Every edge into the cut
carries the obligation that its own implications state each of them, at a
type within the given one.

Likewise a cut's given invariant may state which of its slots hold the
input a promise goal is about: those slots keep the input's name, and
every edge into the cut carries the obligation that its slots mapped there
hold that name. A return under a promise goal is checked as
`ControlFlow.checkReturnResult` checks it: the answer's type, and the
argument, as the step's yields refine it, within the promise at a slot
holding the input's name.

A return under a postcondition (`@ensures`) is checked as
`GraphCode.returnOk` checks it: the output's facts over the result and the
inputs' entry values, each the name the start gave its input, entail it
(`returnEntails`). A cut's given invariant may state which of its slots hold
an input's entry value (`GraphCode.trackTable`'s pairs, [input slots](#input-slots)), those slots
keeping the input's name, each an obligation on every edge into it.

The start is a cut no edge enters on the unit's first invocation; its
entry is checked as `ControlFlow.checkEntryResult` checks an entry
(`SinglePass.entryRefusal`): the start's context is the request's inputs,
the promised input's slot is one of them, its given invariant states no
implication, names a slot after the promised input only at that input's
slot and after an input's entry value only at that input's own slot, and
its written and proposed facts are entailed by the request's entry facts
(its index facts and its inputs' separation, `ControlFlow.entryKnows`).
`TSCERT_FORCE=start-facts` proposes a false fact at every start, the
adversarial proposal the check refuses.
Where an edge enters the start, the start is entered as any loop head: its
slots outside the given inputs and the promised input take fresh names, and
its given state is an obligation on every edge into it; such a unit under
store regions is not handled. The lowering makes no edge into a unit's
start: a function's entry is a node emitted after its body, a lambda's its
block's `closure-entry` node or its expression's first node.

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
type; both are types of its value. The evidence an edge search returns is checked
as the certificate checker checks a target's slots (`checkMappedUsing`, or
under the edge's observation `checkObservedUsing`, `edgeEvidenceChecked`):
an edge whose evidence the check refuses is not established by it. A step's yields are kept where the certificate checker's yield check
accepts them (`checkedYields`, as `ControlFlow.checkYields`): a promise
call's where `promiseYields` states them at an output the promise keeps,
any other's each where `yieldFollows` accepts it; a slot read's yields are
checked against the implications testing the slot's name.

A node's claim type has the shape its continuation assumes, as the
certificate checker checks it (`passShapeCheck'`): only Booleans at a
`branchBind`, the Boolean at a `branch`.

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
of such a name, or a call at a signature stating a fresh result whose
derivation `derivChecked` accepts; a merge
keeps the names every predecessor holds; a cut holds none, its given
invariant stating none); the region from which no normal return is possible
is `GraphCode.deadIterate` over the claims' result types, computed once; at
each node outside it, the node's step is within the bound
(`ExpressionEffects.check`, `writeWithin`, `initWriteWithin`,
`selectedWithinAt` with the receiver's freshness, the step's derivation
claimed at the node's term and its tree accepted, as `nodeChecked` requires
beside it; an empty type), its throw
too where the unit states the bound on a throw, and a return under a fresh
result returns a fresh name; inside it, `deadNode`. A code request of an
async definition has the footprint `top` (`RequestJson.asyncEffects`, as
`RequestJson.codeTableResult` requires of every code): its call returns
normally where its body throws, so no bound its body meets is the call's.
A call whose result is the empty type is within the bound on normal
return; its throw, caught by a live handler, is within it only at a
signature bounding its throws. A graph the bound
refuses may still be within it by its store regions (`regionalChecked`),
which the regional walk decides ([store regions](#store-regions)). A refusal at a
node's footprint check is its own outcome (`Outcome.outsideBound`), the one
the regional fallback answers; a node's exits are typed
(`SinglePass.Exit`: an edge of its continuation, or its handler's).

### A step's derivation

Every step's derivation is checked as the checker's `run` checks it
(`ProgramCertificates.checkTreeUsing`, or `PromiseCalls.requiresTree` for a
call at a precondition the step's facts establish): the checker's `select`
takes a derivation as given, and a derivation the step search selects may
be one the check refuses. A step the search finds is applied at the output
the checker's `select` gives for the evidence the search returns, computed
by the pass over the step's facts and the read summaries after the search. A
step that may write is selected again over every fact; a derivation only
`requiresTree` accepted at the step's facts is checked by `requiresTree`
again at every fact before that selection. The read summaries the derivations read are checked once
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
regions' input slots; at a loop head, the tables the front proposes
([regional tables](#regional-tables)); elsewhere what every edge into it
establishes. At each node: the cells it keeps (`cellsKept`), the fields its
types keep stable, its origins and fresh outputs (`nodeOrigins`,
`freshOut`, `cellOut`, `fieldOut`), and on each edge what it establishes at
the target; `checkNode` decides the node over those facts and the node's
evidence (its derivation, its step, its facts on entry), each loop head's
given facts the obligation on an edge into it. The entry's conditions
(`checkEntryFields`, a unit neither async nor promising a fresh result)
are checked before the walk. Where the fallback accepts and the unit states
regions, the regions' walk runs from the answers before the fallback, and
the read summaries of both runs are checked: the fallback's footprint rests
on its own.

Under store regions the pass checks the entry's fields the regions read
(`ArgumentPathTracking.checkEntryFields`) and, at a node whose step has a
derivation, that derivation as the footprint check does
(`regionalDerivChecked`).

### Qualified bodies

A qualified body (`SourceRequest.checker`) is walked over the request's own
graph and image check at its checker and aliases. The pass takes its
checker as `SinglePass.PassChecker`: the proved layers (`Checker.ordinary`),
whose steps' trees the pass checks, or a qualified body's
(`Checker.withSubtyping`), whose `select` is its `run`
(`PassChecker.select_eq_run`), so a step's derivation is checked by the
step's own check. Its
request-level conditions are those `effectResult`, `regionalResult` and
`ensuresResult` state of a qualified body.

## 7. Output and scope

The output is the verdict, with the first refused obligation located; a
construct the pass does not handle is an explicit `not handled` result,
never an acceptance. Not handled: a qualified body with code requests.

A unit's refusal line names the obligation at its source span: an
expression or return (`source expression obligation at [a,b): evidence
search failed: no derivation of its <role> claim`, or the promise's), a
postcondition (`source ensures refusal at [a,b)`), an edge at its target
(`source incoming edge obligation at [a,b)`), a footprint or stated frame
(`source effect refusal at [a,b)`); the pass's own text follows on the next
line. A refusal before the pass that names no place is named at its unit's
declaration (`source refusal at [a,b)`). `TSCERT_PASS_REFUSALS=raw` prints
the pass's own text alone. A unit refused for a dependency also prints the
refusal that dependency rests on.

`verifier --verify-interface-stage 8 <fragment> <interfaces> <file-key>
<depth> <names>` runs the pass over a file's fragment and the module
interfaces its imports read (`RequestCli.verifyUnitsFile`): each selected
unit's group checked by `FilePlans.passGroupMode8`, each verdict on a line
`{"unit","members","accepted","depends"}` or `{"unit","members","refusal"}`.
`verifier --module-interface <request>` computes a component's module
interfaces, checking each module's groups the same way
([module interfaces](STAGE-STORE.md#single-pass-module-interfaces)).

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

### Counts

`TSCERT_COUNTS` prints, per member, the pass's counts as a JSON line
(`counts: <name> {…}`): the graph's nodes and edges, the nodes reached and
visited, rule applications and those reading the whole store, entailment
queries and the facts they read, merges and the facts their predecessors
state that the met store lacks, the facts per state (sum and largest), the
facts given at loop heads; and once per process the bytes of the files read
(`counts-read:`).

### Work

`TSCERT_PROFILE` in a request's environment names the request's profile
directory. Each verifier stage of the request then runs with
`TSCERT_PROFILE=1` in its environment, which is part of its stage key, so a
profiled stage shares no entry with an unprofiled one. The verifier records
its work by kind and item, an item being a function
(`<sha256 prefix>#<unit>`, the unit by its lexical identity: its name,
`<name>~<k>` for an overloaded function's `k`-th signature, `init`) or a
file (`<sha256 prefix>`): preparation
(`prepare:` the claims, the file lowering, the initialization typing, each
function's extraction, the freezing, the plans over the store, the head
facts, an importer's plans), body walks (`walk:` a proposal walk, the
returned-callable round's, a recursive function's walks after its first,
the retype walk, the instance walk, and within any of them each further
traversal of the body, a growth round or an offers round), checks (`check:` a group, each member
run, each main graph run, each diagnosing walk), proposals (`propose:` a
function's member planned, each establishing of it, its settling runs, its
interface, its preparation, its walks, the regional route's tables and
local effects, the returned-callable round) and interface rows (`rows:`
the decoding of interfaces, an importer's and a publication's store-map
check). Each graph run (`SinglePass.runRecorded`: a member's main graph, a
code request's graph, a diagnosing walk, a proposal's walk) is a line of its
own, of kind `run: <seq>\t<purpose>\t<route>\t<body>\t<whole>\t<visits>\t<context>`:
its purpose, route, a digest of its inputs but its bound and one with its
bound and regional tables (`runDigests`), its transfers and the works open
around it, innermost first (its role: a proposal's or a unit's check); the
digests' own time is the work `account: run digest`. It writes, as the
stage's output `work.jsonl`, one line per kind and
item with the times the work was done, its nanoseconds and its nanoseconds
outside the work nested in it, and a line of kind `process` with the
process's nanoseconds. Stage execution appends every attempt of the request,
from every process, to the directory's `invocations.jsonl`, and keeps each
verifier attempt's work table as `work/<attempt>.jsonl`.
`node dev/work-report.mts report <directory>` reports, from that directory
alone, the work of each function and file, its CPU time, the work done
more than once by repetition site
([processing functions on demand](drafts/on-demand-processing.md#accounting)),
and the graph runs by kind (stage, role, purpose, route): how many repeat an
earlier run of the same function with the same inputs, how many differ from
one only in the bound, and the kind and place of the earlier run each
repeats.

### The performance gate

`node dev/perf-gate.mts <pretext checkout at ba09794f>` runs the pass over a
fixed set of units: pretext's `measureAnalysis`, `prepareRichInline` and
`buildEngineProfile`, and ten pipeline case units of different shapes. Each
unit's fragment is captured through the pipeline, and the pass
(`--verify-interface-stage 8`) run three times. Each unit
is compared with `dev/perf-baseline.json`:

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
correctness half is the pipeline cases.

## 8. The claims-free front

The front computes in Lean what the pass is given: each function's store
and signatures from the fragment's declarations and annotations, every
expression's and statement entry's type, each function's footprint, each
generic call's instance, and each loop head's candidates. The rules are
[the walk's rules](SINGLE-PASS-FRONT.md); `FragmentFront.lean` builds the
plans (`fragmentPlansFromInterfaces`, or `fragmentPlansWithModules` with
the modules checked in the invocation), `Synthesis.lean` walks each unit,
and `HeadInference.lean` proposes the loop heads' facts. No result of the
front is trusted: each is a proposal, an argument the graph theorem
quantifies over ([the hypotheses](SINGLE-PASS-THEOREM.md#2-the-hypotheses)).

### Loop heads' proposals

A loop head's candidates beyond its written assertion are the facts the
front proposes for it from the fragment's statements
(`HeadInference.proposals`), over source names: each is an entry claim at
the loop's execution point, which the lowering records as the head's
candidates, each naming only bindings in scope at the head and no early
binding. The pass checks them on every edge into the head
([loop heads](#4-loop-heads)).

### The diagnosing walk

A member the pass refuses
at an edge into a statement entry for facts it lacks is run again with
those of its proposals there that the refusal names left out (all of them
where its text is cut before naming any; none where it names only facts
no run leaves out, which stands), and every other proposal a diagnosing
walk over those plans finds lacking left out with them
(`FilePlans.inferredNextAll`). The diagnosing walk
(`SinglePass.lackingFacts`, `FilePlans.lackingAt`) is the pass's walk over
the member's main graph, at the arguments of its main run, where an edge
into a head refused for proposals it lacks, or for an implication the head
states, is taken again with those proposals, or that implication, left out
of the head's state, and the walk goes on; its result is what it left out,
by head, and it decides nothing. Each implication is a proposal of its own:
a refusal names the first the edge does not establish by its tested and
narrowed slots (`SinglePass.headImpliesFailing`), and a run refused so is
run again with that one left out (`withoutImplications`). A head's facts left out after
its loop was walked weaken what that walk carried only in the next run, so
the runs are bounded by how deep such facts depend on each other, not by
how many are refused. At most `4·h + 4` runs for `h` statement entries
holding candidates (`FilePlans.passGroupInferred`); each run is the pass
over the facts it states, so an accepted run's verdict needs no other
(`passGroupMode8_safe`, [the unit theorem](SINGLE-PASS-THEOREM.md#the-headline)).
A fact left out at a head is left out, over the same bindings (each
slot's descriptor), at the heads that read that head's facts too: those
nested in its loop, and those after it inside the loop holding it (the
walk carries a head's facts past its loop). A forced proposal
(`TSCERT_FORCE=head-…`) is never left out.

### Counters and the entry's facts

A loop's counter, a binding every write of which in the loop (its body,
update and nested statements, closures included) steps it by one
constant `c` (`x++`, `x += c`, `x = x + c`, their decrements), is proposed
an integer; each of the entry's facts a step keeps (a bound below an
increasing counter, above a decreasing one), over bindings the loop does
not assign; each bound the test's `true` answer states on it, shifted by
`c`; for a step of one towards a disequality the test states
(`e !== n`), `e ≤ n`; and below `2^32 - 1` for an increasing counter the
test bounds above, where the test's bound with the step taken is at
most `0`; a counter the test bounds by no comparison on its step's side
(`while (f(s.charCodeAt(x))) x++`) is no safe integer and is proposed
nothing. The last three only where
the entry entails them, the counter's entry value substituted: by a fact
of the entry whose terms differ by lengths alone, each length's range
(`0 ≤ n.length ≤ 2^32 - 1`) making up the difference; likewise a
linearly written binding's `2^32 - 1`. `TSCERT_FORCE=head-entails` also
states a counter at most `-1` where one of its candidates is left out so:
`logical-guard-reads` `nonzeroPrefix` (`e < to` from `e = 0`, `to`
unbounded below), accepted unforced, is refused at an edge into its loop's
head.
The entry's facts are a
forward walk's over the statements before the loop: a declaration or
assignment of a linear value states its equality, a step restates each
fact, a test states its comparisons on each arm, an arm that leaves
states the other's after the test, an assignment of a choice (`x += c ?
p : q`, `x = a ± (c ? p : q)`) is each arm's assignment under what its
answer of `c` states, the two joined, an `if` is joined from what its two
arms state after them (an arm that leaves aside), a block states what its
statements state after them, its own bindings forgotten, a write of a binding forgets its
facts and a heap write those of lengths and paths
(`declaration`, `test`, `distribute`,
`assign_arms`). A declaration or assignment of a call of the file's
function stating a postcondition (`@ensures`) states its facts, the result
the binding and each parameter the actual where that is a binding
(`breaks = lineBreaks(s)` under `@ensures result.length === s.length + 1`:
`breaks.length = s.length + 1`); one of a choice `c ? a : b` states, on
each arm under what its answer of `c` states, the binding equal to a
linear arm (a length among its terms: `t = c ? f(s) : s.length`) or a
call's postcondition, the two joined (`declaration`'s conditional). An
assignment states of its binding what a declaration of it to the same
value states (`Ctx.bindTo`). Two arms are joined into the facts both
establish: each fact `Σ cᵢ·tᵢ ≤ d` of one arm is kept where the other arm,
with the facts before the choice, has a fact of the same terms (kept at
the larger bound), or entails it by a fact whose terms differ by lengths
alone, each length's range making up the difference, or does so with a
binding it states equal to a linear value replaced by that value
(`Ctx.join`): `i += c ? 2 : 1` keeps `0 <= i` and takes `i <= n + 1` from
`i < n`; `from = c ? trailing : 0` keeps `0 <= from` where `0 <=
trailing`.
An imported function's postcondition is its signature's
(`Effect.ensures`), a parameter's type invariant its body keeps among
them. A declaration of an object literal of named fields states each
linear field's value its path's (`const cursor = { segmentIndex: 0 }`:
`cursor.segmentIndex = 0`); the literal, as an array literal without
spreads, writes only its own fresh locations, so the walk keeps the facts
of paths across it (`declaration`'s
`Alloc`). At a loop head, each fact a call in the loop states of its
actuals' fields at its return (its postcondition at the actuals'
positions), where the entry entails it and the loop assigns no binding it
names: `0 ≤ cursor.segmentIndex` of a call `step(prepared, cursor)` whose
parameter's type states it. Across
a loop that may write a field, each carried fact also with a field path's
term replaced by the value over bindings an entry equality gives it
(`segmentCount = prepared.widths.length` and `segmentFlags.length =
prepared.widths.length` give `segmentCount = segmentFlags.length`).
`TSCERT_FORCE=head-called` and `head-eliminated` also state the first
term of each such fact at most `-1`: `cursor-invariant-after-writing-call`
`countMarked`, accepted unforced, is refused at an edge into its loop's
head.
`TSCERT_FORCE=head-ensures` also states each term of the binding a call's
postcondition names at most `-1`: `assignment-call-postcondition`
`sumBreaks`, accepted unforced, is refused at an edge into its loop's
head. `TSCERT_FORCE=head-arms` also states a binding assigned a
choice at most `-1` after the assignment: pretext's `needsComplexTextPath`
(`prepare.ts`), accepted unforced, is refused at
an edge into its inner loop's head.
`TSCERT_FORCE=head-counters` also states each counter at most `-1`:
`adjacent-pair-reads` `pairProducts`, accepted unforced, is refused at an
edge into its loop's head.
The facts a loop's entry holds over bindings the loop does not assign
are proposed at its head too, and those of the bindings it assigns that
enter as integers and that each of its writes sets to a linear value
(`i = j`, `i += c ? 2 : 1`): their integrality, their entry's lower
bounds and `2^32 - 1` below a test's bound (the join's candidates). The
entry holds the precondition's linear facts and integralities over the
parameters (`@requires`), the written invariant of each loop around it,
a choice's bounds (`x = a < b ? a : b` is at most both), a typed array's
construction's length (`new Int32Array(n)`) and a test's comparisons only
where each binding they name is an integer there; a test's comparison of a counter only so too, and a counter the
test does not read is proposed nothing. A length is an array's, a typed
array's (`%ByteLength%`) or a string's by a parameter's type, read in the
type store (a string's where each of its clauses but `null` and
`undefined` is a string, an array's where each holds an array store, a
typed array's where each states a view length), and by a declaration's
written type or initializer; a parameter whose type says none of them, or
says two, has an array's. `TSCERT_FORCE=head-kinds` also states each
string's or typed array's length a head's proposal names at most `-1`:
`blocker-pretext-code-point-at-assertion` `astral`, accepted unforced, is refused
at an edge into its loop's head. A heap write keeps a length but where it resizes the array
by name (`push`, `pop`, `shift`, `unshift`, `splice`, an element or
`length` write), and a path's facts only across quiet expressions. A
`for...of` head is a loop head whose test reads nothing.
A counter's or a linearly written binding's `2^32 - 1` is proposed only
below a test's bound by arrays' or typed arrays' lengths (or by a binding
the entry bounds by one), and a test's bound on a field path's length only
across a loop of quiet expressions.
A binding the test does not read, written by a step of `c` once at most
an iteration (one step, in no nested loop) and equal to a linear value at
entry, beside a counter the update steps by `c`, is proposed its
integrality, its entry value as a bound and its difference from the
counter at entry: `n - i <= 0` for `n++` under a test in `for (let i = 0;
…; i++)`, both ways where the update steps both (`for (…; i++, j++)`:
`j - i = at`). `TSCERT_FORCE=head-paired` also states each such binding at
most `-1`: `element-write-keeps-lengths` `f`, accepted unforced, is refused
at an edge into its loop's head.
`TSCERT_FORCE=head-carried` also states each term of a carried fact at
most `-1`: `precondition-lengths` `dot`, accepted unforced, is refused at
an edge into its loop's head.
A store separation is proposed for a fresh empty array field
(`{ f: [] }`) against every binding of the function that may hold an
array (by its written type or initializer, or bound by a destructuring),
for a copy (`x = o`) as `o`'s, and for a choice of a value and `null`
(`c ? o : null`) guarded by `x === null`; the precondition's and the
written invariants' separations are entry facts too. A separation is kept
but across a write of a field its paths read. A separation names value bindings alone, and at a loop head
only bindings whose type there, where the walk types it, makes them
arrays (no string, no `null`): a destructured string or a nullable
parameter is no store a separation could keep apart.
A quantified fact (`forall i in xs: B`) of the precondition, of a loop's
written invariant or of a loop's exit (where the written invariant holds)
is carried to the heads after it over bindings the loop does not assign,
across expressions that write no element and resize none of its arrays
by name; a step of a binding it names forgets it; `xs.push(a)` keeps one
over `xs`'s whole array whose body the facts state of `a` at the index
`xs.length`; a read of a path (`const w = d.widths`, `w = d.widths` of a
`let w`, `const { widths } = d`) restates it, and a linear fact, through
the path: `w` and `d.widths` denote one value there
(`egrown`, `erestate_read`). An element
read `xs[k]` at an index the facts place in `xs`'s range is bounded by
such a fact's body at `k`: a binding it sets is proposed its integrality
and the bounds, and a test comparing it bounds a counter
(`element_facts`, `instantiate`). `TSCERT_FORCE=head-every` also states
each carried quantified fact with the body `xs[i] <= -1`:
`quantified-element-reads` `sumUpTo`, accepted unforced, is refused at an
edge into its loop's head.
A path read (`const x = o.f`) whose path a fact names is a safe integer
equal to it (a path term's fact holds only where the path reads a safe
integer, `is_int`). A test-free loop
(`while (true)`) bounds a counter by each exit test after its last step
(`if (x >= n) return`, `if (++x >= n) return`), the test's failure
unshifted, where no `continue` goes back earlier and the entry entails it. An alias or a cast
(`const r = o as T`) restates every linear fact of `o`'s paths over `r`
(`erestate_read` of the empty path). A guarded fact (`x.f === null || K`,
a type invariant's) is carried and restated as a linear one is, and a test
failing its guard (`x.f !== null`) gives `K` on that arm.
An array's element read (`%ElementAt%`) writes nothing: a fact of a path
is kept across it. An element read `xs[k]`
(a typed array's too) below a quantified fact's stop, its array's length
or a prefix's bound (`forall i < n of xs`), is bounded by the fact's body.
`TSCERT_FORCE=head-elements` also states a binding an element read bounds
at most `-1`: `typed-array-prefix-write` `buildPostfixPrefix`, accepted
unforced, is refused at an edge into its inner loop's head; the control
of quantified facts (`head-every`) is shown on
`bounds-quantified-invariant` `read` too, its parameter's invariant kept
across the element reads.
`TSCERT_FORCE=head-exits` also states a counter an exit test bounds at most
`-1`: `cursor-invariant-loop-write` `nextMarked`, accepted unforced, is
refused at an edge into its loop's head. `TSCERT_FORCE=head-restated` also
states each restated linear fact's first term at most `-1`:
`invalid-sealed-handle-resize` `lastFlag`, accepted unforced, is refused at
an edge into its loop's head. `TSCERT_FORCE=head-guards` also states a
discharged guarded fact's first term at most `-1`:
`invalid-guarded-invariant-short` `narrowing`, accepted unforced, is refused at
an edge into its loop's head.
`TSCERT_FORCE=head-separations` also states a carried separation's first
store apart from itself: `stated-argument-path` `measure`, accepted
unforced, is refused at an edge into its loop's head.

### Input slots

For a unit whose postcondition names inputs (`@ensures`),
the slots holding each input's entry
value at its statement entries are computed from its plan
(`FilePlans.computedGiven`): the input's own slot at the start, carried
along every edge to each slot whose mapping reads a slot holding it, those
every predecessor carries (`GraphCode.trackTable`'s propagation over the
claimed contexts' widths). Each is an obligation on every edge into a
head.
`TSCERT_FORCE=head-inputs` also restates each pair at a cut at the next
slot: `written-ensures` `zeros`, accepted unforced, is refused at an edge
into its loop's head.

### Implications at statement entries

A statement entry is proposed the implications its branches read
(`branchImplications`, the rows' `implies`): of each test on a constant
holding a comparison's value (`const p = x === "a"; … if (p)`) whose
`true` arm's claim narrows a binding (`x : "a"`), `p = true ⟹ x : "a"`
at each statement entry from which the test is reached: whose span holds
the test, ends before it, or lies in the span of an entry that holds it
(a loop around the test reaches it again from after it), and whose context
describes both bindings: a branch inside the loop reads them, one after a
loop reads them across its head
(`invalid-guard-constant-across-loops`: `const has = v !== undefined`,
forty loops, then `if (has) total += v`), and a loop after the branch in
the loop holding it carries them back to it
(`loop-implication-after-branch`).
The pass checks each on every edge into the entry; a member an edge
refuses one for is run again without that one (each implication a
proposal of its own, [the diagnosing walk](#the-diagnosing-walk)).
`TSCERT_FORCE=head-implications` also states each at `undefined`:
`blocker-pretext-constant-implication-statements` `advances`, accepted
unforced, is refused at an edge into its loop's head.

### Regional tables

For a unit with store regions or a footprint's
regional fallback, the regional facts
at its statement entries ([store regions](#store-regions)) are computed
from its plan (`regionalLines`): the slots holding entry argument paths
(`SourceExtraction.regionTable`), the fresh values and cells and the
fresh fields, each a greatest fixed point (`freshTables`) over the
evidence the computed claims give (`claimedCertificate`: a call of a slot its derivation read off the
callee's signatures, any other node its sequent). A call is taken to
keep its cells, its step's own evidence deciding it in the pass. The field
names are those the callees' store regions read through one field
(`calleeRegionNames`). The pass checks each loop head's tables on every
edge into it; a member it refuses at its store regions is run again
without them. `TSCERT_FORCE=head-region-values`, `head-region-cells`,
`head-region-facts` and `head-region-fields` each add at every statement
entry one entry of that kind no edge establishes (the next slot as a fresh
value or cell, an argument path `forced` of slot 0, a fresh field of the
first name): `stated-region-fresh` `marks`, `stated-region-lazy` `longer`,
`stated-region-steps` `scan` and `stated-slot-collect` `collect`, accepted
unforced, are refused at their store regions on an edge into a loop's
head.

### Region separations

At each loop head, the pairs of array bindings
an allocation states apart (`IndexWrites.regionAtoms`: a literal's store
apart from every array slot), carried along every edge to the slots whose
mappings read them and kept where every predecessor carries them, of an
allocation whose array the loop writes an element of outside every loop
it holds (`freshApartAt`), as `IndexFact.apart`: an element write keeps a
quantified fact over an array apart from the written one
(`IndexWrites.writeAtoms`, `every-apart-write`). The pass checks each on
every edge into the head; a member an edge refuses one for is run again
without it. `TSCERT_FORCE=head-apart` also states each written side apart
from itself: `quantified-freshness-builder` `build`, accepted unforced, is
refused at an edge into its loop's head.

## 9. The theorems

Each level's theorem rests on the one below it; [the unit
theorem](SINGLE-PASS-THEOREM.md) states each with its hypotheses.

- **The graph** (`run_sound_single_pass : RunSound`, proved,
  [the graph proof](SINGLE-PASS-PROOF.md)). An accepted call of
  `SinglePass.run`, under its checker's scope, with a sound code table and
  sound read summaries, gives its graph's guarantee: safety at every
  admitted assignment from every entry meeting its inputs, its footprint
  and fresh result, its postcondition, its regional bound and its stated
  assertions. Beside it, `runKeepsSummaries` (proved): a call keeps the
  read summaries it was given.
- **A group** (`passGroupMode8_safe`, proved under `RunSound` and
  `RunKeepsSummaries`). A group mode 8's check accepts is safe, by the
  given lines or by the inferred route, whose runs differ only in their
  candidates (`Recandidated`), which no request's safety reads
  ([the headline](SINGLE-PASS-THEOREM.md#the-headline)). `passUnit_safe` is
  it over `fragmentPlans`.
- **A unit at the command's verdict** (`passUnitVerdict_safe` and
  `passUnitCli_safe`, proved under `RunSound` and `RunKeepsSummaries`;
  `passUnitVerdict_sound`, proved, with both discharged). Where
  `--verify-interface-stage 8` prints a unit accepted, every member of its
  group is safe ([the final statement](SINGLE-PASS-THEOREM.md#the-final-statement)).
- **The acceptance theorem** (`mode8Accepted_sound`, proved, the theorem
  `AxiomCheck` names as acceptance's). A unit printed accepted at either of
  mode 8's print sites, the file's own check and a module's in the
  interface stage, has every member of its group safe.
- **A file** (`passFile_safe_kinds`, proved under its hypotheses). Every
  closed unit's laid-out function's value meets its interface
  ([the file-level theorem](SINGLE-PASS-THEOREM.md#6-the-file-level-theorem)).
- **Modules** (`crossModule_safe`, [module linking](#10-module-linking)).

The hypotheses, by level ([their statements](SINGLE-PASS-THEOREM.md#the-hypotheses-by-level-and-class)):

| Level | Theorem | Hypotheses |
| --- | --- | --- |
| Graph | `run_sound_single_pass`, `runKeepsSummaries` | none |
| Unit | `mode8Accepted_sound`, `passUnitVerdict_sound` | none |
| File | `passFile_safe_kinds` | `ReceiverDropSound`; the layout (`ModuleLayout`); the established slots (`EstablishedSlots`); the four outside kinds met (`KindMet` for `declared`, `standIn`, `host`, `moduleCell`) |
| Cross-module | `crossModule_safe` | `ReceiverDropSound`; the importer's layout; the publication order (`ReadsEarlier`); each published entry's step (`EstablishedStep`) and layout (`StepLayouts`); the chosen slots (`ChosenSlots`); each established slot reading an entry of the order; the other three outside kinds. With `established_of_provenance` the steps follow from `InterfaceProvenance` and `EstablishProvenance`. |

What stays trusted at every level: the parser's fragment, the
interpretation of annotations, the source-to-graph lowering, sparse
handler placement, declaration-only import and host contracts, the
compiled replacements and the stage store's replay
([the boundaries that stay trusted](SINGLE-PASS-THEOREM.md#5-the-boundaries-that-stay-trusted)).

## 10. Module linking

An import whose declaration has no body is read at its declared type
(`import`). An import from a module with a body is read at its declared
type and at what its module's check establishes, its interface entry,
where the fragment resolves it to a function of a module the fragment
lists ([certified imports](SOURCE-CONTRACTS.md#certified-imports),
[imports](SINGLE-PASS-FRONT.md#imports)); with no entry it is read at its
declared type with the ordinary effect, its precondition kept
(`import-body`, `ordinaryImport`): no footprint, postcondition, guard's
promise, throw bound, regions or fresh result is assumed of it. A
module's interface is computed component by component
(`establishModules`), each module's reached groups checked by the pass,
an entry published where its function is laid out, its group is accepted
with its dependencies and its interface rows agree with the module's
store (`moduleRowsAgree`); a function is published where the walk
proposes it more than the ordinary effect or its declaration states a
postcondition or a guard's promise (`Front.statesMore`), and an entry
reads one fixed signature, a guard's beside it (`importedSignatures`).
The importer reads an entry where its rows agree with the slot's type
(`importerRowsAgree`), and refuses the units reading the slot otherwise
(`signature rows differ`).

**Theorem** `crossModule_safe` (proved, under the cross-module hypotheses
above). For plans over their store and a set of units each a selected unit
whose group is safe, whose established slots read entries published along
the order, every function the layout lays out meets its interface at every
budget and its captures meet their types: the imports are discharged by
their modules' own checks
([module interfaces](SINGLE-PASS-THEOREM.md#7-module-interfaces)).

### The module layout

A laid-out function's value meets the arrow its declaration states, with
every condition the call rule reads from that arrow: a caller discharges
the arrow's precondition and assumes its postcondition by the call rule it
applies to any callee of that arrow (`ensuresCall_sound`), within a module
or across one; the function's own request establishes what the arrow
promises; and what the request assumes beyond the arrow is a fact of the
closure's own captured values. The module rows are module code at
`RowSpec`; the code a unit creates for a closure is at `GraphCodeSpec`,
with no postcondition and no entry separation.

**Definition** (the module row's specification, `RowSpec`). For code $`c`$
of arity $`a`$ collecting no rest, a signature $`p`$ and a separation
$`\Sigma`$ of its frames,

```math
\begin{aligned}
\mathrm{RowSpec}_G(c, p, \Sigma) \iff{} & a \le |p.\mathrm{arguments}| \wedge \mathrm{belowRow}(a, p.\mathrm{effect}) \\
 & \wedge \text{every run of } c \text{ from a frame meeting } p\text{'s frame, } p\text{'s precondition and } \Sigma \\
 & \quad \text{is safe at } p\text{'s result and post} \\
\mathrm{belowRow}(n, e) \iff{} & \mathrm{below}(n, e \text{ without its postcondition}) \\
 & \wedge \text{each postcondition fact names only positions} \le n + 1
\end{aligned}
```

the positions being the result (0), the receiver (1) and the first
$`n`$ parameters. `GraphCodeSpec` collecting no rest is `RowSpec` at
$`\Sigma = \{\}`$ with no postcondition (`rowSpec_of_graphCodeSpec`).
`rowSpec_of_requestSafe` (proved) gives `RowSpec` at the request's entry
separation from a unit request's safety
([H5: the realization](SINGLE-PASS-THEOREM.md#h5-the-realization)).

- **A guard's plain row through its promise row.** A type guard's or an
  assertion function's interface is a clause of a promise row $`p`$, of
  result $`T`$ and promise $`\pi`$ (`guards k`, `asserts k`), and beside it
  its plain row $`\mathrm{plain}(p, R)`$ (`promisePlain`): $`p`$ with the
  result $`R`$ and no promise, its receiver, actuals and effect otherwise
  $`p`$'s. Its one request is at the promise's goal, so it realizes $`p`$;
  the plain row follows where $`R`$ admits the promise's results
  (`promiseAdmits`: `true` and `false` for a guard, by `booleanMember`;
  `undefined` for an assertion, by `admitsUndef`).

**Lemma** `rowSpec_plain_of_promise` (proved). Where $`p`$ states the
promise $`\pi`$ and $`R`$ admits its results,
$`\mathrm{RowSpec}_G(c, p, \Sigma) \Rightarrow \mathrm{RowSpec}_G(c, \mathrm{plain}(p, R), \Sigma)`$:
the frame, the precondition and both postconditions read no promise, and a
run's normal value, `true` or `false` for a guard, `undefined` for an
assertion, is in $`⟦R⟧`$ at every budget and world. `RowRealized` admits a
row so realized, and the layout check (`FilePlans.layoutOwn`) realizes a
plain row through the clause's promise row of the same receiver, actuals
and effect, at the promise's goal.

- **A postcondition over the call's values.** A unit request states its
  postcondition at its entry frame (`EnsuresClause`), each call position
  read at the input slot holding it on entry, so a reassigned parameter
  leaves it unchanged. `UnitIsCode` relates the request's postcondition to
  the row's; `UnitIsReceiverless` relates them past the receiver
  (`ensuresPast`: each position $`i \ge 2`$ at $`i - 1`$), a function
  declared without `this` stating none of its receiver. The layout check
  (`FilePlans.layoutOwn`) asks the same of the member's request.
- **Module cells apart at entry.** A request reading two module cells
  states their `value` fields apart at its entry
  (`moduleCellSeparation`), facts naming the frame's capture slots that
  hold module cells. In the module's environment those slots hold the
  module's cells at every depth, so the fact is one of the closure's
  captured values, which no caller can falsify or has to discharge.
  `ModuleCode.sep` is the member's entry separation (one depth deeper for
  a function declared without `this`, behind its receiver's prologue,
  `receiverSeparation`), `Realizes` asks it of every frame a call of the
  closure enters, and `ModuleLayout.apart` (H5a) states it of the module's
  environment: the initialization allocates each cell fresh. The layout
  check admits an entry separation only where its facts name captures that
  are no function of the file.
- **One type at two labels.** A store map relates the importer's and the
  module's stores where one of them holds a type at two labels
  ([signature agreement](SINGLE-PASS-THEOREM.md#where-signature-agreement-is-decided)).

The module-layout conditions are `ModuleLayout` (H5a) at the importer and
`StepLayouts` at each module step: each laid-out function's interface one
clause, one slot per capture, each linked slot's callee laid out at its
interface, each signature realized by a member's request at `RowSpec` (a
guard's plain row through its promise row), and
the module cells apart (`apart`). They are hypotheses; their decidable part
is the layout check. `ReceiverDropSound` (a named hypothesis) gives
`RowSpec` of a receiverless request's code with the receiver dropped, at
the request's entry separation one depth deeper.

## 11. Controls

The boundaries no proof covers (the parser's fragment, the front's
proposals, the interface stages and the trusted contracts) each have
controls: forged fragments, forced proposals and mutations of the pass
([the controls](SINGLE-PASS-CONTROLS.md)).
