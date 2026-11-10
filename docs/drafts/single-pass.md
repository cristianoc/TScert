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
`GraphCode.compositionalChecked` checks it: a state also carries the names
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
turn), or a loop head's given invariant. `dev/single-pass-state.mts` runs
it over a kept pipeline run and prints these over source names, with the
bindings' types.
