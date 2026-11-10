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
does today).

Beside the store, a state carries the implications its edges establish
(`PromiseCalls.Implication`: where the test holds `true`, the target has
the type), over names: a step's conditional yields, at a pushed edge, state
them of its result; a read of a tested name yields them again at every slot
holding the target; a merge keeps those every predecessor carries.

## 3. Order

The graph without the edges into cuts is acyclic (every cycle passes through
a cut, `produceRawUsing`'s invariant, cited). The pass visits its nodes once,
in a topological order. A node with one predecessor takes that edge's state;
a merge takes the facts every predecessor holds, a slot whose predecessors
give it different names named afresh, each predecessor's facts renamed to it.

## 4. Cuts

A cut's state is exactly its given invariant: its written assertion
(`@invariant`, required assertions) and the facts the claims document
records there. Every edge into a cut, a back edge included, carries the
obligation that its state entails that invariant; the cut is visited once,
from its invariant. The pass computes no invariant, guesses none and
retries nothing. Where a unit that verifies today needs a fact at a cut
that neither source gives, that fact is supplied as an input of the pass
and listed.

## 5. Steps and obligations

A step's rule is applied to the facts over the names its expression reads,
closed through alias links, read links and linear facts (the facts an
entailment over those names may chain through), at the slots the node's
table gives. A step whose effect may write (`ordinary`, `written`,
`boundedWrite`) reads every fact, since its output states which heap facts
survive. Obligations (a required assertion, an edge into a cut) are
entailment queries against the facts over the names they mention, closed
the same way.

### A call of a slot

A call whose callee is a slot is read off the callee's signatures, in the
order `CertificateProducer.expressionWithUsing` tries them (those promising
elements first; those stating a precondition `admits` holds of, then those
stating none): the first whose receiver, actuals and result the slots'
types meet, each by identity or a subtype proof; `undefined` at its own
type. Each stated precondition is decided once per call, over the index
facts connected to the call's slots. The step is `ordinary` at that
derivation. Its output is the one `HeapExpressionRules.Checker.ordinary`
gives, its layers' predicates read without their tree check (the
derivation's premises are the pass's checked comparisons), mirrored by
`SinglePass.callBase` and `SinglePass.callOutput`:

- the base: `PromiseCalls.elementsOutput` (`elementsCall`),
  `promiseOutput` (`requiresCall`), `freshOutput` (`freshCall`),
  `ownOutput` (`ownCall`), the entry shifted (`keepsCall`), else
  `HeapExpressionRules.ordinaryOutput`;
- then `ensuringCalls` (`withEnsures`, `withGrown`, whose kept facts are
  `effectKept`, `appendKept`, `writeKept`, `linearAppendKept`),
  `negatingSlots`, `emptyArrays`, `indexing` (`stepAtoms`, `linearAtoms`,
  `lengthAtoms`), `boundedWrites`' `IndexWrites.growOutput`, and
  `keepingStable`'s `withStable`.

Where the base keeps the heap (elements, a heap-keeping precondition,
fresh, keeps), every fact the call does not name stays where it is, and
the output over the named facts is the step's delta. `ownOutput` and
`ordinaryOutput` decide per fact over the whole store.

## 6. Where the rules read more than a step's names

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
  its store regions) read every node's evidence: the pass does not make
  them, and a unit stating one is not handled.

## 7. Output and scope

The output is the verdict, with the first refused obligation located; a
construct the pass does not handle is an explicit `not handled` result,
never an acceptance. Not handled: handlers, promise goals, graph code,
qualified bodies, postconditions (`ensures`), store regions, footprints
other than a pure program's.

`verifier --verify-units 3 <fragment> <claims> <file-key> <depth> <name>`
runs the pass; `TSCERT_COMPARE=1` checks, at every node, that the state
entails the knowledge the existing search's certificate holds there.
