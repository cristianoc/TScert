# Draft: a loop head carries the invariant facts of its entry edge

A design written against branch `pretext-twelve` at 961314ec, for review
before anyone builds it. Its progress is [WORK.md's](../../WORK.md#status).

**Evidence labels.** **Measured** gives the command, the commit and the date.
**Cited** names inspected code. **Proved** names a Lean theorem.
**Conjectured** marks a design claim, a proof obligation or an estimate.

## The existing mechanism this extends

Three mechanisms, each owned by its document:

- **Support and respect** ([FOOTPRINTS.md](../FOOTPRINTS.md#support-and-respect)):
  a fact $`P`$ with a support $`S`$ in a context $`C`$ holds after any
  transition whose effect respects $`S`$; an empty support is proved
  invariance in $`C`$ (`Supports.of_invariant`), so a fact of empty support
  holds after every transition that leaves its slots' bindings alone
  (`IndexFact.keeps_sound`). The tolerant-frames note states it
  ([§4–§6](../REFERENCES.md#the-tolerant-frames-note)), with rule Entry and
  the checked transfer as one entailment.
- **The pass's loop heads** ([SINGLE-PASS.md](../SINGLE-PASS.md)): a head
  is a cut whose knowledge is given before the walk, its written invariant
  and the facts supplied for it (`SinglePass.setupGiven`), and every edge
  into it is checked to entail that knowledge. The note's "Sound graphs"
  states the same: merges and heads are targets like any other, and a
  head's knowledge is supplied and checked on its edges.
- **The front's proposals** ([SINGLE-PASS.md](../SINGLE-PASS.md), the
  front's walk; `HeadInference.proposals`): the facts supplied at a head
  are proposed by an interpreter over the source and left out where an edge
  refuses them (`FilePlans.inferredNextAll`, `laterDrops`), each leaving
  out one rerun of the pass.

This draft changes what a head's knowledge is made of, not how it is
checked: the knowledge stays a target every incoming edge entails.

## The statement

At a loop head $`h`$ with entry edge $`e = (n \to h)`$, renaming
$`\pi_e`$ and given knowledge $`\Sigma_h`$ (written invariant and claims):

```math
K_h \;=\; \Sigma_h \;\cup\; \{\, F \in \pi_e(\mathrm{out}(n)) \mid \mathrm{supp}_h(F) = \emptyset \ \wedge\ \mathrm{slots}(F) \subseteq \mathrm{Stable}_h \,\}
```

where $`\mathrm{supp}_h(F)`$ is $`F`$'s support in the head's context
(the knowledge query $`K`$ of $`\pi_e(\mathrm{out}(n))`$,
`Footprints.knowledgeQuery`), and $`\mathrm{Stable}_h`$ is the set of
head-stable slots (below).

**Why every back edge establishes the added part** (conjectured; the proof
obligation of the change). Let $`F`$ be an added fact and $`b = (m \to h)`$
a back edge. Every path from $`h`$ to $`m`$ in the loop is a sequence of
steps, merges and inner heads. Each step's output contains every fact of
its input whose support in the step's context is empty and whose slots it
does not rebind (§"What each step must keep", the step-2 work of
[FOOTPRINTS.md](../FOOTPRINTS.md#support-and-respect)): $`F`$'s support is
empty at $`h`$ and stays empty along the path, since the context only grows
by facts the path establishes and $`F`$'s slots keep their bindings. A merge
keeps a fact every predecessor states. An inner head carries $`F`$ by this
same statement applied to its own entry edge. So $`\mathrm{out}(m)`$
holds $`F`$ at the slots $`\pi_b`$ maps to $`F`$'s slots, and the edge check
entails it. Nothing about $`F`$ is proposed, so nothing is refused.

## Head-stable slots

A slot $`x`$ of $`h`$ is head-stable when every back edge $`b`$ into
$`h`$ maps $`x`$ to the slot holding the same binding it had at $`h`$:
$`\pi_b(x)`$ is the slot $`\pi_b`$ assigns $`x`$'s binding and no step on a
path from $`h`$ to $`b`$'s source binds that slot anew. In the graph's
terms: the binding is not the target of a `bind` continuation inside the
loop's nodes (the loop's counters, every `let` the body assigns, the
slots of bindings declared in the body); the slots the head adds for its
own temporaries are not stable. The renaming at the head maps the
entry edge's slots onto the head's: a fact is taken at the head's slots,
and a fact naming a slot the head drops is not taken.

`mi < to` at the inner loop over `extraSpacings` in `measureAnalysis`
(pretext prepare.ts:523): `mi` and `to` are bound outside the inner loop,
which binds only `k` and `width`, so both are stable there; the fact is
over values alone, so its support is empty. It is taken.

`to <= analysis.flags.length` at the outer loop: `analysis` is bound
outside, `flags` is a `@stable` field and the array's length location is
written by no step of the loop (its support is the length's location at
`grow`, which the loop's effects respect where its stores are apart:
a nonempty support, so the fact is not taken by this statement; it is
the case the next design step extends to supports the loop's own summary
respects, out of scope here).

## What changes in the walk

1. **Order.** A head is visited after its entry edge's source: the
   in-degree counts the entry edge (`inDegrees` today leaves edges into a
   head out, and `initialQueue` queues a head at in-degree 0). Back edges
   stay uncounted, so the order is still a topological order of the
   graph with back edges removed.
2. **The head's state.** `setupGiven` fixes $`\Sigma_h`$; the head's
   state becomes $`\Sigma_h \cup \mathrm{taken}(e)`$ when its entry edge is
   walked (`visitEntry`), at the head's slots.
3. **The checks.** Unchanged: every edge into the head entails the head's
   state, the entry edge included (it entails the taken part by
   construction).

Theorems whose statements change (cited names; each statement as it would
become):

- `SinglePass.setupGiven_get` / `SetupOk.recInv`: the record of a head's
  given state holds $`\Sigma_h`$ from setup; a second invariant,
  `HeadTaken`, states that after the entry edge is walked the head's state
  is $`\Sigma_h \cup \mathrm{taken}(e)`$ and that the entry edge's output
  entails it.
- `ofPass_heads`, `passHeads_cuts`, `HeadsCutCycles.mono`
  (`TolerantFramesDriverHeads`): heads still cut every cycle; the
  statement is unchanged, its proof reads the new in-degree.
- `Drives.inv`, `walk_of_accepts` (`TolerantFramesDriverWalk`): the
  queue invariant states that a head is queued only after its entry edge's
  source is settled.
- `entryStart_incoming`, `visitEntry_settled`
  (`TolerantFramesDriverSettleEntry`): a head's knowledge is fixed when it
  is entered; the soundness of every later edge into it is the edge check,
  as now.
- The headline theorem `checkUnitJson_safe` is unchanged.

## What it deletes from the front

The front proposes, at a head, the facts of the entry it can name
(`HeadInference.headFacts`): `carried` (facts of the entry over bindings
the loop does not assign), `eliminated` (a carried fact with a path's term
replaced by its entry value), `called` (a call's postcondition at its
actuals), `paired` and `joined` facts of bindings, and the front's
implications at cuts after a branch (`branchImplications`' widened cut
set). Each is a fact of the entry edge's state with an empty support at
the head or one the loop changes. With the statement above, the front
keeps only what the entry edge cannot give: the counters' widening
(`counterFacts`: the edge holds `i = from`, the head needs `from <= i`).
Deleted: `carried`, `eliminated`, `called`, `Ctx.bindTo`'s restatement,
`Ctx.join`'s entailment and substitution (`equalOf`, `substitute`),
`declaredIn` and the block and `if` joins of `walkStmt`, the path rule of
`Ctx.across`, and the `laterDrops` reruns for the deleted families.

**Measured** (`TSCERT_OBSERVE=heads`, pretext 9268edb1 `rich-inline.ts`,
`prepareRichInline`, branch at 961314ec plus the front's join fix,
2026-11-14): 571 proposals at 22 heads (153 integralities, 267 linear
facts over bindings, 151 linear facts over paths); the pass left out 840
in 4 runs: 192 refused by an edge into their head (131 path facts, 35
binding facts, 5 integralities, 21 implications), 645 left out at later
heads (`laterDrops`: 523 path facts, 95 binding facts, 27 integralities),
3 refused at an edge (2 implications, 1 integrality).

Removed by this design (**conjectured** from the families above): the 654
path-fact drops and the 23 implication drops are of facts the front
carries from the entry, which the head now takes where their support is
empty and otherwise never states; 677 of 840. The 163 binding and
integrality drops include counter facts the front keeps; how many of them
are carried facts is not established (the drop lines do not name the
family). The reruns that leave them out (3 of the 4 runs, and the
diagnosing walks, about 8 s of the pass's 10 s per the profile of
2026-11-13) go with them where no counter proposal is refused.

## Relation to the forward-facts work

The forward-facts draft ([forward-facts.md](forward-facts.md), branch
`forward-facts-retry`) took the forward facts $`F_c`$ at every cut and
measured `measureAnalysis` at 61.9 s against 35.0 s and
`prepareRichInline` past 850 s against 27.3 s (its §2a, measured
2026-11-10 in the search architecture): every statement entry was a cut,
each took every forward fact, and each edge's elimination derived new
combinations that accumulated along the function. This statement differs
in three ways (conjectured; not measured):

- **Heads only.** In the single pass a statement entry other than a head
  is no cut: its knowledge is already the forward one, so it adds nothing
  there.
- **No derivation at the head.** The taken facts are the entry edge's own
  atoms, selected; nothing is eliminated or combined at the head. The
  head's knowledge is a subset of the entry edge's output, which the walk
  already holds.
- **A filter, not a candidate set.** A taken fact is never refused (every
  back edge establishes it), so it causes no rerun; the forward-facts
  draft's facts had to be checked as candidates on refusal.

A prototype outside the proofs would measure the head's state size and the
pass's time on `measureAnalysis` and `prepareRichInline`; it is the first
step of the implementation.

## Open questions

- A fact of nonempty support that the loop's own effects respect
  (`to <= analysis.flags.length` across a loop writing other stores) needs
  the loop's summary as the context's frame; this draft takes none.
- Implications (`guarded` facts) at a head: taken by the same filter where
  their guard's slot is stable.
