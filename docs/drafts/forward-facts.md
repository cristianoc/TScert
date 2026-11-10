# Draft: facts computed forward, supplied facts as candidates

A design for where the facts of a function's body come from: the search
computes them forward through the graph by each node's rule, and a fact
the producer supplies at a statement entry is a candidate, kept where every
incoming edge establishes it. Base: local branch `chain1-facts` at
5c663703. Claims are labelled **read** (in the code or document named),
**observed** (with the run), **reviewed** (Astra, read-only, 2026-11-10) or
**conjectured**.

## The existing mechanism this extends

**Heap state assertions, checked on every incoming edge**
([heap state and assertions](../PROGRAM-TYPING.md#heap-state-and-assertions),
the mechanism [the general mechanisms](../DESIGN.md#general-mechanisms) list
for what holds at a program point), with
[linear facts](../ARITHMETIC.md) as the integer part and
[evidence produced from supplied claims](../SOURCE-ELABORATION.md#producing-evidence-from-supplied-claims)
as the division of work. Its parts, all **read**:

- **Cuts.** The lowering makes each statement entry a cut whose assertion
  is the entry's claimed facts concatenated with the written invariant
  (`Source/Lowering/Flow.lean`, `recordAssertion`, `recordCut`). The
  producer emits one entry per node of the flow graph
  (`proposal_flow.ml`, `transfer`), so every statement entry is a cut.
- **Forward computation between cuts.** At a node that is no cut the
  search computes the knowledge: with one predecessor, the projection of
  the predecessor's output along the edge; at a merge, `HeapKnowledge.meet`
  of the projections, with the guarded candidates every predecessor
  entails, read-link restatements among them
  (`CertificateProducer.lean`, `produceRawUsing`). A node's output is its
  step checker's (`Checker.run`: `ordinaryOutput`, `lengthOutput`,
  `growOutput`, `effectKept`).
- **The edge test.** Every edge is checked by `checkTargetResult`: the
  source's output, projected, entails the target's knowledge
  (`KnowledgeExpand.checkIn`, sound by `checkIn_sound`; its linear part is
  `Linear.entailsWith`, a bounded Fourier–Motzkin search whose steps
  `Linear.check` re-checks).
- **Assertions.** `checkAssertions` requires a cut's knowledge to equal its
  assertion and every recorded assertion to be entailed. The acceptance
  theorem's conclusion includes that entailment (`RequestsSafe`,
  `UnitSafe`); its proof uses the entailment and no equality (reviewed:
  `checkGraphAssertions_entailed`, `checkAssertions_entailed`,
  `checkRequests_assertions_at`).
- **Seeded implications.** At a cut whose back edge is not yet produced the
  search starts with no implication, acquires seeds, and retries, at most
  four seeded and two waiting rounds (`meetImplications`); element atoms
  are seeded the same way (`metElems`). A cache keyed by a node's input
  (`latest`) spares re-running a node whose input did not change.

The design changes what a supplied entry fact is, from a promised
assertion to a candidate, and gives the forward computation's facts to
cuts as it gives them to other nodes. It adds no rule and no kind of
knowledge.

## What the present division costs

- **The transfer is written twice.** The producer's dataflow over the
  source (`linear_facts.ml`, which states that it mirrors Lean's steps;
  seven families: bounds, linear, guarded, disjunctions, `every`, regions,
  store separation) infers what the search's forward pass infers again by
  Lean's rules; the check then validates the evidence.
- **Acceptance is not monotone in the proposal** (observed, 2026-11-10): a
  fact claimed at an entry that the preceding node's rule does not keep
  refuses the unit. Proposing the general element write's growth before
  its Lean rule existed turned pretext's `getSegmentFit` from verified to
  refused. A fact the producer does not claim at an entry is lost there
  though the node's rule keeps it: `measureAnalysis` lost
  `to <= flags.length` at 31 entries, 18 of them only because the
  producer's lists of forms lacked a case Lean's rules have.
- **Evidence size** (observed, `element-write-keeps-lengths.ts`): 963 KB of
  evidence for 11 statements, 176 lowered nodes; 59 % is the knowledge
  table, 223 entries of 19.7 index atoms on average. Claims carry 10.8
  index facts per entry.

## The design

### 1. Required assertions and candidates, by provenance

What the lowering records at a cut splits by where it comes from, before
any concatenation:

- **required** $`R_c`$, recorded as assertions as today: a written
  `@invariant`, an expression's observation, a return's postcondition, an
  effect's promise, the bindings' types;
- **candidates** $`C_c`$, recorded apart: every fact the producer supplies
  at the entry (bounds, linear, guarded, `either`, quantified, `apart`,
  `storesApart`, and the links, element and content facts it supplies).

A `@requires` is an assumption at the function's entry and an obligation at
each call, as today; the entry's external check is unchanged.

The acceptance theorem keeps its statement: every recorded assertion is
entailed. Its meaning changes in one place, which this design states: a
fact the producer supplies at a statement entry is no longer among the
assertions the accepted program is shown to meet.

### 2. A cut's knowledge

```math
K_c \;=\; R_c \,\cup\, \{\, a \in C_c \mid \forall (n \to c).\ \mathrm{proj}_{n \to c}(\mathrm{out}(n)) \vdash a \,\} \,\cup\, F_c
```

where $`F_c`$ is what the forward computation gives a node that is no cut:
the projection of the one predecessor's output, or the meet of the
predecessors', with its entailed guarded candidates. The check requires
$`R_c \subseteq K_c`$ and checks every edge into the cut, as today. Safety
needs nothing more of a cut (reviewed): established entry knowledge,
checked steps, checked incoming edges.

So a fact a rule keeps reaches the next entry whether or not the producer
claims it, and a claimed fact no rule keeps is left out of $`K_c`$.

### 3. Solving

The candidates of a function are finite, $`M`$ in all. The search solves
the graph's strongly connected components in order, each by a worklist:

- a cut starts at $`R_c \cup C_c`$, with $`F_c`$ of the predecessors
  produced so far; a predecessor not yet produced is unknown, neither
  establishing nor refuting;
- an edge that does not establish a candidate removes it from the cut, and
  the nodes that read the cut's knowledge are re-run, through the
  input-keyed cache;
- candidates only leave, so a component ends after at most $`M + 1`$
  passes over it; no inner component is restarted for an outer one's
  removal unless its input changed.

A handler's entry takes its predecessors from the exceptional edges
(`handlerFacts`), which the table of incoming edges does not hold today.
The candidates a loop head takes from its entry edge (§5) are fixed for the
component's solving.

This replaces the bounded seed rounds for facts. Implications and element
atoms keep theirs until they are shown to fit the same solver.

### 4. Monotonicity

**Of certificates** (follows from §2): evidence accepted with candidates
$`C`$ is accepted with any $`C' \supseteq C`$, since the check requires
only $`R_c \subseteq K_c`$ and the edges.

**Of the search** (conjectured, with its conditions): the search that
starts from every candidate finds a certificate with $`C'`$ where it finds
one with $`C`$ if each node's transfer is monotone in its input, the
executable entailment is monotone in its hypotheses, and the candidates are
fixed while a component is solved. The entailment is not known to be
monotone: it picks representatives by which terms are known defined, and
its row and fuel limits are reached sooner with more hypotheses. Where it
is not, a cut's knowledge is searched at the smaller of two sets before the
unit is refused.

### 5. The producer's part

The producer keeps supplying facts at every entry. With §2 they are
candidates, harmless where no rule keeps them, and they carry what the
forward computation does not: the bounds its join synthesizes at a merge
(at `0`, the maximum array length, the maximum safe integer: `i = 0` joined
with `i - xs.length ≤ -1`), the facts relating bindings a loop's body
changes, and intermediate facts that make a later bounded entailment
succeed.

A loop head also takes as candidates the index atoms on its entry edge,
within the head's scope.

Each family of the producer's dataflow is retired where the corpus
verifies without it, by measurement, family by family. None has to be
retired for §2 to hold.

### 6. Evidence at cuts only

The check validates each node's supplied knowledge and output
(`checkNodeResult`), and `outputFits` lets the supplied output be weaker
than the computed one. Carrying knowledge at cuts only makes the check
compute the rest: a reconstruction that either keeps that weakening or
shows it unused.

## What changes for whom

| | Today | With the design |
| --- | --- | --- |
| A fact a rule keeps, the producer has no case for | lost at the entry | kept |
| A fact the producer claims, no rule keeps | the unit is refused | the candidate is left out at that cut |
| A new Lean rule keeping more facts | needs its mirror in the producer | takes effect alone |
| A written `@invariant` an edge does not establish | refused | refused |
| A refused read's diagnostic | the read | the read, and the candidates left out with their edges |
| A control forging an entry fact | refused at the cut | left out; refused where an obligation needs the fact |

A refused obligation's diagnostic lists the candidates left out on the
paths reaching it, each with the edge that did not establish it:
[where a proposal drops facts](../OBLIGATION-DIAGNOSTICS.md#where-a-proposal-drops-facts),
stated by the search about the rules.

## Costs and risks

- **Passes over a component.** Bounded by $`M + 1`$; the count per unit is
  recorded from the first step on.
- **Entailment calls.** One per candidate and incoming edge where the
  syntactic match fails; each is the bounded Fourier–Motzkin search.
- **Controls of forged claims.** Each control that forges an entry fact
  and expects a refusal at the cut is reread: where it tests that a false
  fact is not believed, its refusal moves to the obligation needing the
  fact; where it tests which point a claim attaches to, it keeps its
  meaning through the required part.
- **Types.** Bindings' types are claimed at every statement entry and
  checked on every edge (read). They stay required.

## Steps, each mergeable and measured

| # | Step | Shows | Measured by |
| --- | --- | --- | --- |
| 1 | §1–§3 for the candidates at the present cuts, without $`F_c`$; the list of candidates left out, in the diagnostic | over-proposal no longer refuses; the theorem under the split | the corpus (pipeline cases, pretext's 210 functions) unchanged; the `getSegmentFit` experiment verifies; passes and search time per unit |
| 2 | $`F_c`$ at cuts | a fact a rule keeps is not lost at an entry | `measureAnalysis`'s baseline with the producer of 3807e8c0, which lacks 18 cases; corpus unchanged or larger |
| 3 | Loop-head candidates from the entry edge | fewer facts needed from the producer at loops | corpus; passes per unit |
| 4 | The producer's families retired where the corpus verifies without them | the mirror shrinks | corpus per family; claims bytes |
| 5 | §6 | evidence size | bytes per lowered node; check time |

Step 1 removes the regression class observed and is the riskiest for the
search's scheduling. Step 4 is the largest risk for completeness, and is
optional family by family.

## Beside this design

Two levers on the time to a verdict are separate designs (reviewed, not
measured):

- **Old evidence as an untrusted proposal.** Across a change of the
  verifier, a unit's stored evidence is checked by the new verifier (4 s
  for `measureAnalysis`) before any search (25 s), and searched again only
  where the check refuses. Acceptance stays the current checker's.
- **Emitted effect interfaces.** A module's certified footprints, emitted
  once and read by its importers, in place of the module's search and
  check in each importer's run
  ([certified imports](../SOURCE-CONTRACTS.md#certified-imports)).

A gate for regressions: a required CI check over a pinned pretext (source,
rewrites, configuration), which fails on any baseline function missing,
refused, errored or timed out, by identity and not by count, and a small
cold set (`measureAnalysis`, nested loops, an import-heavy file) recording
search time, check time, passes and evidence bytes.

## Open questions

1. Whether implications and element atoms move to the solver of §3.
2. The conditions of the search's monotonicity (§4), and whether the
   entailment's choice of representatives can be made independent of the
   hypotheses added.
3. Passes per unit on pretext and on TScert's own code.
