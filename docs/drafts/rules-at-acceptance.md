# The note's rules at acceptance

## The existing mechanism this extends

| Concern | Lean definitions | Owning document |
|---|---|---|
| Effects per exit, rebasing, composition of summaries | `Exits`, `ExitSpec`, `CommandSummary`, `CommandSummary.Sound`, `ThenEvidence`, `Post.compose_rebases`, `rebaseAll`, `RebaseOk` | [Effects of commands](effects-of-commands.md), [Footprints](../FOOTPRINTS.md) |
| Checked consequence and derivations | `checkDerivation`, `checkScoped`, `checkConsequences`, `ExitSpec.weakenCheck`, `RawDerivation`, `Derivation` | [Parity interfaces](parity-interfaces.md) |
| Recorded visits of the pass | `SinglePass.VisitRecord`, `StepCertificate`, `StepGrades`, `footprintCheck`, `recordsAdmit`, `SinglePassClose.run_rebound_of_records` | [Source elaboration](../SOURCE-ELABORATION.md#checking-a-unit-in-one-pass) |
| Loops | `LoopEvidence`, `CommandLoops`, `headExit` | [the note](tolerant-frames-note/note.tex), Loop |

This design makes those mechanisms the ones acceptance applies. The
comparison it starts from is the [rule table](parity-rule-table.md).
Signatures below are design sketches, not compiled Lean; `CheckedBody`,
`CompositionEvidence`, `EdgePremises`, `pullback`, `EdgeRun`,
`LoopRegion`, `LoopCertificate` and `CertifiedLoop` are new interfaces over
the existing graph certificates.

"The mechanism the pass applies" means: every accepted fact in scope has a
derivation in the note's rules, and the soundness of acceptance consumes
that derivation. A decision proved sound by its own theorem meets the
safety goal and leaves the rule's correspondence open.

## A. Composition used by acceptance

**The target.** Every accepted body has a certified summary relative to its
entry, and every exported exit guarantee is a weakening of it. A local
certificate is sound by itself, with no enclosing bound. A list of
alternative specifications keeps the evidence that selects or combines
them.

**The decisions it replaces.**

- `footprintCheck` (through `boundOk`) checks each visit against the
  enclosing normal and exceptional bounds.
- `VisitRecord.of` projects regional frames and postconditions to closed
  grades (`StepCertificate.grades`), and `recordsAdmit` checks a completed
  walk's grades again (`VisitRecord.admits`, `StepGrades.admits`).
- An escaping throw requires the declared normal bound within the
  exceptional bound, whatever the effect of its actual prefix.
- A caught throw is checked within the enclosing normal bound; its
  handler's summary takes no part.
- The regional checks keep their own entry links and freshness and check
  each step.
- `ExitProposals.ClassSummary` composes proposed effects over an untrusted
  walk of the source; its composition theorems are about summaries, not
  about the verifier's graph.

A closed join stays a valid optimization where it is a proved instance of
command composition. What the target adds is the connection between the
checked graph's executions and its composed summary.

```lean
-- Sketch, not compiled.
def checkComposition (b : CheckedBody) (ev : CompositionEvidence b) :
    Except LocatedError CommandSummary

theorem checkComposition_sound
    (h : checkComposition b ev = .ok S) :
    CommandSummary.Sound b.arena b.pre b.runs S

theorem accepted_summary
    (h : bodyAccepted b claimed = true) :
    ∃ S, CommandSummary.Sound b.arena b.pre b.runs S ∧
      ∀ c, ExitSpec.Weakens b.arena b.pre (S.get c) (claimed.get c)
```

**Commits, in order.**

1. Each visit's local exit specifications are tied to its checked
   operation, its actuals, its entry valuation and its runs; both exits
   and the operation's postconditions are kept.
2. An executable check of `ThenEvidence.Valid` and `ThenEvidence.Into`,
   from the existing rebasing, class evidence and checked consequence.
3. Prefixes and branches compose over the graph's actual edges; a caught
   throw and its handler's exits compose explicitly; a theorem connects
   the graph's executions to `Runs`.
4. Cyclic composition is certified from supplied prefix summaries and
   closure checks, by `LoopEvidence` for effects; C adds the shared
   frame assertion.
5. Summary weakening takes the place of `recordsAdmit` and the walk's
   algebra of enclosing bounds; an exceptional exit is checked from its
   actual prefix, with no inclusion of the normal bound in the
   exceptional one.
6. Exports of codes and modules, and the assumptions of recursion, go
   through that certificate; the acceptance checks it makes redundant are
   retired; `ExitProposals` stays a producer.

Return, throw, break and continue keep distinct destinations while the
graph composes. The two exits of a `Completion` describe a command's
boundary, and distinct destinations inside a body stay distinct until
their command ends.

Commits 1 to 3 add definitions and theorems that acceptance does not read;
commits 5 and 6 change decisions. The headline theorem
`PassUnit.mode8Accepted_sound` keeps its premise and conclusion.

## B. Checked transfer

The note's checked transfer (§7) requires, for each fact of the target, a
derivation from the source's knowledge at the entry, the selected exit's
transition and postcondition and the edge's branch condition, concluding
the target assertion under the edge's renaming.

The existing deciders become producers of derivations that `checkScoped`
checks. Their search stays; the checked judgment is the one acceptance
reads.

- `frameKeeps` produces the support, respect and elimination of the
  modality.
- `postKeeps`, `callChanges` and `Composer` produce Entry and its
  consequences from exact postconditions.
- The arithmetic producers emit the existing linear and operation-rule
  certificates.
- An allocation emits freshness, emptiness and separation, arrays reached
  through defined paths included.
- Every edge uses its own completion, its bound result or thrown value,
  its branch condition and its renaming; at a handler, the exceptional
  frame and postconditions keep the facts they support.
- A merge requires a derivation from each reachable predecessor; a loop
  head has the same obligation.
- Definedness from typing and the rigidity of a singleton contract enter
  through explicit bridges into the checker.

```lean
-- Sketch, not compiled.
def checkEdgeFact (e : CheckedEdge) (A : AssertionRef) (raw : RawDerivation) :=
  checkScoped e.arena e.scope (EdgePremises e) (.at .after (pullback e A)) raw

theorem edgeFact_sound
    (h : checkEdgeFact e A raw = .ok d)
    (hr : EdgeRun e s s') (hΣ : KnowledgeHolds e.source s) :
    Sat e.arena (e.rename s'.env) e.mark s'.heap A
```

| Architecture | Cost and guarantee |
|---|---|
| General proof search for every fact | the largest change, with repeated support and arithmetic search and large proof trees; no soundness gain over certified schemas |
| The existing deciders produce a `RawDerivation` that `checkScoped` checks | moderate cost, some checking done twice; reuses the search, locates failures, one proof interface; **the first implementation** |
| Boolean deciders with proved derivation schemas | the lowest running cost and the largest proof maintenance; equivalent where success constructs a `Derivation` under exactly the edge's premises |

After the integration, a hot schema is specialized by proving its check
correct and building the typed derivation directly, under the same
certificate interface and premises.

## C. Rule Loop with its frame

```math
\frac{\{I\land\Box_\Phi R\}\ c\ \{I\} \qquad c:\Phi \qquad \Phi\ \text{rigid}}
     {\{I\land\Box_\Phi R\}\ \mathrm{loop}\ c\ \{I\land\Box_\Phi R\}}
```

The guard belongs to the body. The loop-carried variables occur in the
invariant `I`; the frame `R` and the effect `Φ` mention none of them. The
conclusion is the normal one; exceptional departures use their own
composed summaries.

`headExit` checks the supplied facts, implications and identities of entry
values on every edge into the head. `CommandLoops` proves closure of
iteration, preservation under the modality and reliance at a prefix. The
integration:

1. The head's invariant and its frame assertion are proposed separately:
   counters and changing relations in the invariant, stable external facts
   in the frame.
2. The body's command summary is proposed and certified under the head's
   combined condition; its normal frame, or a checked rigid widening of it,
   is the loop's effect.
3. Rigidity by `RigidityEvidence.check`: closed effects, or regions whose
   paths are certified rigid on an invariant domain, that domain proved at
   the entry.
4. The combined condition is established on every external entry, the
   invariant on each back edge; Frame+ gives the modal conjunct.
5. The frame and the effect are checked invariant under the renaming of
   every back edge.
6. Every use inside the body has a certified prefix bounded by the loop's
   effect: a body that changes something and restores it meets a bound at
   its exit and keeps no bound inside.
7. Normal and exceptional departures compose separately, through nested
   handlers and loops.

The candidate frame is an induction hypothesis, discharged by the external
entry, the checked effect of the body, the recurrence and rigidity.

```lean
-- Sketch, not compiled.
def checkLoop (L : LoopRegion) (ev : LoopCertificate L) :
    Except LocatedError CertifiedLoop

theorem checkLoop_sound
    (h : checkLoop L ev = .ok q) :
    q.summary.Sound q.arena q.entry L.runs ∧
    q.NormalExitsEstablishInvariantAndFrame ∧
    q.CertifiedPrefixesJustifyFrameUses
```

The last two predicates expand to the note's invariant and modality and to
`reliance_at_prefix`, the agreement of valuations included, and to no
stronger hypothesis.

Commits, in order: the head's representation and the renaming checks;
rigidity introduced from typing; certification of the body's and the
prefixes' summaries; the derivations at entries and back edges; departures
and handlers; retirement of the special preservation branches.

The fixtures related to loops, with what each requires, are the last
table of the [rule table](parity-rule-table.md#five-fixtures-and-what-each-requires).

## D. The checking round

The note's examples are the five labelled examples (`alias`, `sep`,
`fresh`, `view`, `full`), the thirteen rows of the patterns, and the
examples inline with the definitions and operations.

| Subject of the note | Existing cases to inspect |
|---|---|
| Bounds tolerant of aliasing | `array-push-keeps-facts`, `bounds-pattern-write-at-length` |
| Regional and stable-path frames | `stated-region-steps`, `bounds-pattern-grow-upper-refused`, `bounds-pattern-two-field-guard-refused` |
| Fresh effects | `map-stable-fresh-store`, `stated-fresh-frame`, `exceptional-footprint-fresh` |
| Exact growth | `bounds-pattern-known-growth-refused` and `bounds-pattern-write-at-length-refused`, both positive; `written-ensures-push-refused`, a gap |
| Views | `typed-array-element-writes`, `typed-array-length-across-field-write`, `invalid-typed-array-element-read-after-write` |
| Exceptional bounds | `exceptional-footprint-handler`, `normal-return-rethrow` |
| Derivations alone | `ParityDerivationTests`: view frames, P4, P18, shift and mask, arithmetic, exact length |

These are declared expectations; whether each fixture reproduces its
example of the note is what the round establishes.

The round adds one table to the repository, with the columns: identifier
in the note; exact obligation; source case and function; expected outcome;
derivation by the rules; negative neighbour. It includes the inline
examples and the note's four stated limits. A static check enforces unique
identifiers, existing cases and functions, and agreement with `cases.mts`.

The round exercises the derivation path acceptance applies, checks every
positive and negative obligation, inspects each refusal, and then reads
both notes again. A research test retires where a pipeline case carries
its signal; the controls of malformed certificates stay.

## Risks and decisions

- Proved derivation schemas meet the goal "the same statement in Lean and
  the mechanism the pass applies"; a decider proved sound without a
  derivation meets safety alone.
- Write-End: the note states `x[i] ≐ v` and the extension of density. Lean
  and its assertions extend to state both; a weaker note needs the
  owner's approval.
- Push: the note states `y = |x|`. Lean proves it for the modelled
  execution, with an audit of the native contract; a stronger library
  assumption goes through the trust review and its trailer.
- Str-Read: the note reads the UTF-16 code unit at `i`. Parity there needs
  the exact representation of string values, reviewed.
- Loop: the note states that neither `R` nor `Φ` mentions a loop-carried
  variable and that an iteration's exit alone gives no bound inside it.
  Relaxing either needs a new theorem and text the owner approves.
- Every: the note's axiom is for a scalar predicate. Support of a
  predicate that reads the heap proves its additional dependencies.
- Conj keeps its condition, the second specification's postconditions
  independent of the world, rigid paths and modal postconditions
  included.
- A to C change neither the deterministic reduction, the trust in hosts,
  the scope of closure specifications, nor the one serialized form. The
  note's limit on replacement records stays for the second note (E)
  unless a derivation changes it.
