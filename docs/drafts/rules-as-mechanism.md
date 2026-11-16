# The paper's definitions and rules as the mechanism of acceptance

A design draft. It proposes that the verifier accept a function by the
definitions and rules of the paper
[Tolerant frames](tolerant-frames-note/note.tex), so that the paper and the
Lean development have the same organisation. Lean sketches in this draft
are not compiled. The draft was reviewed against the sources by
gpt-6-astra on 2026-11-16, with nothing built or run; its corrections are
part of this text.

## The existing mechanism this extends

| Concern | Lean definitions | Owning document |
|---|---|---|
| Location kinds and roles, fixed for a location's life | `Kind`, `Role`, `roleAt`, `HeapOk`, `RootsOk`, `RefsOk` (`Semantics/Worlds.lean`, `Semantics/Heaps.lean`, `Semantics/Kinds*.lean`) | [Location kinds](location-kinds.md) |
| Regions, changes, effects | `Footprints.Region`, `Region.mem`, `Selector`, `Change`, `Footprint`, `Post` | [Footprints](../FOOTPRINTS.md#changes-and-footprints), [parity interfaces, I1](parity-interfaces.md#i1-entry-relative-regions-and-exit-specifications) |
| Support of a fact, respect, the frame theorem | `Term.support`, `IndexFact.support?`, `respects`, `respect_sound`, `keeps_sound` (`Semantics/Survival.lean`, `Semantics/FootprintStability.lean`) | [Support and respect](../FOOTPRINTS.md#support-and-respect) |
| Disjointness of two regions | `SepQuery`, `knowledgeQuery` (`classQuery` and store-site separation, `Semantics/SurvivalSeparation.lean`), `SepKnowledge.apart₁` | [Separation queries](../FOOTPRINTS.md#separation-queries) |
| The paper's rules as checked derivations | `RawDerivation`, `Derivation`, `SupportEvidence`, `checkDerivation`, `checkScoped`, `checkScoped_sound` (`Semantics/ParityDerivations.lean`, `Semantics/ParityEvidence.lean`) | [Parity interfaces](parity-interfaces.md) |
| The judgment at an edge | Checked transfer, section "Transfer along edges" of the paper | [the paper](tolerant-frames-note/note.tex) |
| What acceptance applies today, rule by rule | the deciders named in each row | [The rule table](parity-rule-table.md) |

This design adds no mechanism. It makes existing ones the only ones: the
roles of locations decide where regions can overlap, and the paper's
checked transfer, with derivations in the paper's rules, decides which
facts hold at each point.

## The requirement

Each definition and each rule of the paper is the definition and the rule
that acceptance applies. Stated as an invariant of acceptance:

> Every fact and every effect that acceptance consumes has evidence in the
> system organised as the paper is. No fact reaches acceptance through a
> preservation check that establishes no such evidence.

A decision procedure with its own soundness proof, which establishes no
derivation in the paper's rules, does not meet the requirement, however it
is proved.

The invariant concerns organisation. It gives "accepted implies derivable
by the paper's rules". It does not by itself give equal verdicts with a
reader of the paper: the pass searches for a derivation and may not find
one that exists. Equal verdicts also need the paper to state what the pass
searches for (part 5), and are measured by the paper-reader test of the
[parity skill](../../.claude/skills/parity/SKILL.md#the-paper-reader-test).

## Where the organisation differs

### A program that shows it

```ts
type Cursor = { at: number };
function grow(out: number[]): void { out.push(1); }
/** @requires safeInteger(cursor.at) && 0 <= cursor.at && cursor.at < flags.length */
export function read(flags: Uint8Array, cursor: Cursor, out: number[]): number {
  grow(out);
  return flags[cursor.at]!;
}
```

By the paper the read verifies. The paper gives `push` the effect
$`\{\mathit{out}.\mathsf{store} : \mathsf{grow}\}`$, the effect of `grow`
at its entry is the same by Seq-Eff, and the fact
$`\mathit{cursor}.\mathit{at} < \mathsf{view}(\mathit{flags})`$ reads one
field location, which that effect does not contain.

Observed on `single-pass` at `de40292b`, 2026-11-16, each variant run
through the pipeline:

| The step before the read | Verdict |
|---|---|
| `out.push(1)` written directly | verified |
| a call of a function type stating the empty effect | verified |
| a call stating `values: "keep"; stores: "keep"` | verified |
| `grow(out)`, its effect inferred | refused |
| `grow(out)` stating `values: "keep"; stores: "keep"; "out[*]": "any"` | refused |
| a call of a function type stating `values: "keep"; stores: "grow"` | refused |
| the same call, with `cursor.at` first copied to a local variable | verified |

The cause is not established by an experiment that changes the code. The
review's trace of the sources finds two obstacles, described next. The
trace predicts that a closed effect on stores alone keeps the field; the
sixth row is a refusal under such a stated effect, so at least one step of
the trace, or of the route a stated function type takes, is still to be
found.

### Effects of native steps, and what a wrapper keeps of them

The paper gives each native step a regional effect: `push` changes the
receiver's store by `grow`. In the verifier the frame of `push` is
`{values: any, arrays: grow, views: grow}`, and its precise guarantee is in
its postconditions: the transition of the receiver's store, the extension
and the append (`tools/array-prototype.mts`, `tools/type-graph.mts`).

A function's inferred effect is the closed bound of its steps' frames
(`PassProposals.localSummary`, `ExitSummaries`). The postconditions of the
steps do not pass through the function's interface. So `grow` has the
effect `values: any`, under which a numeric field is not kept, by the
paper's rules too. A direct `push` keeps the field by the other route: its
extension postcondition gives a change that keeps numbers
(`PromiseCalls.callChanges`, `growChanges`).

The difference in organisation: the paper states what a native changes as
an effect, and composes effects by Seq-Eff. The verifier states a wide
frame and a precise postcondition, and composes frames only.

### Disjointness of regions

The paper gives each location one of five kinds, fixed for its life: field,
cell, element cell, store, identity; a store has the form of an array store
or of a view store. A region contains locations of known kinds:
$`\pi.f`$ a field or a cell, $`\pi.\mathsf{store}`$ a store,
$`\pi[\ast]`$ a store and its element cells,
$`\mathsf{all\text{-}values}`$ every location of a value kind,
$`\mathsf{all\text{-}stores}`$ every store. The paper uses kinds to keep a
field apart from a binding's cell.

Lean has the kinds and the forms in its worlds (`Role`, `roleAt`) and
proves that every transition keeps them. The regions of an effect do not
use them. A class region is read from the contents a location holds
(`Region.mem` at `cls`, `Selector.selects`), over three categories: value,
array store, view store. The query a call's check asks, `knowledgeQuery`,
answers by class only for a pair of a region marked with its class
(`inCls`) and a class region, and otherwise by separation of store sites.
The support of a numeric term at a path is an unmarked `path` region, so a
field against the stores, or against another array's element cells, has no
answer.

Three region forms differ in meaning from the paper's:

- `own x` includes the object's internal store slot; the paper's
  $`\pi.\mathsf{own}`$ is the object's value fields.
- `cell b` selects every location of the value category; the binding's name
  is not read. [Parity interfaces, I1](parity-interfaces.md#regions) records
  this as conservative, with exact selection left open.
- `all` selects every natural number, allocated or not.

### Which rule decides

The [rule table](parity-rule-table.md) compares the paper's 26 rules in
scope with what acceptance applies. Call and Conj are applied as the paper
states them. Every other rule is applied through a separate decider with
its own soundness theorem: Entry, Frame, Loop, Alloc, Seq-Eff, Fresh-Eff,
the seven axioms of the modality, Transfer, the arithmetic rules and the
writes. Frame+ is applied by nothing.

Lean contains the paper's rules as a derivation system with a checker
(`checkDerivation`, `checkScoped`). Acceptance does not use it.

## The design

### Part 1. A call edge, complete, by checked transfer

The first step takes one kind of edge, a call's normal exit, and makes its
facts hold by the paper's judgment of checked transfer: each target fact
has a derivation from the source's knowledge, the exit's transition, the
exit's postcondition and the branch condition, under the edge's renaming.

```lean
def checkEdgeFact (e : CheckedEdge) (A : AssertionRef) (raw : RawDerivation) :=
  checkScoped e.arena e.scope (EdgePremises e) (.at .after (pullback e A)) raw

theorem edgeFact_sound
    (h : checkEdgeFact e A raw = .ok d)
    (hr : EdgeRun e s s') (hΣ : KnowledgeHolds e.source s) :
    Sat e.arena (e.rename s'.env) e.mark s'.heap A
```

`CheckedEdge`, `EdgePremises`, `pullback` and `EdgeRun` are adapters
between the graph and the checker. `checkScoped_sound` proves consequence
from premises it assumes. The adapters carry the rest, and each is a
theorem to prove: that the premises hold at the edge, that the renaming is
the edge's, definedness, scope, and the transport of the entry mark.

This part also settles, for a call, how a function's interface carries the
guarantee of its steps. The proposal is the paper's: the effect of a step
is regional where the step's change is regional (`push`:
$`\{x.\mathsf{store} : \mathsf{grow}\}`$), and a body's effect is the
composition of its steps' effects by Seq-Eff with rebasing. The wide frame
with a precise postcondition is replaced by the regional effect where the
two say the same.

Its measure is the program above: the fourth row verifies, and the cause of
each refused row is established.

### Part 2. Regions are bounded by roles

**Definition.** A *role class* is one of field, cell, element cell, array
store, view store, identity: the roles of `Worlds.lean` without their
parameters. It projects to the paper's five kinds and to the three
categories of `Selector`; neither of those two partitions refines the
other, and the role classes refine both.

A region has a *bound*: a set of role classes that contains the role class
of every allocated location in it, in a well-formed state.

| Region | Bound |
|---|---|
| `field x k`, `path x p k` at a key other than the store key | field, cell; one of the two where the object's role evidence says which |
| `field x k`, `path x p k` at the store key | array store |
| `store x p` | array store, view store |
| `elems x`, `pathElems x p` | element cell |
| `own x`, `pathOwn x p` | field, cell, array store |
| `cls c` | the role classes of the categories `c` selects |
| `inCls r c` | the bound of `r`, restricted to the role classes of `c` |
| `cell b`, `all` | every role class, until `cell b` selects its binding's cell |

**Disjointness.** Two regions are disjoint when their bounds are disjoint,
or when the state's knowledge separates them: provenance, distinct field
pairs and store separation, as `SepKnowledge` holds today. A restriction of
a region inherits each separation of the region.

**Theorem to prove.**

```lean
theorem Region.bound_sound {n : Nat} {W : WorldT n} {ρ : Env} {h : Heap}
    (hok : HeapOk n W h) (hρ : RootsOk W ρ) {r : Region} {l : Nat}
    (hl : l < h.length) (hm : r.mem ρ h l = true) :
    ∃ c ∈ r.bound, (roleAt W l).map Role.cls = some c
```

Its proof for a path is by induction on the path: a read from a value with
valid references gives a value with valid references. It needs no rigidity,
which concerns two states. `SepQuery.Sound` quantifies over every location;
it is restated over allocated locations, the ones `Post` and `Supported`
constrain.

**Respect.** The paper defines respect semantically and gives the pairwise
check, "the change is small enough or the regions are disjoint", as
sufficient. Lean keeps that distinction: `Supported` is the definition, and
`respects` with the query above is the check.

**The three region forms.** `own` is given the paper's meaning, the value
fields, with the store named separately where an effect means it. `cell b`
selects its binding's cell, which is the open item of I1. `all` is read
over allocated locations.

**Where it applies.** In the query of acceptance and in the support
evidence of the derivation checker, which are one definition after this
part.

### Part 3. Every decider produces a derivation

The deciders that keep or establish facts today stay as the search. Each
produces a derivation in the paper's rules, and acceptance checks it by
part 1's judgment.

| Decider today | What it decides | The paper's rule |
|---|---|---|
| `frameKeeps`, `IndexFact.keeps` | a fact kept because the frame respects its support | Frame |
| `postKeeps`, `callChanges`, `Term.keptBy` | a fact or term kept by a change read from the exit's postconditions, or from the frame's closed bound | Entry, with consequence |
| `effectKept` | either of the two above | the rule of the route taken |
| `Composer.fact` | old facts, kept terms, relational postconditions and renaming combined | Entry; each premise its own derivation |
| `everyKept` | a quantified fact under a change keeping stores and numbers | Frame |
| `keepsLengths`, `boundedLength_sound` | lengths across a write in bounds | Write-In |
| `linearAtoms`, `smallOperand`, `bitAtoms`, `stringLengthPlusOne` | arithmetic | the arithmetic rules |
| `IndexWrites.regionAtoms`, `Checker.emptyArrays` | freshness and separation of a new array | Alloc |

Six deciders keep facts for which the derivation checker has no rule form
today:

| Decider | The fact |
|---|---|
| `cellKept`, `keptCells` | $`y.f \in V`$ across a write that may alias, when the written value is in $`V`$ |
| `fieldEvery` | a quantified fact with an index-independent body across a field write whose value satisfies the body |
| `everyGrown`, `appendKept` | a quantified prefix across growth; a whole-array fact across an append that satisfies it |
| `everyWritten`, `writtenPrefix`, `writeKept` | a typed array's quantified prefix kept or extended by an exact write |
| `writeAtoms` | separation kept when a store changes and lists only its old cells and fresh ones |
| `IndexFact.keeps`, `Term.keptBy` in general | facts at paths, guarded facts and compound facts, by supports the checker's `SupportEvidence` does not represent |

Each of these is one of three things, and the inventory of part 3 says
which:

1. a consequence the paper's rules already justify, whose rule form is
   missing in the derivation system; the form is added to Lean;
2. a sound rule the paper lacks; it is added to the paper with the owner's
   approval, and to Lean;
3. a fact the decider is wrong to keep; a soundness defect.

The paper's section "What verifies" already describes several of the six
(the write that keeps a field's contents, the append, the exact write of a
typed array), which points to the first case for them. The limit met there
is the certificate language: `SupportEvidence` has support for a literal
equality at one field and for linear atoms at empty paths, and
`RawDerivation` has no constructor for a weak update or a quantified
update.

The reverse case is known: `edgeStoreOf` drops heap facts at a handler edge
that rule Frame keeps at the exceptional exit.

**The headline theorem.** `mode8Accepted_sound` keeps its statement. Its
proof reads the facts at each point from `edgeFact_sound`. A decider's own
theorem is deleted only where its derivations replace it; the lemmas about
operations and supports from which derivations are built stay, and so do
the controls that guard the unproved translation from the source.

### Part 4. Merges, loops and composition by their rules

The same change for the rest of the graph. The earlier designer's answer
sized each ([the note's rules at acceptance](rules-at-acceptance.md),
designs A and C).

- **Every edge and merge.** Part 1's judgment at each exit, each branch and
  each incoming edge of a merge. `exitStep`, `edgeTransfer`, `assertionExit`
  and the merge checks become its producers.
- **Loop.** The facts at a loop head are an invariant $`I`$ and a frame
  $`\Box_\Phi R`$, checked by rule Loop with the rigidity of $`\Phi`$.
  `headExit` becomes the producer of the two parts.
- **Seq-Eff and Fresh-Eff.** A body's effect at its entry is the
  composition of its steps' effects on both exits, with rebasing.
  `footprintCheck` and `StepGrades.admits` become producers of the
  composition's evidence.

### Part 5. Statements that differ between Lean and the paper

- **Write-End.** The paper concludes $`x[i] \doteq v`$ and the extension of
  density. `Derivation.writeEnd` concludes the growth of the length, and the
  assertion language of the checker has no atom for an ordinary array's
  element. The atom is added, then the conclusion.
- **Push.** The paper concludes $`y = |x|`$. `Derivation.pushPost` concludes
  the growth of the length. The Lean statement is strengthened to the
  paper's.
- **Str-Read.** The paper's section "Future work" states it as a
  conjecture; `Derivation.stringRead` concludes a result of length one, and
  no producer emits it. It stays future work.
- **Sep, Init, Every.** The paper states each under conditions on what the
  atom reads: Every for a bound that is a variable and a body over scalars.
  Lean proves Sep and Init for linear atoms and Every for the represented
  scalar predicates. Each is proved for every atom form that meets the
  paper's conditions, by cases over the inductive definition of atoms.

### Part 6. The paper's section "What verifies"

With parts 1 to 4, an accepted function has a derivation in the rules of
sections 5 and 6. Section 7 keeps one job: to say which derivations the
pass searches for. Its definitions of obligations, of clauses and of the
candidates at a loop head stay. Its definition "Facts across a step" is
restated as rule Frame with the forms of part 3, and the list of what the
search does not try is the section "Future work".

## Order of work

Each step is one design reviewed before it is implemented, lands with the
suites passing, and is measured by the paper-reader test and by pretext's
count of verified functions.

1. **The baseline.** The paper-reader test on the current text of the
   paper.
2. **Part 1**, with the program above as a pipeline case.
3. **Part 2.**
4. **Part 3**, starting with its inventory: each of the six deciders
   assigned to one of the three cases.
5. **Part 4**: every edge and merge, then Loop, then composition.
6. **Part 5**, each statement with the rule that uses it.
7. **Part 6**, with the owner's approval of the paper's text.

## Costs and risks

- **Checking time.** Producing and checking a derivation for each fact at
  each edge repeats work a decider does once. The cost is measured at part
  1 on the pass's performance gate, before parts 3 and 4 are committed to.
- **Verdicts that move.** A fact a decider keeps and no rule form derives
  stops being kept until its form exists. Part 3's inventory lists such
  facts before any decider changes; none is dropped silently.
- **Proof effort.** Not sized here. Part 2 threads the state's
  well-formedness through the consumers of the query and changes three
  region forms. Parts 3 and 4 touch every decider on the acceptance path.
  The review of each step sizes it.

## Decisions for the owner

1. **A decider proved to construct a derivation.** The review recommends
   permitting it when its accepted result is indexed by the paper's
   judgment and acceptance consumes that certificate, and preferring
   producers shaped like the rules. A theorem that an independently
   organised algorithm implies a derivation does not meet the requirement.
   This draft follows that recommendation.
2. **Membership of a region.** This draft keeps `Region.mem` as it is, read
   from the heap, and adds the bound by roles as a theorem about
   well-formed states, as
   [parity interfaces, I1](parity-interfaces.md#state-and-role-interpretation)
   does for categories. The alternative defines membership by the world's
   roles, as the paper does literally, and changes every statement about
   effects. The review recommends the first.
3. **The effect of a native step.** Part 1 proposes the paper's regional
   effect for a native step in place of a wide frame with a precise
   postcondition. It changes the trusted contracts of the natives, which
   the owner reviews.
4. **The order**, and whether part 1 starts before the baseline is read.
