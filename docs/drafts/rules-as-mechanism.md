# The paper's definitions and rules as the mechanism of acceptance

A design draft. It proposes that the verifier accept a function by the
definitions and rules of the paper
[Tolerant frames](tolerant-frames-note/note.tex), so that the paper and the
Lean development have the same organisation. Lean sketches in this draft
are not compiled.

## The existing mechanism this extends

| Concern | Lean definitions | Owning document |
|---|---|---|
| Location kinds, fixed for a location's life | `Kind`, `Role`, `roleAt`, `HeapOk.kinds`, `RefsOk` (`Semantics/Worlds.lean`, `Semantics/Heaps.lean`, `Semantics/Kinds*.lean`) | [Location kinds](location-kinds.md) |
| Regions, changes, effects | `Footprints.Region`, `Region.mem`, `Selector`, `Change`, `Footprint`, `Post` | [Footprints](../FOOTPRINTS.md#changes-and-footprints), [parity interfaces, I1](parity-interfaces.md#i1-entry-relative-regions-and-exit-specifications) |
| Support of a fact, respect, the frame theorem | `Term.support`, `IndexFact.support?`, `respects`, `respect_sound`, `keeps_sound` (`Semantics/Survival.lean`, `Semantics/FootprintStability.lean`) | [Support and respect](../FOOTPRINTS.md#support-and-respect) |
| Disjointness of two regions | `SepQuery`, `SepKnowledge.apart₁`, `knowledgeQuery` | [Separation queries](../FOOTPRINTS.md#separation-queries) |
| The paper's rules as checked derivations | `RawDerivation`, `Derivation`, `checkDerivation`, `checkScoped`, `checkScoped_sound` (`Semantics/ParityDerivations.lean`) | [Parity interfaces](parity-interfaces.md) |
| What acceptance applies today, rule by rule | the deciders named in each row | [The rule table](parity-rule-table.md) |

This design adds no mechanism. It makes two existing ones the only ones:
location kinds decide where regions can overlap, and the checked
derivations decide which facts hold at each point.

## The requirement

Each definition and each rule of the paper is the definition and the rule
that acceptance applies. A decision procedure with its own soundness proof,
which establishes no derivation in the paper's rules, does not meet the
requirement, however it is proved.

The reason is the goal of the
[parity skill](../../.claude/skills/parity/SKILL.md#the-goal): a reader with
only the paper gives each example the verdict the verifier gives. A reader
applies the paper's rules. A mechanism organised differently agrees with
those rules on the examples it was tested on and can differ on the next one.

## Where the organisation differs

### Disjointness of regions

The paper gives each location one of five kinds, fixed for its life: field,
cell, element cell, store, identity. A region contains locations of known
kinds: $`\pi.f`$ a field or a cell, $`\pi.\mathsf{store}`$ a store,
$`\pi[\ast]`$ a store and its element cells, $`\mathsf{all\text{-}values}`$
every location of a value kind, $`\mathsf{all\text{-}stores}`$ every store.
Two regions whose kinds differ share no location.

Lean has the five kinds in its worlds (`Kind`, `roleAt`) and proves that
every transition keeps them. The regions of an effect do not use them. A
class region is read from the contents a location holds (`Region.mem` at
`cls`, `Selector.selects`), over three categories: value, array store, view
store. Whether two regions are disjoint is decided by a table of cases over
pairs of region constructors (`SepKnowledge.apart₁`), each case relying on
evidence supplied for it. A pair with no case is answered "not disjoint".

A program on which the two differ:

```ts
type Cursor = { at: number };
function grow(out: number[]): void { out.push(1); }
/** @requires safeInteger(cursor.at) && 0 <= cursor.at && cursor.at < flags.length */
export function read(flags: Uint8Array, cursor: Cursor, out: number[]): number {
  grow(out);
  return flags[cursor.at]!;
}
```

By the paper the read verifies: the fact
$`\mathit{cursor}.\mathit{at} < \mathsf{view}(\mathit{flags})`$ reads one
field location, and the effect of `grow` changes a store and its element
cells. The verifier refuses the read (observed on `single-pass` at
`de40292b`, 2026-11-16). The support of the term is the region
`path cursor [] at`, tolerating `init`; the effect's entry on stores allows
`grow`; the table has no case for a `path` region against a class region or
against another array's cells. The same fact is kept across `out.push(1)`
written directly, by a different mechanism.

### Which rule decides

The [rule table](parity-rule-table.md) compares the paper's 26 rules in
scope with what acceptance applies. Call and Conj are applied as the paper
states them. Every other rule is applied through a separate decider with
its own soundness theorem: Entry, Frame, Loop, Alloc, Seq-Eff, Fresh-Eff,
the seven axioms of the modality, Transfer, the arithmetic rules and the
writes. Frame+ is applied by nothing.

Lean contains the paper's rules as a derivation system with a checker
(`checkDerivation`, `checkScoped`). Acceptance does not use it.

The fact kept across a call shows the consequence. A term is kept if a
change read from the call's postconditions keeps it (`callChanges`,
`Term.keptBy`), or else if the call's frame respects the term's support.
The paper has one rule, Frame, with one definition of support and respect.

## The design

### Part 1. Regions have kinds

**Definition.** Each region form has a set of kinds, the kinds of the
locations it can contain in a well-formed state.

| Region | Kinds |
|---|---|
| `field x k`, `path x p k` at a key other than the store key | field, cell |
| `store x p`, and `path x p k` at the store key | store |
| `elems x`, `pathElems x p` | element cell |
| `own x`, `pathOwn x p` | field, cell, store, identity |
| `cell b` | cell |
| `cls c` | the kinds of the categories `c` selects: value gives field, cell, element cell, identity; array and view give store |
| `inCls r c` | the kinds of `r` that `c` selects |
| `all` | every kind |

**Disjointness.** Two regions are disjoint when their sets of kinds are
disjoint, or when the knowledge of the state separates them: the
separation facts and the allocation order that `SepKnowledge` holds today.

**Theorem to prove.**

```lean
theorem Region.kinds_sound {n : Nat} {W : WorldT n} {ρ : Env} {h : Heap}
    (hok : HeapOk n W h) (hρ : ∀ x, RefsOk W (ρ x)) {r : Region} {l : Nat}
    (hm : r.mem ρ h l = true) :
    ∃ κ ∈ r.kinds, kindAt W l = some κ
```

With it, disjoint sets of kinds give `SepQuery.Sound` at every well-formed
state. The premises are those the modality's states already satisfy
(`IndexedHeap.ok`, and valid references of the environment's values).

**What it replaces.** Each case of `apart₁` is either an instance of
disjoint kinds or a use of separation knowledge. The cases by class
evidence (`otherClass`, the `inCls` cases, `elemsValue`) are instances of
disjoint kinds, and `ClassEvidence` is no longer needed to answer them. The
cases by provenance, by distinct field pairs and by `storeApart` stay as
separation knowledge. The table of pairs becomes one rule with one
exception list.

**Effect.** The program above verifies: a field against a store and against
element cells is disjoint by kind. This part changes no rule of the paper
and adds no annotation.

### Part 2. One rule keeps a fact

**Definition.** A fact $`A`$ holds after a step with effect $`\Phi`$ when
it held before and $`\Phi`$ respects a support of $`A`$: the paper's
Theorem "frame" and rule Frame. A fact that a step establishes comes from
the step's postcondition by rule Entry. These are the only two ways a fact
holds after a step.

**Change.** The deciders that keep facts today stay as the search: they
find, for each fact, why it is kept. Each produces a derivation in the
paper's rules, and acceptance checks the derivation.

| Decider today | Derivation it produces |
|---|---|
| `frameKeeps`, `effectKept`, `IndexFact.keeps` | Frame: a support, the respect check, elimination of the modality |
| `callChanges`, `Term.keptBy`, `postKeeps`, `Composer.fact` | Entry and consequence from the exit's postconditions |
| `everyKept`, `writeAtoms`, the append and write rules | Every, Write-In, Write-End, Push |
| `keepsLengths`, `boundedLength_sound` | Write-In |
| `linearAtoms`, `smallOperand`, `bitAtoms`, `stringLengthPlusOne` | the arithmetic rules |
| `IndexWrites.regionAtoms`, `Checker.emptyArrays` | Alloc |

```lean
def checkEdgeFact (e : CheckedEdge) (A : AssertionRef) (raw : RawDerivation) :=
  checkScoped e.arena e.scope (EdgePremises e) (.at .after (pullback e A)) raw

theorem edgeFact_sound
    (h : checkEdgeFact e A raw = .ok d)
    (hr : EdgeRun e s s') (hΣ : KnowledgeHolds e.source s) :
    Sat e.arena (e.rename s'.env) e.mark s'.heap A
```

`CheckedEdge`, `EdgePremises`, `pullback` and `EdgeRun` are adapters
between the graph and the checker. They add no rule.

**The headline theorem.** `mode8Accepted_sound` keeps its statement. Its
proof reads the facts at each point from `edgeFact_sound`. A decider's own
soundness theorem is deleted when its derivations replace it, with the
tests that only it needed.

**Where a decider keeps a fact the rules do not derive.** Each such case is
one of two things. Either the paper lacks a rule that is sound, and the
rule is added to the paper with the owner's approval and to the derivation
system. Or the decider is wrong to keep the fact, which is a soundness
defect to fix. The handler edge is a known case of the reverse: `edgeStoreOf`
drops heap facts that rule Frame keeps at the exceptional exit.

### Part 3. Transfer, Loop and composition by their rules

The same change, for the three rules about a whole graph. The earlier
designer's answer sized each
([the note's rules at acceptance](rules-at-acceptance.md), designs A and C).

- **Transfer.** At every edge, merge and loop head, each target fact has a
  derivation from the source's facts, the exit's postcondition and the
  branch condition, under the edge's renaming. `exitStep`, `edgeTransfer`,
  `assertionExit` and the merge checks become producers of it.
- **Loop.** The facts at a loop head are an invariant $`I`$ and a frame
  $`\Box_\Phi R`$, checked by rule Loop with the rigidity of $`\Phi`$.
  `headExit` becomes the producer of the two parts.
- **Seq-Eff and Fresh-Eff.** A body's effect at its entry is the
  composition of its steps' effects by Seq-Eff on both exits, with
  rebasing. `footprintCheck` and `StepGrades.admits` become producers of the
  composition's evidence.

### Part 4. Statements weaker in Lean than in the paper

- **Write-End.** The paper concludes $`x[i] \doteq v`$ and the extension of
  density. `Derivation.writeEnd` concludes the growth of the length. The
  Lean statement is strengthened to the paper's.
- **Push.** The paper concludes $`y = |x|`$. `Derivation.pushPost` concludes
  the growth of the length. The Lean statement is strengthened to the
  paper's.
- **Sep, Init, Every.** The paper states them for an atom. Lean proves Sep
  and Init for linear atoms and Every for the represented scalar
  predicates. Each is proved for every atom form of the assertion language,
  by cases over its inductive definition.

### Part 5. The paper's section "What verifies"

With parts 1 to 3, a function verifies when the pass finds a derivation,
and the derivation is in the rules of sections 5 and 6. Section 7 then has
one job: to say which derivations the pass searches for. Its definitions of
obligations, of clauses and of the candidates at a loop head stay. Its
definition "Facts across a step" reduces to a reference to rule Frame and
Theorem "frame", plus the list of what the search does not try, which moves
to the section "Future work".

## Order of work

Each step is one design reviewed before it is implemented, lands with the
suites passing, and is measured by the paper-reader test of the parity
skill and by pretext's count of verified functions.

1. **Part 1.** It is self-contained, it is the smallest, and it closes the
   program above. The program becomes a pipeline case.
2. **Part 2, for calls.** Frame and Entry at a call edge, which is where
   two mechanisms keep one fact today.
3. **Part 2, for writes, allocation and arithmetic.**
4. **Part 3, Transfer**, then **Loop**, then **composition**.
5. **Part 4**, each statement with the rule that uses it.
6. **Part 5**, the paper's section 7, with the owner's approval of the text.

## Costs and risks

- **Checking time.** Producing and checking a derivation for each fact at
  each edge repeats work the deciders do once. The earlier designer's
  answer recommends this form first and, for the schemas that prove hot, a
  decider proved to construct the derivation. The gate is the performance
  baseline of the pass (`dev/perf-baseline.json`), measured at each step.
- **Verdicts that move.** A fact a decider keeps and no rule derives stops
  being kept until its rule is in the paper. Each step lists such facts
  before it lands; none is dropped silently.
- **Proof effort.** Part 1 is one theorem and the rewrite of one function.
  Parts 2 and 3 touch every decider on the acceptance path. This draft does
  not size them; the review of each step does.

## Decisions for the owner

1. **Whether a decider proved to construct a derivation counts.** In that
   form acceptance runs the decider, and a theorem states that its success
   gives a `Derivation` under exactly the edge's premises. It is faster to
   run. It is aligned with the paper only as far as that theorem is the
   decider's sole proof of soundness. This draft proposes checked
   derivations first and this form only for measured hot paths.
2. **The earlier interface decision that regions are read from the heap
   alone** ([parity interfaces, I1](parity-interfaces.md#state-and-role-interpretation)).
   Part 1 keeps `Region.mem` as it is and adds the kinds of a region as a
   derived notion, sound in well-formed states. The alternative is to
   define membership by roles in the world, as the paper does literally. It
   changes every statement about effects.
3. **The order**, and whether parts 2 and 3 start before the paper-reader
   test is rerun on the current text.
