# The paper's definitions and rules as the mechanism of acceptance

A design. The verifier accepts a function by the definitions and rules of
the paper [Tolerant frames](tolerant-frames-note/note.tex), with one
implementation of each, and the deciders that are organised differently
are replaced and deleted one family at a time. Lean sketches here are not
compiled.

The design was reviewed against the sources by gpt-6-astra on 2026-11-16,
three times, with nothing built for the reviews. The measurements are from
pipeline runs of that day and say what was run.

## The existing mechanism this extends

| Concern | Lean definitions | Owning document |
|---|---|---|
| Location kinds and roles, fixed for a location's life | `Kind`, `Role`, `roleAt`, `HeapOk`, `RootsOk`, `RefsOk` (`Semantics/Worlds.lean`, `Semantics/Heaps.lean`, `Semantics/Kinds*.lean`) | [Location kinds](location-kinds.md) |
| Regions, changes, effects | `Footprints.Region`, `Region.mem`, `Selector`, `Change`, `Footprint`, `Post`, `Supported` | [Footprints](../FOOTPRINTS.md#changes-and-footprints), [parity interfaces, I1](parity-interfaces.md#i1-entry-relative-regions-and-exit-specifications) |
| Support and respect on the acceptance path | `HeapKnowledge.IndexFact`, `Term.support`, `IndexFact.support?`, `Footprints.respects`, `knowledgeQuery`, `frame_step`, used by `frameKeeps` | [Support and respect](../FOOTPRINTS.md#support-and-respect), [Separation queries](../FOOTPRINTS.md#separation-queries) |
| The paper's assertions and rules as checked derivations | Parity assertions, `SupportEvidence`, `RespectEvidence`, `RawDerivation`, `Derivation`, `Derivation.sound`, `checkScoped` (`Semantics/Parity*.lean`) | [Parity interfaces](parity-interfaces.md) |
| Effects of commands composed on both exits, loops | `CommandSummary`, `ThenEvidence`, `LoopEvidence` (`Semantics/Command*.lean`) | [Effects of commands](effects-of-commands.md) |
| The judgment at an edge | Checked transfer, section "Transfer along edges" | [the paper](tolerant-frames-note/note.tex) |
| What acceptance applies, rule by rule | the deciders named in each row | [The rule table](parity-rule-table.md) |

The design adds no mechanism. It makes one of each.

## The requirement

The goal is the
[parity skill](../../.claude/skills/parity/SKILL.md#the-goal)'s. As an
invariant of acceptance:

> Every fact and every effect that acceptance consumes has evidence in the
> system organised as the paper is. No fact reaches acceptance through a
> preservation check that establishes no such evidence.

The invariant gives "accepted implies derivable by the paper's rules". The
pass searches for a derivation and may not find one that exists; what it
searches for is a separate statement, measured by the
[paper-reader test](../../.claude/skills/parity/SKILL.md#the-paper-reader-test).

## The state it starts from

**The paper's rules are proved.** An audit of every marked statement of
the paper against the Lean sources found the rules proved in the layer
`Semantics/Parity*.lean` and `Semantics/Command*.lean`: (Sep) for linear
facts over variables and the length of the array, (Every) for the
represented scalar bodies, (Rigid) as a rule of substitution, the
composition of effects on both exits with the handler, Conj. Two
statements are open: rule Entry has no theorem stating it as displayed, and
the Transfer theorem's connection to a run is proved for effects over
classes only. `Derivation.sound` and `checkScoped_sound` are not in the
axiom check.

**No acceptance decision runs that layer.** Acceptance applies Call and
Conj as the paper states them, and every other rule through deciders with
their own soundness theorems ([rule table](parity-rule-table.md)).

**One rule is implemented twice.** "A fact is kept when the effect
respects its support" exists as:

- **A**, in the paper-shaped layer: `SupportEvidence`, `RespectEvidence`,
  `RawDerivation.tolerantFrame`, concluding the modal statement
  $`K \wedge A \vdash \Box_\Phi A`$;
- **B**, on the acceptance path: `Term.support`, `IndexFact.produceSupport`
  with its evidence checked by `FactSupport.check`, `IndexFact.support?` its
  footprint, `respects` with `knowledgeQuery`, concluding that the fact
  holds after the transition at hand.

They share regions, changes, effects, `Supported` and the support relation
`SupportDomain.Supports` (`Semantics/Support.lean`), read over arbitrary
heaps by B and over indexed states by A, and the one respect check
`respects`, sound by `respect_sound`: B asks it under `knowledgeQuery`, A
under the query its disjointness certificates answer. Both conclude through
the one frame theorem `frame_step`: B at the transition at hand, A through
its modal form `frame_box`, whose condition holds of every single action of
the effect from a state of $`K`$ (`ConditionOnActions`). Neither language
contains the other:

| | A | B |
|---|---|---|
| Modality as an assertion, Frame+, existentials, rigid substitution | yes | no |
| Supports of facts at field paths, by the locations read | B's, for a linear fact (`SupportEvidence.paths`); else one coarse support | precise |
| Quantified facts over typed arrays, with offsets | no | yes |
| Unrestricted disjunction, guards that read the heap | no | yes |
| A quantified fact requires each element present | yes | no |
| Spine separation asserts both arrays exist | yes | only if both values have spines |

**Several decisions try two routes in turn.** `effectKept` is `postKeeps`
or `frameKeeps`; `callKeeps` and `callGrown` each tried a change read from
the call and then respect of the support; the deciders for writes,
elements and cells have the same shape (`keptIndices`, `Atom.keptBy`,
`everyGrown`, `writeKept`, `keepsLengths`, `writeAtoms`, `cellKept`,
`IndexFact.keptBy`, `keptWith`, `callKeepsHeap`).

## Measurements

All on `single-pass` at `93857551`, 2026-11-16.

**A fact at a field path.** With `0 <= cursor.at < flags.length` known, the
read `flags[cursor.at]` after one call:

| The call | Verdict |
|---|---|
| a function type stating `values: "keep"; spines: "keep"`, or `"init"` on either | verified |
| a function type stating `values: "keep"; spines: "grow"` | refused |
| a callee stating `values: "keep"; spines: "keep"; "out[*]": "any"` | refused |
| a callee whose effect is inferred from `out.push(1)` | refused |
| `out.push(1)` written directly | verified |

By the paper each of these verifies, since no effect here contains the
field's location.

**The support states the class of each read.** `pathReads` marks each
location a path's read passes with the class of what it holds
(`Semantics/Survival.lean`, 52 lines added and 38 removed, four theorems
re-proved). The second row then verifies, and all 3417 pipeline cases keep
their expected outcome. The third and fourth rows stay refused: a field and
an element cell are both of the value class, and the inferred effect of the
wrapper is the closed bound of push's frame, which includes "any value".

**Routes switched off**, over 3414 pipeline cases and five files of
pretext:

| Switched off | Cases changed | Pretext units lost |
|---|---|---|
| a term kept by a change read from the call (`callChanges` in `callKeeps`, `callGrown`) | 0 | 0 |
| a fact kept by reading the call's postconditions (`postKeeps` in `effectKept`) | 11 | 6 |

The 11 cases and 6 units come from two operations, `push` and the element
write of a typed array. In each, the fact has a support and the frame does
not respect it; none lacks a support. For `push`, the facts are equalities
of lengths across pushes to one or two arrays, and bounds across a push to
a fresh array. For the typed-array write, which pair of support and effect
fails is not established: the support of a view's length at a variable is
empty in the sources.

## The end state

One assertion language, one relation "this evidence supports this
assertion", one respect check with one kind of disjointness evidence, one
frame theorem. The derivation checker and acceptance both consume them.
Each search that keeps or establishes a fact produces a judgment of a named
rule of the paper, and acceptance's soundness proof reads the fact from
that judgment.

Two properties of the shared definitions:

- **Support is a relation with checkable evidence**, since a fact can have
  several supports and none greatest (the paper's example is apartness).
  B's support computation is one producer of such evidence.
- **Evidence about the transition at hand is not evidence for the
  modality.** B omits a support entry for a field it knows stable across
  this call. That justifies rule Entry's consequence at this call. It
  justifies $`\Box_\Phi`$ only with a proof over every transition of
  $`\Phi`$.

Where acceptance builds a derivation itself, it builds the typed
`Derivation` value directly; `RawDerivation` and `checkScoped` check
certificates that come from outside Lean.

Two alternatives were sized and not taken. Routing B's deciders through
A as it is loses B's supports at paths and its quantified facts, which
pretext uses. Restating B alone as the paper's rules leaves out the
modality, Frame+, rigid substitution and rule Loop, which the paper states.

## The order of work

A family of facts is ported whole before its acceptance route is switched,
and the old route is deleted in the same change. No step leaves "try the
new check, else the old decider".

| Step | Replaced and deleted | The paper's rule, and what it needs first | Verdicts |
|---|---|---|---|
| 1 | The untagged supports of path reads | Frame; the class of each read | measured: one refusal becomes a verification, 3417 cases unchanged |
| 2 | The route by `callChanges` in `callKeeps` and `callGrown` | Frame alone for a term across a call | measured: none change on 3414 cases and five pretext files |
| 3 | The duplicate respect check and the two separate frame theorems | one support relation, one respect check; B's supports as evidence in it | intended none |
| 4 | Disjointness answered case by case (`classQuery`, `spineSite`, `SepKnowledge.apart₁`) | Alloc and (Sep): one disjointness evidence, with the bound of a region by role classes, and the separations of allocation and provenance carried through renaming | the third row above verifies; intended none lost |
| 5 | A function's effect as the closed bound of its steps' frames only | Seq-Eff and Fresh-Eff: a native step has the paper's regional effect and its exact postcondition, and effects compose through a function's interface on both exits | the fourth row above verifies; wrappers of `push` gain |
| 6 | `postKeeps`, then the alternative in `effectKept` | Frame for an unchanged fact; Entry with the exact postcondition of Push for a changed length; (View) | the 11 cases and 6 units are re-established before the deletion |
| 7 | `cellKept`, `fieldEvery`, `everyGrown`, `appendKept`, `everyWritten`, `writtenPrefix`, `writeKept`, `writeAtoms`, and the arithmetic deciders, as acceptors of their own | Write-In, Write-End, View-Write, (Every), the arithmetic rules; a rule form for each update the paper's rules justify | intended none, family by family |
| 8 | `exitStep`, `edgeTransfer`, `assertionExit`, the merge checks; the handler edge's dropping of every heap fact | checked transfer at every edge with the edge's own effect, postcondition, branch condition and renaming; Frame at the exceptional exit | ordinary edges intended none; handlers gain |
| 9 | Checking a loop head's facts as ordinary targets, as the only form | Loop with its frame: Frame+, rigidity, the invariant and the frame kept apart | existing loops intended none; framed loops gain |
| 10 | What remains of the duplicate definitions and unused checkers | the acceptance theorem depends on the rules' judgments throughout | none |

Steps 1 and 2 are implemented on one pull request. Step 5 is before step 6
because a postcondition of `push` does not pass through a wrapper's
interface: only an effect does.

### Step 4: a region is bounded by role classes

A *role class* is one of field, cell, element cell, array spine, view
spine, identity: the roles of `Worlds.lean` without their parameters. It
projects to the paper's five kinds and to the three categories of
`Selector`; neither of those refines the other.

#### The bound of a region

A region has a *bound* (`Region.bound`,
[RegionBounds.lean](../../lean/Verification/Semantics/RegionBounds.lean)):
a set of role classes (`RoleClass`, `RoleSet`,
[Worlds.lean](../../lean/Verification/Semantics/Worlds.lean)) that contains
the role class of every allocated location in it, in a well-formed state.

| Region | Bound | From |
|---|---|---|
| `field x k`, `path x p k` at a key other than the spine key | field, cell | the slot's role (`SlotRole`) |
| `field x k`, `path x p k` at the spine key | array spine | the slot's role |
| `fields x`, `pathFields x p` | field, cell, array spine | each slot's role |
| `cells x`, `pathCells x p` | element cell | a spine lists element cells (`HeapOk.entries_cells`) |
| `spine x p` | array spine, view spine | the spine slot's role, or the descriptor's view spine (`RefOk`) |
| `cls c` | the role classes of the categories `c` selects | a location's contents category is its role's (`Shaped.category`) |
| `cell b` | field, cell, element cell, identity | its members are those of `cls values` |
| `inCls r c` | the bound of `r`, restricted to the role classes of `c` | both of the above |
| `all` | every role class | |

`Region.bound_sound` proves: under `HeapOk n W h` and `RootsOk W ρ`, every
`l < h.length` with `r.mem ρ h l = true` has a role `role` with
`roleAt W l = some role` and `r.bound.contains role.cls = true`; a path
read from a valid root reads a value with valid references
(`readPath_refs`). Its corollary `Region.apart_of_bound` proves that when
`(r.bound.inter s.bound).isEmpty = true`, no allocated location is in both
`r` and `s`. The axiom check covers both.

A field's bound holds both field and cell: which of the two a slot is
depends on the object's roles, which region-kind evidence carries.

Two regions are disjoint when their bounds are disjoint, or when the
state's knowledge separates them. `SepQuery.Sound` and the paper layer's
`DisjointUnder` are stated over allocated locations, the ones `Post` and
`Supported` constrain.

The acceptance path proves a query sound with both premises of
`Region.bound_sound` at hand: `knowledgeQuery_sound` takes `HeapOk n W h`
and `RootsOk W ρ`, and so do the call rules that ask it
(`PromiseCalls.effectKept_holds`, `callKept_sound`, `callGrown_sound`,
`callContext_holds`, `ensuresComposed_holds`, `withEnsures_holds`). The
roots come from the graph state's references (`StateRefs`) through the
judgments a node's check is read by: `Checker.sound`, `ControlFlow.ExpressionOk`,
`GraphCode.NodeWithin`, the argument-region obligations and the tolerant
frames' node judgments (`NodesChecked`, `NodesKeep`, `StepParts`) each take
`RootsOk W ρ` beside the term's `RefsOk`. A path that ends at
the spine key reads a spine: step 1 leaves the last read of a guard and of
a spine separation unmarked for that reason, and the bound above marks it.

Three region forms differ from the paper's and are brought to it here:
`fields` includes the object's spine slot where the paper's
$`\pi.\mathsf{fields}`$ is its value fields; `cell b` selects every value
location; `all` selects unallocated locations.

### Step 6: what `push` and a typed-array write need

For an equality of lengths across `texts.push(v)` where `texts` is another
array: the effect of `push` is
$`\{\mathit{texts}.\mathsf{spine} : \mathsf{grow}\}`$, the fact's support
keeps the other array's spine, and respect needs the two spines disjoint,
which Alloc states for a fresh array and step 4 makes available to the
check.

For a fact about the receiver's own length: a lower bound is kept by
growth. An equation is changed by the push. Rule Entry combines the old
equation with the exact postcondition
$`|x| = \mathsf{old}(|x|) + 1`$ and arithmetic gives the new one. Equal
lengths across pushes to two arrays hold again after the second push, by
the same reasoning through the state in between.

For the typed-array write, the pair of support and effect that fails in
each of the affected cases is established first; the step that removes
`postKeeps` does not start before that.

## What changes in the paper

Each item is put to the owner as a change of the paper's text, with the
programs it affects, when its step is reached.

- **Facts the acceptance path has and the paper's language lacks:**
  quantified facts over typed arrays; a quantified fact that does not
  require each element present; disjunction in general; guards that read
  the heap; spine separation of two values that need not both be arrays.
  Each either enters the paper's assertion language or is translated into
  it by a proved translation.
- **Rules Lean states and the paper does not:** introduction and
  elimination of a quantified fact; the atoms for definedness, safe
  integers and the value past the safe range; support relative to a
  context; the condition for moving a rigid path under a modality; a later
  region covered by an earlier entry at `any` in rebasing; the summaries of
  a choice and of a loop's departures.
- **Rule forms for updates** that the paper's rules justify and the
  derivation system cannot yet state: a write that keeps a field's contents
  when it may alias; a quantified fact across a field write, an append and
  an exact write of a typed array.

## Costs and risks

- **A translation can strengthen a fact.** The two meanings of a
  quantified fact and of spine separation differ. Each translation is a
  theorem with the premises it needs, and one definition remains.
- **Native precision can be lost at a wrapper.** Step 5 is before step 6
  for this reason. The exceptional exit of a native keeps its own effect.
- **Loops.** The ordinary facts at a loop head stay checked as they are
  until step 9 adds the frame beside them.
- **Checking time.** Building a derivation where a decider answered
  directly costs time. It is measured on the pass's performance gate at
  step 3, before the later steps depend on the answer.
- **Pretext.** No step lands with a pretext function lost. A step that
  would lose one waits for the rule that keeps it.
- **Size.** Steps 1 and 2 are one file each. Step 3 is about ten core
  modules. Steps 4 to 10 together touch twenty to forty files and every
  decider on the acceptance path. These are estimates from the structure
  of the sources.
