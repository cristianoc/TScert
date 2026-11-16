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

**Several decisions try two routes in turn.** `callKeeps` and `callGrown` each tried a change read from
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

The steps lead to the goal, which is the last of them. Each step replaces
a mechanism by a definition or a rule of the paper and deletes what it
replaces in the same change: no step leaves "try the new check, else the
old decider". No step lands with a pretext function or a pipeline case
lost.

| Step | Done when | Deleted |
|---|---|---|
| 1. One support relation, one respect check, one frame theorem | the acceptance path and the paper-shaped layer use the same three | the duplicate relation, the duplicate respect loops, the separate frame proofs |
| 2. Disjointness as the paper states it | one check decides that two regions are disjoint, by the kinds of their locations or by a separation at hand ($`\mathrel{\#}`$, $`\mathsf{apart}`$, $`\mathsf{fresh}`$); the separations of allocation and provenance feed it; each region form selects the locations the paper's region does | `classQuery`, `spineSite`, `sitesApart`, `SepKnowledge.apart₁`; the spine slot in `fields`, the form `cell b`, the unallocated locations of `all` |
| 3. Regions well-formed by the kind of their path | the tool and Lean refuse a region at a path of another kind | the class tags (`inCls`) on supports |
| 4. Native steps carry the paper's effect and exact postcondition | the contracts of Push, Write-In, Write-End, View-Write, the field write and Alloc each state the regional effect of their rule | the class-wide frames of those contracts |
| 5. A function's effect is composed from its steps | Seq-Eff, Fresh-Eff and rebasing run along the graph, on both exits, through the function's interface; a wrapper of `push` has the effect the paper derives for it | the closed bound of the steps' frames as the only inferred effect |
| 6. A fact across a call is kept by Frame or by Entry | no other route keeps one | `postKeeps` and the alternative in `effectKept` |
| 7. Writes and quantified facts by the paper's rules | each of `cellKept`, `fieldEvery`, `everyGrown`, `appendKept`, `everyWritten`, `writtenPrefix`, `writeKept`, `writeAtoms`, `keepsLengths` and the arithmetic deciders is an application of Write-In, Write-Kept, Push-Every, View-Every, Guard, Inst, Prefix, Empty or an arithmetic rule | each of those deciders as an acceptor of its own |
| 8. Edges, merges, handlers and loops by the paper's transfer | checked transfer on every edge with the edge's effect, postcondition, condition and renaming; a merge keeps what every incoming edge establishes; Try; Loop with a rigid effect | `exitStep`, `edgeTransfer`, `assertionExit`, the merge checks, the handler edge's dropping of every heap fact |
| 9. One assertion language | acceptance and the paper-shaped layer state facts in the paper's grammar, with one satisfaction relation | the second language and the translations between the two |
| 10. A function verifies as the paper defines it | the premise of the acceptance theorem is a sound annotation of the graph that meets the four obligations of rule Fun, by derivations of the paper's Definition "Derivations" | what remains of the duplicate definitions and unused checkers |
| 11. The goal | the implementation applies the paper's rules and no others, and is organised as the paper is | |

Step 11 is checked three ways: each decision of the acceptance path names
the rule of the paper it applies, and no decider with a soundness proof of
its own remains outside those rules; pretext keeps its count and every
pipeline case its outcome; a reader with the paper alone gives the
verifier's verdict on the examples.

A function that verifies only through something the paper does not state
is put to the owner with its consequences: the paper gains the rule, or
the function stops verifying.

Step 5 is before step 6 because a postcondition of `push` does not pass
through a wrapper's interface: only an effect does.

### Step 2: a region is bounded by role classes

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
| `fields x`, `pathFields x p` | field, cell | each slot's role under a key other than the spine key: the field locations of the object |
| `cells x`, `pathCells x p` | element cell | a spine lists element cells (`HeapOk.entries_cells`) |
| `spine x p` | array spine, view spine | the spine slot's role, or the descriptor's view spine (`RefOk`) |
| `cls c` | the role classes of the categories `c` selects | a location's contents category is its role's (`Shaped.category`) |
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

Disjointness is one check of separation evidence (`SepEvidence.query`,
`SeparationEvidence.lean`, [separation queries](../FOOTPRINTS.md#separation-queries)):
$`r \mathrel{\#} s`$ when the bounds of the two regions under the evidence
hold no class in common (a field's bound narrowed by its class evidence),
by freshness against the stamps, or by a separation fact whose sites are the
two regions': a spine separation, an apartness of two arrays, two different
field locations. It is sound at a well-formed state where the evidence holds
(`SepEvidence.query_sound`). `knowledgeQuery` is the check of the evidence
a state's knowledge holds, its index facts' separations and its
allocations' (`HeapSeparation`) among them; the stability check of the
fact kinds (`stable`, `FootprintStability.lean`) is the check of the
evidence its caller gives; the first fields a call growing its receiver's
spine keeps (`growFirst`) are those the check of the call's entry
separates from the receiver's spine field. Every pair a class answers, the part `inCls r c`
of a region against `cls c'` with `c` and `c'` disjoint, the bounds answer
too (`boundQuery_inCls_cls`), and the check answers every pair any of its
parts answers (`SepEvidence.query_of_bound`, `query_inCls_left`,
`query_field_class`, `query_fresh`, `query_locs`, `query_spines`,
`query_pathCells_field`, `query_pathCells_cls`). The bounds also separate a
field or a cell from an array or view spine and from an element cell: the
pipeline case `field-index-kept-by-role` keeps `cursor.at < flags.length`
across a call whose stated effect changes the spine of another array,
`out`.

The paper layer's class certificate (`DisjointEvidence.classes`) decides
by the bounds of the two class regions its witnesses give
(`Region.cls_apart_of_bound`). A class region's bound needs only the heap's
well-formedness, which an indexed state carries, so the paper layer's
judgments range over every valuation. A certificate by the bound of a
region that reads a path needs valuations with valid roots
(`RootsOk`): the judgments, the existential witnesses of $`\exists`$ and the
states a box reaches would each carry them.

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
the spine key reads a spine: the last read of a guard and of a spine
separation carries no class tag for that reason, and the bound above marks
it.

A spine region a frame states (`ArgumentSpineRegion`) is well-formed by
the kind of its path: the entry check of a stated frame
(`ArgumentPathTracking.checkEntryFields`) refuses one whose path's declared
type has a member other than an array, `null` or `undefined`
(`regionKindOk`).

Every region form selects locations as the paper's region does: `fields`
the field locations of an object, its spine slot excluded, and `all` the
allocated locations; a frame that changes module cells states the class
region of values.

### Steps 4 to 6: what `push` and a typed-array write need

For an equality of lengths across `texts.push(v)` where `texts` is another
array: the effect of `push` is
$`\{\mathit{texts}.\mathsf{spine} : \mathsf{grow}\}`$, the normal frame its
contract states, which its growth and append postconditions imply
(`Effect.callPost_receiverGrowFrame`); the fact's support
keeps the other array's spine, and respect needs the two spines disjoint,
which Alloc states for a fresh array and step 2 makes available to the
check.

For a fact about the receiver's own length: a lower bound is kept by
growth. An equation is changed by the push. Rule Entry combines the old
equation with the exact postcondition
$`|x| = \mathsf{old}(|x|) + 1`$ and arithmetic gives the new one. Equal
lengths across pushes to two arrays hold again after the second push, by
the same reasoning through the state in between.

An element write $`x[i] = v`$ has the effect of Write-In and Write-End,
$`\{x.\mathsf{spine} : \mathsf{grow},\ x.\mathsf{cells} : \mathsf{any}\}`$,
the spine at $`\mathsf{keep}`$ at a position its contract requires
(`ExpressionEffects.elemWriteFrame`), and the exact postcondition
$`|x| = \max(\mathsf{old}(|x|), i+1)`$ (`ElemWritten`), both proved from
the reduction (`elemWriteStep_sound`); the closed grade the closed check
reads is the frame's weakening (`elemWriteFrame_closed`). The step's local
effect carries the frame; the postcondition reaches the knowledge through
`keepsLengths` below the length (`ElemWritten.lengths`) and
`atLengthAtoms` at it.

A typed-array write has the frame of rule View-Write, the view spines at
$`\mathsf{grow}`$, and the support of an array's length is its array
spine, so a fact about an array's length is kept across the write by
Frame.

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
  until step 8 adds the frame beside them.
- **Checking time.** Building a derivation where a decider answered
  directly costs time. It is measured on the pass's performance gate at
  step 1, before the later steps depend on the answer.
- **Pretext.** No step lands with a pretext function lost. A step that
  would lose one waits for the rule that keeps it.
- **Size.** Step 1 is about ten core modules. Steps 2 to 10 together touch
  twenty to forty files and every decider on the acceptance path. These are estimates from the structure
  of the sources.
