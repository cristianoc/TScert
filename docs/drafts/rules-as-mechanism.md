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
statements are open: rule Entry has no theorem stating it as displayed
(the acceptance path states it for the linear consequences the composition
derives, `HeapKnowledge.entry_sound`, and for the post's other forms over
the same premises, `Composer.fact_holds`), and the Transfer theorem's connection to a run is proved for effects over
classes only.

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
elements and cells have the same shape (`keptIndices`,
`everyGrown`, `writeKept`, `keepsLengths`, `writeAtoms`, `cellKept`,
`IndexFact.keptBy`, `keptWith`).

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
| 1. One support relation, one respect check, one frame theorem | the acceptance path and the paper-shaped layer use the same three | the duplicate relation, the duplicate respect loops, the separate frame proofs; the cell-fact loop and proof of `cellRespects` and `frameCells`, restated through the one respect check and the one frame theorem |
| 2. Disjointness as the paper states it | one check decides that two regions are disjoint, by the kinds of their locations or by a separation at hand ($`\mathrel{\#}`$, $`\mathsf{apart}`$, $`\mathsf{fresh}`$); the separations of allocation and provenance feed it; each region form selects the locations the paper's region does | `classQuery`, `spineSite`, `sitesApart`, `SepKnowledge.apart₁`; the spine slot in `fields`, the form `cell b`, the unallocated locations of `all` |
| 3. Regions well-formed by the kind of their path | the tool and Lean refuse a region at a path of another kind | the class tags (`inCls`) on supports |
| 4. Native steps carry the paper's effect and exact postcondition | the contracts of Push, Write-In, Write-End, View-Write, the field write and Alloc each state the regional effect of their rule | the class-wide frames of those contracts |
| 5. A function's effect is composed from its steps | Seq-Eff, Fresh-Eff and rebasing run along the graph, on both exits, through the function's interface; a wrapper of `push` has the effect the paper derives for it | the closed bound of the steps' frames as the only inferred effect |
| 6. A fact across a call is kept by Frame or by Entry | no other route keeps one | `ownKept`'s keeping by the separation of field locations (`HeapSeparation`); the second Entry of `push` |
| 7. Writes and quantified facts by the paper's rules | each of `cellKept`, `fieldEvery`, `everyGrown`, `appendKept`, `everyWritten`, `writtenPrefix`, `writeKept`, `writeAtoms`, `keepsLengths` and the arithmetic deciders is an application of Write-In, Write-Kept, Push-Every, View-Every, Guard, Inst, Prefix, Empty or an arithmetic rule | each of those deciders as an acceptor of its own, and the keeping relation they share (`Changes`, `IndexFact.keptBy`, `keptWith`, `keptIndices`) |
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

### What each step changes

The table gives, for each step above, the kind of change it is, the
verdicts it is expected to change, and what acceptance decides by the
paper's rules once the step is done.

| Step | Kind of change | Verdicts expected to change | After it, decided by the paper's rules |
|---|---|---|---|
| 1 | a restructuring of code that runs | none | nothing more: the same deciders, over shared definitions |
| 2 | a change of a check that runs | gains only: more regions are found disjoint; none lost | whether two regions are disjoint |
| 3 | a refusal added; the class tags deleted | an annotation with a region at a path of another kind becomes refused; nothing else | which regions are admitted |
| 4 | a change of contracts that run | gains: a narrower effect keeps more facts. A loss is possible where another part relied on a wide effect; it is a defect of that part | the effect of each native step |
| 5 | a change of inferred effects | gains: the callers of a wrapper keep more facts. A loss is possible as in step 4 | the effect of each function |
| 6 | a route deleted | none | which facts are kept across a call |
| 7 | deciders replaced | none intended, family by family | the facts across a write; quantified facts |
| 8 | the pass's transfer replaced | ordinary edges none; handlers and framed loops gain | the facts along control flow |
| 9 | a language replaced | none intended; a risk where the two languages give a fact different meanings | how every fact is stated |
| 10 | the premise of the acceptance theorem changed | none | the verdict |
| 11 | | | everything, and nothing else |

A step is followed when its "Done when" and "Deleted" conditions hold in
the sources and the verdict changes observed are those this table expects.
A verdict change the table does not expect is investigated before the next
step; a loss is a defect in every step, the refusals step 3 intends
excepted.

### Which step owns a mechanism

Two rules settle which step deletes a mechanism, and so what an audit of
a step counts:

- **A lemma nothing uses is deleted.** A Lean statement that no
  acceptance theorem and no status tag of the paper uses is deleted, not
  restated through the paper's rules.
- **Keeping by Frame is step 1's.** A fact kept because what it depends on
  is not changed is kept by the paper's Frame, whichever decider keeps it:
  a call's, a write's or a step's. Step 1 owns every such keeping. A fact
  kept because of what a write puts in its locations is kept by the
  paper's rules of updates (Write-In, Write-Kept, Push-Every, View-Every),
  which step 7 owns.

### The list of each step

What a step still has to delete or restate is a list, built by reading
the sources for every instance of what the step's row names, and kept in
this plan beside the step. An item leaves the list in the commit that
removes it from the code; an item found later joins it. Progress is
reported as the number of items left. A round of work that leaves an item
open brings it to the owner with its reason, and the discussion decides
the way forward.

### Step 1's list

Built on 2026-11-17 by reading every keeping decision that uses the
change relation (`Changes`, `IndexFact.keptBy`, `keptWith`, `everyKept`,
`keptIndices`, `IntoContents`) up to the acceptance path, and every keeping
lemma that only the axiom check reads. Each frame item is the part of a
decider that keeps a fact because what it depends on is unchanged; its
other part, an update rule, stays with step 7.

Keeping by Frame inside a decider, to go through `respects` and
`frame_step`:

1. a field write's index facts (`writeOutput`, its `keptIndicesWith`);
2. a field write's quantified facts over another array (`fieldEvery`, its
   kept spine, bound and free terms);
3. a field write's cell facts apart from the written field (`cellKept`, its
   `apart` branch, with `writeKeeps`);
4. an element write's kept facts below the length (`lengthOutput`,
   `keepsLengths`);
5. an element write's kept facts at any index (`growOutput`);
6. an element write's cell facts (`writtenCells`), which the field's
   untouched location keeps;
7. the terms an element write at the length keeps or grows
   (`atLengthAtoms`, `keptOf`, `grownOf`);
8. a call changing its receiver's own fields (`ownKept`);
9. a push's quantified facts over another array (`everyGrown`,
   `appendKept`, their kept bound and free terms);
10. the terms a push keeps or grows (`appendEntry`, `linearAppendKept`);
11. a typed-array write's quantified facts, their kept bound and terms
    (`everyWritten`, `writtenPrefix`, `writeKept`);
12. `apart` and quantified facts across an element write (`writeAtoms`,
    `termApart_kept`), proved over the write's heap;
13. `apart(x,y)` across a push (`withGrown`, `grownRegions`), kept against
    an effect rebuilt from push's postconditions instead of the call's own,
    which waits on push's regional effect (step 4).

Keeping lemmas no acceptance theorem and no status tag of the paper uses,
to delete:

14. `rootCells_box`, `Admissible.elem_kept`, `box_idem_on`,
    `stableAt_invariant`, `field_write_keeps_bound`, `grow_write_judgment`,
    `invocation_box`, `rebaseOk_stable`, `keepsCall_frame`,
    `named_le_box`, `slotless_not_framed`, `preserving_step_frame`,
    `stableAt_of_stableFirst`, `writing_frame`, `keep_across_call`,
    `ArgumentPathTracking.read_stable`, `stableField_path`.

Proofs of the paper's rules that no status tag cites, for the paper's tags
to cite:

15. `CommandSummary.frame_at_call`, `frame_at_call_below`,
    `signature_holds`, `signature_holds_below` (rule Call), and
    `LoopEvidence.frame_at_head`, `frame_at_exit` (rule Loop).

The counter-models `unrestricted_not_respects`, `allocation_not_respects`
and `elementWrite_not_respects` are controls of an excluded behaviour and
stay.

### The lists of steps 2 to 10

Built on 2026-11-17 at `16988ca6` by reading every instance of each
step's row up to the acceptance path. "Pretext" names, by reading its
sources at the commit CI pins, the functions that use the construct; it is
not measured. An item marked **owner** waits for a decision of the owner,
for the reason given. The branch `parity/fresh-facts` (paused) resolves
the items marked *branch*.

#### Step 2's list (10)

1. The paper layer's own disjointness evidence (`DisjointEvidence`,
   `DisjointUnder`, `ClassWitness`, `RespectEvidence.query`) answered by
   the one check (`SepEvidence.query`) over evidence read from the
   assertion.
2. Freshness reaching the one check as `fresh(r)` against regions below
   the mark; the typed-field stamps deleted. *branch*. Pretext: the
   `for…of` loops of `measurement.ts`, `line-breaks.ts`,
   `gecko-line-breaks.ts`.
3. The evidence produced: freshness at allocation, Alloc's `apart`, and
   below-the-mark evidence at rigid paths (entry values and fresh call
   results: *branch*). Pretext: array literals followed by `push` in
   `rich-inline.ts`, `analysis.ts`, `layout.ts`, `line-breaks.ts`,
   `gecko-line-breaks.ts`, `measurement.ts`.
4. **Owner.** The separation of field locations (`SepFact.locs`, fed by
   `HeapSeparation`): of two objects allocated in one invocation, and of
   two module cells, which the paper has no rule for; an array literal's
   part becomes Alloc's `apart`. Pretext: `unpackClasses`
   (`line-breaks.ts`), and the functions of item 3.
5. The class evidence `SepEvidence.cl`, which repeats the kinds, deleted.
6. `boundQuery` asked directly, replaced by the one check.
7. `π # π'` answering the paper's region `π.spine`; `spineSite` deleted.
8. One region form for a spine, `π.spine`, in place of `field x []` and
   `path x p []`, in supports and effects.
9. The class regions the paper lacks (`Selector` with `arrays` alone,
   `Region.all`) restated as `val`, `st`, `vw`.
10. **Owner.** Guarded separations (`factSeps .guarded`), which the paper's
    list of evidence lacks: the paper states that a region at a path from
    a value with no object is empty, or this waits for step 9.

#### Step 3's list (11)

1. to 6. The class tags on the supports of a path's reads (`pathReads`),
   a spine read (`spineRead`), a quantified fact (`everyCells`), `apart`
   (`apartSupport`, `regionOf_supported`), an element (`elementSupport`)
   and the growth of `apart` (`apartGrowSupport`). Pretext: every fact at
   a field path.
7. **Owner.** Computed supports carry no kinds (`Term.support`,
   `IndexFact.support?`): either supports read the slots' types, which may
   lose facts at union-typed paths, or the paper's status "the regions of
   supports are not kinded" stays.
8. A decoded contract's regions checked by the kind of their path
   (`EffectCodec.regionOf`).
9. **Owner.** A stated spine region admits arrays only (`regionKindOk`)
   where the paper also admits typed arrays; and the front end passes a
   stated region to Lean unchecked (`statementOf`).
10. The constructor `Region.inCls` and its cases, after step 4 removes the
    tags from the native contracts.
11. `spineOnly` and `spineOnly_mem`, unused, deleted.

#### Step 4's list (12)

1. The field write's effect `{x.f: any}` (`fieldWriteFrame`) in place of
   the class-wide grade. Pretext: field writes in every module.
2. **Owner.** The initializing write `x.f ??= v` has no rule in the paper;
   Lean grants it `{value: init}` class-wide. Pretext: `getEngineProfile`,
   `lazyRegExp`, `getWordSegmenter`, `unpackClasses`, `getScriptFacts`,
   `getSpaceWidth`, `prepareRichInline`, `addWidthTrim`.
3. The element write's effect `{x.spine: s, x.cells: any}`
   (`elemWriteFrame`) in place of the class-wide grade.
4. **Owner.** A write at a present literal index keeps the spine
   (`litWriteChange`); the paper's displayed Write-In effect is `grow`, its
   prose says `keep`.
5. Write-In's postcondition `|π| = old(|π|)` for every `π`, stated by the
   step.
6. Push's frame stated a second time as a postcondition, deleted.
7. View-Write's frame stated a second time as a postcondition, deleted.
8. View-Write's exceptional exit `⊤` (the `%ByteSet%` contract, `fill`,
   `copyWithin`, `set`) where the paper's step never throws.
9. Alloc's effect stated as the empty effect.
10. Alloc's postcondition `fresh ∧ |x| = k ∧ ⋀ apart` as one contract
    (now in `literalArrayAtoms`, `regionAtoms`, `freshApart`,
    `emptyArrays`, the walk's fresh names, the regional route and the
    front).
11. **Owner.** The order of steps 4, 5 and 8: acceptance's node judgment
    carries closed effects only, and regional effects reach it through
    Transfer for regions at paths, which the paper marks as a conjecture;
    or through the regional composition that exists.
12. `field_write_judgment` and `element_write_judgment`, unused, deleted.

#### Step 5's list (11)

1. The front's walk builds closed summaries (`Synthesis`); it composes
   regional summaries per exit.
2. `ExitProposals.lean`, read only by the axiom check, deleted; the
   paper-shaped composition (`ThenEvidence`, `CommandSummary.seq_sound`,
   `handle_sound`, `LoopEvidence`) runs.
3. The pass's proposals by closed routes (`PassProposals`) replaced by
   one regional route, with a widening.
4. The interface formats of effects (`Effect.ofClosed`, `ofStated`,
   `RunBound`, `CodeConditions`, the tools' `StatedFrame` and
   `ClosedFootprint`) regional.
5. A stated region reaches callers as `⊤` (`statedEffect`).
6. **Owner.** `Modifies` admits regions only at `any`: whether written
   effects gain the paper's changes.
7. Acceptance's Seq-Eff over closed bounds (`footprintCheck`,
   `StepGrades`, `boundOk`, `selectedGrades`) replaced by the regional
   check sound by `Post.compose_rebases` and `Post.fresh_eff`.
8. The regional route's second Seq-Eff (`ArgumentRegionGraph`,
   `Post.compose_at`) merged with item 7.
9. Fresh-Eff implemented three times, one left (`Post.fresh_eff`).
10. Rebasing evidence from the paper's read equalities, not only `@stable`
    one-field paths. Pretext: `readScriptRuns`, `getUnspacedGraphemes`,
    `removeItemsSkippableSegmentBreaks`.
11. A pipeline case: a wrapper of `push`, and a callee stating `out[*]`,
    each keeping `cursor.at < flags.length` in its caller.

Pretext has no annotations: every callee effect it relies on is inferred,
so this step is on its path.

#### Step 6's list (4)

1. A call keeps its read links by Frame (`frameLinks`). *branch*.
2. Freshness and entry-value evidence at calls. *branch*.
3. `ownKept`, `ownOutput`, `ownCall` and `Checker.keepingOwnCalls`
   deleted. *branch*.
4. The second Entry of `push` (`appendEntry`, `linearAppendKept`) becomes
   the general one (`callEntry`) once step 4 gives push its exact length
   postcondition.

#### Step 7's list (30)

1. The keeping relation (`Changes`, `IndexFact.keptBy`, `keptWith`,
   `everyKept`, `keptIndices`) deleted once nothing uses it.
2. A step's change stated as a `Changes` value replaced by the paper's
   postconditions of Write-In, Push, View-Write and Field-Write.
3. A field write's written value (`writeOutput`) by Field-Write.
4. `cellKept`'s `R ≤ V` branch by Write-Kept.
5. `fieldEvery`'s branch for an aliased element cell deleted (Frame keeps
   the fact).
6. `keepsLengths`, `lengthOutput` by Write-In and Entry. Pretext: the
   guarded writes of `prepare.ts`, `measurement.ts`, `analysis.ts`,
   `han-kerning.ts`, `rich-inline.ts`.
7. `atLengthAtoms`, `writeCarried` by Write-End, Arithmetic and Entry.
8. `writtenCells`'s value branch deleted (Frame keeps the fact).
9. `appendEntry`'s length by Push and Entry. Pretext: every `push`.
10. `everyGrown`'s every-push branch and `appendKept` by Push-Every.
11. **Owner.** `everyGrown` on the receiver: Push's `Q_<` and the
    introduction of a quantified fact, which the paper lacks.
12. `exactWriteOf` as the premise of View-Write and View-Every.
13. `everyWritten`, `writeKept` by View-Every; **owner**: its branch at
    or past the bound has no body premise, which View-Every lacks.
    Pretext: the typed-array writes.
14. `writtenPrefix` by View-Every and Prefix.
15. `valueAtoms`, `copiedAtoms`, `pastCopies` by the binding `y ≐ a`.
16. **Owner.** `litSlot`: a fact from a declared literal type.
17. The range of an array's length by Arr-Length.
18. A string's length by Str-Length.
19. `concatAtoms` by Concat.
20. Sums and products by Add, Sub and Scale.
21. `stringLengthPlusOne`, `pastSafeAtoms` by the length successor.
22. `smallOperand`, `bitAtoms` by Shr and Mask.
23. **Owner.** `x & m` with `m` declared in `[0, 2^31)` gives an index for
    any `x`; the paper's Mask requires `0 ≤ x < 2^31`. Pretext (read):
    every guarded write, in `analysis.ts`, `han-kerning.ts`,
    `measurement.ts`, `prepare.ts`, `rich-inline.ts`.
24. `releasePast`, `releaseEither` by ∨-elimination; **owner**: the clash
    of `pastSafe` with a safe integer is not among the paper's
    contradictions.
25. `unguardIndices` by Guard and the atoms' contradictions.
26. `guardFollows`, `guardBodyFollows` by the rules of ∨ and Guard.
27. `instantiateEvery`, `elementInstances` by Inst, `z[i].f` bodies
    included; **owner**: bodies with an offset `z[i+d]` have no form in
    the paper.
28. `everyPrefix` by Prefix; **owner**: it also drops and renames body
    clauses under conditions.
29. `linearFollowsIn`'s quantified branch by Empty.
30. `entailsKnown`, `linearEntailed` by Arithmetic, with a certificate.

#### Step 8's list (19)

1. `exitStep`, `visitExits`, `pushExit`: one checked transfer per exit,
   the paper's Check against the target's knowledge.
2. The normal branch's observations and promotions as the edge's
   condition and postcondition.
3. `edgeTransfer`, `mapNames`, `Store.drop`: renaming as substitution,
   forgetting as `∃`-elimination.
4. `assertionExit` deleted; Check against the target.
5. `withStated` only proposes the target's knowledge.
6. `headExit`: Check of the supplied head knowledge on every incoming
   edge. Pretext: every loop.
7. `mergeState` only proposes; each incoming edge's Check carries it.
   Pretext: every conditional.
8. The handler edge keeps by Frame what the node's exceptional effect
   respects, in place of dropping every heap fact. Pretext:
   `getExtraSpacings`.
9. The regional facts along edges, handlers and merges by the same Check.
10. **Owner.** Loop with a frame needs the modality in the knowledge,
    which step 9 brings: a head's frame carried in step 8, or Loop after
    step 9.
11. The edge soundness proofs restated as one theorem through `transfer`.
12. The merge's holding lemmas deleted.
13. The handler soundness premises restated.
14. Transfer's connection to a run proved for regions at paths.
15. Check built as a typed `Derivation`.
16. **Owner.** Types along edges (`exitTypes`, `refinedContext`,
    `mixedContext`, vacuity): the paper's Check has no typing judgment.
17. **Owner.** Implications along edges and merges (a test implies a
    type).
18. **Owner.** Facts read off declared types (`withTypedCells`,
    `withTypedLinks`): the paper derives no atom from a type.
19. Unused loop and example lemmas deleted (`loop_back_edge`,
    `TolerantFramesModelLoop`, `TolerantFramesExamples`).

#### Step 9's list (29)

1. to 4. The three languages, the knowledge (`Knowledge.Holds`), the
   pass's named atoms (`SinglePass.Atom`, `StateHolds`) and the paper
   layer's (`Parity.Sat`), become one, in the paper's grammar.
5. **Owner.** The separation of field locations (as step 2's item 4).
6. **Owner.** Every element of a kind (`ElemAtom`): the paper's
   quantified bodies are linear only.
7. **Owner.** Entry terms in a body's knowledge (`Term.old`): the paper
   puts `old` only in postconditions.
8. **Owner.** Type implications (`Implication`): the paper keeps types
   outside its assertions.
9. Truthiness conditions on facts restated with the paper's value sets
   and `∨`.
10. to 14. `every`, the element, disjunction, `#` and `apart`: the paper
    layer's meanings restated to the paper's.
15. Three languages of value sets become the paper's.
16. Field contents and links restated; **owner**: the paper's optional
    read ignores prototypes.
17. The special forms `index`, `length`, `bound`, `int`, `pastSafe`
    restated as linear, `defined` and `π ≐ 2^53` atoms.
18. Four forms of freshness become `fresh(r)`.
19. Density.
20. One satisfaction domain, the paper's `(ρ, m, s)`.
21. One postcondition language, with `∨`, `⇒` and `∀`.
22. `linear_holdsAt_iff` and its duplicate deleted.
23. `ParityArithmeticBridges.lean`, imported by no module, deleted.
24. The knowledge's facts embedded in postconditions and read back.
25. Postconditions recognised by their syntax (`statesExtension`,
    `statesAppend`, `exactWriteOf`).
26. and 27. The two checkers of support evidence become one.
28. The acceptance theorem's conclusion restated in the one language.
29. The wire and the front end in one new shape.

#### Step 10's list (12)

1. The annotation: knowledge at each label in the one language.
2. A structure of derivations per node and edge with rule Fun's four
   obligations, and one theorem from it to the acceptance conclusion.
3. Each step's precondition by a derivation.
4. A Check derivation per edge (with step 8's item 14).
5. Fun's entry: the precondition in the one language.
6. Fun's returns: a derivation of `Q` at each return.
7. Fun's throws: an exceptional postcondition, `true` by default.
8. Fun's effect: one form.
9. The derivation checkers no acceptance code calls (`checkDerivation`,
   `checkScoped`, `RawDerivation`) replaced by typed derivations; the raw
   checkers deleted.
10. **Owner.** The derivation system is narrower than Definition
    "Derivations": every form acceptance uses becomes derivable, or a
    program is lost.
11. **Owner.** The premise of the acceptance theorem stays the exact
    command-line condition (CLAUDE.md); a sound annotation is then an
    intermediate theorem it goes through.
12. The duplicates left after steps 1 to 9.

### What an audit checks

A step judged done is audited from the sources by a reviewer who has not
worked on it, before it is recorded as done. For each fact acceptance
relies on where the step works, the audit establishes:

1. **The rule.** The decision that keeps or establishes the fact is one
   application of a named rule of the paper: Frame, Entry, an atom axiom
   or the rule of a step.
2. **The paper's premises.** That application checks the rule's premises
   as the paper states them: a support the paper gives, respect by its
   sufficient condition, disjointness from the evidence the paper lists,
   the effect the paper states for the step.
3. **The shared statements.** The check runs the one Lean definition of
   each notion (`Supports`, `respects`, the step's effect), and its
   soundness goes through the one Lean theorem of the rule, such as
   `frame_step`.
4. **No other route.** No other decision on the acceptance path concludes
   a fact of that kind. The step's "Deleted" column names the routes
   known; the audit searches for others.
5. **Lean states the paper.** Each Lean definition and rule used reads,
   side by side, as the paper's numbered definition or rule.

Steps 1 to 6 establish items 3 and 4 for what they replace; steps 2, 3,
4 and 7 establish item 2 for disjointness, regions, effects and writes;
step 10 establishes item 1 for every fact; item 5 is checked at every
step for the definitions it touches. The audit reports, item by item, what
holds, with the place in the sources.

An item that cannot be established is a result to discuss with the owner,
with its reason: the paper's rule may lose a program that verifies, the
Lean may need a premise the paper does not state, or the paper may be
silent. The discussion decides the way forward: the paper gains the rule,
the code changes, or the case stays as it is, recorded where it belongs.

Steps 1 to 6 change the deciders that run and what they share. The
paper's rules as a derivation system (`Parity.Derivation`, its checker and
its soundness theorem) are applied by acceptance from step 7 on: the
deciders steps 7 and 8 name run until those steps replace them.

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
