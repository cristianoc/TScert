# Draft: every unit its own stage

# The promise: a function is analysed again only when its own inputs change

**In one sentence:** after you edit one function, checking it re-does only that function's work and the work of functions whose inputs your edit changed. Everything else is taken from the store, in milliseconds per entry.

Each item below is checked at the end by a measurement or a test. The result goes in the same table, as passed or failed, with the number.

## What you get

1. **Imported files are never re-analysed because you edited the file that imports them.** An imported module's search and check run again only when that module's own source changes. Today they run again after every edit: 43.5 s of a 75 s check, and 185 s of a 390 s one.
2. **Editing one function re-analyses only that function and what reads it.** The other functions of the same file replay, through every stage: proposal, search, check and explanation. A function whose proposal reads the edited one at its declared signature does not re-run, because that signature is unchanged.
3. **Edit-check time, measured on pretext with a warm store after a one-line edit:**
   - `removeItemsSkippableSegmentBreaks` (`analysis.ts`): **at most 5 s**, from 75 s today. Its own search and check are 0.36 s. The rest is reading and type-checking the edited file, which this change keeps whole-file.
   - `createLine` (`rich-inline.ts`): it pays nothing for `prepareRichInline`, the slow function next to it. Today it pays that function's 117 s proposal.
   - `prepareRichInline`: **at most 100 s**, from about 390 s. Its own search of about 80 s stays. That cost is inside the function itself and is a separate problem: this change does not fix it, and it is not hidden.
4. **One mode only.** The census, the cases, `verify-source.mts` and the per-function checks all go through the same per-unit stages. The old whole-file verifier modes are deleted.
5. **No slower cold runs.** A full census from an empty store takes no longer than today's, measured on the same machine.

## What does not change

6. **Same verdicts.** Every pipeline case keeps its expected outcome, and pretext at `2b11a4c` still verifies 210 of 210 functions.
7. **Same soundness.** The acceptance theorem `checkUnitJson_safe` keeps its meaning: an accepted unit is safe. The change adds no trust and no axiom. If a unit's slice ever lacks something its check needs, the check refuses; it never accepts.

## What keeps it from breaking again

8. **A control in `make test` fails if replay is lost.** It edits a file that imports another and asserts that the imported module's search and check replay. It edits one function of a file with several and asserts that the others replay. This is the check whose absence let the regression through on 2026-11-04.
9. **The docs describe what the code does.** `docs/STAGE-STORE.md` and the stale comment in `pipeline/verify-source.mts` are corrected. The stage design is written once, in its owning document.

## How it is checked at the end

- Items 1–3: timed runs, with each stage's replayed or executed outcome read from `invocations.jsonl`, before and after.
- Item 4: the deleted verifier modes no longer exist (`grep`), and every caller uses the per-unit stages.
- Item 5: a cold census, timed before and after.
- Items 6–8: `make test` and `make suite` pass. Pretext is checked file by file.
- Item 9: `node tests/docs.mts`, and a read of the two places.
- Astra, a second model, reviews the design before implementation. It reviews the implementation against this promise before the merge. Each item is reported as passed or failed, with its number. A failed item is reported as failed, never worded around.

# The design

A check of a source runs one stage per unit, keyed on that unit's own
inputs, and this is the only way the verifier and the producer are run. A
unit is a group of a file's functions, the file's initialization (with the
functions in its group), or the run of an imported module
([units of a check](../DESIGN.md#modules-and-code-units)). An edit of one
function then executes the stages of that function's unit and of the units
whose inputs the edit changes; every other unit's stages, and every
imported module's, replay.

**Evidence labels.** **Proved** names existing Lean theorems and their
scope. **Cited** names inspected code or a supplied measurement. **Conjectured**
marks the proposed design, its proof obligations and its estimates. Every
proposed lemma requires a Lean proof.

## The existing mechanism this extends

The [stage store](../STAGE-STORE.md) owns stages, their
[keys](../STAGE-STORE.md#keys), their
[inputs and replay](../STAGE-STORE.md#inputs-and-replay-eligibility) and
the [controls](../STAGE-STORE.md#controls) of replay; it is the mechanism
of the concern "repeated work of the pipeline" in
[general mechanisms](../DESIGN.md#general-mechanisms). [DESIGN](../DESIGN.md#modules-and-code-units)
owns the units of a check, their dependencies and the per-unit acceptance
theorem; [certified imports](../SOURCE-CONTRACTS.md#certified-imports) own
how one module's code reads another's at its certified footprint and
on-throw flag. This design adds no mechanism: it changes what one stage
invocation covers, from a file to a unit, so that the store's existing
content keys give per-unit replay.

The pipeline today (cited: `pipeline/verify-source.mts`,
`lean/Verification/Source/RequestCli.lean`,
`lean/Verification/Source/Claims/Json.lean`):

- The parse (an [observed stage](../STAGE-STORE.md#observed-stages)) gives
  the file's Fragment, each imported module's document nested in it.
- `--lower-control-flow` lowers the file's Fragment; each imported module
  is lowered and proposed on its own (`ModuleRuns`), keyed on the module's
  document and its eligible reads.
- The producer proposes the claims of the whole file in one process.
- One `verifier --produce-units` and one `--check-units` process run per
  file. Each builds the file's front once (`SourceClaimJson.filePlans`),
  searches or checks the selected groups, and searches or checks every
  imported module run (`f.p.modules`), whatever the selection.
- Each of these stages is keyed on the whole Fragment and the whole claims
  document; their file identity is the source snapshot's path, which the
  snapshot's bytes name.
- After a refusal, `producer --explain` runs over the whole file.

Each of the last three items makes an edit of one function execute every
stage of the file and every module run it imports. Measured
(cited, supplied measurement: 2026-11-08, commit `b132a48b`, cold store,
one core):

- `removeItemsSkippableSegmentBreaks` (pretext's `analysis.ts`), 75 s:
  imported module runs 43.5 s; the producer 21.2 s on the imports and
  5.6 s on the file; the front built twice, 0.5 s each; the unit's own
  search and check 0.36 s.
- `prepareRichInline`, about 390 s: module runs 185 s; the producer 117 s
  on the file; the front twice, 5.1 s each; the unit's own search 80 s.

Of the producer's 117 s, `fm_entails` (`ocaml-producer/linear_facts.ml`)
takes 110 s, 86% of its calls repeating an earlier call's arguments; a memo
of it (`/private/tmp/claude-501/perf-probe/probe-instrumentation.patch`)
gives 12 s with byte-identical output (cited, supplied measurement). That
memo is independent of staging and lands as its own change.

This design replaces, and its implementation deletes:

- the modes `--produce-units`, `--check-units` and `--units`, the unit
  selection by names, and the evidence document with a line per unit;
- the whole-file proposal and the whole-file `--explain`;
- `unitRound`'s fallback to a search and check of each unit after a
  whole-file limit;
- the paragraph of [STAGE-STORE](../STAGE-STORE.md#observed-stages) stating
  that a document with qualified reads is searched run by run, the `search
  of a run` row of its stage table, and the comment of
  `pipeline/verify-source.mts` naming `searchRuns`: the current code has no
  run stage, and this design's module-run unit is the stage they describe.

## Stages

One check of a source runs these stages (conjectured design). Each unit's
stages read only that unit's documents.

| Stage | Runs | Inputs beside its implementation |
| --- | --- | --- |
| parse | once per file | as today |
| module | once per imported module, nested in the parse | as today |
| units | once per file | the Fragment |
| lower | once per unit | the unit's slice |
| propose | once per file unit, in dependency order | the unit's slice and flow, its reads document |
| assemble | once per unit | the unit's proposal, its reads document, the claims of the modules its qualified reads use |
| plan | once per unit with qualified reads | the slice and its qualified reads |
| unit | once per unit | the slice, its assembled claims, search depth, subtype rounds |
| explain | once per refused file unit | the unit's slice, flow and reads document |
| TypeScript diagnostics | once per file | as today |

**Units.** `verifier --units <ast.json>` reads the Fragment alone (no
claims) and prints one line per unit:
`{"unit","members","depends","base","slice"}`. `members` are the unit's
code units; `depends` the units its code mentions; `base` the source offset
its slice's positions are relative to; `slice` the unit's
[slice](#slices). Groups are the strongly connected components of the
mention graph, the initialization among them where its mentions place it,
as `Front` computes them today from mentions alone. Each module run of a
certified import is a unit whose slice is the module's document, the one
`ModuleRuns` writes today, and whose `depends` are the module runs its own
qualified reads use. The stage executes on every edit of the file; its
outputs for an unchanged unit are byte-identical, so every later stage of
that unit replays.

**Propose.** The producer proposes one file unit at a time:
`producer <slice.json> <flow.json> <reads.json>`. A unit's reads document
lists, for each module value its code mentions, what the producer reads of
it beyond the slice's declared types: for a function of another unit, its
proposed footprint and on-throw flag; for a constant, its initializer's
claim; for a cell, its storage contract; for a certified import, its
module's certified footprint and on-throw flag. A same-file neighbour is
read exactly as a certified import is today: the `qualified.json` document
is this document's import entries. Units are proposed in the order of the
dependency graph, which is acyclic since mutual mentions put code units in
one group; a unit's reads document is assembled from its dependencies'
proposals. A caller's proposal therefore replays after an edit of a callee
that leaves the callee's footprint and on-throw flag unchanged.

The producer computes footprints at a least fixpoint and on-throw flags at
a greatest fixpoint over the file (cited: `Proposal.infer`). Solving each
strongly connected component of a monotone system in topological order,
the earlier components' solutions fixed, gives the whole system's least
(and, dually, greatest) fixpoint; that the producer's dependencies between
functions are contained in the mention graph is conjectured, and its
check is a criterion of the implementation: on every file of the census of
`tools/` and of pretext, the per-unit proposals assembled equal the
whole-file proposal at the commit before the whole-file mode is deleted.

**Assemble** builds the unit's claims document from its proposal and the
claims of the units and modules its reads document names, as the in-process
assembly stage builds a file's today.

**Unit.** `verifier --unit <slice.json> <claims.json> <evidence.json> <depth>`
builds the unit's front from its slice, searches the unit's evidence,
writes it to `<evidence.json>`, reads that file back, checks the unit at
it, and prints the unit's verdict, `{"accepted","depends","members","unit"}`
or `{"members","refusal","unit"}`. `verifier --check-unit <slice.json>
<claims.json> <evidence.json>` checks given evidence and prints the same
verdict; the controls that forge or mutate evidence use it. The evidence
document is one unit's bundle, or a module run's document evidence. Both
modes build one front, of the slice; no process builds a whole file's
front. The search and the check of a unit share one stage
([decision 1](#decisions)).

**Explain.** `producer --explain <slice.json> <flow.json> <reads.json>`
names the obligations of one refused unit.

**Module runs.** A module run's stages are keyed on the module's document,
its claims and the claims of the modules its reads use, none of which an
edit of the importer changes. A module imported by several files has one
entry per distinct document, which every importer replays. Module runs are
searched and checked before the importer's units are proposed: a refused
run withdraws every read of its module from the importer's reads
documents, as the withdrawal `module#*` does today. A read the plan
refuses (`--plan-imports`) is withdrawn from the reads document of the
unit that names it, and that unit alone is proposed again.

**Command lines.** One shape each; no compatibility mode:

```sh
verifier --units              <ast.json>
verifier --unit               <slice.json> <claims.json> <evidence.json> <depth>
verifier --check-unit         <slice.json> <claims.json> <evidence.json>
verifier --plan-imports       <slice.json> <plan.json>
verifier --lower-program      <slice.json> <claims.json>
verifier --lower-control-flow <slice.json>
producer           <slice.json> <flow.json> <reads.json>
producer --explain <slice.json> <flow.json> <reads.json>
```

`--subtype-rounds <n>` keeps its place before any mode. The `<file-key>`
argument goes: a slice's identity is its own [canonical
form](#position-independence).

## Slices

A unit's slice is a Fragment holding exactly what its extraction reads. The
fields of `Front` (cited: `lean/Verification/Source/Claims/Extraction.lean`)
state what that is; the slice carries, for a file unit:

- its members' code: their entries of `functions`, or the initialization
  statements for the initialization's group;
- the declarations its code, its members' annotations and its reads reach,
  closed under the definitions they name, with the implicit dependencies
  they select (`ArrayProto` among them);
- for each module value its code mentions: a function's declared signature
  and every overload of its name (`overloadSlot`), a constant's
  annotation, a cell's binding, a class's self binding and whether its
  class is generic (`classNames`), an imported value's declaration;
- the generic instances its code names (`generics`);
- the file-wide facts its code depends on: for each module cell it
  mentions, whether the module owns the cell's objects
  (`ownedModuleCells`), which reads every unit's code; the omitted
  mentions (`omittedMentions`) its code names.

The claims of the module values it reads are not in the slice: they are in
its reads document and its assembled claims, keyed with them. The
initialization's order check (`initOrder`) reads only the initialization's
statements, which are its group's code.

**Proof obligation (conjectured, Lean lemma `slicePlans`).** For every unit
`u` of a file and every claims document, the plans `u`'s slice extracts are
the plans `u` extracts from the whole file's front, up to the slice's
renaming of identities ([position independence](#position-independence))
and a renaming of the equation store's heads. Two facts make the per-unit
store compatible: each unit's extraction grows its own store from its own
slice's declarations and claims, so heads are numbered per unit; and the
evidence spells labels by head index, so a unit's evidence is valid for
exactly the store its slice builds, which is the store its check builds
again. `Front.extractAll` reads no unit's plan when it extracts another's
beyond the store it grows; a unit whose extraction fails leaves the store
as it was (cited: `Front.extractAll`). `slicePlans` is proved before the
whole-file modes are deleted ([decision 2](#decisions)).

### Position independence

A key covers only a unit's slice only if the slice holds nothing that an
edit of another unit's text changes. Two things in today's documents do:

- *Offsets.* Positions are byte offsets in the file, so an edit shifts
  every later function's spans. A slice's positions are relative to its
  `base`, the start of its first member's text; `--units` rebases them, and
  the orchestration adds `base` back to every span of a verdict or
  diagnostic before presenting it.
- *Identities.* A code unit is named `name@offset`, a module function's
  identity is its name and `namePos`, a local declaration's is its span,
  and the Fragment's `file` is the source snapshot's path, named by the
  whole source's bytes. In a slice, an identity outside the unit's own
  text is canonical: a function by its name and its index among the
  file's functions of that name, a local declaration by its name and its
  index among the file's declarations of that name, the initialization as
  `init`, a module run by its location. The slice's `file` is the empty
  identity, the same for every slice; `checkIdentity` compares the claims'
  `file` with it as today.

The renaming is injective on each slice and extraction compares identities
only for equality (conjectured, part of `slicePlans`). Two files with
byte-identical slices of a unit, claims and reads share their entries,
which is correct: a stage's result is a function of its key's inputs.

## Soundness

**The acceptance theorem stays exact.** `checkUnitJson_safe` (proved,
`lean/Verification/Source/Claims/Json.lean`) states: `filePlans ast claims
fileKey budget = .ok f` and `unitVerdict f budget unit evidence = .ok deps`
give `UnitSafe f budget unit evidence`. Its statement is unchanged. Its
instance is the slice: `ast` is the unit's slice, `claims` its assembled
claims, `fileKey` the empty identity, and the slice has exactly one unit.
The CLI condition for an accepted verdict of `--unit` and of
`--check-unit` is that premise over the files their arguments name, the
evidence read back from the file `--unit` wrote; both modes reach the
verdict through `unitVerdict` alone. The acceptance path keeps its one
exhaustive conversion to `CertifiedPlan` (`FilePlans.certified`).
`UnitSafe` concludes safety under `EnvOk` of the unit's inputs, the module
values it reads at the signatures its claims state, whatever the other
units' verdicts; that conclusion is per unit today and stays per unit.

**What a unit assumes of its neighbours.** A unit's theorem assumes the
signatures of the module values it reads. Today one claims document gives
every unit the same signature of a neighbour. Per unit, the signature a
unit assumes is the one its reads document gave it, and the signature a
neighbour's verdict certifies is the one its own claims state. A verdict's
`depends` therefore names each dependency with the digest of the signature
entry it assumed, and the neighbour's verdict states the digest of the
signature entry it certified; the deep-status assembly
(`dev/census.mts`, node code without a proof, a row of the
[trust surface](../DESIGN.md#trust-surface)) counts a dependency as
accepted only where the two digests are equal. A composition theorem over
a module's units remains [open work](../../WORK.md#module-composition).

**Replay.** A replayed `--unit` result is the verifier's judgment of
exactly the slice, claims and evidence its key binds, under the binding
and validation the trust surface's replayed-check row states. That row's
"check mode reads the three files its arguments name" becomes "`--unit`
reads the two files its arguments name and the evidence file it writes;
`--check-unit` reads the three".

**What does not change.** The [source boundaries](../DESIGN.md#trust-surface)
(annotation lowering, native contracts, inferred call effects) are read
from the same declarations and claims; a slice holds every declaration its
unit's code, annotations and reads reach, so no contract is cut. A slice
that lacks a declaration its unit needs fails extraction, a refusal, never
an acceptance.

## The census

The census schedules unit stages, not files: a pool of one worker per core
takes any stage whose inputs exist, the proposals of a file in dependency
order, the other stages of different units concurrently. A file's units
no longer wait on one process.

The memory reasons for writing and checking evidence a unit at a time
(cited, commit `7cfce13f`: the whole-file search held every unit's
certificates and the memo of all units, and the check decoded the whole
evidence before its first unit; on `fragment-statements.mts`, the search of
its largest unit alone peaked at 2.0 GB, the front alone at 0.36 GB) hold
by construction: each process holds one unit's slice, front, memo and
evidence, and ends with it. Each process stage keeps its memory limit
(`TSCERT_STAGE_MEMORY`, 8 GiB) and its time limit; a unit over either is
that unit's outcome, and no fallback runs.

## The control

A control of the store itself (a fresh store, executing every time, beside
the replay control of `pipeline/test.mts`) checks one source that imports a
certified function from another module and defines three functions `f`,
`g` and `h`, `g` calling `f`, together with its two edits:

1. Cold: every stage executes.
2. Edit `f`'s body, keeping its signature, footprint and on-throw flag: the
   module run's propose and unit stages replay; `g`'s and `h`'s lower,
   propose, assemble and unit stages replay; `f`'s lower, propose, assemble
   and unit stages execute; the parse and `--units` execute.
3. Edit `f`'s body so that its footprint changes: `f`'s stages and `g`'s
   propose, assemble and unit stages execute; `h`'s and the module run's
   replay.

The control asserts each stage's `execution` in `invocations.jsonl` by its
stage and unit, and that each run's outcome equals a cold run's of the same
source. It is the control whose absence let a whole-file key go unnoticed:
the replay control asserts that an unchanged source replays and a changed
source executes, and no control asserted what an edit leaves to replay.

## Decisions

Each decision follows from the promise and the project's principles.

1. **A unit's search and check run in one stage.** `--unit` searches, then
   checks the evidence it wrote, building the front of its slice once.
   Separate search and check stages would bind the same executable, slice
   and claims, so they would always execute together and build the front
   twice for no replay. Consequence: the front costs once per unit, which
   item 5 needs; `--check-unit` remains for the controls that check forged
   or mutated evidence.
2. **The slicer's correspondence is proved.** Item 7 allows no new trust,
   so the slicer does not join the unproved extraction boundary: the Lean
   lemma `slicePlans` states that a unit's plans from its slice equal its
   plans from the whole file's front. `fileFront` stays a Lean definition,
   the reference the lemma names, reached by no command line. Consequence:
   a proof over the renaming of identities and of the store's heads lands
   before the whole-file modes are deleted; until it is proved, the
   per-unit modes do not replace them.
3. **A module run stays one unit, checked as its document.** Its theorem
   (`DocumentSafe`) is unchanged, which item 7 asks. Consequence: an
   imported module is checked whole once per distinct document, every
   importer replaying it (item 1), including functions of it no importer
   reads.
4. **What a unit assumes of a neighbour is tied to what the neighbour
   certifies,** by the signature digests of [soundness](#soundness).
   Consequence: deep status counts a dependency only where the two match;
   shallow verdicts are unaffected.
5. **The stage design is written once.** At the implementation, this
   draft's stages, keys and slices move into
   [STAGE-STORE](../STAGE-STORE.md) and its units into
   [DESIGN](../DESIGN.md#modules-and-code-units), the stale paragraph and
   comment are corrected, and the draft is deleted (item 9).

## How the design meets each item

1. *Imported files.* A module run's propose and `--unit` stages are keyed
   on the module's document, its claims and the claims of the modules its
   reads use. An edit of the importer re-executes the parse, whose nested
   module lowerings read the project's files; a lowering that gives the
   same document leaves the run's keys unchanged, so its search and check
   replay. The document depends on the importer through one input, the
   run's host-family tag selection
   ([shared work](../STAGE-STORE.md#shared-work)); an edit changing the
   tags the importer uses changes the document of a module that reads them.
2. *One function and what reads it.* A unit's stages read its slice, its
   reads document and its claims. An edit of `f` changes `f`'s slice only
   ([position independence](#position-independence)); a unit reading `f`
   reads `f`'s declared signature from its own slice and `f`'s footprint
   and on-throw flag from its reads document, so it replays unless the
   edit changed that footprint or flag. Explanation is per unit and
   replays with the rest.
3. *Edit-check time.* After a one-line edit, the stages that execute are
   the parse, `--units`, and the edited unit's lower, propose, assemble and
   `--unit`. For `removeItemsSkippableSegmentBreaks` that is the parse plus
   its own 0.36 s and one front of its slice: target 5 s. An edit of
   `createLine` executes no stage of `prepareRichInline`'s unit, whose
   proposal it reads from the store. For `prepareRichInline`: its search
   (about 80 s), one front of its slice (at most 5.1 s, the whole file's)
   and its own proposal (at most the file's 12 s with the `fm_entails`
   memo): target 100 s.
4. *One mode.* `verify-source.mts` runs the per-unit stages; the cases,
   the census and the census's function selection call it. `--produce-units`,
   `--check-units`, the whole-file `--units` and the whole-file proposal
   are deleted.
5. *Cold runs.* Each module run executes once per distinct document
   instead of once per importer, and the producer's `fm_entails` memo
   removes 105 s of `rich-inline.ts`'s proposal alone; each unit builds
   one front of its slice, where today each file builds two whole fronts.
   The risk is a large declaration closure lowered once per unit that
   reaches it; the cold census of `tools/`, timed before and after on one
   machine, decides it.
6. *Same verdicts.* `slicePlans` gives each unit the plans it has today;
   the per-unit proposals equal the whole-file proposal on every census
   file (the criterion under [stages](#stages)); every case keeps its
   expected outcome, and pretext at `2b11a4c` verifies 210 of 210
   functions.
7. *Same soundness.* `checkUnitJson_safe` is unchanged and instantiated at
   the slice; `slicePlans` is proved; no axiom is added. A slice missing a
   declaration its unit needs fails extraction, which is a refusal.
8. *The control.* [The control](#the-control) runs in `make test`.
9. *The docs.* Decision 5.
