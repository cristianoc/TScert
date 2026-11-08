# Draft: every unit its own stage

# The promise: a function is analysed again only when its own inputs change

**In one sentence:** after you edit one function, checking it re-does only that function's work and the work of functions whose inputs your edit changed. Everything else is taken from the store, in milliseconds per entry.

Each item below is checked at the end by a measurement or a test. The result goes in the same table, as passed or failed, with the number.

## What you get

1. **Imported files are never re-analysed because you edited the file that imports them.** An imported module's search and check run again only when that module's own inputs change. Those inputs are its source, and the run's choice of host-library models for the libraries that module itself uses. An edit to the importer that changes that choice really changes the module's lowered text, so re-running it is correct. Changes to models the module doesn't use don't re-run it. Changing which of a module's functions you import is also a change of its inputs: the module is checked once for the new set of functions, and a set it was already checked for replays. Today they run again after every edit: 43.5 s of a 75 s check, and 185 s of a 390 s one.
2. **Editing one function re-analyses only that function and what reads it.** The other functions of the same file replay through proposal, search and explanation. A function whose proposal reads the edited one at its declared signature does not re-run, because that signature is unchanged.

   One exception, kept for soundness: the final trusted check of a function still reads the whole file. The proof that an accepted function is safe is about the whole file, and the Lean code that reads a file cannot be proved to give the same result on a slice. That check runs only for the functions being checked. It costs one read of the whole file, measured at 0.5 s for `analysis.ts` and 5 s for `rich-inline.ts`, plus the function's own check, measured at 0.05–0.1 s.
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
unit is a group of a file's code units that reach each other by the names
their code mentions, the initialization among them where its mentions
place it ([units of a check](../DESIGN.md#modules-and-code-units)). An
imported module is checked through the same unit stages, over its own
document, restricted as today. An edit of one function executes the stages of that function's
unit and of the units whose inputs the edit changes; every other unit's
stages, and every imported module's, replay.

**Evidence labels.** **Proved** names existing Lean theorems and their
scope. **Cited** names inspected code or a supplied measurement.
**Conjectured** marks the proposed design, its proof obligations and its
estimates. The design adds no lemma: the acceptance stays the existing
theorems over the whole document.

## The existing mechanism this extends

The [stage store](../STAGE-STORE.md) owns stages, their
[keys](../STAGE-STORE.md#keys), their
[inputs and replay](../STAGE-STORE.md#inputs-and-replay-eligibility) and
the [controls](../STAGE-STORE.md#controls) of replay; it is the mechanism
of the concern "repeated work of the pipeline" in
[general mechanisms](../DESIGN.md#general-mechanisms).
[DESIGN](../DESIGN.md#modules-and-code-units) owns the units of a check,
their dependencies and the per-unit acceptance theorem;
[certified imports](../SOURCE-CONTRACTS.md#certified-imports) own how one
module's code reads another's at its certified footprint and on-throw flag,
and the comparison of two readings of a declaration (`sameReading`).

Every stage below is an ordinary invocation of the store's one mechanism
(`invokeProcess`, `pipeline/stages.mts`); no second cache is added. The
design adds three computations, each in keyed code (the verifier or the
producer) and each with its proof obligation: the slice of a unit
([slices](#slices)), its canonical coordinates
([canonical form](#canonical-form)) and the interface of a dependency
([interfaces](#interfaces)). The interface is one representation, the
canonical reading `sameReading` compares, used for same-file neighbours and
certified imports alike.

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
  imported module run (`f.p.modules`), whatever the selection. A module run
  is its document restricted to the read closure of the functions read
  qualified of it, its initialization kept (`planImports`).
- Each of these stages is keyed on the whole Fragment and the whole claims
  document; their file identity is the source snapshot's path, which the
  snapshot's bytes name, and the Fragment carries the whole source's
  `sourceSha256`.
- After a refusal, `producer --explain` runs over the whole file.

Each of the last three items makes an edit of one function execute every
stage of the file and every module run it imports. Measured (cited,
supplied measurement: 2026-11-08, commit `b132a48b`, cold store, one core):

- `removeItemsSkippableSegmentBreaks` (pretext's `analysis.ts`), 75 s:
  imported module runs 43.5 s; the producer 21.2 s on the imports and
  5.6 s on the file; the front built twice, 0.5 s each; the unit's own
  search and check 0.36 s.
- `prepareRichInline` (`rich-inline.ts`), about 390 s: module runs 185 s;
  the producer 117 s on the file; the front twice, 5.1 s each; the unit's
  own search 80 s.

Of the producer's 117 s, `fm_entails` (`ocaml-producer/linear_facts.ml`)
takes 110 s, 86% of its calls repeating an earlier call's arguments; a memo
of it (`/private/tmp/claude-501/perf-probe/probe-instrumentation.patch`)
gives 12 s with byte-identical output (cited, supplied measurement). The
memo lands on main first, as its own change, and every measurement below
compares against a baseline that carries it.

This design replaces, and its implementation deletes:

- the whole-file `--produce-units`, whose search moves to the slices;
- the module runs inside `--produce-units` and `--check-units`, which move
  to their own stages ([module runs](#module-runs));
- the whole-file proposal and the whole-file `--explain`;
- `unitRound`'s fallback to a search and check of each unit after a
  whole-file limit;
- the paragraph of [STAGE-STORE](../STAGE-STORE.md#observed-stages) stating
  that a document with qualified reads is searched run by run, the `search
  of a run` row of its stage table, and the comment of
  `pipeline/verify-source.mts` naming `searchRuns`: the current code has no
  run stage.

## Stages

One check of a source runs these stages. Each unit's untrusted stages
(proposal, search, explanation) read only that unit's documents. The
trusted check reads the whole document and its whole claims document: the
acceptance theorem is about the whole document, and the Lean code that
reads a document (its decoding, its store and its lowering are partial
definitions) admits no proof that a slice gives the same plans.

| Stage | Runs | Inputs beside its implementation |
| --- | --- | --- |
| parse | once per file | as today |
| module | once per imported module, nested in the parse | as today |
| units | once per document: the file; each imported module's whole document, for its proposal; each restricted document `--plan-imports` prints, for its certification | the document |
| facts | once per proposed document (the file, each imported module's whole document) | the document |
| lower | once per unit | the unit's slice |
| propose | once per unit, in dependency order | the unit's slice and flow, its reads and facts documents |
| assemble | once per unit | the unit's proposal, its reads document |
| plan | once per document | the document and its assembled claims |
| search | once per unit | the slice, its assembled claims, search depth, subtype rounds |
| translate | once per checked unit | the slice, its claims and evidence, the document and its claims |
| module search | once per restricted module document | the restricted document, its claims and qualified reads |
| module check | once per restricted module document | the same, and the module's evidence |
| check | once per check of a file | the document, its claims, the selected units' translated evidence |
| explain | once per refused unit | the unit's slice, flow, reads and facts documents |
| TypeScript diagnostics | once per file | as today |

**Units.** `verifier --units <ast.json>` reads a document alone (no
claims). It runs every check `fileFront` makes of the document as a whole
before any unit and independent of claims (the source gates, duplicate
identities, the declaration document's shape); one failing prints the
refusal for every unit, as the whole front refuses every unit today.
Otherwise it prints the document's identity list (the canonical identities
of its functions and whether it has an initialization) and one line per
unit, `{"unit","members","depends","slice","positions"}`: `members` the
unit's code units, `depends` the units its code mentions, `slice` the
unit's [slice](#slices) in [canonical form](#canonical-form), and
`positions` the map from the slice's coordinates to the document's. Groups
are the strongly connected components of the mention graph, as `Front`
computes them today.

**Facts.** `producer --facts <ast.json>` prints, for each unit, the
file-wide facts its proposal reads beyond its slice and its reads document.
The producer reads one today: `read_as_values` (`ocaml-producer/proposal.ml`),
the module names read as values anywhere in the file, which decides whether
the initialization's proposal offers a module constant's closure at its
signature extended by a rest of `unknown`. A unit's facts entry lists the
read-as-value status of the constants its code declares. The
implementation audits every read the producer makes of
`program.Source.functions` and `program.Source.init` outside the function
being inferred, and each becomes a field of the facts entry; the criterion
under [propose](#propose) checks the audit.

**Search, translation and check.**

- `verifier --produce-unit <slice.json> <claims.json> <evidence.json> <depth>`
  builds the front of its slice, searches the unit's evidence and writes
  it; a search it refuses prints `refused: {"refusal","unit"}`. It is
  untrusted: its evidence is a proposal the check verifies.
- `verifier --translate <slice.json> <claims.json> <evidence.json> <ast.json> <file-claims.json> <out.json>`
  maps the store labels of the slice's evidence to the document's labels
  of the same equations and writes the unit's evidence over the document.
  It is untrusted: a wrong map gives evidence the check refuses.
- `verifier --check-units <ast.json> <claims.json> <file-key> <evidence.json> <names>`
  is today's trusted check: one process builds the document's front once
  and checks the selected units at their translated evidence, each verdict
  by `unitVerdict`, whose acceptance `checkUnitJson_safe` states. It
  re-executes after every edit of the file, at the cost of one front and
  the selected units' checks.
- `verifier --produce-module` and `--check-module`, each over one restricted
  module document (`--plan-imports` prints it with its claims and
  qualified reads), search and check a module run as `--produce-units` and
  `--check-units` do today inside the importer's process; the check's
  acceptance is `checkDocument_safe`'s.

**Command lines.** One shape each; no compatibility mode:

```sh
verifier --units              <ast.json>
verifier --produce-unit       <slice.json> <claims.json> <evidence.json> <depth>
verifier --translate          <slice.json> <claims.json> <evidence.json> <ast.json> <file-claims.json> <out.json>
verifier --check-units        <ast.json> <claims.json> <file-key> <evidence.json> <names>
verifier --produce-module     <module.json> <evidence.json> <depth>
verifier --check-module       <module.json> <evidence.json>
verifier --plan-imports       <ast.json> <claims.json>
verifier --lower-program      <ast.json> <claims.json> <file-key>
verifier --lower-control-flow <slice.json>
producer --facts   <ast.json>
producer           <slice.json> <flow.json> <reads.json> <facts.json>
producer --explain <slice.json> <flow.json> <reads.json> <facts.json>
```

`--subtype-rounds <n>` keeps its place before any verifier mode. A
slice's identity is its fingerprint ([canonical form](#canonical-form)).
`--plan-imports` also prints each planned module's restricted document,
its claims and its qualified reads (`<module.json>`,
[module runs](#module-runs)).

**Adapters, decoders and consumers.** Each command line has its argument
shape in `pipeline/stage-execution.mts`; each new document (a `--units`
line, an identity list, a reads document, a facts document, a verdict) has
one TypeScript type and one strict decoder in `tools/`, and its Lean and
OCaml readers use the same field names (`tests/json-field-names.mts`). The
census record keeps, per unit, its stage invocations, its verdict, its
`positions` map and its interface digests; `dev/census.mts` reads deep
status from them ([interfaces](#interfaces)). `make lowering` runs
`--units`, then `--lower-program` on the unit it names.

### Propose

The producer proposes one unit at a time:
`producer <slice.json> <flow.json> <reads.json> <facts.json>`. A unit's
reads document holds, for each dependency its code mentions, the
dependency's [interface](#interfaces): a same-file unit's, read exactly as a
certified import is read today, or a certified import's. Units are proposed
in the order of the dependency graph, acyclic since mutual mentions put code
units in one group; a unit's reads document is assembled from its
dependencies' proposals. A caller's proposal therefore replays after an
edit of a callee that leaves the callee's interface unchanged.

The producer computes footprints at a least fixpoint and on-throw flags at
a greatest fixpoint over the file (cited: `Proposal.infer`). Solving each
strongly connected component of a monotone system in topological order,
the earlier components' solutions fixed, gives the whole system's least
(and, dually, greatest) fixpoint. The producer's dependencies between
functions lie in the mention graph together with the facts documents
(conjectured, after the audit above). The criterion for item 6: on every
file of the census of `tools/` and of pretext at `2b11a4c`, the per-unit
proposals assembled equal the whole-file proposal, at the commit before the
whole-file mode is deleted.

The producer is untrusted, and each propose stage is a process reading
only the four files its arguments name, so its result is a function of its
key's inputs whatever the producer computes: a dependency the audit misses
can change a proposal, and so a verdict, but never makes a replay stale or
an acceptance unsound.

**Withdrawal.** Today's policies, unchanged:

- A same-file neighbour is never withdrawn. A unit is read by its callers
  at its proposed interface whatever its own verdict; a caller accepted
  under a refused neighbour's interface is shallow verified, and deep
  status records the neighbour as its blocker.
- A qualified read the plan refuses (`--plan-imports`) is withdrawn alone
  (`module#name`); a module run refused, any unit of its restricted
  document refused, withdraws every read of that module (`module#*`).
- A withdrawal changes the reads document of every unit naming the
  withdrawn read; each such unit is proposed again, and where its
  interface changes, every unit whose reads document names it is assembled
  and proposed again, in dependency order, transitively. Withdrawals only
  grow, so the rounds end; a withdrawal named twice is an error, as today.

### Module runs

An imported module is proposed and checked as today, through the unit
stages:

- *Proposal over the whole document.* `--units` runs on the module's
  whole document, as the `module` stage lowers it, and its slices are
  proposed unit by unit at its own eligible
  reads, its producer facts computed by `--facts` over that document, as
  the producer sees the whole document today. Its proposal stages are
  keyed on the module's slices, reads and facts, which no importer changes.
- *Certification over the restricted document.* `--plan-imports` restricts
  the module to the read closure of the functions the importer reads
  qualified of it, its initialization kept, as `planImports` does today
  (`lean/Verification/Source/Claims/Imports.lean`), and prints that
  restricted document with its claims and qualified reads. The module
  search and the module check run on it, so `owned`, `reaches` and every
  extraction fact are computed over the restricted document, as today. The
  restricted document, and so the closure, is the key of both stages;
  importers asking for the same closure share one entry.
- *Cycles.* Within each import cycle, a strongly connected component of
  the module graph, the reads into the component's least module by
  location are read at their ordinary signatures; the rule is applied
  again to each strongly connected component of what remains, until no
  cycle is left. The choice depends on the component alone, so it is the
  same in every importer. It can differ from today's choice, which follows
  the order the importer's parse reaches the modules; the pipeline cases
  are the gate: a case whose verdict changes is investigated and
  reported.

An importer's edit that changes which functions it reads qualified of a
module changes the restricted document, an input of the module's run: a
closure no importer asked for before executes for the first time, and one
asked for before replays. The module's document changes with the importer
otherwise only through the tag selection of families the module consults
([shared work](../STAGE-STORE.md#shared-work)). Both are changes of the
module's own inputs, as item 1 states them: a set of imported functions
is checked once, and a set checked before replays.

**Acceptance of a module run.** The module check's acceptance is
`checkDocument` of the restricted document at its claims, which
`checkDocument_safe` states, as the module branch of `unitVerdict` states
it today. The importer's verdict lists the module run among its
dependencies; deep status binds it to the module check of the same
restricted document in the same run.

## Slices

A unit's slice is a Fragment holding exactly what its extraction reads, in
[canonical form](#canonical-form). `sliceOf A u` and the claims projection
`sliceClaims C u` are Lean definitions; `--units` prints `sliceOf`, and the
assemble stage builds `sliceClaims` of the unit's claims from its proposal
and its reads document. The fields of `Front` (cited:
`lean/Verification/Source/Claims/Extraction.lean`) state what a slice holds
for a unit `u` of a document `A`:

- the members' code: their entries of `functions`, and, for the
  initialization's group, its statements;
- the declarations the members' code, annotations and reads reach, closed
  under the definitions they name, with the implicit dependencies they
  select (`ArrayProto`, `%Stable%`, native `Promise`);
- for each module value the code mentions: a function's declared signature
  and every overload of its name (`overloadSlot`), a constant's annotation,
  a cell's binding, a class's self binding and whether its class is
  generic (`classNames`), an imported value's declaration;
- the generic instances the code names (`generics`), the omitted mentions
  (`omittedMentions`) it names;
- `owned`: the module cells it mentions whose objects the module owns, as
  `ownedModuleCells` computes them over every body of `A`
  (`lean/Verification/Source/SourceFacts.lean`);
- for the initialization's group, `reaches`: for each function and closure
  constant the initialization's steps reach through mentions, transitively,
  the names its body mentions (`checkInitializationOrder`,
  `lean/Verification/Source/Claims/Sites.lean`, follows function bodies
  this way, reading of each only `stmtNames`).

Extraction from a slice reads ownership from `owned` and the order check's
bodies from `reaches`, never from the bodies the slice holds: dropping a
body that lets a cell's object escape cannot make a slice infer ownership
its document does not have. An edit of a function changes another unit's
slice only where it changes that unit's `owned` or `reaches` entries, which
are inputs of that unit.

`sliceClaims C u` keeps the claims of `u`'s members (their `functions`
entries, and the initialization's claims for its group) and the interface
entries of `u`'s dependencies. The checks of `C` as a whole are the claims
check's.

A slice is an input of untrusted stages only (proposal, search,
explanation). A slice lacking a declaration its unit's extraction reads
makes its search refuse or its evidence fail the check; neither accepts.

## Canonical form

A key covers only a unit's inputs only if its slice holds nothing an edit of
another unit changes. A slice's canonical form fixes three things:

- *Coordinates.* Each member (a function, or one top-level statement of the
  initialization's group) is placed at a canonical origin, the sum of the
  lengths of the members before it; a position inside a member is its
  offset from the member's start plus that origin. Each declaration and
  module value outside the members that the slice holds (a neighbour's
  declared signature, a local type's definition, a constant's annotation)
  is placed after the members the same way, as an entry of its own.
  Lengthening a function between two members of one group, or between two
  top-level statements, changes no position of the slice. `positions` lists
  each entry's canonical origin, document offset and length; the
  orchestration maps every span of a verdict, refusal or explanation back
  through it, a span at a neighbour's declaration included, before
  presenting it, outside every key.
- *Identities.* An identity outside the slice's members is scope-based: a
  declaration by the canonical identity of its enclosing scope (the
  document's top level, a function, or a block within one by its index
  among that function's blocks), its name, and its index among the
  declarations of that name in that scope alone. A function is a
  declaration of the top level; the initialization is `init`; an imported
  module's declaration is its module location with its own scope-based
  identity. A declaration inserted in one scope renumbers no declaration of
  another. A unit's identity is its first member's.
- *Fingerprint.* The slice's `file` and `sourceSha256` are its fingerprint,
  the SHA-256 of its canonical encoding with those two fields empty;
  `checkIdentity` compares the claims' fields with the slice's, so claims
  are about one slice. The source's path and digest are provenance, kept
  beside `positions`, outside every key.

The renaming is injective on each slice, and extraction compares
identities for equality and positions only for order within one member
(conjectured; a slice that breaks this makes its search's evidence fail the check). Two documents with byte-identical
slices, claims, reads and facts of a unit share its entries.

## Interfaces

A dependency's interface is what a unit reading it assumes of it: for a
function, every overload's declared signature with its footprint and
on-throw flag; for a constant, its annotation and initializer claim; for a
cell, its storage contract; for a class, its self binding's construct
signature; for a generic value, its binders and bounds. Its types are
spelled as `sameReading` reads them: terms whose symbol keys name
declaration identities, with the definition of every declaration they
reach, transitively, and the implicit dependencies they trigger
(`canonical`, `lean/Verification/Source/Claims/Imports.lean`). No store
head index appears in an interface.

The interface digest is the SHA-256 of the canonical encoding of the
binding's stable identity (its scope-based identity, with the module
location for an import) and its interface, and of nothing else: no body
and no slice or source fingerprint. An edit of a function's body that
keeps its interface keeps its digest, and its callers' reads documents are
unchanged. One Lean function, `interfaceOf`, computes it from a document
and claims; the reads documents of the proposal stages hold it, and the
plan's comparison of an importer's reading with a module's (`sameReading`)
compares the same canonical form. Deep status is computed as today, from
the whole-file check's verdicts.

## Soundness

`checkUnitJson_safe` (proved, `lean/Verification/Source/Claims/Json.lean`)
states: `filePlans ast claims fileKey budget = .ok f` and
`unitVerdict f budget unit evidence = .ok deps` give
`UnitSafe f budget unit evidence`. The check stage runs that premise over
the whole document and its assembled claims, as today; nothing a slice
holds reaches it except through the evidence, which it checks. The module
check's acceptance is `checkDocument_safe`'s over the restricted document.
No theorem changes, and the change adds no trust row and no axiom (item 7).

The assembled claims are the producer's, untrusted as today; the criterion
under [propose](#propose) checks that they equal the whole-file proposal,
which bears on verdicts (item 6), not on soundness.

## The census

The census schedules unit stages, not files: a pool of one worker per core
takes any stage whose inputs exist, the proposals of a document in
dependency order, the other stages of different units concurrently. Within
one census run each stage key executes once: a stage whose key is being
executed by another worker waits for that execution's result, so a module
closure two importers ask for, or a slice two documents share, runs once
though the store would allow both to miss.

The memory reasons for writing and checking evidence a unit at a time
(cited, commit `7cfce13f`: the whole-file search held every unit's
certificates and the memo of all units, and the check decoded the whole
evidence before its first unit; on `fragment-statements.mts` the front
alone peaked at 0.36 GB and the search of its largest unit alone at
2.0 GB) hold by construction: each process holds one unit's slice, front,
memo and evidence, and ends with it. A unit's search or check over its time
or memory limit is that unit's outcome, as today, and no fallback runs.

## The controls

Controls of the store itself, in `make test` (fresh stores, executing every
time, beside the replay control of `pipeline/test.mts`), check edits of
pipeline fixtures. Each run's attempt records are read from
`invocations.jsonl` by stage and unit; a replayed attempt must be a replay
of a finished entry, never of a timeout; each edited run's outcome must
equal a cold run's of the same edited source in a fresh store.

1. *Imports.* A file imports a certified function from a module and defines
   `f`, `g` calling `f`, and `h`. An edit of `f`'s body that keeps its
   interface: every stage of the module's run replays; `g`'s and `h`'s
   lower, propose, assemble, search and check replay; `f`'s execute, and
   `g`'s reads document is byte-identical.
2. *Shared imports.* Two importers asking for the same closure of one
   module, checked in one census run: each stage of the module's run
   executes once.
3. *Changed interface.* An edit of `f` that changes its footprint: `f`'s
   stages and `g`'s propose, assemble, search and check execute; `h`'s and
   the module's replay.
4. *Length-changing edit.* An edit lengthening `f` by several lines, which
   keeps every interface and every file-wide fact (`owned`, `reaches`, the
   producer's facts): every unit after `f` replays, and a local type alias
   declared after `f` keeps its identity.
5. *Noncontiguous group.* Mutually recursive `p` and `q` around an
   unrelated `r`, and a top-level statement after `r`; an edit lengthening
   `r` that keeps its interface and the file-wide facts: the stages of `p`
   and `q`'s unit and of the initialization replay.
6. *Same-named declaration.* A local type `T` inserted in one function, in
   a file where another function declares its own `T`: every unit but the
   edited one replays.
7. *Explanations.* A file with a refused unit and an accepted one: an edit
   of the accepted unit replays the refused unit's stages and its
   `explain`.
8. *Ownership.* A file whose function `e` lets a module cell's object
   escape: the slices of the units mentioning the cell carry it as not
   owned, and an edit removing the escape executes those units.
9. *Restricted module facts.* A module defining `good`, which uses a module
   cell, and an unrelated `escape`, which returns that cell's object; an
   importer reading only `good`: the module's run is over the restricted
   document without `escape`, its outcome today's, and an importer reading
   `escape` too executes a run of the other closure.
10. *Claims check.* A claims document missing one function's claim: every
    unit of the document is refused, as the whole front refuses today.

The replay control asserts today that an unchanged source replays and a
changed source executes; these controls assert what an edit leaves to
replay.

## Decisions

Each decision follows from the promise and the project's principles.

1. **Search is per unit, the check per file.** The search of a unit is
   keyed on its slice and replays; the trusted check builds the whole
   front once and checks the selected units. Consequence: an edit
   executes the check of the selected units every time, at the cost of one
   whole front, measured at 0.5 s for `analysis.ts` and 5 s for
   `rich-inline.ts`.
2. **Slicing is untrusted** (route chosen by the lead, 2026-11-08). The
   Lean code that reads a document is partial, so no lemma relating a
   slice's plans to the document's can be proved. Consequence: slices feed
   only proposal, search and explanation; slice evidence is translated to
   the document's labels by untrusted code and the check verifies it.
3. **Module runs are their own stages** over the restricted document,
   searched and checked as today. Consequence: an importer's edit replays
   them unless it changes the closure or a tag selection the module
   consults.
4. **File-wide facts reach a slice as fields computed from the whole
   document,** in keyed code: `owned` and `reaches` by `--units`, the
   producer's facts by `--facts`. Consequence: a slice cannot gain an
   ownership premise by dropping a body, and an edit that changes such a
   fact executes exactly the units that read it.
5. **A module is certified over its restricted document,** the read closure
   of its imported functions plus its initialization, as today, its
   extraction facts computed there and the closure part of the key.
   Consequence: verdicts are unchanged (item 6); importers asking for one
   closure share one entry, and a new closure executes once.
6. **Withdrawal policies are today's; the cycle rule is fixed by each
   import cycle alone.** Same-file neighbours are never withdrawn; module
   withdrawal keeps its scope; the reads made ordinary in an import cycle
   are those into its least module by location. Consequence: shallow
   verdicts are unchanged where no import cycle is involved, a module's
   interfaces are the same in every importer, and a case whose verdict the
   cycle rule changes is investigated and reported.
7. **Interfaces are canonical readings bound to stable identities,** with
   no body or fingerprint in their digest; the binding to the current
   artifact is deep status's. Consequence: an interface-preserving edit
   leaves its callers' inputs unchanged.
8. **Declaration identities are scope-based.** Consequence: a declaration
   added in one scope renumbers none in another.
9. **The census runs each stage key once per run,** and every timing
   compares against a baseline carrying the `fm_entails` memo.
   Consequence: shared dependencies cost once in a cold census, and the
   memo's saving cannot hide a cost of staging.
10. **The stage design is written once.** At the implementation, this
    draft's stages, keys and slices move into
    [STAGE-STORE](../STAGE-STORE.md), its units and lemmas into
    [DESIGN](../DESIGN.md#modules-and-code-units), module runs into
    [certified imports](../SOURCE-CONTRACTS.md#certified-imports), the
    command lines into [REQUEST-PROTOCOL](../REQUEST-PROTOCOL.md#run-the-verifier);
    the stale paragraph and comment are corrected, and the draft is
    deleted.

## How the design meets each item

1. *Imported files.* A module run's stages are keyed on its whole
   document's slices for proposal and on its restricted document for
   certification. An edit of the importer re-executes the parse and its
   nested module lowerings; a lowering giving the same document, and an
   importer asking for the same closure, leave every key of the module's
   run unchanged. A changed tag selection the module consults, or a changed
   set of functions the importer reads of it, is a change of the module's
   own inputs, as the item states.
2. *One function and what reads it.* An edit of `f` changes `f`'s slice,
   and another unit's inputs only where it changes `f`'s interface or a
   file-wide fact that unit reads ([canonical form](#canonical-form),
   [interfaces](#interfaces), decision 4). Every other unit's propose,
   search and explain stages replay; the check of the selected units runs
   over the whole front (decision 1).
3. *Edit-check time.* After a one-line edit the stages that execute are the
   parse (with TypeScript's diagnostics where enabled), `--units`,
   `--facts`, the plan, the edited unit's lower, propose, assemble, search
   and translate, and the check of the selected units; every other stage,
   the module runs included, is a store lookup. Budgets, each measured per
   component from `invocations.jsonl`:
   - `removeItemsSkippableSegmentBreaks`: its search and check 0.36 s, a
     front of its slice and the whole front (0.5 s); the parse, `--units`,
     `--facts`, its proposal and the lookups share the rest of 5 s.
   - `createLine`: no proposal or search of `prepareRichInline`'s unit
     executes; the check reads the whole front.
   - `prepareRichInline`: its search about 80 s and its proposal at most
     12 s with the memo leave 8 s for its slice's front, the whole front
     (5.1 s), its check, the parse and the lookups.
4. *One mode.* `verify-source.mts` runs the per-unit stages; the cases,
   the census and the census's function selection call it. The modes
   listed above are deleted, and `grep` finds none.
5. *Cold runs.* Each module closure executes once per census run instead of
   once per importer. Each unit builds two fronts of its slice where each
   file builds two whole fronts today; the adverse case is many small
   units sharing a large declaration closure, each lowering it, with
   process start, serialization and publication per stage. The cold census
   of `tools/`, timed before and after on one machine against the baseline
   with the memo, decides the item.
6. *Same verdicts.* The check is today's, over the whole front; module certification keeps its restricted document; withdrawal keeps
   today's policies and each stage today's limit, timeouts measured; the
   cycle rule is gated by the pipeline cases; per-unit proposals equal the
   whole-file proposal on every census file. Every case keeps its expected
   outcome, and pretext at `2b11a4c` verifies 210 of 210 functions.
7. *Same soundness.* `checkUnitJson_safe` and `checkDocument_safe` are
   unchanged and are the acceptance; no axiom and no trust row is added;
   slices reach only untrusted stages.
8. *The controls.* [The controls](#the-controls) run in `make test`.
9. *The docs.* Decision 10.
