# Draft: every unit its own stage

# The promise: a function is analysed again only when its own inputs change

**In one sentence:** after you edit one function, checking it re-does only that function's work and the work of functions whose inputs your edit changed. Everything else is taken from the store, in milliseconds per entry.

Each item below is checked at the end by a measurement or a test. The result goes in the same table, as passed or failed, with the number.

## What you get

1. **Imported files are never re-analysed because you edited the file that imports them.** An imported module's search and check run again only when that module's own inputs change. Those inputs are its source, and the run's choice of host-library models for the libraries that module itself uses. An edit to the importer that changes that choice really changes the module's lowered text, so re-running it is correct. Changes to models the module doesn't use don't re-run it. Changing which of a module's functions you import is also a change of its inputs: the module is checked once for the new set of functions, and a set it was already checked for replays. Today they run again after every edit: 43.5 s of a 75 s check, and 185 s of a 390 s one.
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
estimates. Every proposed lemma requires a Lean proof, and lands before the
whole-file modes are deleted.

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

- the modes `--produce-units`, `--check-units` and the whole-file
  `--units`, the unit selection by names, and the evidence document with a
  line per unit;
- the module branch of `unitVerdict` and of `UnitSafe`
  ([module runs](#module-runs));
- the whole-file proposal and the whole-file `--explain`;
- `unitRound`'s fallback to a search and check of each unit after a
  whole-file limit;
- the paragraph of [STAGE-STORE](../STAGE-STORE.md#observed-stages) stating
  that a document with qualified reads is searched run by run, the `search
  of a run` row of its stage table, and the comment of
  `pipeline/verify-source.mts` naming `searchRuns`: the current code has no
  run stage.

## Stages

One check of a source runs these stages. Each unit's stages read only that
unit's documents, except the claims check, which reads the whole claims
document by design.

| Stage | Runs | Inputs beside its implementation |
| --- | --- | --- |
| parse | once per file | as today |
| module | once per imported module, nested in the parse | as today |
| units | once per document: the file; each imported module's whole document, for its proposal; each restricted document `--plan-imports` prints, for its certification | the document |
| facts | once per proposed document (the file, each imported module's whole document) | the document |
| lower | once per unit | the unit's slice |
| propose | once per unit, in dependency order | the unit's slice and flow, its reads and facts documents |
| assemble | once per unit | the unit's proposal, its reads document |
| claims check | once per document | the document's identity list, its whole claims document |
| plan | once per unit with qualified reads | the slice and its assembled claims |
| search | once per unit | the slice, its assembled claims, search depth, subtype rounds |
| check | once per unit | the slice, its assembled claims, its evidence, subtype rounds |
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

**Claims check.** `verifier --check-claims <identities.json> <claims.json>`
runs every check `fileFront` and `equationFront` make of a claims document
as a whole: the function claim count and identities against the identity
list, the initialization's claims present exactly where it has code, the
claims' shape and the identities of their entries. The claims document is
the assembly of every unit's proposal, the document a whole-file proposal
gives today (the criterion under [propose](#propose)). Its refusal refuses
every unit of the document, exactly as `fileFront` refuses today; a unit's
verdict is accepted only where its document's claims check passes. The
stage executes on every edit, at the cost of decoding one claims document;
its result for unchanged claims replays.

**Search and check.** Each unit has two stages, each with today's limit
for its kind. Extraction from a slice and the work of one process differ
from today's, so a unit's timeout outcomes are measured on the census, not
assumed equal to today's:

- `verifier --produce-unit <slice.json> <claims.json> <evidence.json> <depth>`
  builds the front of its slice, searches the unit's evidence and writes
  it; a search it refuses prints `refused: {"refusal","unit"}`.
- `verifier --check-unit <slice.json> <claims.json> <evidence.json>` builds
  the front of its slice, checks the unit at its evidence and prints the
  unit's verdict, `{"accepted","assumes","certifies","members","unit"}` or
  `{"members","refusal","unit"}` ([interfaces](#interfaces)). The controls
  that forge or mutate evidence use it (`pipeline/evidence-mutations.mts`
  and the forged evidence controls of `pipeline/test.mts`).

The evidence document is one unit's bundle. Each process holds one unit,
and the front of a slice is built twice per unit, by the search and by the
check.

**Command lines.** One shape each; no compatibility mode:

```sh
verifier --units              <ast.json>
verifier --check-claims       <identities.json> <claims.json>
verifier --produce-unit       <slice.json> <claims.json> <evidence.json> <depth>
verifier --check-unit         <slice.json> <claims.json> <evidence.json>
verifier --plan-imports       <slice.json> <claims.json>
verifier --lower-program      <slice.json> <claims.json>
verifier --lower-control-flow <slice.json>
producer --facts   <ast.json>
producer           <slice.json> <flow.json> <reads.json> <facts.json>
producer --explain <slice.json> <flow.json> <reads.json> <facts.json>
```

`--subtype-rounds <n>` keeps its place before any verifier mode. The
`<file-key>` argument goes: a slice's identity is its fingerprint
([canonical form](#canonical-form)). `--plan-imports` also prints each
planned module's restricted document ([module runs](#module-runs)).

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
  restricted document. `--units` runs again on it and gives the slices of
  certification; the claims check, the search and the check run on those, so `owned`, `reaches` and every extraction fact are
  computed over the restricted document, as today. The restricted
  document, and so the closure, is part of every one of these stages'
  keys; importers asking for the same closure share one entry.
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

**DocumentSafe.** Today a module run's acceptance is `checkDocument` of
the restricted document at its restricted claims, through the module
branch of `unitVerdict`. **Lemma `documentSafe_of_units`** (conjectured):
for a restricted document `D` and its one claims document `C` (the module's
claims restricted as `planImports` restricts them), if the claims check of
`C` against `D` passes and every unit `u` of `D` is accepted at
`sliceOf D u` and `sliceClaims C u`, then `DocumentSafe D C` holds, with the
evidence assembled from the units' bundles transported by `slicePlans`.
Every unit's assumed interfaces are then the certified ones of the same
`C`, by construction. The module branch of `unitVerdict` and of `UnitSafe`
has no caller and is deleted, which narrows `UnitSafe` to its group branch.

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

**Lemma `slicePlans` (conjectured).** For every document `A`, claims `C`
and unit `u` that `--units A` prints with slice `s = sliceOf A u` and
members `M`:

1. *Membership.* The groups of `s` are one group, of members `M`, the group
   of `u` in the front of `A`: the recursive boundary certified together is
   the same.
2. *Refusals.* Extraction of `u` from `fileFront A C` fails if and only if
   `--units A` refuses, or the claims check of `C` against `A`'s identity
   list refuses, or extraction from `filePlans s (sliceClaims C u)` fails.
   The original refusing while the slice accepts is impossible: a refusal
   of the whole claims document reaches every unit through the claims
   check.
3. *Stores.* With `F` the frozen store of `A` and `Fs` the slice's, a map
   `h` of `Fs`'s heads to `F`'s heads sends every equation reachable from
   the labels of `u`'s requests and environment to `F`'s equation of its
   image: `Fs`'s graph below those labels is `F`'s graph below their
   images, so each label's interpretation in `Fs` is its image's in `F`.
4. *Plans.* `u`'s plans from `s`, mapped by `h` and by the canonical
   renaming, are `u`'s plans from `A`: the same requests, the same input
   contracts (`EnvOk` of the same module values at the same signatures,
   effects and storage contracts), the same qualified reads with their
   footprints and on-throw flags.
5. *Evidence.* Evidence accepted for `u` at `s`, mapped by `h`, is accepted
   for `u` in `A`'s front, so `UnitSafe` over `s` gives the safety of `u`'s
   requests over `A`.
6. *The emitted slice.* The slice `--units` prints decodes, under the
   strict decoder `--produce-unit` and `--check-unit` use, to
   `sliceOf A u`, and the members a verdict reports are `M` mapped by
   `positions`.

A slice lacking a declaration its unit's extraction reads fails extraction
(part 2), a refusal. A slice whose `owned` or `reaches` is not `sliceOf`'s
is a different document, as a forged Fragment is today; the pipeline passes
only `--units`'s output.

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
(conjectured, part 4 of `slicePlans`). Two documents with byte-identical
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
unchanged. One Lean function, `interfaceOf`, computes it from a slice and
claims, on both sides:

- `--check-unit`'s accepted verdict lists `certifies`, the digest of the
  interface of each member its claims state;
- it lists `assumes`, for each dependency its slice reads, the
  dependency's identity and the digest of the interface the slice's reads
  entry states;
- the plan's comparison of an importer's reading with a module's
  (`sameReading`) compares the same canonical form.

Deep status (`dev/census.mts`, node code without a proof, a row of the
[trust surface](../DESIGN.md#trust-surface)) binds each dependency to the
artifact checked in the same run: it counts a dependency accepted only
where the verdict the run produced for that dependency's current slice is
accepted, its `certifies` digest equals the dependent's `assumes` digest,
and its initialization and transitive dependencies are accepted. This keeps
computed deep status consistent; it does not discharge the composition of a
module's units, which remains [open work](../../WORK.md#module-composition).

## Soundness

`checkUnitJson_safe` (proved, `lean/Verification/Source/Claims/Json.lean`)
states: `filePlans ast claims fileKey budget = .ok f` and
`unitVerdict f budget unit evidence = .ok deps` give
`UnitSafe f budget unit evidence`. It applies to the slice: `ast` is the
slice, `claims` its assembled claims, `fileKey` its fingerprint, and the
slice has exactly one unit. The CLI condition for an accepted verdict of
`--check-unit` is that premise over the three files its arguments name; it
reaches the verdict through `unitVerdict` alone, and the acceptance path
keeps its one exhaustive conversion to `CertifiedPlan`
(`FilePlans.certified`). Deleting the module branch narrows `UnitSafe` to
the group branch; the theorem's meaning, an accepted unit is safe, is
unchanged.

The theorem speaks of the slice's requests. `slicePlans` carries it to the
unit of the source document, under the claims check of the whole claims
document: the same group, the same requests at the same input contracts and
qualified reads, interpreted over the same equations, refused exactly where
the whole front refuses. `documentSafe_of_units` carries the units of a
restricted module document to today's module-run acceptance. Both are Lean
lemmas, so the change adds no trust row and no axiom (item 7).

A replayed check is the verifier's judgment of exactly the slice, claims
and evidence its key binds, under the binding and validation the trust
surface's replayed-check row states. The
[source boundaries](../DESIGN.md#trust-surface) (annotation lowering,
native contracts, inferred call effects) are read from the same
declarations and claims; a slice holds every declaration its unit's code,
annotations and reads reach, so no contract is cut.

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

1. **Search and check stay separate stages per unit, each with today's
   limit.** Consequence: limits are preserved per stage, and timeout
   outcomes are measured on the census, not claimed identical; the front
   of a slice is built twice per unit, which the cost budgets include.
2. **Slicing is proved, not trusted** (`slicePlans`,
   `documentSafe_of_units`). Item 7 allows no new trust. Consequence: the
   lemmas land before the whole-file modes are deleted; `fileFront` stays a
   Lean definition, the reference the lemma names, reached by no command
   line.
3. **Whole-document checks are their own stages:** `--units` for the
   document, the claims check for the whole claims document. Their refusal
   refuses every unit, as `fileFront` does today. Consequence: the
   refusal clause of `slicePlans` holds for every claims document.
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
   search, check and explain stages replay.
3. *Edit-check time.* After a one-line edit the stages that execute are the
   parse (with TypeScript's diagnostics where enabled), `--units`,
   `--facts`, the claims check, and the edited unit's lower, propose,
   assemble, plan, search and check; every other stage is a store lookup.
   Budgets, each measured per component from `invocations.jsonl`:
   - `removeItemsSkippableSegmentBreaks`: its search and check 0.36 s and
     two fronts of its slice (at most 0.5 s each); the parse, `--units`,
     `--facts`, the claims check, its proposal and the lookups share the
     rest of 5 s.
   - `createLine`: no stage of `prepareRichInline`'s unit executes; its
     interface is read from the store.
   - `prepareRichInline`: its search about 80 s and its proposal at most
     12 s with the memo leave 8 s for two fronts of its slice, its check,
     the parse, the whole-document stages and the lookups. The whole file's
     front is 5.1 s; the budget holds only if its slice's front is at most
     about 2 s, which the implementation measures first.
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
6. *Same verdicts.* `slicePlans` gives each unit the plans and refusals it
   has today; the claims check refuses what the whole front refuses;
   module certification keeps its restricted document; withdrawal keeps
   today's policies and each stage today's limit, timeouts measured; the
   cycle rule is gated by the pipeline cases; per-unit proposals equal the
   whole-file proposal on every census file. Every case keeps its expected
   outcome, and pretext at `2b11a4c` verifies 210 of 210 functions.
7. *Same soundness.* `checkUnitJson_safe` keeps its meaning; `slicePlans`
   and `documentSafe_of_units` are proved; no axiom and no trust row is
   added; a slice missing what its check needs is refused.
8. *The controls.* [The controls](#the-controls) run in `make test`.
9. *The docs.* Decision 10.
