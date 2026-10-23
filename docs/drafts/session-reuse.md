# Draft: declaration compiler session reuse before parsing each file once

The design approved by the owner (2026-10-23); its status is in
[WORK](../../WORK.md#status). Base: TScert main at 2f777e5.

## Scope and evidence

**Proposed.** Each serial census/case worker retains compatible declaration
compilers. Parsing keeps the existing slice text, resolution file, Fragment,
claims and whole-document checker. Coverage and worker count stay fixed.

Labels: **measured** means observed in the supplied records; **cited** means
source behavior or attributed evidence; **conjectured** means an unproved
explanation or illustrative estimate; **proposed** means a design requirement.

**Measured (owner-supplied census baseline):** 445 slices from 37 files;
2,849 s total CPU, 1,424 s parse CPU and 506 s wall time.
**Measured (record sums):** timing inputs are
`fresh.json`,
`reuse-forward.json`
and `reuse.json`.
The following sums include every record, including the initial forward
`booleanReturn` invocation. Each cell is aggregate Node + child CPU seconds;
`load:fs` is shown separately as recorded. No cell is a per-module cost.

| Recorded phase | Fresh (9 attempts) | Forward reuse (9) | Reverse reuse (8) |
| --- | ---: | ---: | ---: |
| main/parser.open | 0.018357 | 0.001778 | 0.001989 |
| main/parser.load | 0.735789 | 0.107396 | 0.105177 |
| main/parser.load:fs | 0.010296 | 0.007966 | 0.006983 |
| imported/parser.load | 3.367769 | 1.042139 | 1.073205 |
| imported/parser.load:fs | 0.463556 | 0.221013 | 0.239647 |
| main/decl.open | 0.047721 | 0.006009 | 0.004941 |
| main/decl.load | 6.884146 | 0.868012 | 0.826204 |
| main/decl.load:fs | 0.837441 | 0.081149 | 0.111014 |
| imported/decl.open | 0.042523 | 0 | 0 |
| imported/decl.load | 6.448767 | 0.020337 | 0.011774 |
| imported/decl.load:fs | 0.788454 | 0.000947 | 0.000811 |
| Entire attempt CPU | 39.609501 | 21.237447 | 20.445370 |

**Measured.** In fresh `expr`, imported parser loading totals 0.705676 s
across six calls, plus 0.082546 s in its filesystem bucket. Imported
declaration loading totals 3.074792 s across four calls, plus 0.381157 s
in its filesystem bucket. Parser loading is amortized within a parse.
Forward totals excluding the first invocation are 38.333767 and 19.920934 s:
48.0% reduction; including it gives 46.4%. These runs reuse both roles.
`shadowingLocals` takes 2.9844 s forward and 0.6693 s reverse.
**Conjectured:** retained checker caches explain this order dependence.

**Cited (both supplied reviews):** sixteen retained artifacts compare equal:
eight successful Fragments and their diagnostics. The experiment overwrites
the repeated `booleanReturn` artifact. Refusal fidelity and separate repeated
invocation fidelity therefore require the controls below.
## Concrete compatibility and project state

**Cited.** [parseSource](../../pipeline/verify-source.mts)
places different slice contents in different snapshot directories.
[projectFor](../../tools/fragment-parse.mts)
launches the parser with `dirname(snapshot)` as compiler cwd and selects
`getDefaultProjectForFile`. [withProject](../../tools/declaration-graph.mts)
uses `dirname(resolutionFile)` as cwd. An explicit project opens only that
project and selects `getProject(config)`; automatic selection opens the file
and uses its default project. Declaration collection requires a strict
configured project containing the resolution file.

**Proposed parser predicate:** cross-request compatibility is always false.
Each executed parse opens a fresh parser at the snapshot directory and closes
it at request end. Within that request, snapshot and imported documents and
their automatically selected projects may coexist as in `projectFor` today.
All parser documents, projects and overlays die with that compiler. This
preserves fresh project selection without asserting cwd independence across
snapshot directories. All cross-request parser savings are excluded below.

**Proposed declaration predicate:** retain one idle declaration session per
worker. A collection may reuse it iff all of the following hold:

1. Both collections explicitly name the same normalized absolute config path
   (`tsconfigOf`), and have equal absolute `dirname(resolutionFile)` paths.
2. Compiler/runtime/keyed implementation identities and the serialized active
   family configuration are equal; role is declaration in both cases.
3. The full lifetime ledger passes validation, with complete metadata and
   healthy Node process state; the session has a verified clean base state.

**Proposed.** Automatic/inferred selection uses a fresh declaration compiler
and closes it after collection. Any predicate failure releases the retained
session before opening its replacement; cwd stays fixed for its lifetime.
Explicit selection retains exactly the named project between collections,
with no explicitly open documents and an empty overlay. Other projects are
excluded; inability to establish this state requires replacement. The
project's internal loaded source files and compiler caches may remain.

Each explicit collection reacquires a snapshot and `getProject(config)`;
it checks config identity, strictness, client membership and program diagnostics
as `withProject` does. It never asks default-project selection for this role.
Different slice snapshot directories can therefore share this declaration
session when their resolution files satisfy the predicate. The slice path
is not a declaration cwd. Different resolution directories require replacement
even when the config path is equal. Imported collections obey the same test.
Diagnostics collections obey it too; family context is explicit in their
compatibility descriptor and stage inputs if they share these sessions.

**Proposed.** Gate state, collectors, numbering, selected members, declaration
graphs, diagnostics, probe callbacks and checker/program handles are fresh
for each collection. Handles never cross snapshot lifetimes. Store hits
open no compiler. CLI completion, eviction, retirement and worker shutdown
release sessions; timeout termination reaps compiler children.
## Overlay transactions and key binding

**Cited.** [compilerFileSystem](../../tools/files.mts)
serves overlays before disk, so overlay bytes are absent from disk observations.
`projectFor` closes an open document before replacing its text. `withProject`
tracks probe-replaced paths and disposes the preceding probe snapshot.

**Proposed.** Keep each base snapshot alive through its dependent queries.
For every probe, track all replaced paths, close affected open documents,
install exactly that probe's overlay and notify changes for the union of old
and new overlay paths. In `finally`, close probe documents, clear overlays,
notify every restored path, reacquire the named base project, and dispose
obsolete snapshots once their consumers finish. Assert zero open documents,
empty overlays and the single retained config before marking the session idle.
Clearing a map alone does not restore the compiler's view.
A refusal follows this same cleanup. Failed or uncertain restoration discards
the session and prevents publication of that attempt's result.

**Proposed.** Filesystem validation cannot establish overlay or project
selection correctness. Compatibility explicitly binds selection mode, config,
cwd and family configuration; the protocol enforces the corresponding open
project/document state. Stage inputs bind source bytes, snapshot path,
resolution path, selection mode/config, role-specific cwd, families and
compiler/runtime/keyed-code identities. Deterministic probe overlays derive
from these inputs, observed declarations and keyed transformations. Any
externally supplied overlay must bind its complete path/byte map as input.
Prior-request overlays must be removed and their compiler views invalidated
before use. Session generation and request order are telemetry, not key inputs.
## Observation ledger and stage store

**Cited.** [files.mts](../../tools/files.mts)
keeps `Noted` answers with a Node-origin bit; `remembered` preserves both this
bit and incompleteness and propagates them to consuming recordings. Validation
with that bit checks Node's first answers. Plain `observationsHold` treats
triples as non-Node observations. Incomplete Node reads set process retirement;
inconsistent Node answers make the process stale.

**Proposed.** A session ledger contains operation/path/answer triples, the
Node-origin bit (OR on merging), incompleteness reasons, inconsistency and
Node-retirement state. It accumulates across the entire lifetime, including
dependencies first read by later queries, diagnostics or probes. Preserve
metadata through validation, merging and every consuming attempt, including
cache-only attempts. A triples-only validation API is insufficient.

Before use, validate the entire ledger outside the new attempt's recording.
Validation retains Node-origin semantics and process-level first-answer checks.
A changed non-Node answer discards the session; a Node inconsistency retires
the worker. Incomplete Node observations require retirement before any further
execution, even when all known triples match. Other incompleteness makes the
session ineligible for reuse and the consuming attempt ineligible for storage;
propagate the reason rather than treating matching known answers as completeness.

Within the attempt, import the validated ledger and its metadata into every
consuming recording, then accumulate new observations. Include absent
resolution candidates, directory contents/kinds, symlinks, source/declaration
files, configurations and extensions, and package metadata. Compiler
installation dependencies remain bound by implementation identity.
Revalidate the resulting ledger before publication; conflicting answers,
incompleteness or inconsistency prevent storage and discard the session.
Retry only in an eligible fresh session/process or report tool failure.
These checks retain the store's filesystem stability assumptions; they do
not create an atomic filesystem snapshot.

**Proposed.** The final observed key binds all accumulated external answers;
only complete, consistent attempts produce entries. History may enlarge
observation sets and cause safe over-invalidation, conditional on restoration
and cache correctness. Replay validates the stored entry's observations;
a live session receives its own pre-use validation on subsequent execution.
Keep session semantics in keyed front-end modules, preserving codecs, complete
input binding, timeout replay rules and directory-wide code invalidation.
## Fidelity argument and required controls

**Conjectured.** For fixed explicit inputs and unchanged external answers,
a completed reused parse has the fresh parse's encoded Fragment/refusal and
ordered diagnostics. This requires identical base project/overlays, correct
compiler caches across valid snapshot updates, and fresh Gate/collector state.
The ledger binds cached dependencies only under complete observation metadata
and exact restoration. Cache correctness is a trusted obligation, not a Lean
result. Timing may change deadline outcomes; report those separately.

**Proposed controls.** Use production adapters, replay disabled for execution
comparisons, and identical paths/bytes for each fresh reference invocation.
Record role, generation, compiler-open count, reuse count, cwd, selected config,
open projects/documents and overlay state at each boundary.

1. Run fresh, forward, reverse and A–B–A sequences. Save and compare every
   invocation separately, including both A results, with its fresh reference.
   Compare complete encoded outputs, imported Fragments, identities, spans,
   ordered diagnostics, refusal code/detail and located refusal positions.
2. Use distinct snapshot directories with the same explicit resolution project
   and resolution cwd. Assert one declaration generation/open across compatible
   collections and increasing reuse count; assert a fresh parser each request.
   Insert diagnostics between parses and assert compatible declaration reuse
   and clean base state before and after diagnostics and probes.
3. Vary explicit config, resolution cwd, family context and automatic-selection
   mode. Assert replacement generation/open increments and old-session release.
   Include same-path text replacement, probe-heavy declarations, shadowing,
   imports, located refusals and cleanup failure; verify fresh output fidelity.
4. Discover dependency D only in a later query or probe, after session creation.
   Assert D enters the lifetime ledger and that attempt's stored entry. Mutate D;
   force execution to assert old-generation rejection and replacement, then
   separately request replay of that entry and assert a miss/invalidation.
   Compare the replacement result with fresh execution.
5. Mutate previously read declarations/configs, create absent resolution targets,
   alter directories/symlinks and remove files. Assert replacement plus stored
   entry rejection. Inject incompleteness and Node-origin changes: assert
   metadata propagation, publication rejection and required worker retirement.
6. Keep disk answers fixed while changing overlay bytes or project selection.
   Assert input-key/compatibility changes and exact cleanup; deliberately leaked
   overlays or extra projects must fail clean-state checks. Test private-store
   miss, valid warm replay and invalidation without conflating them with reuse.

**Proposed.** Run required front-end checks, `make test` and `make suite` for
implementation; compare census coverage under repository policy. These are
controls of the trusted boundary; the saved experiment does not discharge them.
## CPU accounting and expected gain

**Cited.** [stages.mts](../../pipeline/stages.mts)
accounts for compiler lifetime CPU near process release. Cross-attempt compiler
lifetimes require a different measurement boundary.
**Proposed.** Track the live compiler set via `compiler-processes.mts`; sample
user/system CPU at attempt start and end, adding deltas to Node's delta.
New processes start at zero; ending processes contribute their final sample
exactly once before release. Use generation identities against PID reuse.
Include validation/cleanup, avoid nested double counting and report missing
samples as unavailable. Check totals against independent lifetime deltas through
replacement and failure. Memory high-water marks describe compiler lifetime;
replay retains stored execution measurements and reports replay overhead apart.

**Conjectured, illustrative scenario only.** Suppose removable declaration
setup is 30% of the census's 1,424 s parse CPU, with zero parser saving and
zero assumed query/lowering saving. Gross saving is 1,424 × 0.30 = 427.2 s;
remaining parse CPU is 996.8 s and total CPU is 2,421.8 s, a 15.0% reduction
and 2,849 / 2,421.8 = 1.18× CPU throughput. The 30% is an assumption, not a
measured class-weighted census fraction. Warm-up, validation, restoration and
eviction reduce net gains. The experiment's 46–48% result includes excluded
parser reuse and cannot predict this proposal's gain or wall time.

**Proposed.** Measure declaration-only reuse with this predicate: phase CPU,
validation/restoration cost, openings/replacements, memory, wall time and
coverage. Measure replay separately. Pursue shared collection/lowering only
if its repeated work dominates after reuse. Per-unit verdicts require complete
unit inventory, conservative initialization/dependencies, terminating refusal
states and a safety theorem preserving `DocumentSafe`'s quantified guarantees.
## Trust boundary

**Cited.** [DocumentSafe and checkJson_safe](../../lean/Verification/Source/Claims/Json.lean)
connect whole-document checking to modeled safety; source fidelity and native
contracts are separate trusted boundaries.
**Proposed.** Session lifetime, project/overlay restoration, cache validity and
observation propagation are cross-request front-end obligations. Extraction,
certification and verdict assembly retain their interfaces and proof duties.
File-front/per-unit work needs separate review; cross-store certificate sharing
requires checked correspondence of equations and assumptions. Independent
store extension needs interpretation preservation; closure acceptance alone
does not establish module composition.
