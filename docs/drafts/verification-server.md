# Draft pre-plan: the verification server

A draft kept for a later decision: neither accepted nor rejected by the owner (2026-10-22). Its decisions D1–D7 are open. Astra passed it as a design on its fifth review round; nothing of it is implemented.


Design only. Base: TScert main at e9dfc1a. Measurements carry their source;
everything else is a decision or a stated obligation.

## 0. Goal and measured motivation

One mechanism verifies a set of files: it parses each requested file once,
gives one outcome per code unit, executes only the stages whose keys miss,
runs independent stages in parallel, and keeps its memory in the stage
store. It replaces the census's slicing (`dev/census.mts`), the case
runner's pool (`pipeline/run-cases.mts`), `verify-source.mts`'s worker pool
and monolithic `check()`, and `make check`.

Measured (census records under `$TMPDIR/tscert-census/2db902ca8b7b`):

- Census at e9dfc1a, `TSCERT_STEP_LIMIT=600`: 436 slices of 37 files,
  102,025 slice lines; 529 s wall, partly replayed. Executed: parse 250
  invocations, 3,992 s (p10 0.76 s, p50 10.9 s, max 87 s); search 164,
  1,804 s (p50 0.63 s, max 123 s); check 90, 222 s (p50 0.24 s, max 38 s);
  lower, propose, assemble and explain together under 70 s.
- Census at 6e33f39, fully replayed: 115 s wall; 139 verified, 131
  unsupported/source, 58 unsupported/proposal, 87 unverified/search, 20
  timeouts.

A slice's parse costs the project load whatever its size (p50 10.9 s for
slices of 14 lines). Parsing each file once makes 37 parses of `tools/`
where the census makes 436; checking each unit once removes the overlap of
slices (101,589 slice lines over 26,404 lines of `tools/`).

## 1. The unit and its outcome

### 1.1 Units

A **unit** is what Lean already certifies as one plan (`FunctionPlan`): a
top-level function declaration, the module initialization (constants,
cells, classes with their members, enums, top-level statements, in source
order), or a unit of a module run (`Fragment.modules`, the certified-import
modules parsed with the importer). Its identity is (module location, name,
name position), unique as `extractPlans` requires today.

### 1.2 The file front and the unit extraction

Today `extractPlans` (Claims/Extraction.lean) does two things: a **file
front** that reads the whole Fragment and claims (`planImports`,
`equationFront` with its gates and the declaration equations, the module
environment `moduleFunctions`, `moduleConstants`, `classSelves`, the
generic instances, `checkInitializationOrder`, `sourceClasses`), then a loop
extracting each unit, threading one equation store through all units.

The design splits the front's failures by owner and makes the loop per
unit. A failure of the front is either **document integrity** (a wire or
decoding error, a duplicate identity, a claim at a site no unit owns, a
claims document for another Fragment) and refuses the file, or it is
**owned**, and becomes a located result in `Front` instead of a throw:

- each declaration-graph item (definition, written application, value,
  symbol) lowers to its own `Except`: a failed item is absent from the
  front's store and recorded with its reason (today `lowerSource` lowers
  every written application up front and one failure refuses the file);
- each unit's annotation reading, its claims (present, matching its
  identity; the global "function claim count mismatch" becomes per unit),
  and for the initialization `checkInitializationOrder` and its claims;
- each module value of the environment (`moduleFunctions`,
  `moduleConstants`, `classSelves`) is an `Except` already
  (`ModuleValue`'s `.error`), kept;
- each qualified read (`qualifiedRead`, `sameReading`) is an `Except`; a
  failed read is a **withdrawal request** (§2.3).

A unit's extraction that reaches a failed item, a failed module value or a
failed read is refused with that item's reason and location. The item
failures are thus owned by every unit that reaches them, through the same
reachability that lowering follows, and by no other unit.

Then:

```
fileFront : (ast claims : Json) → fileKey → Except String Front
extractUnit : Front → UnitId → Except String (FunctionPlan …)
```

`extractUnit` starts from the front's store (`d.types`), never from another
unit's: a unit's extraction sees what the front computed and nothing any
other unit's extraction added. Every input a unit's extraction reads beside
its own body and claims is a field of `Front`, computed from the whole
Fragment and claims; this is the only channel between units (enforced by
the type of `extractUnit`).

There are no unit documents: search and check take the file's Fragment and
claims, as today, and a unit identity. Correspondence between what a
caller assumes of a callee and what the callee's check certifies is then
the correspondence today's whole-document check relies on: both readings
come from one `Front` of one (Fragment, claims) pair. A caller reads `g` at
`moduleArrow g (footprintOf g) (onThrowOf g)`; `g`'s own request is
extracted against the same claim entry. The verdict assembly (§1.5)
combines only checks of one (Fragment, claims) pair, so the pair, and
hence the front, is the same for every edge.

### 1.3 Dependencies

`Front` also computes each unit's **dependencies**: the same-file units
whose code or whose established values the unit's lowered body mentions
directly, after the parser's shadow renames (the closure is §1.5):

- a module function `g` whose name the unit's body mentions → unit `g`;
- a module constant, cell, class or enum it mentions → the initialization;
- a qualified import `M#g` it reads → the module-run unit `M#g`;
- for the initialization, every function its statements mention.

Mentions over-approximate reads, as `checkInitializationOrder` already
relies on ("Mentions over-approximate calls, so this refuses some safe
orders and admits no unsafe one"); a unit's extraction resolves a module
value only through the front's environment, by name. A value reaching a
unit as an input (a parameter of a class type, a callback) is an input at
its declared type, as in every unit's theorem today: the caller's
obligation, part of the open [module composition](../../WORK.md#module-composition).
This is also what a census slice included: the declarations its function
mentions.

### 1.4 Per-unit search and check, and the headline theorem

- `--produce-unit ast claims snapshot evidence unit depth` (search,
  untrusted): `fileFront`, `extractUnit`, freeze, search. The shared answer
  cache of `produceDocument` becomes per unit.
- `--check-unit ast claims snapshot evidence unit` (check): `fileFront`,
  `extractUnit`, freeze, the exhaustive `FunctionPlan.certify` into
  `CertifiedPlan`, decode, `checkRequests`. On success it prints
  `accept`, then `depends:` and the unit's dependencies as `Front`
  computed them.

The headline theorem becomes `SourceClaimJson.checkUnitJson_safe`:

```
theorem checkUnitJson_safe
    (h : checkUnitJson ast claims fileKey unit evidence budget = .ok deps) :
  ∃ front, fileFront ast claims fileKey budget = .ok front ∧
    deps = front.dependencies unit ∧
    UnitSafe front unit evidence budget
```

`UnitSafe` is today's `DocumentSafe` for one plan: it crossed
`certifyPlans`, its certified request is safe at every admitted assignment
of its parameter rows for every environment meeting its inputs (`EnvOk`
over parameters, the front's module values, imported, ambient and host
values), and stays within its footprint where it claims one. The premise is
the exact CLI success of `--check-unit`. `checkJson`, `checkDocument`,
`checkModules`, `checkJson_safe`, `produceJson`, `--check-source-claims`
and `--produce-source-claims` are deleted: one acceptance path, one
headline theorem, which `AxiomCheck.lean` checks.

The theorem fixes `deps` to the front's dependencies of the unit. That the
front's dependencies include every same-file unit the unit's code reaches
by name is a reviewed property of `Front.dependencies` (a mention scan over
the unit's lowered body, as `checkInitializationOrder`'s), stated in the
trust surface beside source extraction. That the printed list is `deps`
is the CLI's serialization, reviewed with `RequestCli.lean`.

### 1.5 The verdict of a unit

A unit's **own result**: accepted (its check printed `accept`); unsupported
(the gate, the lowering, the producer, the front or its extraction refused
it, located); unverified or exhausted (search or check); error (a tool
failure or a timeout).

A unit is **verified** when its own result is accepted and every unit of
its dependency closure is accepted, the closure taken over the `depends`
lists of the accepted checks of one (Fragment, claims) pair. Otherwise it
is **blocked** by the first unit of the closure (breadth-first, in
`depends` order) that is not accepted, with that unit's own result. A cycle
is closed over like any edge.

The **verdict assembly** (`pipeline/verdicts.mts`, new trusted code, about
40 lines) computes this. Given the file's final Fragment and claims bytes,
it obtains each unit's check through `invokeProcess` on exactly those bytes
and that unit's evidence, with the request's pinned verifier (§6.1 B3), and
reads `depends` only from those judgments. It reads no result any other
way.

In the model, a verified unit's certified request is safe assuming its
inputs, the front's module values and the external values meet their
types, and each same-file module value its code mentions is established by
an accepted unit of the same front, under the same assumptions. A theorem
composing these into the module's whole execution remains open work, as
for today's per-unit obligations.

### 1.6 Module initialization

The initialization stays one unit. `checkInitializationOrder`, which reads
every function body, stays in the front; its refusal refuses the
initialization unit, located, and leaves the functions' results alone. A
later top-level statement can change what an earlier constant holds (a
write into its object, a call), so no prefix of the initialization
establishes a constant's type by itself; splitting the initialization by
statement would need an analysis the model does not have.

### 1.7 What a refusal in one unit can and cannot reach

1. **Parser facts over the source text** (name binding, shadow renames,
   block types, globals, strictness, a local `let` nothing writes read as
   a `const`; every module-level `let` stays a cell whatever writes it,
   `fragment-statements.mts`) are computed over the whole source tree, refused bodies
   included (§2.1).
2. **Declarations** are collected only from the roots of units not refused;
   a refused unit contributes none, and a refusal while collecting for a
   unit refuses that unit (§2.1, rounds).
3. **Lean whole-file analyses** that read other units' bodies
   (`checkInitializationOrder`, `qualifiedRead`'s `assignsStmt` stability
   scan, `sourceClasses` and `genericClassNames` of the initialization)
   read a refused unit as **unknown**: it mentions and writes every name,
   and a refused initialization declares no class. Each analysis is then
   conservative: the initialization reaching a refused function is refused
   by order, a module with a refused unit offers no qualified read, an
   empty class list admits fewer grow sites. The fast check lists every
   reader of the Fragment's `functions` and `init` outside `extractUnit`'s
   own unit and requires each to be one of these.
4. **Equations**: each unit is extracted from the front's store.
5. **Claims** are proposals: a unit lacking a claim it needs is refused by
   its own extraction.
6. **A refused unit's interface**: its written signature still reaches its
   callers through the front, so they extract, and are blocked by it; a
   refused unit whose signature is refused has no module value, and a
   unit mentioning it is refused by its own extraction ("reads `g`, a
   refused unit"), never resolved to another binding (the front keeps the
   name bound to the refused unit).

## 2. Stages and their granularity

| Stage | Granularity | Input (key, beside implementation) | Output |
| --- | --- | --- | --- |
| parse (observed, in-process) | requested file | as today | Fragment: per-unit lowerings, refused units |
| TypeScript diagnostics | file, on demand | as today | display only |
| lower (`--lower-control-flow`) | file | Fragment | flow; per-unit plans or refusals |
| propose (producer) | file, withdrawal loop | as today | claims; per-unit refusals |
| assemble claims | file | as today | claims |
| search (`--produce-unit`) | unit | Fragment, claims, unit, depth, rounds | evidence or refusal |
| explain | unit, on failure | as today, for the unit | display only |
| check (`--check-unit`) | unit | Fragment, claims, evidence, unit, rounds | `accept` and `depends`, or refusal |

Search and check are per unit: their cost is heavy-tailed (search max
123 s, check max 38 s, census at e9dfc1a), and a per-file invocation would
let one unit's timeout take the file. Each per-unit invocation repeats the
file front (decoding, the declaration equations): its cost per unit is to
be measured before merge (§5.5); if it dominates, D4.

### 2.1 The parser: per-unit refusal by rounds

Today a parse collects the declaration graph over the whole file
(`collectDeclarations`: every local type rooted, whole-source scans such as
`outsideViews`, contextual parameter types, computed types, private keys,
intrinsic selections), then lowers, and the gate and the collector refuse
by throwing, with shared state (`Gate`, the collector's tables). The
design keeps that order and that throwing, and scopes both to a set `R` of
**refused units**, starting empty. The parse keeps one TypeScript program
and checker per file and one declaration session (the compiler
`withProject` opens, today once per `collectDeclarations` call) for all
rounds.

1. Over the source tree, compute the binding facts of §1.7(1); a refusal
   here (a syntax error, a project that is not strict, a top-level form
   that belongs to no unit) is whole-file.
2. A round, with fresh gate and collection state over the same session,
   for the units not in `R`, in three passes:
   - **gather**, unit by unit with that unit as the **current owner**: its
     use contributions (the types, values and symbols its signature and
     body name; its body's queries such as `outsideViews`; its contextual
     types; the members and overloads of a global it selects; the
     prototype and host-family uses it makes), each tagged with its owner;
   - **finalize** the shared entries from the union of the gathered
     contributions (a global's one definition holding every selected
     member, the selected overloads, the prototype contracts, the
     host-family tag selection over the candidate-module closure), each
     shared entry with the owners that contributed to it;
   - **lower** the units, unit by unit with that unit as the current owner.

   A unit in `R` contributes no use, no scan and no lowering; it contributes
   its identity and, where its signature gathers, finalizes and lowers on
   its own, its signature: the signature's uses are gathered into the
   round's shared passes like any unit's, under that unit as owner, and
   lowered against the round's final tables (one symbol and private-key
   numbering for the whole Fragment); a refusal in them leaves the unit
   without a signature.
3. A refusal raised while a unit is the current owner adds that unit to
   `R`. A refusal while finalizing a shared entry adds the contributor
   whose contribution the failing step was processing, else the last
   contributor in source order. Either starts the next round. A refusal
   raised with no current owner and no contributor is whole-file; the change
   makes every whole-source scan of the collector run per unit, so that
   this happens only for the forms of step 1.

Refusing a unit is always sound; a refusal blamed on a contributor that
was not its cause costs that unit's coverage, and the next round shows
whether the failure persists without it. Shared entries are computed from
every unrefused unit's uses, so a unit's equations can depend on what
other units of the file select (a global's members, a host-family
selection): this is the file's own declaration graph, as today.

Each round adds one unit, so the loop ends within the number of units plus
one. Every round starts from fresh state, so the Fragment is the last
round's by construction. A refusal reaches every unit whose roots reach
its cause (an item that fails for `u` fails again, in a later round, for
every other unit reaching it, each joining `R` in turn), and possibly a
contributor blamed by the finalize fallback, which the record marks as
fallback attribution: refusal is conservative, not exact.
Controls: two units selecting different members of one global (`Math.max`,
`Math.min`), in both source orders, beside an unrelated refused third
unit: both verified, one `Math` definition holding both members. A local
type no unit reaches is no longer collected (today every local type is a
root): its errors no longer refuse the file.

Cost: one TypeScript program and one declaration session per parse, one
collection and lowering per round. The rounds per file, their share of
parse time and the compiler openings per parse are recorded and reported on
`tools/` (§5.5).

`evalForms`, which scans the whole file, becomes a step-2 check attributed
to the unit holding the `eval`. Each refusal site of `fragment-parse.mts`
and its parts is classified as step 1 or step 2 in the same change; a
step-1 refusal names why it belongs to the file.

The imported modules a parse lowers for certified imports
(`parseModules`) are lowered with the importer's host-family selection,
inside its parse; a module refused by the gate is left out, as today.
Their units are therefore per importer: two importers of `m.ts` lower and
check `m.ts`'s units twice. This is a stated cost (D6).

### 2.2 The producer

The OCaml producer proposes for every unit it can and records per unit it
cannot a located refusal (`refusals` in the claims wire, typed in
`tools/source-claims.mts`, display only). Exit status 2 stays for a
document it refuses whole. A unit it skipped has no claims; its own
extraction refuses it.

### 2.3 Certified imports and withdrawal

A qualified read of `M#g` stays eligible exactly as `planImports`'s
`qualifiedRead` and `sameReading` decide today, in the front. The
withdrawal loop stays per file. A read `M#g` is withdrawn when (a) the
front records it failed (a withdrawal request, §1.2: ineligible, readings
that differ, a module offering no read), or (b) a unit reading it is
blocked through the module-run unit `M#g` (its own result or its
closure's). Either is structured (the read's identity), never parsed from
a diagnostic's text. The file is then proposed,
assembled, searched and checked again; the next round's checks are of a
new claims document, so no judgment of a withdrawn round enters a verdict
(the assembly takes one pair). Each round withdraws a read not withdrawn
before; the loop ends. Cyclic imports keep today's rule (a read closing a
cycle is read at its ordinary signature).

### 2.4 Incrementality

There is no invalidation logic: every stage's key is its inputs' content,
the scheduler runs each file's chain from its bytes, and a stage replays
when its key hits. A change therefore invalidates exactly what its inputs
reach:

- an edit of file `F` changes its snapshot and Fragment: every stage of `F`
  misses, every unit of `F` is searched and checked again. Parses of files
  importing `F` miss through their observations; their later stages miss
  only where their Fragment or claims bytes changed.
- an edit of a keyed front-end module misses every parse; a file whose
  Fragment and claims bytes are unchanged replays all its searches and
  checks.
- an edit of the verifier or producer misses every stage of that
  executable.

Within an edited file nothing is reused: per-unit keys include the whole
Fragment and claims. D4 states what reuse inside a file would take.

### 2.5 The scheduler

Per request, in memory, a DAG: per file parse → lower → propose → assemble
→ per unit search → check; per requested unit a verdict, ready when its
closure's checks have settled; the withdrawal loop adds rounds. In-flight
invocations are de-duplicated by stage key within the process. The DAG
holds no results; results live in the store and the request record.

One pool per client process, one worker per core: forked Node processes
that run in-process stages (keeping loaded modules) and spawn process
stages; retirement on observation inconsistency as today
(`processInconsistency`, `processRetirement`).

## 3. Interface and lifecycle

### 3.1 Library, not daemon (D1)

The server is a library, `pipeline/verification.mts`, with a CLI,
`pipeline/verify.mts`. A client is one process that runs the scheduler and
its pool, and exits when its request is answered. The store is the only
state shared across clients, runs, worktrees and crashes. A daemon would
hold orchestration and the trusted verdict assembly in memory while the
checkout changes under it; a library loads the checkout's code per request.

### 3.2 Requests

```
verify({
  files: { path: string,
           project?: string,            // a tsconfig or directory, as --project
           typescriptErrors?: boolean,  // display, as today
         }[],
  units?: string[],           // restrict search and check to these units' closures
  stepLimitMs?: number,       // default TSCERT_STEP_LIMIT's
  retryTimeouts?: boolean,    // default TSCERT_RETRY_TIMEOUTS's
}, events?: (e: Event) => void): Promise<RequestRecord>
```

Each file carries its own project and display options, as each case does
today; they are inputs of its parse as today.

### 3.3 Records

`RequestRecord`: source identity (commit, dirty paths), policy (store, step
limit, retry flag), pinned verifier and producer digests, start, elapsed;
per file: snapshot digest, whole-file outcome or null, withdrawal rounds,
units. Per unit: identity, own result (status, phase, first detail line,
location), verdict (verified, or blocked by a named unit), `depends`, and
the ordered references to its stage invocations (the census's
`InvocationReference`). It replaces the census record; `report <before>
<after>` compares records by unit identity (`file#name`).

### 3.4 Clients

- `make check FILE=f.ts [PROJECT=d]`: one file, a per-unit table.
- `make suite`, `run-cases.mts <pattern>`: one request over the cases'
  files; each case's expectation is checked against the file outcome
  (§5.2).
- `make census [DIR] [FILES] [FUNCTIONS]`: the directory's files in place,
  one request (`FUNCTIONS` → `units`). `SHARD` goes.
- `pipeline/test.mts` controls: forge at the Fragment, claims or evidence
  level and run the remaining stages through the library's per-file chain.
- Agents: the CLI, or `verify()` from a script.

### 3.5 Concurrency across clients and worktrees

Different worktrees have different code, hence different keys; they share
entries where code and inputs agree. Two clients requesting one key may
both execute it; publication is atomic and duplicate computation is
permitted (the store's rule; D5). Each client's pool is sized to the
machine; concurrent clients oversubscribe it, as concurrent runners do
today. No machine-wide cap is promised (D5).

### 3.6 Crash and restart

A killed client leaves complete published entries and abandoned temporary
directories (`make clean-store`, as today). A rerun replays every finished
stage and every timeout at a limit at least the requested one.

## 4. Policy

- **Limits.** Each process stage has the step limit (60 s default); the
  parse is bounded by the worker deadline (4× step, as today), its expiry an
  error of the file. A unit's timeout is its own result; its dependents are
  blocked by it.
- **Retries.** As today: a recorded timeout at a limit ≥ the requested one
  replays as a timeout; a larger limit or `retryTimeouts` executes again.
- **Priorities.** Files in descending expected parse time; then units of
  requested closures first, in descending expected search time (the last
  attempt's elapsed time for the same unit identity, from attempt records,
  outside every key; unknown first).
- **Cancellation.** Aborting a request kills its running process stages
  and workers; their attempts are recorded `interrupted`; finished entries
  stay.
- **In progress.** Events in order: `file-parsed` (units, refused units),
  `unit-own` (tagged with its withdrawal round), `unit-verdict` (only
  once the file's withdrawal loop has reached its fixed point and the
  unit's closure has settled), `file-done`,
  `progress` (counts every 10 % or 10 s), printed by the CLI on standard
  error.

## 5. Migration

### 5.1 Deleted

- `dev/census.mts`'s slicing and directory copy (`slicesOf`, `prepare`,
  `writeStable`), `invocationsOfRequest`, `--shard`.
- `verify-source.mts`'s pool (`checkApart`, `dispatch`, `--serve`) and
  `check()`; the per-file chain moves to the library. What the controls
  import (`readFragmentFile`, `readClaimsFile`, `sourceKey`) moves with it.
- `run-cases.mts`'s `pooled`.
- Lean: `checkJson`, `checkDocument`, `checkModules`, `produceJson`, the
  whole-document `produceDocument`, `checkJson_safe`, `--check-source-claims`,
  `--produce-source-claims`; the threaded-store loop of `extractPlans`.
- The parser's whole-file `gate:` outcome for unit-local refusals.

### 5.2 Kept, and the file outcome

- The stage store, its keys, observed stages, timeouts, publication.
- `cases.mts`: each case keeps its expected status, phase and diagnostic,
  now of the **file outcome**: a whole-file refusal if any; else verified
  when every unit is verified; else the own result of the first unit not
  accepted, by phase (source, proposal, search, check), then source
  position. This is the order today's run fails in; each expectation that
  changes is inspected for its cause before it is updated.
- The unkeyed list gains `pipeline/verification.mts` (orchestration),
  `pipeline/verify.mts` (CLI), each with its reason, and
  `pipeline/verdicts.mts` (computes no stage's result; trusted, §6).

### 5.3 The census's meaning and the one-time comparison

A function's census result is its unit's verdict on the file: its code and
the code of every same-file unit it mentions, transitively, accepted. This
is today's slice result except where the slice was another program or
another search:

- the slice's initialization held only the declarations its function
  mentions; the file's holds all of them (§1.6);
- the parser's file facts were the slice's (bindings, globals, block
  types, shadow renames over the slice's text);
- search is per unit, without the shared answer cache across a slice's
  units, so an exhausted or timed-out outcome can differ with no logical
  difference;
- shared declaration entries (a global's selected members, overloads,
  host-family tags) are selected by every unit of the file, where a
  slice's were selected by the slice's units;
- the slice's dependencies were lexical (every identifier, property names
  included), the server's are the lowered body's mentions after shadow
  renames, so a slice could include, and be refused by, a function its
  code does not reach.

Before the old census is deleted, one comparison runs both at the same
commit and classifies each differing function as: initialization, file
fact, search resource (exhausted or timeout on one side only), lexical
over-approximation of the slice, declaration selection (a shared entry or
host-family selection differing because other units of the file select
more, the differing contracts recorded), or defect (anything else, fixed before
merge). The script is research code, retired
in the same branch.

### 5.4 Controls

Every control forging a Fragment or claims document forges it for the file
and runs search and check through the library: the forged-claim controls
keep testing extraction and claim association. The cold and warm replay
control covers `--produce-unit` and `--check-unit`. New controls are §6.2.

### 5.5 Targets, measured once before merge on the same machine

Baseline: today's census at the merge base with a fresh store and
`TSCERT_STEP_LIMIT=600`, and today's `make suite`.

- Cold census: executed parses = requested files (37 for `tools/`);
  executed searches and checks = units each, plus withdrawal rounds;
  wall time ≤ 1/3 of the baseline.
- Warm census, nothing changed: ≤ 30 s wall, every stage replayed.
- After a commit editing one `tools/` file: searches and checks executed
  only for that file's units and for files whose Fragment or claims bytes
  changed (the record lists each with the reason its key missed).
- The file front's share of per-unit search and check time, the
  re-lowering rounds' share of parse time and the compiler openings per
  parse (one program, one declaration session), reported; either above 25 %
  opens D4 or a revision of §2.1.
- `make suite` cold and warm no slower than today's.

## 6. Trust boundaries and adversarial completeness

### 6.1 Boundaries added or changed

| Boundary | Covers | Refuses |
| --- | --- | --- |
| B1 `checkUnitJson_safe` (proved) | safety of the accepted unit's request from the file's front, and `depends` = the front's dependencies of the unit | anything but this exact CLI success |
| B2 The front and `Front.dependencies` (trusted extraction) | §1.2–1.3, §1.7(3): one front per (Fragment, claims); dependencies over-approximate the same-file units a unit's code reaches by name; refused units read as unknown | a unit reading a name the front binds to a refused unit |
| B3 Pinned executables (store) | a process stage runs the bytes its key names: the verifier and producer are copied once per request into a content-addressed store location named by their digest, validated on copy, spawned from there; their linked libraries must lie on the sealed system volume (`/usr/lib`, `/System`), which `executableIdentity` checks, else the stage is not replay-eligible and its judgment is not used by the assembly; a digest mismatch of the pinned copy after execution makes the attempt a tool failure: its judgment is discarded, not only unpublished | a binary or library replaced between binding and spawn |
| B4 Per-unit parsing (trusted parser) | §2.1: file facts over the whole tree; each round's Fragment from fresh gate and collection state; a refused unit contributes its identity and signature only; every collector scan runs per unit, under its owner | a refusal with no current owner: whole file |
| B5 The verdict assembly (trusted, node) | verified = own accepted ∧ closure accepted, every judgment obtained in this request by `invokeProcess` on one (Fragment, claims) pair with the pinned verifier | a judgment of another pair, round, build or request |
| The stage store | unchanged otherwise | as today |

Trust-surface changes: the row "A replayed check …" is restated over
`--check-unit` and B3 (today `bindProcess` digests the program at its path
and `executeProcess` spawns that path, so a replacement between the two
runs other bytes under the key); the source-extraction row gains B2; the
parser row gains B4; a new row states B5.

### 6.2 Bypass attempts that must fail (each a case or control)

1. **Stale callee signature.** Edit `g`'s annotation; `f` calls `g`. The
   file's Fragment changes, so every unit's search and check key misses;
   the assembly reads `f` and `g` from the one pair. Control: warm store
   from the old version; the record shows `f` and `g` executed.
2. **Uncertified callee footprint.** The producer proposes a footprint for
   `g` that `g`'s check refuses; `f` relies on it and is accepted alone;
   `f` is blocked by `g`. Case.
3. **Refused callee.** `g`'s body holds a gate-refused form; `f` calls `g`;
   `h` does not. `g` unsupported, `f` blocked, `h` verified. Case.
4. **Refused unit's writes.** `let x: number | string` at module level,
   written only in `g`, whose body is refused; `f` narrows `x`, calls a
   parameter callback, then uses `x` as a number: `f` not verified (`x`
   stays a cell). A regression case: module `let`s are cells today, and
   must stay cells when their writer is refused.
5. **Declaration collected for a refused unit.** `g` refused while
   collecting type `T`; `h` uses `T`: `h`'s outcome equals its outcome in
   the file without `g`. Case pair.
6. **Initialization order through a function.** `function g(): number {
   return c; } const a: number = g(); const c: number = 1;`: the
   initialization is refused by order; a function not mentioning `a`, `c`
   or `g` is verified. Case. With `g` refused by the gate: the
   initialization, reaching an unknown unit, is refused. Case.
7. **Unrelated `eval`.** `eval` in `g`; `f` unrelated: `g` unsupported, `f`
   verified. Case.
8. **Binary replaced between binding and spawn.** A control replaces the
   verifier at its build path with the mutation verifier between
   `bindProcess` and `executeProcess` (an injected hook in the control):
   the pinned copy runs; no entry is published under a digest the run did
   not execute.
9. **Mixed rounds.** A forged module-run failure triggers withdrawal; the
   first round's accepted checks never enter a verdict. Control.
10. **File edited during the run.** The parse reads a snapshot; the record
    names its digest. An import edited during the parse is caught by the
    observed stage's validation. Existing observed-stage controls.
11. **Two clients racing.** Two processes request one file at once: equal
    verdicts; one entry per key. Control in the store's tests.
12. **Initialization refused.** A refused top-level statement unrelated to
    `c`; `f` reads `c`: blocked by the initialization; `k` mentioning only
    functions: verified. Case.
13. **Mutual recursion, one side unverified.** `f`↔`g`, `g` unverified:
    neither verified. Case.
14. **Unit dropped.** The record lists the file's inventory (the
    Fragment's units and refused units) and, separately, the scheduled
    units (all, or the requested closures); every scheduled unit has an own
    result, else the file is an error; an unscheduled unit is reported
    `unrequested`. Control forging a lost search result.
15. **Evidence for another unit.** `g`'s evidence given to `f`'s check:
    refused, or evidence for `f` (any evidence that checks is evidence).
    The evidence-mutation controls, per unit.
16. **Replayed timeout.** A unit whose search timed out has no evidence, is
    not accepted, and blocks its dependents. Control.
17. **Shadowed module name.** `f` declares a local `g` shadowing the module
    function `g`, which is refused: the parser's shadow rename makes `f`'s
    local another name, so `f` does not depend on unit `g` and is verified
    on its own merits. Case. Its contrast, `f` calling the module `g`:
    blocked.
18. **Declaration reached only by one unit.** An imported type the
    collector cannot collect, used only by `g`: `g` unsupported with its
    reason, `h` verified; the same type used through a local alias by `h`:
    `h` unsupported too. Case pair. And an unreviewed member read in `g`'s
    body (`outsideViews`, e.g. `p.getCompilerOptions()` on an imported
    compiler `Program`): `g` unsupported, an independent `h` verified.
    Case.
19. **Written application failing a bound.** Append an unrelated function
    to `invalid-collections-record-collection.ts`: the application's
    failure refuses the units reaching it, the appended function verified.
    Case.
20. **Withdrawal from the front.** Imported module `m` with eligible `g`
    and gate-refused `h`; the importer's proposal qualifies `g`: the front
    records the read failed, the read is withdrawn, the importer verified
    at `g`'s ordinary signature where that suffices. Case.

## 7. Decisions for the owner

- **D1. Library or daemon.** Recommend the library (§3.1).
- **D2. Initialization as one unit** (§1.6). Recommend yes; the comparison
  (§5.3) measures what it costs.
- **D3. Class members as units.** A refused member refuses the
  initialization and blocks every unit mentioning a constant, class or
  enum. Recommend deferring until the comparison measures it.
- **D4. Reuse inside an edited file.** Unit documents carrying only what a
  unit's extraction reads (its body and claims, the front's environment
  entries it mentions, the declaration tables kept whole, positions rebased
  to the unit), with interface contracts compared by bytes between the
  assuming and the establishing unit. It saves the front's repetition and
  re-searching unchanged units of an edited file, at the cost of a trusted
  projection and a byte-level correspondence check. Recommend deferring
  until §5.5 measures the front's share and the edit loop.
- **D7. Fallback attribution** (§2.1 step 3). When finalizing a shared
  entry fails without a processing contributor, the last contributor is
  refused. Recommend accepting it and counting fallback attributions in the
  census record; a precise attribution would finalize each contributor
  alone.
- **D5. Cross-client coordination** (in-flight markers, a machine-wide
  slot cap). Recommend no: duplicate computation is correct, one census is
  one process, and a crash-safe lock with atomic reclamation is machinery
  whose only gain is scheduling.
- **D6. Imported modules checked per importer** (§2.1). Recommend keeping
  it: a module's lowering depends on the importer's host-family selection;
  sharing would need module lowering as its own observed stage keyed by
  that selection.
