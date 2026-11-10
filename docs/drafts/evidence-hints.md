# Draft: earlier evidence as a proposal to the current check

A design for the time a check takes after a change of the Lean verifier:
evidence an earlier verifier build found for a unit's exact inputs is
offered to the current build's check before any search, and the unit is
searched only where that evidence is not usable or the check refuses it.
Base: branch `evidence-hints` at 3303c669. Claims are labelled **read** (in
the code or document named), **observed** (with the run), **reviewed** (by
an independent review of the code named), **estimated** (arithmetic on
observed numbers) or **conjectured**.

## The existing mechanism this extends

**The stage store** ([STAGE-STORE.md](../STAGE-STORE.md)), and within it
the **references of observed stages**: an index under a pre-key whose
entries name finished entries and are only candidates, each validated by
its reader ([observed stages](../STAGE-STORE.md#observed-stages)). Its
parts this design uses, all **read**:

- **Keys.** A process stage's key is the digest of its manifest: stage,
  code, runtime, implementation (the executable and its libraries), runner,
  argument vector, environment, exit protocol, input digests by role, output
  roles (`bindProcess`, `pipeline/stage-execution.mts:752–767`;
  [keys](../STAGE-STORE.md#keys)). A search's inputs are the slice, the
  slice's claims and the qualified reads; its arguments the depth and the
  unit's members (`verifierCall`, `stage-execution.mts:661–664`). A check's
  inputs are the Fragment, the assembled claims and the evidence document
  (`stage-execution.mts:665–667`).
- **References.** `Store.reference` writes an empty file
  `observed/<stage>/<pre-key>/<key>` once; `Store.candidates` lists a
  pre-key's keys newest first (`pipeline/stage-store.mts:500–534`). Eviction
  and cleaning recognise the `observed` root by name
  (`stage-store.mts:821, 842, 854, 912`) and remove a reference with its
  entry ([location and size](../STAGE-STORE.md#location-and-size)).
- **Units of a check.** Each unit is searched over its slice
  (`--produce-unit`); one check (`--check-units`) reads the file's front and
  every unit's line; a module run's unit lines are checked together
  (`--check-module`) ([units of a check](../STAGE-STORE.md#units-of-a-check)).
- **Replay and trust.** A replayed check trusts the store's binding of a
  result to its exact manifest; acceptance is the check's verdict
  ([replay and trust](../STAGE-STORE.md#replay-and-trust)). Search is
  replaceable and untrusted ([search](../DESIGN.md#search)).

The design generalizes the reference index to a second root, `proposed`,
for search stages under a key that leaves out the identity of the program
that searched, and adds one fallback to the orchestration; no stage, wire
field or trusted part.

## The present cost

- **Observed** (pretext, 2026-11-10): a cold check of `measureAnalysis`
  takes 105–130 s: its own search about 25 s, its check about 4 s, and
  about 88 s the searches and checks of the modules it imports (72 module
  searches, one of them 42 s). Five pretext files take 661 s after a
  Lean-only change and 126 s after a producer-only change.
- **Read**: after a Lean change every verifier stage misses, its
  implementation identity in its key (`stage-execution.mts:752,759`).
- **Estimated**: where the slices and claims are unchanged, reuse replaces
  `measureAnalysis`'s 25 s search by nothing and its module searches by
  module checks. Taking the file's own check-to-search ratio for the
  modules gives about 12 s for the imported checks and 4 s for the file's;
  that ratio is not validated for the 72 module searches. What remains
  after the saving: the whole file's and every slice's lowering, the
  producer's proposals, the claims assembly and the import plans
  (`pipeline/verify-source.mts:423, 465, 493, 822, 951–993`), all verifier
  or producer stages that miss after the change that keys them.

## The design

### 1. The proposal key

For a stage `search` or `module-search`, the **proposal key** is the
digest of the manifest with four fields left out: `implementation`,
`code`, `runtime` and `runner`. Kept: `stage`, `argv` (the role names, the
depth, the members), `environment`, `protocol`, `inputs` (slice, claims,
qualified reads, by digest), `outputs`. The four left out identify what
produced a proposal, which bears on nothing accepted. Keeping
`environment` separates the mutation verifier's searches
(`TSCERT_TEST_MUTATIONS`, [controls](../STAGE-STORE.md#controls)) from the
verifier's. The key binds the claims; a key without them is an open
question.

### 2. The index

The store's reference index has two roots, `observed` and `proposed`,
each `<root>/<stage>/<pre-key>/<key>`, written and listed by one
implementation. Eviction accounts a reference of either root as an item of
the entry it names and removes it with that entry; cleaning removes both
roots.

### 3. The mode

Reuse is on only where `TSCERT_EVIDENCE_REUSE=1`; off, nothing is read
from or written to `proposed/`. The variable is outside every key, as
`TSCERT_RETRY_TIMEOUTS` is (`pipeline/stages.mts:134–136`). `make test`,
`test-all.sh`, `pipeline/test.mts`, `pipeline/run-cases.mts` and
`dev/census.mts` remove it from their environment, so their stages search;
the controls of reuse set it on the runs they start, each over a store of
its own. On, by the caller's choice: `dev/check-functions.mts` and
`verify-source.mts` by hand while iterating on Lean.

### 4. Publication

Under the mode, the orchestration references, under the proposal key, the
entry of each search whose units a check accepted: a search whose unit a
`--check-units` verdict accepts, or every search of a module run its
`--check-module` verdict accepts. A search that printed a `refused:` line,
ended at a limit, or whose unit was refused references nothing. A reused
result is never published under the current search key: the current key
holds only what the current search computed.

### 5. Lookup

Under the mode, a search invocation whose ordinary key misses, finished
entry and timeout observation alike, reads the candidates of its proposal
key, newest first, and takes the first whose entry is valid
(`Store.finished`) and whose stored manifest equals the invocation's with
the four fields left out. Its outputs are delivered as a replay's. The
attempt's execution is `reused`, its `replay` the entry's measurement, and
its `reusedFrom` the entry's key and implementation identity. No candidate
valid, the search executes.

### 6. Fallback

The pipeline uses a reused result only when it is a complete success: exit
0, no `refused:` line, and every evidence line carrying its unit name and
relocating to the document's symbols (`verify-source.mts:543–556`).
Anything else is a miss: the unit is searched with reuse off, and no tool
failure is raised by the candidate.

- **The file's units.** The check runs over reused and searched lines.
  Where it refuses units whose lines were reused, those units are searched
  with reuse off and the check runs again. A later check that refuses a
  reused unit, and any check with a reused line that fails as a whole (a
  refusal with no verdicts, a timeout, a memory limit or another tool
  failure), is followed by a search of every unit still reused and one more
  check with no reused line. At most three checks per round; the last one
  that runs has its verdicts reported, or its failure as a cold run's.
- **Module runs.** A `--check-module` refusal, or a failure, of a run with
  any reused line searches every reused unit of that run with reuse off
  and checks the run again: at most two module checks per run.
- A search that refuses or ends at its limit on fallback is that unit's
  outcome, phase `search`, as in a cold run.
- Every fallback of a round completes before the round's withdrawal
  decision (`withdrawal`, `verify-source.mts:812–819, 859–864`), so a
  refusal that names a certified import and withdraws it comes from
  searched evidence.

### 7. Visibility

`invocations.jsonl` shows each search attempt as `reused`, with
`reusedFrom`, or as executed or replayed; a fallback is an executed search
of the same manifest after a `reused` one. The outcome of a check with the
mode on carries `reused`, the number of its units whose checked evidence
was reused, a module run counting as one unit; `dev/check-functions.mts`
prints `reused <n> of <m> units`.

### 8. Concurrency and size

References are immutable files written with `wx`; two processes
referencing different entries under one key leave two candidates, and a
reader takes the newest valid one, so a race costs at most one check. A
reused entry is a use in the use log, so least recent use keeps it while
runs reuse it; it goes with its references, within `TSCERT_STORE_BUDGET`.

## The guarantee

**Read**: an accepted verdict is the current checker's on the current
claims and source: a unit is `verified` only from a verdict line of
`--check-units` with `accepted: true` (`verify-source.mts:797–798`) or of
`--check-module` (`verify-source.mts:852–853`), and the check's key binds
the current executable and the evidence document's digest
(`stage-execution.mts:665–671, 750–766`). **Reviewed**: the checker checks
the current relocation of the supplied evidence, which
`checkUnitJson_safe` covers (`Translate.lean:614–629, 703`).

A refusal that reaches the user comes from searched evidence: every
refusal of a unit or a run whose evidence was reused is followed by its
search with reuse off.

A run with reused evidence can differ from a run with the mode off in two
ways. It may accept a unit for which the current search finds no
evidence. It may keep a certified import a run with the mode off would
withdraw, and the claims proposed after that withdrawal then differ
(`verify-source.mts:859–874, 972–1014`). The outcome's `reused` count
says which runs these can be.

**Reviewed**: one unit's verdict in `--check-units` does not depend on the
lines before it. The translation target threaded through the lines holds
rounds and dictionaries derived from the document alone; a slice's own
refinement dictionaries are local and discarded
(`Translate.lean:58–82, 395–403, 501`). Earlier lines change the cost, and
so possibly a resource limit's outcome, which the fallback covers.

## Controls

Each registers with `control(…)` in `pipeline/test.mts`, names a fresh
store under `$TMPDIR` and sets the mode on the runs that need it; the
index's own tests are in `tests/stage-store.mts`.

1. **Two identities.** Evidence a verifier build stored is reused under a
   build of another identity: no search executes, the check executes and
   accepts, the outcome equals the first build's.
2. **Refused, then searched.** A referenced entry whose evidence the check
   refuses: the unit is searched, its verdict the searched one.
3. **Unusable candidates.** A line that is no JSON, one without a unit
   name, one naming an absent symbol: a miss, then the search; no tool
   failure.
4. **Mixed.** Reused and searched units in one check.
5. **Before withdrawal.** A module run whose reused evidence the check
   refuses is searched and checked again, and its import is not withdrawn.
6. **Off.** With the mode off, nothing is read from or written to the
   index.
7. **Not published.** After a reused run, a run with the mode off executes
   the search.
8. **Eviction and cleaning.** A proposed reference goes with its entry;
   cleaning removes the root.
9. **The intended divergence.** Old evidence accepted while the current
   search refuses, and a run with the mode off reporting the refusal.

## Steps, each mergeable and measured

| # | Step | Measured by |
| --- | --- | --- |
| 1 | The generalized index (§2), with eviction and cleaning; control 8 | the store's tests |
| 2 | Lookup, fallback, publication and the mode (§1, §3–§7) for the file's units and module runs | the suites, with the mode off |
| 3 | Controls 1–7 and 9 | the controls |

A pretext gate keeps a required leg with the mode off, which decides; a
leg with the mode on over a store seeded by an earlier build is reported
separately and measures latency. A timing measurement runs over a fresh
store, so the stages it measures execute.

## Open questions

1. **A key without the claims.** With 3303c669's statement-entry rule the
   check reads no candidate (read: its record), so evidence accepted with
   a candidate set is accepted with a larger one. The proposal key binds
   the claims' bytes, so a producer change that only adds candidates
   misses. A secondary lookup without the claims, the check deciding,
   would cover producer-only changes (126 s for the five files, observed)
   at one check per changed unit; claims differing in required facts can
   make it a net loss. To be measured before it is built.
