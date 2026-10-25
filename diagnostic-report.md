# Diagnostic mode report

**The diagnostic mode does not replace the rewrite loop.** Its recovery boundaries and approximation semantics are specified in [Diagnostic traversal](docs/DIAGNOSTIC-MODE.md). The acceptance path retains its separate result type, envelope rejection and exhaustive certification conversion.

## Measurement: 2026-10-25

Four shards cover 495 functions in 461 slice groups, with a 300-second stage limit. 177 functions pass aggregate checks under diagnostic assumptions. Coverage with holes is **1325/12813 (10.34%)**. These are diagnostic approximations, not verified coverage.

| Comparison | Original rewrite snapshot | Latest rewrite snapshot |
| --- | ---: | ---: |
| Common target functions | 172 | 210 |
| Diagnostics reach the end | 2 | 2 |
| Rewrites reach the end | 159 | 179 |
| Rewrite coverage with holes, including baseline verified functions | 2106/12698 (16.59%) | 2623/12698 (20.66%) |

The original snapshot has 159 total rewrite completions: 1 shared with diagnostics and 158 rewrite-only. Coverage percentages here are recomputed from each snapshot’s inventory and holes.

The latest snapshot contains 202 recorded experiments, 3426 attempts and 1775 refusal steps. It covers 210 of the baseline’s 312 unverified target functions. The diagnostic inventory has 4831 occurrence records across all slices; repeated or conditional occurrences are not distinct proved blockers.

The longest diagnostic shard takes 1235.57 seconds; the rewrite snapshot records 4256.98 seconds. Diagnostics invoke 1345 stages, 0 replayed and 614 without a key. Source revisions, target sets, cache histories and concurrent workloads differ; comments edited in a keyed module during the diagnostic run also disabled replay for part of it. These timings establish no controlled speedup, and completion parity is absent.

Against the preceding diagnostic census, aggregate completion and coverage with holes are unchanged. Occurrence records increase from 3,693 to 4,831; this is not a count of distinct newly discovered blockers. The [comparison data](/tmp/diag-resume-summary.json) records the target sets.

## What prevents completion

1. **Shared source declarations.** `collectDeclarations` has one failing result for the declaration document. Its declaration queue, symbol identities, generated definitions, value dependencies and callbacks into the gate have no joint diagnostic transaction. The outer gate recovery cannot reconstruct that document after failure. Continuation requires a diagnostic declaration state with explicit opaque contracts, stable identities and recovery at each queued declaration and dependency.
2. **Shared typed preparation.** `equationFront` calls `EquationLowering.source` before per-unit recovery. A refusal constructing the shared equation store yields no plans to inspect. Local recovery inside `extractNormalizedFn` is also absent: a typed failure discards that unit. Completing these boundaries requires diagnostic hole operations that preserve slots, bindings, control-flow edges and conservative heap effects through lowering; replacing a function by empty claims does not do that.
3. **Dependency attribution.** Occurrences inherit all earlier source and proposal recoveries in the document. Values, stores, joins and closure captures carry no recovery identifiers. Filtering that list by source span cannot establish the requested dependency relation.
4. **Aggregate obligations and budgets.** Independent node traversal checks expressions, every normal edge, handlers and return promises. It assumes supplied interfaces and forgets predecessor facts. Whole-graph and footprint checking can still stop at an earlier refusal; local success does not discharge those aggregate obligations. A stage timeout leaves its inventory incomplete.

For example, `array-prototype.mts#reviewedEntries` reports only the shared `Readonly` mapped-key refusal. The rewrite snapshot also encounters a closure-signature claim outside its source annotation and a return-contract evidence failure, then reaches the end. Diagnostics therefore demonstrably miss later blockers on that target.

Terminal groups below count target functions, not distinct causes:

- aggregate complete: 177.
- shared typed extraction: 17.
- local search attempted; aggregate incomplete: 90.
- shared source preparation: 173.
- no local search obligations attempted: 14.
- tool error or timeout: 22.
- planning: 2.

Timeouts/tool errors:

- `fragment-statements.mts#patternStmt` (19 target functions sharing this slice): Error: timeout: verifier --diagnose-source-claims did not finish within 300 s.
- `fragment-statements.mts#readCannotThrow` (1 target function): Error: timeout: verifier --diagnose-source-claims did not finish within 300 s.
- `fragment-statements.mts#abrupt` (1 target function): Error: timeout: verifier --diagnose-source-claims did not finish within 300 s.
- `fragment-statements.mts#functionDecl` (1 target function): Error: timeout: verifier --diagnose-source-claims did not finish within 300 s.

## Disk and validation

Programmatic verification and diagnostic results release artifact directories by default. File consumers request retention and use scoped disposal; the census releases each run after reading its logs. Inspection commands explicitly keep artifacts. Every new run checks for at least 10 GiB free, and the worker dispatcher also checks before starting queued work. [Artifact lifetime](docs/STAGE-STORE.md#locations) documents the API.

Disk checks show 70 GiB free before work and more than 150 GiB during the later census. Samples of live census roots show one active diagnostic directory and zero accumulated pipeline directories. These observations do not attribute changes in total free space to this run alone. [Disk sample](/tmp/diag-resume-disk.log).

- `make suite`: 2,199/2,199 cases pass; 2,834 ordinary functions verified.
- `make test`: 19/19 suites pass, including 157 controls, diagnostic-envelope rejection, default artifact cleanup, disposal on a consumer exception and the low-disk exit.
- The diagnostic binding case retains both failed destructuring reads and the following cast refusal. Forged graph claims exercise a failed expression beside two failing edges, a handler and a return promise.
- The commit record passes its independent glossary/readability check. [Commit record](/tmp/diag-resume-commit.txt).

## Records

[Comparison data](/tmp/diag-resume-summary.json); [census shard 1](/tmp/diag-resume-1.json), [census shard 2](/tmp/diag-resume-2.json), [census shard 3](/tmp/diag-resume-3.json), [census shard 4](/tmp/diag-resume-4.json). Each census record links its per-slice detail files and contains source hashes, original spans, rankings and stage timings.

[Original rewrite snapshot](/tmp/diagnostic-rewrite-full-snapshot.json), SHA-256 `2fd980315cae46c8a11db5ab3dae81707ed5721fd22767510be355a14670ddb9`. [Latest rewrite snapshot](/tmp/diag-resume-rewrite-snapshot.json), SHA-256 `94b393e89c0b6472ac1a972deeaae65847bf39521c3406cbaf16ec39a15c7db3`.
