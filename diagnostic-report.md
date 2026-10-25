# Diagnostic mode report

**Completion parity with the rewrite loop is absent.** [Diagnostic traversal](docs/DIAGNOSTIC-MODE.md) specifies the recovery and approximation rules. [WORK.md](WORK.md#status) owns the remaining work.

## Measurement: 2026-10-25

Eight shards cover 496 functions in 461 slice groups at a 300-second stage limit. 246 functions pass aggregate checks under diagnostic assumptions. Coverage with holes is **1942/12958 (14.99%)**. These figures describe diagnostic approximations, not verified coverage. 7 completed functions retain no counted statements outside holes; their target names are in the comparison data.

| Comparison | Original rewrite snapshot | Latest rewrite snapshot |
| --- | ---: | ---: |
| Common target functions | 172 | 210 |
| Diagnostics reach aggregate completion | 33 | 45 |
| Preceding diagnostics reach aggregate completion | 11 | 13 |
| Rewrites reach the end | 159 | 179 |
| Diagnostics reach local search or aggregate completion | 149 | 172 |
| Preceding diagnostics reach local search or aggregate completion | 141 | 164 |
| Rewrite coverage with holes, including baseline verified functions | 2106/12698 (16.59%) | 2623/12698 (20.66%) |

Local search is a traversal measurement and does not count as aggregate completion. Completion requires every retained unit to pass whole-graph search and certificate checks. Recovered expressions can read explicit assumed inputs; their source regions remain holes. The comparison procedures use different approximations, and completion counts alone do not establish equal retained behavior.

Against the preceding diagnostic census, aggregate completion gains 57 target functions and loses 0. Lost completions: none. 9 targets gain local attempts or aggregate completion, and 0 lose that measured reach. The comparison data lists these target sets and retained statement counts per target. Unchanged source files lose 0 previously retained statement spans; the data lists any losses.

The inventory contains 57658 occurrence records across slices. Repeated occurrences, conditional checks and overlap between slices prevent interpreting that number as distinct blockers.

## Observed boundaries

The [design](docs/DIAGNOSTIC-MODE.md#recovery-boundaries) owns the source, equation, unit and expression approximations. The diagnostic syntax fixture reaches both body refusals beside constructor and hoisting refusals. The diagnostic blocker fixture, including a branch, a mutable local and an exception handler, completes aggregate checking with opaque expression regions. A retained footprint failure prevents completion in the effect fixture. These are diagnostic outcomes; the ordinary fixtures remain refused.

The inventory's limits include execution-plan construction, a failed unit setup retry, document decoding and tool failures. The shared-source-preparation group contains `strip-types.mts#stripTypes`, refused for using namespace import `nodeModule` outside member reads or qualified type names. Planning refusals for `"name" in value` occur before typed graph recovery. Retained graph edges, promises, closure bodies and footprint obligations can prevent aggregate completion after expression recovery. A failed certificate attempt can leave certificate obligations unexamined. Traversal has its own cached stage, so an aggregate retry failure preserves its inventory; 19 target functions have such a retry failure. Unit-reference dependencies conservatively cover closures and shared declarations; individual values, stores and aliases are not tracked. External equation failures without a client use site have document scope. The exact fixed-input assumptions and their limits are stated in the design.

Terminal groups count target functions, including every function sharing a slice:

- aggregate complete: 246.
- local search attempted; aggregate incomplete: 186.
- tool error or timeout: 31.
- planning: 32.
- shared source preparation: 1.

## Validation and resources

- `make suite`: 2,215/2,215 cases pass; 2,843 ordinary functions verified.
- `make test`: 19/19 suites pass, including 158 controls.
- The forged unsupported return annotation bypasses the parser and producer and completes diagnostic aggregate checking. Ordinary source commands reject diagnostic documents.
- An injected completion-stage failure preserves the traversal inventory and keeps completion false.
- The axiom and documentation checks pass. The commit record passes its independent glossary/readability check.

Recorded free-space samples remain above 10 GiB. Census processes retain one active diagnostic directory each and release it before the next slice. The 10 GiB guard and scoped artifact disposal apply to every run. [Disk samples](/tmp/diag-parity-disk.log).

The longest final census shard takes 2503.38 seconds, with 2008 stage invocations, 0 replayed and 0 without a key. The two interrupted intermediate censuses are excluded. Source revisions, cache histories and concurrent workloads differ from the rewrite snapshots; these figures establish no controlled speedup.

## Records

[Comparison data](/tmp/diag-parity-summary.json); [shard 1](/tmp/diag-parity-census-1.json), [shard 2](/tmp/diag-parity-census-2.json), [shard 3](/tmp/diag-parity-census-3.json), [shard 4](/tmp/diag-parity-census-4.json), [shard 5](/tmp/diag-parity-census-5.json), [shard 6](/tmp/diag-parity-census-6.json), [shard 7](/tmp/diag-parity-census-7.json), [shard 8](/tmp/diag-parity-census-8.json). The records include per-slice inventories, source hashes, original spans and stage timings. Their source identity contains the base revision and a dirty flag; stage keys identify the executed inputs and binaries.

[Preceding comparison](/tmp/diag-redesign-summary.json), with its four census records: [shard 1](/tmp/diag-redesign-final-1.json), [shard 2](/tmp/diag-redesign-final-2.json), [shard 3](/tmp/diag-redesign-final-3.json), [shard 4](/tmp/diag-redesign-final-4.json).

[Original rewrite snapshot](/tmp/diagnostic-rewrite-full-snapshot.json), SHA-256 `2fd980315cae46c8a11db5ab3dae81707ed5721fd22767510be355a14670ddb9`. [Latest rewrite snapshot](/tmp/diag-resume-rewrite-snapshot.json), SHA-256 `94b393e89c0b6472ac1a972deeaae65847bf39521c3406cbaf16ec39a15c7db3`.
