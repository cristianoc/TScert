# Diagnostic mode report

**Completion parity with the rewrite loop is absent.** [Diagnostic traversal](docs/DIAGNOSTIC-MODE.md) specifies the recovery and approximation rules. [WORK.md](WORK.md#status) owns the remaining work.

## Measurement: 2026-10-25

Eight shards cover 496 functions in 461 slice groups at a 300-second stage limit. 282 functions pass aggregate checks under diagnostic assumptions. Coverage with holes is **2140/12958 (16.51%)**. These figures describe diagnostic approximations, not verified coverage. 14 completed functions retain no counted statements outside holes; their names are in the comparison data.

| Comparison | Original rewrite snapshot | Latest rewrite snapshot |
| --- | ---: | ---: |
| Common target functions | 172 | 210 |
| Diagnostics reach aggregate completion | 55 | 70 |
| Preceding diagnostics reach aggregate completion | 33 | 45 |
| Rewrites reach the end | 159 | 179 |
| Diagnostics reach local search or aggregate completion | 171 | 195 |
| Preceding diagnostics reach local search or aggregate completion | 149 | 172 |
| Rewrite coverage with holes, including baseline verified functions | 2106/12698 (16.59%) | 2623/12698 (20.66%) |

Local search is a traversal measurement. Completion requires every retained unit to pass whole-graph search and certificate checks. The comparison procedures use different approximations; completion counts alone do not establish equal retained behavior.

Against the preceding diagnostic census, aggregate completion gains 36 target functions and loses 0. 25 targets gain local attempts or aggregate completion, and 0 lose that reach. Coverage with holes gains 198 retained statements, from 1942/12958 (14.99%) to 2140/12958 (16.51%). Unchanged source files lose 0 previously retained statement spans. The comparison data lists all gains, losses and retained statement counts per target.

The inventory contains 72795 occurrence records across slices. Repeated occurrences, conditional checks and overlapping slices prevent interpreting this as a count of distinct blockers.

## Observed boundaries

The [design](docs/DIAGNOSTIC-MODE.md#recovery-boundaries) owns the recovery rules. The planning fixture reaches both invalid casts after the excluded `"name" in value` test. The closure fixture completes aggregate checking with its enclosing closure expression opaque. The footprint fixture remains incomplete. Ordinary verification refuses all three fixtures.

Execution-plan construction outside literal-key test recovery, shared source preparation, module-cell and other unit setup, document decoding and tool failures can stop traversal. No target stops in planning, compared with 32 in the preceding census. No target retains a failed unit-extraction retry. Graph edges, return promises, retained closure bodies, footprints and certificate checks can prevent aggregate completion after expression recovery. A failed certificate attempt can leave certificate obligations unexamined. 22 targets have an aggregate-stage tool failure or timeout, compared with 19 in the preceding census; their traversal inventories remain available. `strip-types.mts#stripTypes` refuses namespace import `nodeModule` outside member reads or qualified type names. The `collectDeclarations` compiler API failure on an empty tuple type also occurs in the preceding census.

Dependency scopes conservatively follow unit references, including closures and shared declarations; they do not track individual values, stores or aliases. External equation failures without a client use site have document scope. The design states the limits of fixed assumed inputs and opaque regions.

Terminal groups count target functions, including every function sharing a slice. A recovered planning occurrence does not classify a slice that reaches local attempts as stopped in planning.

- aggregate complete: 282.
- local search attempted; aggregate incomplete: 175.
- tool error or timeout: 38 (preceding census: 31).
- shared source preparation: 1.

## Validation and resources

- `make suite`: 2,217/2,217 cases pass; 2,843 ordinary functions verified.
- `make test`: 19/19 suites pass, including 158 controls.
- Diagnostic planning and closure cases pass. The footprint case prevents completion.
- Forged annotation recovery, ordinary rejection of diagnostic envelopes and traversal retention after an injected completion failure pass.
- The axiom, schema, boundary and documentation checks pass. The commit record passes its independent glossary/readability check.

The minimum recorded free space is 148.45 GiB. Census processes retain one active diagnostic directory each and release it before the next slice. The 10 GiB guard applies to every run. [Disk samples](/tmp/diag-continue-disk.log).

The longest census shard takes 3444.72 seconds, with 2097 stage invocations, 0 replayed and 0 without a key. Source revisions, cache histories and concurrent workloads differ from the rewrite snapshots; these figures establish no controlled speedup.

## Records

[Comparison data](/tmp/diag-continue-summary.json); [shard 1](/tmp/diag-continue-census-1.json), [shard 2](/tmp/diag-continue-census-2.json), [shard 3](/tmp/diag-continue-census-3.json), [shard 4](/tmp/diag-continue-census-4.json), [shard 5](/tmp/diag-continue-census-5.json), [shard 6](/tmp/diag-continue-census-6.json), [shard 7](/tmp/diag-continue-census-7.json), [shard 8](/tmp/diag-continue-census-8.json). Records include inventories, source hashes, original spans and stage timings. Source identity contains the base revision and a dirty flag; stage keys identify the executed inputs and binaries.

[Preceding comparison](/tmp/diag-parity-summary.json), whose eight census records are `/tmp/diag-parity-census-1.json` through `/tmp/diag-parity-census-8.json`.

[Original rewrite snapshot](/tmp/diagnostic-rewrite-full-snapshot.json), SHA-256 `2fd980315cae46c8a11db5ab3dae81707ed5721fd22767510be355a14670ddb9`. [Latest rewrite snapshot](/tmp/diag-resume-rewrite-snapshot.json), SHA-256 `94b393e89c0b6472ac1a972deeaae65847bf39521c3406cbaf16ec39a15c7db3`.
