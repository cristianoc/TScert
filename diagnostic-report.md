# Diagnostic mode report

[Diagnostic traversal](docs/DIAGNOSTIC-MODE.md) specifies the recovery and approximation rules. [WORK.md](WORK.md#status) owns the remaining work.

## Measurement: 2026-10-25

Twelve shards cover 496 functions in 461 slice groups at a 300-second stage limit. 391 functions pass aggregate checks under diagnostic assumptions. Coverage with holes is **3128/12961 (24.13%)**. These figures describe diagnostic approximations, not verified coverage. 39 completed functions retain no counted statements outside holes; their names are in the comparison data.

| Comparison | Original rewrite snapshot | Latest rewrite snapshot |
| --- | ---: | ---: |
| Common target functions | 172 | 210 |
| Diagnostics reach aggregate completion | 139 | 160 |
| Preceding diagnostics reach aggregate completion | 136 | 153 |
| Rewrites reach the end | 159 | 179 |
| Both reach completion | 134 | 151 |
| Diagnostics reach local search or aggregate completion | 171 | 195 |
| Preceding diagnostics reach local search or aggregate completion | 171 | 195 |
| Rewrite coverage with holes, including baseline verified functions | 2106/12698 (16.59%) | 2623/12698 (20.66%) |

Local search is a traversal measurement. Completion requires every retained unit to pass whole-graph search and certificate checks. The comparison procedures use different approximations; completion counts alone do not establish equal retained behavior.

Against the preceding diagnostic census, aggregate completion gains 11 target functions and loses 0. Both diagnostic censuses reach local attempts or aggregate completion for the same 457 targets. Coverage with holes changes from 3025/12961 (23.34%) to 3128/12961 (24.13%). Unchanged source files lose 0 previously retained statement spans. The comparison data lists all gains, losses and retained statement counts per target. Source hashes distinguish changed sources from unchanged spans.

The inventory contains 72381 occurrence records across slices. Repeated occurrences, conditional checks and overlapping slices prevent interpreting this as a count of distinct blockers.

## Observed boundaries

The [design](docs/DIAGNOSTIC-MODE.md#recovery-boundaries) owns the recovery rules. The syntax-value and syntax-identity fixtures complete with opaque syntax expressions. The closure-promise and closure-edge fixtures complete with their enclosing closure expressions opaque. The footprint and closure-footprint fixtures complete with their offending expressions opaque. The top-level promise and empty-result fixtures remain incomplete. Ordinary verification refuses all these fixtures. A probe using the syntax-identity fixture with coincident synthetic spans reproduces the duplicate-identity decoder refusal.

Execution-plan construction outside literal-key test recovery, shared source preparation, module-cell and other unit setup, document decoding and tool failures can stop traversal. No targets retain failed unit extraction. Uninhabitable supplied result or destination types, remaining graph edges, a unit's own return promise and result contract, footprints and certificate checks can prevent aggregate completion. A failed certificate attempt can leave certificate obligations unexamined. 25 targets have an aggregate-stage tool failure or timeout, compared with 25 in the preceding census; their traversal inventories remain available. `strip-types.mts#stripTypes` refuses namespace import `nodeModule` outside member reads or qualified type names. The `collectDeclarations` compiler API failure on an empty tuple type also occurs in the preceding census.

Of the 179 targets the latest rewrite run reaches, 151 complete diagnostic checking and 28 remain incomplete. Their terminal records contain 8 return-promise failures, 12 expression obligations, 5 tool failures or timeouts and 3 incoming edges. This classifies the last recorded refusal, with tool failures taking precedence; a slice can contain additional blockers. The comparison data includes each target and its terminal reason.

Dependency scopes conservatively follow unit references, including closures and shared declarations; they do not track individual values, stores or aliases. External equation failures without a client use site have document scope. The design states the limits of fixed assumed inputs and opaque regions.

Terminal groups count target functions, including every function sharing a slice. A recovered planning occurrence does not classify a slice that reaches local attempts as stopped in planning.

- aggregate complete: 391.
- local search attempted; aggregate incomplete: 66.
- tool error or timeout: 38.
- shared source preparation: 1.

## Validation and resources

- `make suite`: 2,225/2,225 cases pass; 2,843 ordinary functions verified.
- `make test`: 19/19 suites pass, including 158 controls.
- All 15 diagnostic cases meet their expected completion and refusal outcomes, including opaque closure boundaries and retained top-level promises.
- Forged annotation recovery, ordinary rejection of diagnostic envelopes and traversal retention after an injected completion failure pass.
- The axiom, schema, boundary, formatting and documentation checks pass. The commit record passes its independent glossary/readability check.

The minimum recorded free space is 140.55 GiB. Census processes retain one active diagnostic directory each and release it before the next slice. The census driver stops its workers below 11 GiB to preserve the 10 GiB floor. [Disk samples](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-footprint-emkmnquw/run-disk.log).

The initial twelve shards record 2098 stage invocations, 0 replayed and 0 without a key. The longest shard takes 2761.01 seconds. Source revisions, cache histories and concurrent workloads differ from the rewrite snapshots; these figures establish no controlled speedup.

The initial run records an aggregate timeout for `moduleEntries`, which completes in the preceding census. A separate retry at the same 300-second limit completes in 260.58 seconds. Shard 10 replays that outcome. [Initial shard 10](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-footprint-emkmnquw/run-census-10.json); [retry](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-footprint-emkmnquw/run-retry-moduleEntries.json).

## Records

[Comparison data](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-footprint-emkmnquw/run-summary.json); [shard 1](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-footprint-emkmnquw/run-census-1.json), [shard 2](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-footprint-emkmnquw/run-census-2.json), [shard 3](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-footprint-emkmnquw/run-census-3.json), [shard 4](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-footprint-emkmnquw/run-census-4.json), [shard 5](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-footprint-emkmnquw/run-census-5.json), [shard 6](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-footprint-emkmnquw/run-census-6.json), [shard 7](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-footprint-emkmnquw/run-census-7.json), [shard 8](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-footprint-emkmnquw/run-census-8.json), [shard 9](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-footprint-emkmnquw/run-census-9.json), [shard 10](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-footprint-emkmnquw/run-final-census-10.json), [shard 11](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-footprint-emkmnquw/run-census-11.json), [shard 12](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-footprint-emkmnquw/run-census-12.json). Records include inventories, source hashes, original spans and stage timings. Source identity contains the base revision and a dirty flag; stage keys identify the executed inputs and binaries.

[Preceding comparison](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-parity-998ja8w3/run-summary.json).

[Original rewrite snapshot](/tmp/diagnostic-rewrite-full-snapshot.json), SHA-256 `2fd980315cae46c8a11db5ab3dae81707ed5721fd22767510be355a14670ddb9`. [Latest rewrite snapshot](/tmp/diag-resume-rewrite-snapshot.json), SHA-256 `94b393e89c0b6472ac1a972deeaae65847bf39521c3406cbaf16ec39a15c7db3`.
