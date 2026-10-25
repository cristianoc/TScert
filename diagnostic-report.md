# Diagnostic mode report

**Completion parity with the rewrite loop is absent.** [Diagnostic traversal](docs/DIAGNOSTIC-MODE.md) specifies the recovery and approximation rules. [WORK.md](WORK.md#status) owns the remaining work.

## Measurement: 2026-10-25

Twelve shards cover 496 functions in 461 slice groups at a 300-second stage limit. 350 functions pass aggregate checks under diagnostic assumptions. Coverage with holes is **2764/12958 (21.33%)**. These figures describe diagnostic approximations, not verified coverage. 24 completed functions retain no counted statements outside holes; their names are in the comparison data.

| Comparison | Original rewrite snapshot | Latest rewrite snapshot |
| --- | ---: | ---: |
| Common target functions | 172 | 210 |
| Diagnostics reach aggregate completion | 110 | 127 |
| Preceding diagnostics reach aggregate completion | 55 | 70 |
| Rewrites reach the end | 159 | 179 |
| Both reach completion | 105 | 118 |
| Diagnostics reach local search or aggregate completion | 171 | 195 |
| Preceding diagnostics reach local search or aggregate completion | 171 | 195 |
| Rewrite coverage with holes, including baseline verified functions | 2106/12698 (16.59%) | 2623/12698 (20.66%) |

Local search is a traversal measurement. Completion requires every retained unit to pass whole-graph search and certificate checks. The comparison procedures use different approximations; completion counts alone do not establish equal retained behavior.

Against the preceding diagnostic census, aggregate completion gains 68 target functions and loses 0. 0 targets gain local attempts or aggregate completion, and 0 lose that reach. Coverage with holes gains 624 retained statements, from 2140/12958 (16.51%) to 2764/12958 (21.33%). Unchanged source files lose 0 previously retained statement spans. The comparison data lists all gains, losses and retained statement counts per target.

The inventory contains 73292 occurrence records across slices. Repeated occurrences, conditional checks and overlapping slices prevent interpreting this as a count of distinct blockers.

## Observed boundaries

The [design](docs/DIAGNOSTIC-MODE.md#recovery-boundaries) owns the recovery rules. The edge fixture completes aggregate checking across assignments, branches and a catch handler; both ends of its recovered edge are opaque. The empty-result fixture remains incomplete. The planning fixture reaches both invalid casts after its excluded test. The closure fixture completes aggregate checking with its enclosing closure expression opaque. The footprint fixture remains incomplete. Ordinary verification refuses these fixtures.

Execution-plan construction outside literal-key test recovery, shared source preparation, module-cell and other unit setup, document decoding and tool failures can stop traversal. 0 targets retain failed unit extraction. Uninhabitable supplied result or destination types, remaining graph edges, return promises, retained closure bodies, footprints and certificate checks can prevent aggregate completion after expression and edge recovery. A failed certificate attempt can leave certificate obligations unexamined. 23 targets have an aggregate-stage tool failure or timeout, compared with 22 in the preceding census; their traversal inventories remain available. `strip-types.mts#stripTypes` refuses namespace import `nodeModule` outside member reads or qualified type names. The `collectDeclarations` compiler API failure on an empty tuple type also occurs in the preceding census.

Of the 179 targets the latest rewrite run reaches, 118 complete diagnostic checking and 61 remain incomplete. For those 61 targets, the terminal records contain 28 expression obligations, 19 return promises, 9 incoming edges, 2 footprint refusals and 3 tool failures or timeouts. This classifies the last recorded refusal, with tool failures taking precedence; a slice can contain additional blockers.

Dependency scopes conservatively follow unit references, including closures and shared declarations; they do not track individual values, stores or aliases. External equation failures without a client use site have document scope. The design states the limits of fixed assumed inputs and opaque regions.

Terminal groups count target functions, including every function sharing a slice. A recovered planning occurrence does not classify a slice that reaches local attempts as stopped in planning.

- aggregate complete: 350.
- local search attempted; aggregate incomplete: 107.
- tool error or timeout: 38.
- shared source preparation: 1.

## Validation and resources

- `make suite`: 2,219/2,219 cases pass; 2,843 ordinary functions verified.
- `make test`: 19/19 suites pass, including 158 controls.
- Diagnostic edge recovery records both endpoint spans as holes. Empty result contracts and the footprint case prevent completion.
- Forged annotation recovery, ordinary rejection of diagnostic envelopes and traversal retention after an injected completion failure pass.
- The axiom, schema, boundary and documentation checks pass. The commit record passes its independent glossary/readability check.

The minimum recorded free space is 145.41 GiB. Census processes retain one active diagnostic directory each and release it before the next slice. The 10 GiB guard applies to every run. [Disk samples](/tmp/diag-edge-disk.log).

The initial twelve shards record 2097 stage invocations, 191 replayed and 0 without a key. The longest shard takes 2676.87 seconds. Source revisions, cache histories and concurrent workloads differ from the rewrite snapshots; these figures establish no controlled speedup.

The initial census times out on `library-modules.mts#moduleEntries`, whose preceding aggregate run takes about 269 seconds. An isolated retry at the same 300-second limit completes in 277.37 seconds. The final shard 10 replays that result. [Retry record](/tmp/diag-edge-module-retry.json); [initial shard 10](/tmp/diag-edge-census-10.json).

## Records

[Comparison data](/tmp/diag-edge-summary.json); [shard 1](/tmp/diag-edge-census-1.json), [shard 2](/tmp/diag-edge-census-2.json), [shard 3](/tmp/diag-edge-census-3.json), [shard 4](/tmp/diag-edge-census-4.json), [shard 5](/tmp/diag-edge-census-5.json), [shard 6](/tmp/diag-edge-census-6.json), [shard 7](/tmp/diag-edge-census-7.json), [shard 8](/tmp/diag-edge-census-8.json), [shard 9](/tmp/diag-edge-census-9.json), [shard 10](/tmp/diag-edge-final-census-10.json), [shard 11](/tmp/diag-edge-census-11.json), [shard 12](/tmp/diag-edge-census-12.json). Records include inventories, source hashes, original spans and stage timings. Source identity contains the base revision and a dirty flag; stage keys identify the executed inputs and binaries.

[Preceding comparison](/tmp/diag-continue-summary.json), whose eight census records are `/tmp/diag-continue-census-1.json` through `/tmp/diag-continue-census-8.json`.

[Original rewrite snapshot](/tmp/diagnostic-rewrite-full-snapshot.json), SHA-256 `2fd980315cae46c8a11db5ab3dae81707ed5721fd22767510be355a14670ddb9`. [Latest rewrite snapshot](/tmp/diag-resume-rewrite-snapshot.json), SHA-256 `94b393e89c0b6472ac1a972deeaae65847bf39521c3406cbaf16ec39a15c7db3`.
