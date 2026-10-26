# Diagnostic mode report

[Diagnostic traversal](docs/DIAGNOSTIC-MODE.md) specifies recovery and approximation. [WORK.md](WORK.md#status) owns the remaining work.

## Measurement: 2026-10-26

The comparison covers 496 functions in 461 slice groups at a 300-second stage limit. 391 functions pass aggregate checks under diagnostic assumptions. Coverage with holes is **3128/12961 (24.13%)**. These figures describe diagnostic approximations, not verified coverage. 39 completed functions retain no counted statements outside holes.

| Comparison | Original rewrite snapshot | Latest rewrite snapshot |
| --- | ---: | ---: |
| Common target functions | 172 | 210 |
| Diagnostics reach aggregate completion | 139 | 160 |
| Rewrites reach the end | 159 | 179 |
| Both reach completion | 134 | 151 |
| Diagnostics reach local search or aggregate completion | 171 | 195 |
| Rewrite coverage with holes, including baseline verified functions | 2106/12698 (16.59%) | 2623/12698 (20.66%) |

Local search measures traversal. Completion requires every retained unit to pass aggregate search and certificate checks. The procedures use different approximations, so completion counts alone do not establish equal retained behavior.

The preceding measurement (2026-10-25) reports 391 completed functions and 3128/12961 retained statements (24.13%). This measurement gains 0 completed functions and loses 0; local attempts or completion are gained for 0 functions and lost for 1. Unchanged source files lose 0 previously retained statement spans: none. The comparison data lists each affected function and statement. Source hashes distinguish changed sources from unchanged spans.

`written-applications.mts#writtenApplications` reaches the 300-second local-traversal limit. The preceding run finishes that stage in 292 seconds. Neither run completes aggregate checks, and both have zero retained coverage. This timeout accounts for the one loss of local-search reach.

## Observed boundaries

The inventory contains 70948 occurrences across slices. Repeated occurrences, conditional checks and overlapping slices prevent interpreting this as a count of distinct blockers. 24 functions have an aggregate-stage tool failure or timeout; their traversal inventories remain available. 0 functions retain failed unit extraction.

The [recovery boundaries](docs/DIAGNOSTIC-MODE.md#recovery-boundaries) specify the opaque replacements. Environment recovery marks the affected statement region. Decoder and execution-body planning refusals have generic recovery transactions. Shared preparation, document decoding and tool failures can stop traversal; unit contracts, graph edges and certificate checks can prevent aggregate completion. Dependency scopes follow unit references rather than individual values or aliases.

Terminal groups count target functions, including functions sharing a slice:

- aggregate complete: 391.
- local search attempted; aggregate incomplete: 65.
- tool error or timeout: 39.
- shared source preparation: 1.

## Reproducibility

At revision `bb7a5a2`, the 33 saved slice groups with a planning or environment refusal are rerun. The other 428 groups reuse the preceding measurement. They either stop in unchanged earlier stages or pass planning without recovery and report no environment recovery; these fixes therefore preserve their retained programs. Source hashes agree. Each comparison record identifies its reused or rerun origin. The 12 comparison shards combine these results; this is a targeted rerun, not a fresh full census. The minimum sampled free space on `/` is 137.7 GiB. The targeted rerun uses the existing stage store and releases per-run artifacts after reading their logs.

[Comparison data](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-review-4a_5e0kp/run-summary.json); [shard 1](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-review-4a_5e0kp/run-final-census-1.json), [shard 2](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-review-4a_5e0kp/run-final-census-2.json), [shard 3](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-review-4a_5e0kp/run-final-census-3.json), [shard 4](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-review-4a_5e0kp/run-final-census-4.json), [shard 5](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-review-4a_5e0kp/run-final-census-5.json), [shard 6](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-review-4a_5e0kp/run-final-census-6.json), [shard 7](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-review-4a_5e0kp/run-final-census-7.json), [shard 8](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-review-4a_5e0kp/run-final-census-8.json), [shard 9](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-review-4a_5e0kp/run-final-census-9.json), [shard 10](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-review-4a_5e0kp/run-final-census-10.json), [shard 11](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-review-4a_5e0kp/run-final-census-11.json), [shard 12](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-review-4a_5e0kp/run-final-census-12.json). Records contain source hashes, original spans and stage timings. [Preceding comparison](/var/folders/gx/wxqwh_fx6zl3y19s4gvwccjw0000gn/T/tscert-diagnostic-footprint-emkmnquw/run-summary.json).

[Original rewrite snapshot](/tmp/diagnostic-rewrite-full-snapshot.json), SHA-256 `2fd980315cae46c8a11db5ab3dae81707ed5721fd22767510be355a14670ddb9`. [Latest rewrite snapshot](/tmp/diag-resume-rewrite-snapshot.json), SHA-256 `94b393e89c0b6472ac1a972deeaae65847bf39521c3406cbaf16ec39a15c7db3`.
