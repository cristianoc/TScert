# Diagnostic mode report

**Completion parity with the rewrite loop is absent.** [Diagnostic traversal](docs/DIAGNOSTIC-MODE.md) specifies the recovery and approximation rules. [WORK.md](WORK.md#status) owns the remaining work.

## Measurement: 2026-10-25

Four shards cover 496 functions in 462 slice groups at a 300-second stage limit. 189 functions pass the ordinary aggregate checks under diagnostic source and proposal assumptions. Coverage with holes is **1369/12941 (10.58%)**. These figures describe diagnostic approximations, not verified coverage.

| Comparison | Original rewrite snapshot | Latest rewrite snapshot |
| --- | ---: | ---: |
| Common target functions | 172 | 210 |
| Diagnostics reach aggregate completion | 11 | 13 |
| Rewrites reach the end | 159 | 179 |
| Diagnostics reach local search or aggregate completion | 141 | 164 |
| Previous diagnostics reach local search or aggregate completion | 34 | 57 |
| Rewrite coverage with holes, including baseline verified functions | 2106/12698 (16.59%) | 2623/12698 (20.66%) |

Local search is a traversal measurement. It does not substitute for aggregate completion in this comparison. The completion and coverage definitions retain the preceding report’s meaning; typed recovery and conditional local checks alone do not count as aggregate completion.

The inventory contains 49270 occurrence records across slices. Repeated occurrences, conditional checks and overlap between slices prevent interpreting that number as distinct blockers. Across all 496 functions, 164 targets absent from the preceding local-search set have local attempts or aggregate completion. The comparison data lists the target sets.

Against the preceding diagnostic census, aggregate completion gains 12 target functions and loses 0. Lost completions: none.

## Recovery and remaining boundaries

The declaration collector retains imported bindings and queued declaration identities after local refusals. Equation preparation recovers type terms and jobs and attempts bounds independently. Typed operations and flow actions retain continuations, destinations and lexical slots. Local footprint checks use partial node attempts independently of whole-graph evidence production. The [design](docs/DIAGNOSTIC-MODE.md#recovery-boundaries) states the precise replacements and their limits.

The `array-prototype.mts#reviewedEntries` probe over the preceding census source reaches 4,198 local attempts after its mapped-type refusal and reports its closure-signature refusal. The `type-term.mts#constructorForms` probe over this census source returns an inventory with 22,226 local attempts. Neither probe passes aggregate checking. These measurements show later traversal, not completion parity.

The following boundaries limit the inventory:

1. Source preparation outside the declaration transactions can stop the document, including class-constructor and hoisting restrictions.
2. Equation well-formedness, source-unit setup and quantified-call preparation can refuse before a unit has a graph. Local typed recovery does not cover those operations.
3. Dependency links conservatively include earlier source, producer and typed recoveries in the document. They do not track individual values, stores, joins or closure captures. External equation failures without a client use site have document scope.
4. Local checks assume interfaces and can report failures discharged by whole-program search. The completion flag comes only from the initial ordinary whole-document attempt; recovered typed plans do not complete that aggregate check. A failed aggregate check leaves certificate obligations unexamined. A stage timeout or tool failure leaves the inventory incomplete.

Terminal groups count target functions, including every function sharing a slice:

- aggregate complete: 189.
- local search attempted; aggregate incomplete: 234.
- shared source preparation: 17.
- tool error or timeout: 31.
- planning: 24.
- no local search obligations attempted: 1.

## Validation and resources

- `make suite`: 2,215/2,215 cases pass; 2,843 ordinary functions verified.
- `make test`: 19/19 suites pass, including 158 controls.
- Diagnostic cases cover import recovery followed by two body refusals, binding and syntax recovery, and footprint inspection after a failed expression.
- A forged unsupported annotation bypasses the parser and producer and reaches graph attempts through diagnostic equation recovery. Ordinary source commands reject diagnostic documents.
- The axiom check and documentation checks pass. The commit record passes its independent glossary/readability check.

Observed free space remains above 150 GiB. Census processes retain one active diagnostic directory each and release it before the next slice. The existing 10 GiB guard and scoped artifact disposal apply to every run. [Disk samples](/tmp/diag-redesign-disk.log).

The longest census shard takes 2082.28 seconds, with 1746 stage invocations, 596 replayed and 0 without a key. These timings describe the execution census. The linked inventory replay adds transitive dependency links from unchanged stage results; it is separate from that timing. Interrupted exploratory censuses are excluded. Source revisions, target sets, cache histories and concurrent workloads differ from the rewrite snapshots; these figures establish no controlled speedup.

## Records

[Comparison data](/tmp/diag-redesign-summary.json); [shard 1](/tmp/diag-redesign-final-1.json), [shard 2](/tmp/diag-redesign-final-2.json), [shard 3](/tmp/diag-redesign-final-3.json), [shard 4](/tmp/diag-redesign-final-4.json). The records include per-slice inventories, source hashes, original spans and stage timings. Execution records for the timing measurement: [shard 1](/tmp/diag-redesign-1.json), [shard 2](/tmp/diag-redesign-2.json), [shard 3](/tmp/diag-redesign-3.json), [shard 4](/tmp/diag-redesign-4.json).

[Original rewrite snapshot](/tmp/diagnostic-rewrite-full-snapshot.json), SHA-256 `2fd980315cae46c8a11db5ab3dae81707ed5721fd22767510be355a14670ddb9`. [Latest rewrite snapshot](/tmp/diag-resume-rewrite-snapshot.json), SHA-256 `94b393e89c0b6472ac1a972deeaae65847bf39521c3406cbaf16ec39a15c7db3`.
