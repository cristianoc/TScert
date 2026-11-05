# Draft: certificate size and verification cost

Four stages of this design are part of the checker, each stated by its
owner: node headers referring to their effect's proof and the wire-text scan
([evidence](../REQUEST-PROTOCOL.md#evidence),
[wire text](../REQUEST-PROTOCOL.md#wire-text)), read summaries
([PROGRAM-TYPING](../PROGRAM-TYPING.md#read-summaries),
[wire](../REQUEST-PROTOCOL.md#read-summaries)), the evidence document's
tables ([evidence document](../REQUEST-PROTOCOL.md#evidence-document)) and
separation facts ([PROGRAM-TYPING](../PROGRAM-TYPING.md#separation-facts),
[heap freshness](heap-freshness.md)). This draft holds the design's two
remaining parts: a structural decoder in place of the strict round trip, and
a general fact arena conditional on residual cost. Their status and
measurements are the Certificate size row of [WORK](../../WORK.md#status).

**Evidence labels.** **Proved** names existing Lean theorems and their scope.
**Cited** identifies inspected code or supplied measurements.
**Conjectured** identifies proposed designs, proof obligations and estimates.
Every proposed lemma below requires a Lean proof.

## The existing mechanism this extends

The [evidence document](../REQUEST-PROTOCOL.md#evidence-document) and its
strict decoders (`decodeStrict`, `EvidenceWire.lean`; cited), which accept
exactly the current shape of each document, and the
[heap state assertions](../PROGRAM-TYPING.md#heap-state-and-assertions)
the evidence carries, with their
[separation facts](../PROGRAM-TYPING.md#separation-facts) (cited). The
structural decoder below accepts the same shapes in one traversal; the
fact arena stores the same facts once, referred to by index, as the
evidence document's tables store node headers and read summaries.

## Strict structural decoding

**Conjectured — representation.** Replace `decodeStrict`'s `fromJson`/`toJson`/
`sameJson` round trip with structural decoders that enforce the same exact
shape while traversing each field once. Preserve explicit required fields,
unknown-field rejection, constructor arity, labels, numbers, optional values
and the existing parser's object-key semantics. Audit nested codecs as well
as the outer bundle. Use one current encoding, updating all consumers and
fixtures together, without a version tag or compatibility decoder.

**Required lemmas and review.** Establish strict-decoder equivalence to the
round-trip acceptance relation (`decodeStrict`), over total reference codecs
audited against the derived ones. The text-to-JSON boundary requires direct
adversarial controls; `checkUnitJson_safe` starts with JSON.

**Trust.** The decoder is trusted code.

**Cited gain.** A profile of 2026-10-23 attributes roughly 19% of
`moduleFunction`'s check samples to re-encoding plus `sameJson`; these are
removable-work ceilings, not speedup promises. Replacement validation still
costs time.

## A general fact arena, conditional on residual cost

**Conjectured.** Add subtype, image and expression facts only if measurements
after the landed stages show worthwhile repeated semantic validation.
Each fact states its full judgment and references earlier facts in its scope.
Check every supplied entry, including unused entries, once per scope.
Effects retain incoming knowledge, output and exceptional obligations.

**Scope identity and executable schedule.** The consumer reconstructs scope
identities from the frozen document/module, request/body, graph, image checker
and budget, ordinary or qualified subsumption, source signature, aliases,
obligation mode and exact permitted code prefix. Restricted environments,
including `typedRead`'s optional branch with no available codes, have separate
scopes. A wire scope index selects an existing scope; it declares no assumptions.

Starting with a sound empty code prefix, check the next closure's fact block
against precisely that prefix, then its graph, effects and footprint obligations.
Publish its code entry only after those checks succeed. Repeat in existing
code order, then check enclosing-body facts and its graph. Check supplemental
obligations in their reconstructed environments. Backward fact references stay
within scope; cross-scope reuse requires an explicit transport theorem.

The joint invariant states that published code satisfies `CodesSound`, and
each checked fact denotes its judgment under its recorded sound code prefix.
This excludes self-dependent code and sibling or later-code borrowing.
Existing graph/self rules retain their own premises.

**Required lemmas.** Prove checked-prefix and lookup soundness jointly with
code extension, plus `facts_reassign` and reference-aware effect/graph
transport. [Parametricity.lean](../../lean/Verification/Programs/Parametricity.lean)
and [RequestJson.lean](../../lean/Verification/Source/RequestJson.lean) establish
the required scope: ordinary bodies quantify over all parameter assignments;
qualified bodies quantify over admitted arguments satisfying binder lengths,
domain admission and bounds, with sound aliases and the source signature.
Extend `checkBodyEntry_reassign` using equality of the body checkers and
qualified subsumption soundness. Soundness only at the frozen graph is
insufficient. Reconnect request safety and footprints to `checkUnitJson_safe`.

**Trust and gain.** Arena decoding, scope reconstruction, scheduling and
checking change trusted code; arena construction remains untrusted.
The measured exact-check reuse is small, and image-validation time is not
isolated. No whole-program speedup estimate justifies this stage yet.

## Validation and decision gates

**Conjectured — required validation.** For each stage, preserve acceptance
and run affected pipeline cases plus controls for what source cases cannot
forge: effect-only nodes; promise and footprint inspection; mismatched roots;
missing/extra summary arms; changed fields, results and `length` views;
receiver coercions and unsupported-read fallback; wrong-kind, cyclic and
cross-scope references; qualified/ordinary and restricted-code reuse;
self-dependent code; context edits; instance substitutions; forged freshness,
aliases, loop allocations, joins and exceptional paths; malformed wire text.

Measure the same five saved inputs serially, with executed stages and fixed
toolchain, budgets and limits. Report three-run median/range for search and
check CPU separately, wall time, bytes, RSS, summary eligibility by scope,
checked nodes and subtype/image validations. Include producer validation.
Report incremental gains and unchanged outcomes; overlapping baseline
estimates are not additive. Keep `protocolPattern` as a separate search-timeout
measurement. Run the targeted functions' units during development, required suites before
merge, and the full census once on main. These measurements determine whether
the fact arena earns its proof and maintenance cost.
