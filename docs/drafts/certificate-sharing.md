# Draft: certificate size and verification cost

The design approved by the owner (2026-10-23); its stages and their status
are in [WORK](../../WORK.md#status). Base: TScert main at 2f777e5.

This design targets verification of TScert's own `tools/` before scaling the
census. The proposed order is: remove redundant serialization and decoding,
summarize direct union reads, share wire structure, redesign heap distinctness,
then consider a general fact arena if residual measurements justify it.

**Evidence labels.** **Proved** names existing Lean theorems and their scope.
**Cited** identifies inspected code or supplied measurements.
**Conjectured** identifies proposed designs, proof obligations and estimates.
Every proposed lemma below requires a Lean proof.

## Measurements and their limits

**Cited — attribution, 2026-10-23.** The supplied
`attribution report`
partitions five certificates. Its scripts and raw outputs reside in
a scratch directory of the 2026-10-23 measurement, outside the repository.
These are supplied measurements, not benchmarks reproduced for this draft.

| Slice | File MB | Context MB | Heap-knowledge MB | Hash-consed MB estimate |
| --- | ---: | ---: | ---: | ---: |
| `moduleFunction` | 154.4 | 128.1 | 12.3 | 5.5 |
| `inertRead` | 145.2 | 124.1 | 9.0 | 4.2 |
| `resolve` | 132.7 | 115.8 | 6.1 | 3.5 |
| `collect` | 410.7 | 1.0 | 408.1 | 68.2 |
| `closeStatements` | 265.8 | 1.0 | 263.7 | 44.4 |

The last column models exact-subtree sharing with six-byte references; it
is not a measured implementation. Component and holder partitions describe
the same bytes from different perspectives and must not be added.

**Cited — union reads.** `moduleFunction` contains 187 `unionVar` occurrences,
occupying 125.6 MB, including 62.8 MB in expression trees beside effects.
Of these, 165 have `readAt field (var slot)` shape, occupying 121.5 MB,
with 26 distinct receiver/field/result triples. The field breakdown reports
160 `kind` occurrences, rather than 165. The dominant compiler API `Node`
reads have 109–110 alternatives, with `sub(readView(var))` arms and no
receiver coercion. Those arms account for approximately 83% of checked
evidence nodes in the supplied attribution.

The report gives 22 and 20 summary triples for `inertRead` and `resolve`.
These counts omit checker scope: safe summary tables may contain more entries.
Other union proofs include conditionals, member binding and optional reads.

**Cited — storage versus checking.** All measured nodes have effects.
In `moduleFunction`, 1,144 of 1,840 node expressions are byte-identical
to the effect's proof: 69.0 MB, approximately 45% of the file.
Exact-subtree caching reduces counted evidence checks from 21,957 to 21,251,
approximately 3.2%. A term/type-only key gives much larger apparent savings,
but omits context and assumptions and is not a valid checking cache key.

**Cited — heap knowledge.** `collect` contains 3,811,682 distinctness links
occupying 404.2 MB; one node has 16,143 links over 30 cells and 38 values.
`closeStatements` contains 2,475,154 such links occupying 259.5 MB.
Heap knowledge occupies 99% of both files; distinctness alone occupies
approximately 98%. Exact sharing compresses these links but retains the
pairwise representation that generates them.

**Cited — check profiles.** Sample shares approximate CPU attribution.

| Component | `moduleFunction`, 15.6 s user | `collect`, 19.8 s user |
| --- | ---: | ---: |
| JSON reading | 26% | 62% |
| Strict decoding, including round trip | 34% | 26% |
| Plan extraction and freezing | 12% | Not separately reported |
| Checking proper | Approximately 21% | Approximately 6% |

Peak RSS is 9.4 GB and 12.2 GB respectively. For `collect`, lone-surrogate
checking accounts for approximately 20% of all samples.
The owner's separate timing reports approximately 57 s search user CPU
versus 19 s check CPU for `moduleFunction`; these timings are not the same
profile run. `protocolPattern` has a 300 s search timeout and no certificate.
Its image-validation contribution is unmeasured.

## Acceptance and proof scope

**Proved.** In [ProgramCertificates.lean](../../lean/Verification/Programs/ProgramCertificates.lean),
`checkTreeUsing_sound` derives `HasTyUsing` from checked evidence and
`CodesSound`. [ProgramTyping.lean](../../lean/Verification/Programs/ProgramTyping.lean)
supplies semantic typing soundness.
[Claims/Json.lean](../../lean/Verification/Source/Claims/Json.lean)'s
`checkJson_safe` connects exact CLI acceptance to `DocumentSafe` for the
main document and every imported module.

**Cited.** [CertificateProducer.lean](../../lean/Verification/Programs/CertificateProducer.lean)
can return `.node j .var []` as a header when precise effect evidence succeeds
without ordinary typing. [ControlFlow.lean](../../lean/Verification/Programs/ControlFlow.lean)
checks the selected effect against that header.
Its `checkYields` also inspects and sometimes checks the expression tree.
[GraphCode.lean](../../lean/Verification/Programs/GraphCode.lean)'s footprint
checking can inspect and check that tree under restricted code availability.
Consequently, “only the root is read” describes the main effect-check path,
not every consumer of `NodeEvidence.expression`.

**Conjectured — invariant.** Preserve every accepted effect-only node,
promise/yield obligation, footprint obligation, exceptional edge and source
obligation. Preserve request counts before zipping, `freezePlans`, exhaustive
`FunctionPlan` to `CertifiedPlan` conversion, and the exact premise and
main/module conclusion of `checkJson_safe`. Resource exhaustion stays distinct
from rejection. Source and host assumptions retain their
[existing scope](../DESIGN.md#trust-surface).

## Stage 1: node headers and strict decoding

**Conjectured — representation.** Separate the node's sequent from optional
ordinary typing evidence. Encode its header as either an explicit sequent
or a reference to the root of its selected effect's typing proof.
Permit the latter only for constructors whose selected root is exactly the
node's sequent; a sliced-read premise may have a different result type.
Check the resolved header against the reconstructed program and claims.

Ordinary typing evidence may select that same effect proof or carry a separate
proof. Its absence is valid when precise effects establish safety and no
other consumer needs ordinary evidence. An effect-free node requires ordinary
typing evidence. Promise/yield and footprint consumers retain the rule and
premise inspection they need, validating evidence in their own environments.
A root reference supplies a sequent; it does not establish ordinary typing.

Initially replace byte-identical duplicates by local references. Retain
separate evidence wherever an existing consumer needs it. This avoids making
a general proof arena a prerequisite for removing the measured duplication.

**Conjectured — decoding.** Replace `decodeStrict`'s `fromJson`/`toJson`/
`sameJson` round trip with structural decoders that enforce the same exact
shape while traversing each field once. Preserve explicit required fields,
unknown-field rejection, constructor arity, labels, numbers, optional values
and the existing parser's object-key semantics. Audit nested codecs as well
as the outer bundle. Use one current encoding, updating all consumers and
fixtures together, without a version tag or compatibility decoder.

Replace `loneSurrogate text.toList` with an allocation-light scan over UTF-8
text, preserving escaped-backslash, quote and surrogate-pair handling.
Keep invalid UTF-8 and lone-surrogate refusal: the JSON parser's replacement
character is not an equivalent wire string.
The target is linear structural decoding and text scanning; label validation,
plan extraction and semantic checking have separate costs.

**Required lemmas and review.** Prove header resolution preserves the exact
sequent and consumer behavior, including promise and footprint inspection.
Establish strict-decoder equivalence to the old round-trip acceptance relation
and scanner equivalence on valid UTF-8 JSON text. The text-to-JSON boundary
also requires direct adversarial controls; `checkJson_safe` starts with JSON.

**Trust.** Decoder, text scanner and checker consumers change trusted code.
Producer selection and duplicate detection remain untrusted.

**Conjectured gain.** Eliminating the measured exact duplicates targets
69.0 MB, taking `moduleFunction` toward 85.4 MB before reference overhead.
This removes serialization and decoding work, not 45% of semantic checks.
The profile attributes roughly 19% of `moduleFunction` samples to re-encoding
plus `sameJson`, and roughly 6% to surrogate scanning; these are removable-work
ceilings, not speedup promises. For `collect`, the corresponding measured
targets include 20% surrogate scanning and approximately 10% re-encoding.
Replacement validation still costs time. Savings overlap with smaller input.

## Stage 2: a narrow union-read summary

**Conjectured — boundary.** Introduce `ReadSummary G images C field B`,
initially using ordinary universally valid subtyping only. Its checked meaning
is ordinary typing of `readAt field (var slot)` in any context whose selected
slot has exactly type `C`. It depends on the fixed graph and image-checking
environment, and requires no available code entries or body-specific coercion.

The first rule covers direct `readView(var)` arms, optionally followed by
ordinary subsumption. The checker enumerates `ProgramTyping.members G C`.
For each member it checks representation, `namedMembers`, field membership,
the `readView` restriction on `length`, and the field-result coercion to `B`.
Every enumerated arm must have a witness; extra or missing witnesses fail.
Receiver coercions, ordinary fields, callable fields and other read rules
retain their existing evidence until separately justified summary cases exist.

A use checks the exact term, slot bounds, receiver type, field and result.
An immutable slot fixes a value, not the referenced object's contents.
The summary proves a read at its lifetime contract in an admissible heap.
It supplies no cached observation, field location, heap link or getter effect.
The source boundary assumes modeled data properties; accessors remain outside
the admitted fragment. Preserve `lenView`'s distinct term, optional/index
missing-value behavior and prototype exclusions.

`typedRead` retains its `fieldOperand`/`optionalOperand` checks and frame
construction. A typing summary cannot discharge those checks or an effect's
normal or exceptional postcondition.

**Conjectured — encoding before an arena.** Each reconstructed checking scope
has a `readSummaries` array; expression evidence carries `readSummary(index,slot)`.
Check each entry once in that scope and check each use's exact judgment.
Entries contain member witnesses and ordinary subtype evidence, without
contextual expression trees. Entries have no dependencies on other summaries.
This provides consumer reuse independently of producer memoization.

**Required lemmas.** `readSummary_sound` derives the existing `unionVar`,
`var`, `readView` and subsumption judgment. `readSummary_reassign` transports
successful checking to reassigned graphs and image environments.
Ordinary summaries used inside qualified bodies require a proved embedding
of ordinary subsumption into that body's rule. Any future qualified summary
needs the qualified transport obligation below and a distinct scope.

**Trust.** The summary decoder and derived-rule checker change trusted code;
their soundness is proved in Lean. Search memoization by exact environment,
receiver, field and result remains untrusted and emits compact evidence
directly, avoiding construction of the contextual arm trees.

**Conjectured gain.** The measured direct-read family occupies 121.5 MB before
Stage 1; much of it overlaps Stage 1's duplicates. Approximately half remains
on the checked side, so the incremental byte opportunity is roughly 60 MB
before compact witnesses and scope duplication. Replacing the dominant arms
targets approximately 83% of counted evidence nodes, while retaining arm
coverage and subtype checks. The profile does not isolate their CPU cost;
83% fewer evidence nodes does not imply 83% less check CPU. This stage also
targets repeated proof construction in the larger search stage.

## Stage 3: hash-consed wire structure

**Proved and cited — the document.** A bundle is written as typed tables
of types, contexts, links, heap knowledge and derivation nodes, and the
responses and obligations naming their entries by position
([evidence document](../REQUEST-PROTOCOL.md#evidence-document),
[EvidenceWire.lean](../../lean/Verification/Source/EvidenceWire.lean)). A
derivation's premises are earlier entries of its table; a reference is a
position in the table its field's kind gives. The decoder reads the shape
strictly, then builds each table in order, each entry from the entries it
names: a reference past its table, or a premise at or after its
derivation, is refused, so kind, bounds and acyclicity are checked. The
built table satisfies the unfolding equations (`proofs_unfold`), which have
one solution (`unfold_unique`): resolution preserves the unfolded
structure. An entry named twice is one value of the decoded bundle.

**Cited — checking.** The checker reads the decoded bundle, the bundle the
references unfold to, through the existing checks: reference-aware checking
is the existing checking of that bundle, its transport under reassignment
the existing one, and every inspector, promises and footprints included,
reads the same rules and premises. `checkJson_safe` keeps its premise and
its safety conclusions; `DocumentSafe` names the decoder
(`EvidenceWire.decode`) where it named `decodeStrict`. A derivation named
twice is checked at each use: storage sharing is no checking cache. The
`Answered` subtype-search cache is unchanged.

**Cited — what is interned.** Search writes its bundle through
`EvidenceWire.encode`, which interns each type, context (by its types'
positions), link, heap knowledge (by its facts and its links' positions)
and derivation node (by its claim, rule and premises' positions), comparing
keys in full on a hash collision. A sequent is written inside its
derivation node, its context and type by reference: in the measured
certificates distinct sequents and distinct derivation nodes are one to one
(`moduleFunction`, 3,823 and 3,822). Contexts are exact: their table holds
0.08 MB of `moduleFunction`'s 5.8 MB, so context deltas are not taken.
Edges, handlers, promise facts and read summaries are written in full.

**Trust.** The reference decoder is trusted code; its resolution is proved
to unfold. The shape of the tables is read by `decodeStrict`, whose
`fromJson`/`sameJson` round trip stays as trusted as before. Interning and
hashing are untrusted; collision resistance is not assumed.

**Cited — measured, 2026-10-23.** See the
[Certificate size](../../WORK.md#status) row: certificate bytes fall by
roughly five times on the three `fragment-expressions.mts` slices and the
two heap-knowledge slices, check memory with them. The residual bytes of
`collect` and `closeStatements` are their distinct links (55.7 MB of
`collect`'s 77.5 MB), Stage 4's target. Checking proper dominates
`moduleFunction`'s check after this stage.

## Stage 4: allocation freshness and slot-relative heap knowledge

**Cited.** [HeapLinks.lean](../../lean/Verification/Semantics/HeapLinks.lean)
defines distinctness as inequality of two field locations.
[HeapExpressionRules.lean](../../lean/Verification/Programs/HeapExpressionRules.lean)
derives fresh-allocation separation from older contract fields.
[HeapKnowledge.lean](../../lean/Verification/Semantics/HeapKnowledge.lean)
transports knowledge through slot shifts and projections.
The measured input/output link differences are almost their combined size
because pushing a result shifts slots; raw per-node deltas offer little help.

**Conjectured.** Represent each allocated cell's freshness once, with its
allocation provenance and the older locations from which it is separated.
Resolve current slots through a checked slot-relative map to stable local
value identities. Derive field-location inequality on demand rather than
materializing every cell/field pair. Allocation-event identities must be local
to the justified execution state: a source allocation site alone cannot
identify repeated loop allocations. Distinct slot names do not imply separation.

Retain explicit residual separation facts where freshness provenance does not
justify them. Joins keep only justified common information. Projections,
aliases, dropped results, writes, calls and handlers preserve exactly their
existing guarantees. Read links remain heap-dependent; separation concerns
locations and survives heap updates. A freshness token supplies no claim
that arbitrary imported objects or later aliases are distinct.

**Required lemmas.** Fresh allocation establishes the compact invariant;
its separation query entails `HeapLinks.Holds`' location inequality.
Prove transport through mappings and joins, write-frame preservation,
normal/exceptional effect soundness, and reassignment compatibility.
Prove old accepted knowledge has a suitable compact representation where
claimed, with a residual representation for other cases.

**Trust.** Heap-knowledge semantics, decoders and effect/edge checkers change
trusted code. Producer knowledge propagation remains untrusted.
This has higher semantic risk than structural sharing and is a separate item.

**Conjectured gain.** The target is 404.2 MB in `collect` and 259.5 MB in
`closeStatements`, approximately 98% of baseline bytes, before replacement
facts. No compact-size prediction is measured. JSON reading and decoding
occupy approximately 88% of `collect` check samples, making representation
reduction the principal opportunity. Earlier-stage savings overlap.

## Stage 5: a general fact arena, conditional on residual cost

**Conjectured.** Add subtype, image and expression facts only if measurements
after the preceding stages show worthwhile repeated semantic validation.
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
insufficient. Reconnect request safety and footprints to `checkJson_safe`.

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
measurement. Run targeted slices during development, required suites before
merge, and the full census once on main. These measurements determine whether
the fact arena earns its proof and maintenance cost.
