# Diagnostic traversal

A diagnostic run inventories refusals under explicit approximations. Its result
is `diagnostic` even when every local attempt succeeds. It establishes no source
safety judgment. [Verification](DESIGN.md#what-verified-means) owns that judgment.

```sh
node pipeline/diagnose-source.mts source.ts project-directory
make census DIAGNOSTIC=1
```

The census accepts its ordinary file, function and shard selectors. Its JSON
record contains every occurrence, source spans mapped back to the original
module, opaque regions, a ranking by distinct target functions and affected
statements, and statement coverage with holes. Counts across ranking groups
overlap. A group describes diagnostic wording, not a proved common cause.

## Recovery boundaries

The syntax gate recovers at expression, statement and annotation boundaries.
A typed refusal restores a copy of the gate's entry state, then substitutes
`undefined`, an empty block or `unknown`, respectively. The entire replaced
region is recorded as opaque. Compiler and file-system failures propagate as
tool failures. The original file remains the source of all offsets.

The producer recovers at expressions, statement transfers, binding-schedule
operations, conditions and iterator steps. Each refusal restores candidate
state and records the failed region as opaque. An expression assumes its
expected type, or `unknown`. A failed declaration preserves its name and
storage mode at its annotation, or `unknown`; existing storage contracts stay
fixed. Failed binding reads supply `unknown` and continue through the remaining
bindings. Statement and binding recovery forget field observations and widen
local slots to their contracts. Control-flow edges remain those of the supplied
graph. A function analysis that refuses outside these boundaries yields empty
claims, allowing sibling functions to be analyzed. These approximations can
create or hide downstream failures. They carry no effect guarantee.

Typed extraction retains sibling units after a unit's refusal, with its
immutable equation store restored to the value at the unit's entry. Shared
annotation and equation preparation is a document boundary: a refusal there
leaves the document unexamined.

Search first attempts the complete retained program. A successful aggregate
check leaves no search blockers. After a refusal, diagnostic search attempts
every extracted standalone expression obligation and every
graph node, including closure bodies. A node assumes its supplied interface
and stated heap requirements; predecessor-derived facts are forgotten. Closure
code is provisionally admitted during those local attempts. Expression search, every normal edge, the exception handler and the return
obligation receive independent attempts. After expression failure, outgoing
attempts assume its supplied result type and forget output heap facts. Edge
attempts check both target types and supplied heap requirements. Return promises
use argument positions propagated through the graph. These local attempts do
not propagate predecessor implications or retry combinations of promise yields;
they can therefore report failures that aggregate search discharges. Each extracted sibling unit also receives its own graph and footprint checks.
Aggregate checking uses the ordinary search and checking operations. Its
evidence is discarded. Imported program values are read at their declared
contracts; the diagnostic parser does not certify imported module bodies.

Shared declaration collection, execution-plan construction and producer
initialization can refuse before local recovery is available. Their remaining
regions are unexamined. The inventory therefore does not claim to enumerate
all refusals hidden behind those boundaries, or those inside an opaque region.

## Attribution and coverage

Each occurrence has a source span, layer, refusal summary, identifier and
dependencies. Repeated type-graph tables are omitted from the inventory.
Source and producer recovery identifiers conservatively taint subsequent
observations in the document. Local graph attempts additionally name
`supplied-interfaces`. These dependencies are conservative scope attribution;
they are not a data-flow or causal analysis. An occurrence independent of
recovery can still depend on ordinary supplied claims.

Slicing records the original span of each copied declaration. Reconstructed
imports retain the original import's whole span. Helpers retain their original
module and offsets across target functions. The census ranks distinct target
functions, counting each once per wording group, and counts their original
executable statements using the [statement inventory](DESIGN.md#statement-coverage).

Coverage with holes counts statements only when the retained slice passes
aggregate checks under diagnostic assumptions and no opaque region intersects
the statement. Enclosing statements intersecting a hole are holes too. A slice
that cannot complete contributes no retained statements. This is conditional
coverage of a diagnostic approximation, not verified statement coverage or a
prediction of coverage gains from implementing a feature.

## Acceptance boundary

Diagnostic source and proposal documents use separate envelopes. Ordinary
source commands refuse those envelopes. The diagnostic CLI writes an inventory
and has no evidence output parameter. Its result type has no `verified` variant.
The stages `diagnostic-parse`, `diagnostic-lower`, `diagnostic-propose` and
`diagnostic-search` have distinct identities in the [stage store](STAGE-STORE.md).

Ordinary extraction stops at its first refusal and requires every unit's plan.
The exhaustive conversion to `CertifiedPlan` and the theorem
`SourceClaimJson.checkJson_safe` govern ordinary acceptance. Diagnostic traversal
has no conversion to that acceptance result. A control in
[`pipeline/test.mts`](../pipeline/test.mts) submits diagnostic envelopes to
ordinary source checking, including envelopes over an otherwise verified
source.
