# Keeping contract facts across calls

Part of [checked bound annotations](checked-bound-annotations.md) (#115). Drafted by Astra on `5701f1e9`.

## The existing mechanism this extends

[Record invariants](../PROGRAM-TYPING.md#record-invariants) are boundary contracts:
callers establish parameter facts; bodies establish result and retained-parameter facts.
[Footprints](../FOOTPRINTS.md) determine which facts survive between boundaries.
[Field paths §4.1 and sealed handles §5](field-paths-and-record-invariants.md)
supply the same interpretation for records and their opaque handles.
The proposal extends regional footprints, separation facts and checked default binding.
`receiverOwn`, `freshObject` and fresh-store tracking provide existing special cases;
the regional composition and framing lemmas exist, but their general integration is deferred.

## Target and evidence

The target is pretext `2b11a4c` minus its bound rewrites, with arithmetic annotations,
at `/private/tmp/claude-501/astra-115/target/final/pretext/src`.
The owner reports 137 accepted functions with record invariants versus 148 without.
That comparison identifies a regression; it does not establish how many this proposal closes.
Complete verification requires every target function and its initialization dependencies.
Any actual unsafe source requires an explicit repair or contract decision; annotation alone cannot establish safety.

## Proposed footprint and separation judgment

A call summary bounds writes by explicit regions, alongside its existing closed footprint.
Regions name module binding cells, receiver or argument own locations, and checked paths;
allocation during the invocation may additionally supply fresh locations.
“Module-owned” abbreviates a certified region with stated separation, never allocation provenance alone.
A caller may pass back an object obtained from a cache, and two arguments may alias.
The preservation judgment therefore checks the fact's complete support against every write region.
Support includes intermediate field cells, terminal stores or number cells, and guard reads.
A kept root field alone does not protect the array or record reached through it.
Where supports overlap, the existing change relation may still prove stability;
otherwise the fact expires and must be re-established at its next boundary.

Use `receiverOwn` directly when all modeled writes belong to that receiver.
Generalize its region representation only for summaries needing multiple roots or module cells.
`freshObject` states freshness of a result's own locations, not of everything reachable from it.
Similarly, freshness relative to a helper's entry permits writes during that invocation;
a cached object reused on a later invocation needs an explicit region on that later call.
Root substitution, path reads and joins must preserve or check the region's interpretation.

## Certifying helpers, natives and callbacks

For `getEngineProfile`, the proposed summary writes `cachedEngineProfile`'s binding cell
and locations freshly allocated by `buildEngineProfile`, subject to auditing its host reads.
Prove the private binding cell apart from source objects' field and store locations.
Returning the profile does not expose that binding cell; subsequent profile-field writes would need their own region.
Certification follows the graph, including initialization, transitive calls and exceptional handlers.
The producer proposes summaries; Lean checks writes and selected callee summaries at every node.
Recursive summaries require mutually checked bodies; imports transport the certified summary.

For `Map.set`, audit the standard operation as changing its table and observable size.
The current model exposes `size`, so the WeakMap empty-footprint argument does not transfer.
Use `receiverOwn` only after the model represents all affected locations as receiver-owned
and establishes their separation from ordinary record fields and array stores.
An existing broad numeric view of `size` does not itself establish that separation.
Keys and stored values remain aliases; inserting an array does not write that array.
Model internal-state separation explicitly and record its native correspondence as reviewed trust.

Measurement helpers receive summaries naming the actual cache, context and receiver locations they modify.
A helper that writes `measurement.spaceKerning` needs that field's region and any nested mutations.
Canvas operations and other host calls need audited contracts covering reentrancy and observable state.
Their safety cannot follow merely from taking no prepared-data parameter.

Give `onLine` an explicit effect-qualified callback contract through the existing callable mechanism.
Start with heap preservation; admit captured output accumulation through certified separated regions.
Check each supplied closure's body and captures, then propagate its summary through wrapper callbacks.
An ordinary arrow supplies no preservation promise: a callback can capture and truncate a prepared array.
External callbacks must meet the stated contract, with that obligation documented at the public boundary.
Normal-return guarantees frame normal continuations; caught throws require `onThrow` or renewed proofs.

## Default parameters and module constants

For `p: R = d`, the incoming contract is “argument is undefined or satisfies `I_R`”.
Missing arguments take the undefined branch; supplied arguments establish the invariant at the call.
Lower the default in JavaScript order, proving `I_R` of its value after its evaluation.
At the branch join, both alternatives establish the invariant of the effective parameter.
Later defaults may mutate earlier arguments: preserve or reprove those facts before body entry.
Retained-input ensures remain about original actuals, guarded when those actuals are undefined;
the default value needs separate local tracking and must not be substituted for the caller's actual.

The initialization unit proves `TEXT_START_CURSOR`'s invariant from its two zero fields.
Transporting that fact into later invocations additionally requires preservation of its support.
A `const` binding proves stable identity, while its object remains potentially mutable.
For this constant, certify all uses, aliases and callees as preserving the two cursor fields;
escaped aliases require checked contracts, and initialization order must justify every fact read.
A general mutable module constant carries only facts established for the current heap.
Initialization facts and their preservation evidence become explicit dependencies of consuming units,
within the documented module-composition boundary rather than an implicit new entry assumption.

## Proofs, cases and delivery

All Lean paths below are relative to `lean/Verification/`; the extensions are proposed obligations.
`Semantics/{Footprints,FootprintProvenance,HeapSeparation,IndexFacts,CallEffects}.lean`
must prove region interpretation, separation, composition, substitution and support preservation.
`Programs/{ExpressionEffects,GraphCode,PromiseCalls}.lean` must certify summaries and frame facts;
`Source/Lowering/Bindings.lean` must establish default-branch facts with faithful evaluation order.
`Source/{SourceExtraction,SourceRequests}.lean` and `Source/Claims/Imports.lean`
must connect initialization, entry assumptions, exported summaries and checked returns.
Audit effect subtyping, substitution, binding, overloads, all wire mappings and exceptional edges.
`SourceClaimJson.checkUnitJson_safe` must cover the exact accepted verdict and every accepted function.

Keep census-linked positives for cached-profile calls, Map insertion, measurement and callback wrappers,
plus both layout defaults with omitted, undefined and explicit cursor arguments.
Run Node negatives for captured-array truncation, cached-object alias mutation, invalid defaults,
a later default invalidating an earlier parameter, and mutation of a shared default constant.
Forge separation, native effects, initializer facts and default certificates through production and checking.
Preserve unsafe constructor, cast and parallel-array mutation controls; safe unsupported forms remain gaps.

The smallest first step is a `getEngineProfile`-shaped helper writing one private module cell:
certify that singleton write region, prove its separation, and retain one caller's path invariant.
Then add Map internal-state precision, default contracts, constant facts and callback summaries.
Keep invariant obligations while improving transport through calls, loop joins, aliases and imports.
Run targeted before/after functions and one dependent function, then `make test` and documentation checks.
Report identical-scope gains and losses; full target acceptance, including initialization, decides completion.