# A conservative own-key test for the function compiler

## The existing mechanism this extends

The shared `Tag`, `tagHolds`, `tagHoldsIn` and `test` reduction in
[Calculus.lean](../../lean/Verification/Semantics/Calculus.lean) already provide
pure object predicates. The finite tag representation/normalization in
[ValueSets.lean](../../lean/Verification/Semantics/ValueSets.lean) and the
[request JSON boundary](../../lean/Verification/Source/RequestJson.lean) own
their representations. Extend that test mechanism, not heap/world semantics.
The paper's objects are maps of own keys; B's fieldRead executes an own-field
check before choosing readAt or undefined.

## Why the existing operations do not directly reify B's read

`Operation.code` can inspect the closed value held by its environment. At a
symbolic graph variable it cannot inspect the eventual object's field map.
Shared readAt follows prototypes on an absent key, and hasKey/tagHoldsIn does
too. Neither directly implements the own-key branch. Assuming no prototypes
would restrict the embedding without deriving that property for the complete
paper domain. A missing backend observation is not a false paper statement.

Add a pure `hasOwnKey key` tag: on an object it tests its own immutable field
map; otherwise it is false. Compile the existing B own-read branch using the
object tests isRef/isFun, this own-key test, readAt and undefined. Nonobjects
must retain raw readAt stuckness, not become a successful undefined read.
Prove finite administrative simulation and inversion for arbitrary machine
value environments. This is not definitional code equality and is not a native
library contract assumption.

## Preserve A's request language

RequestJson currently derives FromJson Tag. Adding a semantic constructor alone
would expose the new tag at every request nesting, including graph code. Freeze
the existing eighteen-constructor request tag vocabulary explicitly. A private
legacy wire datatype with the exact existing constructor/parameter names can
retain its derived codec, with conversion into the shared Tag. The public Tag
FromJson instance decodes only that datatype, and must be installed before
Tm/CallCode/Continuation decoding. The new model-only tag is rejected everywhere.
Keep old ToJson results exactly equal to legacy ToJson, proved for every legacy
constructor and arbitrary payload; prove successful Tag decoding lies in the
legacy image. Constructor-name/parameter spelling and strict re-encoding must
stay unchanged. Do not rely on a top-level-only JSON scan.

Append the new tag's internal key after all existing tag keys. Extend the
closed normalization/soundness cases, treating own-key predicates as pure;
do not inherit prototype-sensitive premises from hasKey. Preserve old meanings,
key encodings and default source inference. No A producer starts emitting the
new constructor. A and shared code must not import Paper.

## Validation and trust

Before claiming conservativity, prove legacy codec conversion/encoding and
range properties, compare old-tag semantic/key equations and check the actual
request boundary at nested tests/graph continuations. Run focused shared builds,
both full axiom audits, the import boundary and all required regression suites.
Report the exact changed shared files and any diagnostic differences separately.
The old acceptance theorem remains, and the accepted request-tag vocabulary is
unchanged. No new axiom, opaque safety premise or global native contract is added.
The primitive defines the shared model's own-key observation; this is not a claim
that a real native library implementation has been verified.

Astra independently inspected the paper, shared prototype semantics and derived
JSON instances before this design. It confirmed the reification gap, accepted
this conservative extension of the existing mechanism, and identified the wire
boundary as a required proof obligation. Implementation and validation are
separate from this design.
