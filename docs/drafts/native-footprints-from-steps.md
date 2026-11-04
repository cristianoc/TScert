# Draft: native footprints from their specification steps

A design for making the proved array-mutator lemmas part of what acceptance
rests on. Base: TScert main at b7fa8da8. Claims are labelled **proved** (with
the Lean name), **cited** (with the document and its scope) or
**conjectured**.

## The existing mechanism this extends

[Native footprints](../SOURCE-CONTRACTS.md#native-footprints) (cited): each
native signature states a closed footprint
([FOOTPRINTS](../FOOTPRINTS.md#changes-and-footprints)), and the checker
consumes it at a selected call as it consumes any signature's
(`ExpressionEffects.selected_sound`, proved). The footprint of a native is a
trusted row of the trust surface; for the array mutators the row's argument
is a proof about a separate model of the specification steps:

- `FootprintNatives.lean` models a store as `Arr` (its element locations and
  the next location) and the ECMA-262 steps as `Arr.set`, `Delete` and a
  length change; `Arr.push_grow`, `Arr.unshift_grow`, `Arr.setLength_grow`
  and `sort_grow` prove the store relation `grow` of the step sequences, and
  `map_rely` proves `map`'s density between callbacks (proved);
- `array_native_post` turns the store relation, with the audited fact that a
  native changes nothing but its store and element contents, into the
  footprint's postcondition (proved);
- the checker never reads these lemmas: the footprint is data in the native's
  signature, so the trust row says "push grows the store" and the lemma is
  evidence for an auditor (no module outside `FootprintNatives.lean` and its
  controls names them at b7fa8da8; observed).

## The design

A native's trusted row states its specification steps, and its footprint is
derived from them:

1. Lean holds a table from each modelled mutator (`push`, `unshift`, `pop`,
   `shift`, `reverse`, `sort`'s writeback) to its step sequence over `Arr`.
2. The footprint a native signature may state is computed from that table
   (`grow` for a sequence `Arr.*_grow` covers, `receiverStore` otherwise),
   and the declaration decoder refuses a signature of a modelled mutator
   whose stated footprint is not below the computed one.
3. The trust premise of a selected native call becomes "the native runs the
   steps its row names, and changes nothing but its store and element
   contents" (audited, against ECMA-262); `array_native_post` with the step
   lemma discharges the footprint (proved once the rule takes this premise;
   conjectured until then).

The trust surface's array-mutator rows narrow from a footprint per native to
a step sequence per native; `map`'s dense signature takes `map_rely` the same
way.

## Separation knowledge

`map_rely` and the stability lemmas take `SepKnowledge`, whose provenance
stamps (`FootprintProvenance.lean`: marks, `after` and `before` stamps, the
mark-renaming edge check) no checker uses and no work item plans beyond
[deferred precision](../FOOTPRINTS.md#deferred-extra-precision). The
implementation of this design removes the stamps from `SepKnowledge` (its
class evidence and distinct pairs remain), with the stamp controls of
`FootprintControls.lean`, and FOOTPRINTS's deferred section names the commit
that held them.

## Cost

The derivation runs where native declarations are decoded, once per
signature, over a table of six entries; a verification run reads no new
document and searches nothing new (conjectured: no measurable change; the
implementation is benchmarked by the merge census).

## Open questions

- Whether `splice`'s row (`receiverStore`) gets a step sequence too, or stays
  audited.
- Whether the step table lives beside the overlay in Lean or is read from the
  declaration document with its steps named there.
