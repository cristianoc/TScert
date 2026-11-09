# Element facts

Part of [checked bound annotations](checked-bound-annotations.md) (#115).
The design of the quantified facts over array elements that
[quantified clauses](../ARITHMETIC.md#quantified-clauses) do not state:
facts over a typed array's bytes as its views share them, across the
natives that write them, and over a prefix a function fills and counts.

## The existing mechanism this extends

[Quantified clauses](../ARITHMETIC.md#quantified-clauses): the index fact
$`\mathrm{every}(x.p,t,\Phi)`$ over an array's or a typed array's element
store, read at an element by `every-read`, kept across a push, an exact
typed-array element write and a write apart from its
[element region](../FOOTPRINTS.md#element-regions), and extended to a
prefix by an exact write at its bound. A typed array's elements are the
store at its model key `[[viewElements]]`, one per view
([typed arrays](../SOURCE-CONTRACTS.md#stated-library-types)).

## Views sharing bytes

**Proposed.** Model a typed array's elements as bytes of its buffer at the
view's offset and kind, so two views over one buffer read the same bytes.
A fact over one view then transfers to a `subarray` of it, read at the
offset, and a write through either changes what both read. Every native
writing a view's contents (`fill`, `set`, `copyWithin`, a write through an
overlapping `subarray`) states its writes, and a fact it may change is
recomputed or dropped. The fixed-size, never-detached buffer assumption
stays a host assumption. A typed write proves the bound of its converted
value: `Int32Array` wraps, `Uint8Array` reduces modulo 256, and a float
array admits NaN and fractions.

## A counted prefix

**Proposed.** A function filling a typed array up to a count it returns
(pretext's `findGraphemeEnds`, its `ends` conditional on `ends !== null`)
states a postcondition over the prefix below its result, with the capacity
the prefix needs and the bounds of the stored endpoints. Its callers read
$`[0,\mathit{count})`$ whatever the unused capacity holds
(`getUnspacedGraphemes`, `countEmojiGlyphs`, `setupClusterBoundaries`).

## Generated tables

**Proposed.** Tables decoded at load (`unpackClassRuns`, `unpackTable`,
`markRuleBoundaries`) need their decoding checked: row and stride
predicates over the decoded elements, products of variable terms, and the
bit arithmetic of their encodings. A comment of the table generator states
no fact.

## Cases

Positive cases for a fact read through a `subarray`, a counted prefix and
its caller, and a decoded table's row read. Negative cases, each run under
Node: a `fill` of a value the body excludes, a `set` from an array whose
elements it excludes, and a read past the counted prefix. Forged controls: a fact over a view
claimed of its `subarray` at another offset, and a prefix fact claimed past
the returned count.
