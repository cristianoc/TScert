# String lengths as terms

Part of [checked bound annotations](checked-bound-annotations.md) (#115).
The design of the string-length facts that the
[audited string contracts](../SOURCE-CONTRACTS.md#string-method-postconditions)
do not state: the lengths of further string natives' results, and a
string's element read below its length.

## The existing mechanism this extends

[Linear facts](../ARITHMETIC.md#linear-facts): the term
$`\mathrm{strLength}(x.p)`$, a string's count of UTF-16 code units, at most
$`M=2^{53}-1`$; `string-length`, which states it of a `length` read on
normal return; `string-concat`, the exact sum on normal return, a
concatenation past $`M`$ throwing; and the audited postconditions of
`charCodeAt`, `codePointAt`, `slice` at
$`0\le a\le b\le\mathrm{strLength}(s)`$, `indexOf` and `lastIndexOf`,
consumed by `call-ensures`.

## Further natives' lengths

**Proposed.** Each string native whose result a bound reads states its
result's length on normal return, audited against
[ECMA-262](../REFERENCES.md#ecma-262)'s algorithm, its argument conversion
and clamping included:

- `replace` and `replaceAll` with the empty string as the replacement:
  a result no longer than the receiver; with a string pattern and no
  replacement function, a length the occurrences determine (pretext's
  `mapSourceLineBreaks` and `segmentAtLineBreaks`, which need
  `breaks.length >= normalized.length + 1`);
- `slice` and `substring` at one argument or at arguments the audited form
  does not bound: the length after clamping;
- `repeat`: the receiver's length times the converted count, the count
  converted as JavaScript does (negative and infinite counts throw, NaN is
  zero);
- `padStart`, `padEnd`, `trim`, `normalize` and `JSON.stringify`, each with
  its callbacks and abrupt outcomes audited.

An oversized result is an abrupt outcome, never a truncated or oversized
normal string. A length-preserving contract reads UTF-16 code units: the
model's replacement of a lone surrogate occupies one code unit, so the
length holds where scalar equality does not. These contracts await the
owner's review of the trust each states.

## A string's element below its length

**Proposed.** A read `s[i]` of a string at a safe integer
$`0\le i<\mathrm{strLength}(s)`$ is a one-unit string, never `undefined`,
so `normalized[i]!` checks. The model's `elemStr` step reads it; a typing
rule states it, as [reads below the length](../PROGRAM-TYPING.md#reads-below-the-length)
does for an array.

## Cases

Positive cases for each contract's pretext caller and for a string's
element read in a loop below its length. Negative cases, each run under
Node: a read at the length, a bound on the wrong string, and a `replace`
whose replacement lengthens the result. Forged controls: a length fact
claimed of a native's result its contract does not state.
