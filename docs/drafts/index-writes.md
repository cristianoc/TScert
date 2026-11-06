# Draft: array writes at a run-time index

The design of `xs[k] = v` with `k` a `number` the program computes, on an
array of a writable homogeneous contract; its status is in
[WORK](../../WORK.md#status). Base: TScert main at `e4598052`. Claims are
labelled **proved** (with the Lean name), **cited** (with the document and
its scope) or **conjectured**.

## The existing mechanism this extends

- **`setElem`** ([arrays](../PROGRAM-TYPING.md#arrays); cited): a write is
  typed at a literal index no greater than the required length, so it lands
  in bounds or appends and never leaves a hole. The calculus step it rests
  on is general in the index (`Step.setPresent`, `Step.setGrow` in
  `Semantics/Calculus.lean`): a present element's location takes the value,
  and any other index takes a fresh location, holes filling any gap
  (`placeAt`). The typing rule is what restricts the index to a literal.
- **Checked heap assertions** ([checked expression
  postconditions](../PROGRAM-TYPING.md#checked-expression-postconditions);
  cited) and their transport along graph edges and across calls by
  [footprints](../FOOTPRINTS.md). [#104](https://github.com/cristianoc/TScert/issues/104)
  (Astra's design comment; conjectured there) extends them with index facts
  `integer(i)`, `length(array,x,n)`, `extent(array,x,i,c)` and
  `present(x,i)`; its §8 names this use: "appending requires a valid array
  index, `i = length`".

The rules below consume facts of that one language; they add none of their
own.

## 1. The judgment that fails

For `xs : T[]` (readable, writable, homogeneous) and `k : number`, the
lowering refuses `xs[k] = v` before any rule is tried: `arrayIndex`
(`Source/Lowering/Types.lean`) requires the key's claim to be one array-index
singleton ("a numeric array key needs a proved array-index singleton"). No
rule types `setElem` at a key the claim gives only as `number`, and none
could without a fact about the key's value. In JavaScript the write

- at an array index `k < length` replaces the element and adds no key;
- at `k = length` appends, and the store stays dense;
- at an index `k > length` leaves holes at `length … k-1`, which a readable
  `number[]` admits nowhere ([arrays](../POSITIVE-TYPES.md#arrays): a hole
  is readable only where the position admits `undefined`);
- at a numeric key that is no index (`-1`, `0.5`, `NaN`, `2³²−1`) sets an
  own property. The model admits such a property on an input array, at a
  location whose contract only implies `T` (`numericOwn`,
  [the array invariant](../SEMANTICS.md#the-array-invariant)): another
  reference may hold the object at a type pinning that key narrower, so
  writing any `T` there is unsafe in the model and in JavaScript alike
  (`const o = Object.assign([1], {"-1": 1 as const}); const r: {"-1": 1} = o;
  const xs: number[] = o; xs[-1] = 2` leaves `r["-1"] === 2`, run under
  Node).

The write therefore needs, in the state it runs in (after the right side is
evaluated), that `k` is a valid array index, `0 ≤ k ≤ 2³²−2`, with
`k ≤ length(xs)`; or that `xs`'s store holds an element at `k`, which
implies both.

## 2. What pretext's 57 sites rely on

The target is pretext `18360b74`: the minimal rewrite set `f715061c` with
its 56 `splice` writes and one `length` cut turned back into index writes.
Its census verifies 199 of 211 functions; the 12 refused are the functions
holding a site, each refused at its first one (measured, §7).

Two facts recur:

- **RMW**: a read-modify-write `xs[k] = f(defined(xs[k]))`, or a write whose
  guard reads `xs[k]`. Every RMW site's read passes through pretext's
  `defined<T>(value: T | undefined): T`, which throws on `undefined`. Its
  signature relates nothing between its argument and its result, so the
  read's presence reaches the write only through a certified normal-return
  postcondition: `defined` returns its argument, which is not `undefined`.
- **Clean**: an array whose own keys are its store and its prototype, as an
  array literal or a standard `slice` allocates it. The model fixes an
  object's keys at its allocation ([the array
  invariant](../SEMANTICS.md#the-array-invariant)), so cleanliness is a fact
  about the value, kept by every heap change. On a clean array a read at a
  numeric key that is no index answers `undefined`, so an RMW read that
  `defined` passes was at a present element.

Kinds:

- **P, presence**: a clean receiver and an RMW read at the same evaluated
  receiver and key, the store kept between the read and the write.
- **N, numeric**: integrality and range from the function's own arithmetic,
  comparisons and length reads, the store kept across the calls between:
  #104 steps 1–4.
- **B, from a caller or a callee**: integrality or range of a parameter
  (`from`, `to`, `base`, a closure's `i`), or the length or cleanliness of a
  callee's result (`zeros(n)`, `zeroList(n)`, `measureFitAdvances`,
  `measureAnalysis`'s appends, `lastIndexOf`'s range): #104's owner
  decision P.
- **C, between structures**: a relation between two arrays' lengths, a
  cursor and a length grown in lockstep across a loop, or a flag and a
  cursor.

A site lists the kinds of one sufficient route; none is shown necessary.

| # | Site | Index | Kind | Fact relied on |
|---|---|---|---|---|
| 1 | `analysis.ts:386` `segmentAtLineBreaks` | `flags.length - 1` | P | `flags` a clean literal; RMW |
| 2 | `analysis.ts:423` | `j` | P or N | RMW on clean `flags`; or `0 ≤ j ≤ count−2`, `count = flags.length` observed, length kept |
| 3 | `analysis.ts:425` | `j + 1` | P or N | as 2, `j + 1 ≤ count−1` |
| 4 | `analysis.ts:428` | `j + 1` | P or N | as 3 |
| 5 | `analysis.ts:431` | `j` | P or N | as 2, `0 ≤ j < count` |
| 6 | `han-kerning.ts:210` closure `addWidthTrim` | `i - from` | B | RMW on `out.widthTrims`, clean as `zeros`' result, kept in the captured field; or `i`, `from` integral and `zeros(to−from)`'s length |
| 7 | `han-kerning.ts:220` | `i - from` | B | `from`, `to` integral; `zeros(to−from)`'s length; the field `out.lineStartExtras` kept across iterations |
| 8 | `han-kerning.ts:246` | `i - from` | B | as 7, field `out.lineEndTrims` |
| 9 | `han-kerning.ts:249` | `i - from` | B | as 7, field `out.overflowLineEndTrims` |
| 10 | `measurement.ts:707` `getExtraSpacings` | `i` | B | `zeros(count)`'s length, `i < count` |
| 11 | `measurement.ts:1260` `getSegmentFit` | `g - 1` | B | `advances.length = count` from `measureFitAdvances`' result, or its result clean and RMW; `g ≥ 1` integer |
| 12 | `measurement.ts:1262` | `g` | B | as 11 |
| 13 | `measurement.ts:1264` | `g` | B | `lineStartExtras` from `[0]` and pushes or `zeros(count)`: its length, or its cleanliness and RMW |
| 14 | `measurement.ts:1291` `countLigaturesOnFirstLetter` | `first` | N | `first ∈ {0, i}`, `0 ≤ first ≤ i < advances.length`; kept across `getTextWidth`, `isLigature` |
| 15 | `measurement.ts:1292` | `i` | N | `1 ≤ i < advances.length` from the loop condition |
| 16 | `measurement.ts:1360` `measureFitAdvances` | `count - 1` | P | `advances` a clean literal; RMW |
| 17 | `prepare.ts:192` `readScriptRuns` | `length = opened + 2` | B | `opened` from `lastIndexOf` (−1 or an index below the length), `opened ≥ 0`; `openBrackets[opened+1]` is `0` or passes `defined`, so `opened + 2 ≤ length` but at the maximum index, where the cut throws `RangeError` |
| 18 | `prepare.ts:199` | `k` | N | `k` integer from `length − 1` by −2, `k > 0`; the guard read `openBrackets[k] === 0` |
| 19 | `prepare.ts:489` `measureAnalysis` | `at - 1` | C | `at − 1 ≥ 0` from `spaceBefore ⇒ mi > from` |
| 20 | `prepare.ts:527` | `mi - from` | B | `from`, `to` integral; `new Array(to−from)`'s length, kept across iterations |
| 21 | `prepare.ts:532` | `fitAdvances.length - 1` | P | `fitAdvances` a clean `slice`; RMW |
| 22 | `prepare.ts:536` | `k` | P | as 21 |
| 23 | `prepare.ts:540` | `defined(unspaced[k])` | P | as 21; the key is another array's element |
| 24 | `prepare.ts:576` | `at` | C | append: `at = widths.length`, one append per iteration; `widths` kept across the body's calls |
| 25 | `prepare.ts:577` | `at` | C | `at = breakableFitAdvances.length`: the paragraph's lists of equal length at entry |
| 26 | `prepare.ts:578` | `mi - from` | B, C | `segments.length = mi − from` in lockstep; `from` integral |
| 27 | `prepare.ts:590` | `mi - from` | B, C | `zeros(mi−from)`'s length; lockstep length |
| 28 | `prepare.ts:592` | `mi - from` | B, C | as 27 |
| 29 | `prepare.ts:608` | `base + i` | B | `base = widths.length`, `i` integer, `base + i ≤ 2³²−2`; RMW alone needs `widths` clean, which `paragraph.widths` is not shown to be |
| 30 | `prepare.ts:665` `addKanaKerning` | `at` | B | `at = base + i − from`: `base`, `from` integral parameters, `at` a valid index |
| 31 | `prepare.ts:667` | `at - 1` | B | as 30, and `at ≥ 1` |
| 32 | `prepare.ts:669` | `at` | B | as 30 |
| 33 | `prepare.ts:671` | `i - from` | B | `from`, `to` integral; `zeros(to−from)`'s length |
| 34 | `prepare.ts:719` `addIdeographicSpaceHangs` | `i - from` | B | as 33 |
| 35 | `rich-inline.ts:447` `prepareRichInline` | `at` | B, C | `at = widths.length < flags.length`; `zeroList(n)`'s length |
| 36 | `rich-inline.ts:456` | `at - 1` | C | `breakableFitAdvances.length = widths.length − 1` here, `at ≥ 1` |
| 37 | `rich-inline.ts:465` | `at` | B, C | as 35 |
| 38 | `rich-inline.ts:473` | `from` | S | the guard read finds the same string at the same key: a same-value write (§3) |
| 39 | `rich-inline.ts:481` | `index` | B | `zeros(items.length)`'s length, `index < items.length` |
| 40 | `rich-inline.ts:482` | `index` | B | as 39 |
| 41 | `rich-inline.ts:483` | `index` | B | as 39 |
| 42 | `rich-inline.ts:496` | `at` | B, C | `at = itemAt + s` below the length `measureAnalysis` appended to |
| 43 | `rich-inline.ts:497` | `g` | P | `advances` a clean `slice`; RMW |
| 44 | `rich-inline.ts:498` | `0` | — | literal index 0: today's `setElem` |
| 45 | `rich-inline.ts:500` | `at` | B, C | as 42 |
| 46 | `rich-inline.ts:501` | `at` | B, C | as 42 |
| 47–56 | `rich-inline.ts:528, 530, 532, 535, 554, 560, 568, 573, 574, 575` | `at` | B, C | `at` below `flags.length`; `zeroList(n)` or `new Array(n).fill(null)`'s length |
| 57 | `rich-inline.ts:774` `setEmptyObjectFacts` | `first` | C | cross-structure (#94) |

S is the same-value write of §3.

## 3. The rules

**Conjectured.** All operands are evaluated and bound before the current
store is read: the receiver `x`, the key `k`, then the right side `v`, as
JavaScript evaluates them. The premises hold in the state after `v`.

```math
\frac{\Gamma\vdash_G x:L\quad \mathit{store}_G(L)\equiv_G\mathsf{list}(\tau)\quad
      \tau\ \text{homogeneous, writable, element}\ A\quad
      \Gamma;\Pi;\Sigma\vdash \mathrm{index}(k)\land\mathrm{extent}(x,k,0)\quad
      \Gamma\vdash_G v:A}
     {\Gamma;\Pi;\Sigma\vdash_G x[k]=v:\mathsf{Null}}\ \textsf{setElem-bounded}
```

with $`\mathrm{index}(k)`$ that slot $`k`$ holds a valid array index
(`indexOfBits` is some $`i\le 2^{32}-2`$) and $`\mathrm{extent}(x,k,0)`$
that $`i\le|\mathit{store}(x)|`$. `present(x,k)`, the store holding an
element at $`k`$, implies both. The step is `setPresent`, a fill of a hole
below the length, or `setGrow` at $`i=|\mathit{store}(x)|`$; `placeAt` then
adds no hole, and the written location's contract is $`A`$'s. The write
invalidates every fact the store or the written element location supports,
by the heap dependencies of the facts, aliases included; on a throw from the
right side only that side's own effects apply.

**Conjectured.** `present(x,k)` comes from an RMW read: a read at the same
evaluated receiver and key whose result is shown not `undefined`, on a clean
receiver, or with `index(k)`, the store kept since.

**Conjectured (same-value write).** Where the facts give that `x` owns the
key `k` with the value `v` itself (`analysis.texts[from] === item.text`,
then `analysis.texts[from] = item.text`), the write leaves the heap's
contents as they were, so it is safe at any contract of that location.

**Conjectured (length cut).** `x.length = m` with `integer(m)` and
`0 ≤ m ≤ |store(x)|`, `m ≤ 2³²−1`, on a homogeneous writable array,
truncates the store to its first `m` positions; it needs its own execution
step and source correspondence, and invalidates the store's facts.

**Soundness (conjectured).** `IndexWrites.setElemBounded_safe` and
`IndexWrites.lengthCut_safe`, step cases of
`HeapExpressionRules.Checker.sound`, so reaching
`SourceClaimJson.checkUnitJson_safe`. No trust is added.

## 4. Routes and what each accepts

**Presence (P).** Needs, beside the rule: a read relation from
`%ElementAt%`'s result to the receiver's element at the evaluated key; the
clean fact of an array literal and of `slice`'s result; and a certified
normal-return postcondition for `defined` (#104 §5's relational
`ensures`, with a `result` reference). No `Float` lemma. Sites 1–5, 16,
21–23, 43; with 44 (today's rule), the functions entirely covered are
`segmentAtLineBreaks` and `measureFitAdvances` (conjectured).

**Numeric (N).** #104 steps 1–4 for scalars and arrays: an index decoding of
a double's bits other than the opaque `Float.floor`, and the `Float` lemmas
for integer addition, subtraction and comparison (decision N); the fact
transport; loop interfaces on every edge; length reads and store
preservation across calls. Adds sites 14, 15, 18 and the function
`countLigaturesOnFirstLetter` (conjectured).

**Caller and callee facts (B) and relations (C).** #104's decision P
(relational parameter preconditions and result postconditions, certified at
every caller and definition), and loop or object invariants relating two
receivers. Every other function with a site (`getHanKerningTrims`,
`getExtraSpacings`, `getSegmentFit`, `readScriptRuns`, `measureAnalysis`,
`addKanaKerning`, `addIdeographicSpaceHangs`, `prepareRichInline`,
`setEmptyObjectFacts`) has a site of kind B or C.

Each route is thousands of lines across the semantics, the rules, the
lowering, the producer and the controls (Astra's estimate for N); P alone
reaches at most 201 of 211, P and N 202.

## 5. Cases and controls

Positive: an RMW loop on an array literal; an RMW at a key read from another
array on a `slice`; a forward and a reverse loop writing `xs[j]` under
`j < xs.length` (route N); an append `xs[xs.length] = v`; a same-value
write; a length cut below the length.

Negative, each run under Node: `xs[xs.length + 1] = v` on `number[]` leaves
a hole read as `undefined` at `number`; a write at a key whose present read
came before a callback emptied the array, so that the write leaves a hole;
`xs[-1] = 2` through an alias pinning `"-1"`; an RMW on a parameter array at
a key that is no index; a forged presence or extent fact (a control
bypassing the producer).

## 6. Owner decisions

- The route: P, N or both, and whether either lands before #104's
  decisions N and P.
- #104's decision P for every site of kind B or C.

## 7. Measured

The census of pretext `18360b74` over TScert `e4598052`
(`TSCERT_STEP_LIMIT=300`): 199 of 211 functions shallow verified, 196 deep;
each of the 12 refused functions is refused at a write with "a numeric
array key needs a proved array-index singleton" (2026-11-06).
