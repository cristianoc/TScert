# String lengths as terms

Part of [checked bound annotations](checked-bound-annotations.md) (#115). Drafted by Astra on `cdda1137`.

## The existing mechanism this extends

**Proposed draft section: String lengths as terms.**

This extends [Linear facts](../PROGRAM-TYPING.md#linear-facts):
partial integer terms, checked linear entailment, exact safe-integer arithmetic,
footprint preservation, and call preconditions and result facts.
String lengths use those mechanisms; the additional semantic obligation is string admissibility.

**Admissible strings.**

Let $`M=2^{53}-1`$ and $`L(s)=|\mathrm{utf16Units}(s)|`$.
Define admissibility by $`L(s)\le M`$.
ECMAScript bounds strings by this many UTF-16 code units. [String type](https://tc39.es/ecma262/multipage/ecmascript-data-types-and-values.html#sec-ecmascript-language-types-string-type)

The present `Types.strT` admits every Lean string.
`Calculus.Step.lenStr` returns `bitsOfNat (utf16Units s).length`.
Consequently, the present string typing premise supplies no safe-integer bound.

The proposed string interpretation includes admissibility.
String singletons and finite string types must satisfy the same restriction,
so singleton introduction or subtyping cannot bypass it.
An input typed `string` then supplies the bound through `EnvOk`;
stored strings supply it through their declared types and `HeapOk`.
External inputs and native results must meet this strengthened interpretation.

Literal introduction checks the decoded UTF-16 length, with a checked Lean premise.
A front-end check alone cannot establish this for forged certificates.
Every string-producing operation must preserve admissibility on normal return:

- **Concatenation:** normal return requires the concatenated length at most $`M`$.
  Both operands being admissible does not establish this.
  `Calculus.binop` currently concatenates without that restriction.
  Its result and exceptional semantics, and `OperatorTyping.add_string`,
  must account for oversized results together.
- **Slice and substring:** the result length is bounded by the receiver’s length;
  prove this after JavaScript’s argument conversion and clamping.
- **Repeat:** convert the count with JavaScript semantics, then bound the
  mathematical product of the receiver’s length and the converted count.
  Negative and positive-infinite counts throw; NaN converts to zero.
  Normal return must produce an admissible string. [Repeat](https://tc39.es/ecma262/multipage/text-processing.html#sec-string.prototype.repeat)
- **JSON:** parsed string leaves and property names must be admissible;
  stringify must account for escaping, separators, callbacks and abrupt completion.
  Its output length is not bounded by the input string lengths individually.
- **Other natives:** audit every string result, including conversion, replacement,
  joining, padding and normalization; their normal-return contracts include admissibility.

An oversized construction must have an explicit abrupt outcome, never an oversized
normal string, truncation, or a stuck execution accepted as safe.
The host model must also accommodate implementation allocation limits below $`M`$.
Exact exception classes and callback effects require each operation’s own audit;
the specification’s string bound alone does not establish them.

The existing scalar-string representation also needs an explicit scope decision:
`SEMANTICS.md` records its difference from JavaScript for lone surrogate results.
Length-preserving slice contracts require UTF-16-faithful results at those boundaries.
Counting code points or replacing lone surrogates does not establish that correspondence.

**The term and its rule.**

Add `Term.Kind.strLength` and the empty-path constructor `strLength(x)`.
Its interpretation is partial:

```math
⟦\mathrm{strLength}(x)⟧_{\rho,h}=L(s)
\quad\Longleftrightarrow\quad
\rho(x)=\mathsf{str}(s)\ \land\ L(s)\le M.
```

Its range is $`0\le\mathrm{strLength}(x)\le M`$.
For an empty path it reads only the environment and survives every heap change.
Reassigning the binding requires the existing slot substitution/elimination rules.
If paths are supported, `strLength(p.text)` reads the path’s heap locations:
immutability of the resulting string does not make the field path immutable.

A typed `r ← text.length` establishes `int(r)` and
$`r=\mathrm{strLength}(\mathit{text})`$, represented by two inequalities.
Prove this from `Step.lenStr`, admissibility and `SafeIntegers.SafeInt`.
Reuse `int-compare`, `int-exact`, read bridges and call-requires thereafter.
All derived arithmetic remains subject to its safe-result premise.

**Connecting the loop and its allocation.**

Write $`L=\mathrm{strLength}(\mathit{text})`$.
Starting at zero, the body of `i < text.length` has $`0\le i<L`$.
Thus its increment satisfies $`i+1\le L\le M`$ and is exact.
The bounded `charCodeAt(i)` result is a code unit, hence a safe integer.
Its general signature remains `number`: out-of-range reads return NaN,
which a non-null assertion does not exclude.

For `new Uint8Array(text.length + 1)`, first establish $`L\le M-1`$.
The universal string bound alone does **not** justify this addition as a safe integer.
Then `int-exact` supplies $`n=L+1`$, and the existing constructor postcondition
supplies $`\mathrm{view}(a)=n`$ on normal return.
The loop bounds imply $`0\le i<\mathrm{view}(a)`$, selecting the bounded read.
A read at $`i=L`$ also fits this extra element.
Ordinary arrays additionally require their existing length/index ceilings
and an element-presence contract; allocation size alone does not establish density.

**Implementation obligations and first delivery.**

In `Types/Types.lean`, strengthen string membership and audit singleton inclusion.
In `Semantics/Calculus.lean`, account for string construction and abrupt outcomes;
repair the affected `Rules.lean` and `Programs/OperatorTyping.lean` proofs.
In `Semantics/IndexFacts.lean`, extend interpretation, ordering, mapping and preservation;
increase the kind-code stride so the fourth kind cannot collide with another slot.
In `Semantics/HeapKnowledge.lean`, extend ranges, definedness and entailment support.
In `Programs/IndexWrites.lean`, add and prove the string-length result facts.
Extend annotation lowering, every wire decoder and OCaml’s term/range/preservation logic.

Cases should cover a pretext-shaped loop and allocation, empty and astral strings,
a bound on the wrong string, an index at the end, and a replaced string field.
Keep forged controls for unjustified length facts and unsafe arithmetic;
check NaN and conversion counterexamples under Node.
Oversized strings need symbolic boundary proofs rather than enormous allocations.

The smallest first delivery is the admissibility foundation and construction audit.
It establishes the premise needed for string-length facts; it does not yet verify the loops.
The next delivery adds the term and one annotated pretext-shaped end-to-end case.

