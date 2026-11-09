# Arithmetic: integers, lengths and bounds

This document owns the integer facts TScert reasons with: linear facts
over values, array lengths, typed-array lengths and strings' lengths, read
through field paths, which the producer proposes at program points and Lean
checks on every incoming edge; the rules that state, carry and decide them;
and the clauses a source writes to state them at function, record and loop
boundaries. The facts are index facts of heap knowledge
([stored knowledge](PROGRAM-TYPING.md#stored-knowledge-and-how-it-is-read)).
The typing rules that consume them are program typing's:
[writes at a checked index](PROGRAM-TYPING.md#writes-at-a-checked-index),
[reads below the length](PROGRAM-TYPING.md#reads-below-the-length),
[typed arrays](PROGRAM-TYPING.md#typed-arrays) and
[code points](PROGRAM-TYPING.md#code-points). The heap changes that keep a
fact are [frame conditions](PROGRAM-TYPING.md#frame-conditions), with
[footprints](FOOTPRINTS.md#index-facts) for calls and
[element regions](FOOTPRINTS.md#element-regions) for arrays kept apart; the
audited integer contracts of string natives are
[string method postconditions](SOURCE-CONTRACTS.md#string-method-postconditions).

## Linear facts

A **linear fact** over integer variables is $`c\cdot x\le d`$ or
$`c\cdot x\ne d`$, with $`c\cdot x=\sum_i c_i x_i`$, integer coefficients
$`c_i`$ and an integer bound $`d`$. A **linear certificate** is a list of
steps, each concluding one fact from the facts held before it, its conclusion
held by the later steps:

```math
\frac{a_j\cdot x\le b_j\ \ (j\in J)\qquad \lambda_j\in\mathbb{N}\qquad g\ge 1\qquad
      \sum_j\lambda_j a_j=g\,c\qquad \Bigl\lfloor\frac{\sum_j\lambda_j b_j}{g}\Bigr\rfloor\le d}
     {c\cdot x\le d}\ \textsf{combine}
\qquad
\frac{c\cdot x\le d\qquad c\cdot x\ne d}
     {c\cdot x\le d-1}\ \textsf{strict}
\qquad
\frac{0\le b\qquad b<0}
     {F}\ \textsf{absurd}
```

The equality of linear forms is decided on their normal forms, sorted by
variable with one nonzero coefficient each. With $`g=1`$, `combine` is a
nonnegative combination; with $`g>1`$ it rounds once, valid because
$`c\cdot x`$ is an integer at an integer valuation. A strict comparison of
integers is $`x-y\le -1`$, an equality two facts. Proved: every fact an
accepted certificate concludes holds of every integer valuation meeting the
facts it starts from. The steps are incomplete for the integers: an
implication that no chain of them derives is refused. The search for a
certificate tightens bounds, applies strict steps and eliminates variables,
and the checker decides what it finds (proved). An inequality gives the strict
bound on the side the facts bound it, before a search and before an
elimination (proved):

```math
\frac{c\cdot x\ne d\qquad K\vdash c\cdot x\le d}{c\cdot x\le d-1}
\qquad
\frac{c\cdot x\ne d\qquad K\vdash -c\cdot x\le -d}{-c\cdot x\le -d-1}\ \textsf{strengthen}
```

so the false branch of `e === xs.length`, with $`e\le|\mathit{xs}|`$ known,
bounds a read at $`e`$.

**Terms.** Two more index facts state integers: $`\mathrm{int}(k)`$ and
$`\mathrm{linear}(F)`$. The variables of a linear fact are **terms**: a root
slot $`x`$, a **path** $`p`$ of named data fields read from its value in turn,
and what the term reads of the value $`v`$ the path ends at: $`x.p`$, the
safe integer $`v`$ is; $`|x.p|`$, the length of $`v`$'s array store, where
that is at most $`2^{32}-1`$; and $`\mathrm{view}(x.p)`$, the **typed-array
length** of $`v`$, the safe integer at least $`0`$ that the location of its
model key $`[[\mathrm{viewLength}]]`$ holds; and $`\mathrm{strLength}(x.p)`$,
the **string's length** of $`v`$, its count of UTF-16 code units, where that
is at most $`2^{53}-1`$, the most a JavaScript string holds. The empty path
reads the slot's value itself, $`x`$, $`|x|`$, $`\mathrm{view}(x)`$ and
$`\mathrm{strLength}(x)`$:

```math
\begin{aligned}
\mathrm{read}(\rho,h,x) &= \rho(x)\\
\mathrm{read}(\rho,h,x.p.f) &= v \iff \mathrm{read}(\rho,h,x.p)=\mathsf{objAt}\,fs\,c\,i\land fs(f)=\ell\land h(\ell)=v\\
\mathrm{int}(k)(\rho,h) &\iff \exists b\,i.\ \rho(k)=\mathsf{num}\,b\land\mathrm{SafeInt}(b,i)\\
⟦x.p⟧_{\rho,h} &= i \iff \exists b.\ \mathrm{read}(\rho,h,x.p)=\mathsf{num}\,b\land\mathrm{SafeInt}(b,i)\\
⟦|x.p|⟧_{\rho,h} &= n \iff \mathrm{store}(\mathrm{read}(\rho,h,x.p))=s\land h(s)=\mathsf{arr}\,\ell\land n=|\ell|\le 2^{32}-1\\
⟦\mathrm{view}(x.p)⟧_{\rho,h} &= n \iff \mathrm{read}(\rho,h,x.p)=\mathsf{objAt}\,fs\,c\,i\land fs([[\mathrm{host}]])\ \text{defined}\land fs([[\mathrm{viewLength}]])=\ell\land h(\ell)=\mathsf{num}\,b\land\mathrm{SafeInt}(b,n)\land 0\le n\\
⟦\mathrm{strLength}(x.p)⟧_{\rho,h} &= n \iff \mathrm{read}(\rho,h,x.p)=\mathsf{str}\,s\land n=|\mathit{units}(s)|\le 2^{53}-1\\
\mathrm{linear}(F)(\rho,h) &\iff (\forall t\in\mathrm{vars}(F).\ ⟦t⟧_{\rho,h}\ \text{is defined})\land F\ \text{holds at}\ t\mapsto⟦t⟧_{\rho,h}
\end{aligned}
```

with $`fs(f)`$ the location of the string key $`f`$ the object owns and the
safe integers of [the operational language](SEMANTICS.md#operational-language).
`read` is partial, defined where every object on the path owns its next field
at an allocated location, and a term is defined where its read is and the
read value meets its kind. A fact over a path states no own key: where a
field is absent or the value is no object, the term denotes nothing, and no
fact naming it holds. A typed-array length is defined only of a host object
(one owning $`[[\mathrm{host}]]`$), which no allocation of the program makes,
and no step copies the key; that its location holds the typed array's length
is the host's trust ([typed arrays](SOURCE-CONTRACTS.md#stated-library-types)).

**The locations a fact reads.** A term reads the location of each field its
path reads, then, for a length, the location of the store's elements, and for
a typed-array length, the location of the view's length; a string's length
reads no location past its path, a string being a value. A fact reads the
locations its terms read; a fact of slots' values and slots' strings'
lengths alone reads only the environment, so every heap change preserves it,
and a heap extension preserves every read (proved). Which other
heap changes preserve a fact is stated by [frame conditions](PROGRAM-TYPING.md#frame-conditions).

**Entailment.** The linear facts a knowledge $`\Sigma`$ states,
$`\mathrm{lin}(\Sigma)`$, are its unconditional linear atoms, each with the
range $`0\le|x|\le 2^{32}-1`$ of every length and the range
$`0\le\mathrm{view}(x)\le 2^{53}-1`$ of every typed-array length and
$`0\le\mathrm{strLength}(x)\le 2^{53}-1`$ of every string's length it names,
and, for each length atom $`\mathrm{length}(x,n)`$, the equality $`n=|x|`$
with its range. A value term denotes a safe integer, whose magnitude is below
$`2^{53}`$; an entailment $`K\vdash F`$ reads $`\mathrm{lin}(\Sigma)`$ and,
where it alone entails no $`F`$, also the range of each value term
$`\Sigma`$ states defined, by a linear fact naming it, an $`\mathrm{int}`$
atom or a length atom (proved):

```math
\frac{\mathrm{lin}(\Sigma)\vdash F}{K\vdash F}
\qquad
\frac{\mathrm{lin}(\Sigma)\cup\{-(2^{53}-1)\le t\le 2^{53}-1\mid t\ \text{a value term}\ \Sigma\ \text{states defined}\}\vdash F}{K\vdash F}\ \textsf{value-range}
```

so `i - 1` under $`1\le i`$ and `i + 1` under $`i<n`$ are safe integers. The
search over $`\mathrm{lin}(\Sigma)`$ alone comes first, since each range adds
a row to every elimination of its term; elimination reads
$`\mathrm{lin}(\Sigma)`$. Facts are renamed with their slots and carried as
the other index facts are. On an edge, a target atom holds where a source atom
gives it, term by term of the same kind, or, unconditional, where the
source's linear facts entail it, each target term renamed to a source term of
the same kind at a slot of the class of the slot the edge maps it to, which
the source states defined: a value by $`\mathrm{int}`$, a length by a length
atom or a linear fact naming it, a typed-array length or a path by a linear
fact naming it (proved).

**The read bridge.** A current read link $`x.f\mapsto v`$ (not an alias,
$`f`$ a string key; through an optional key as
[guarded clauses](#guarded-clauses) state) states that $`v`$ holds what
reading $`f`$ from $`x`$'s object gives, so for every kind and path $`p`$ the
term rooted at $`v`$ with $`p`$ denotes what the term rooted at $`x`$ with
$`f.p`$ denotes, or neither denotes an integer (proved):

```math
\frac{x.f\mapsto v\in\Sigma}{⟦v.p⟧_{\rho,h}=⟦x.f.p⟧_{\rho,h},\quad ⟦|v.p|⟧_{\rho,h}=⟦|x.f.p|⟧_{\rho,h},\quad ⟦\mathrm{view}(v.p)⟧_{\rho,h}=⟦\mathrm{view}(x.f.p)⟧_{\rho,h}}\ \textsf{read-bridge}
```

Three places use it.

- *Entailment.* Where an atom of the source or the target names a path, the
  check of index atoms, on edges and at a call's precondition, restates every
  term by the source's links toward its root: its slot taken to its alias
  class's representative, then, while a read link gives the root's value as
  field $`f`$ read from slot $`c`$, the term rooted at $`c`$ with $`f`$
  before its path (proved). The source's and the target's linear facts are
  compared restated, a restated term defined where the source states defined
  a term restated to it, and a bound or safe-integer target atom is read
  alike.
- *The read.* A field read restates of the read's slot each linear atom
  naming a term rooted at the receiver's class whose path starts with the
  read field (proved), so the read value of `cursor.itemIndex` is a safe
  integer an operand may be; a read a current read link answers, the linked
  slot's value copied, restates them alike (proved).
- *A dropped slot.* Before a slot is eliminated, at a step's output or an
  edge's projection, each linear fact or length atom naming a term rooted at
  it is restated rooted at a retained slot the reads reach (proved), so
  `const n = flow.data.widths.length` retains
  $`n=|\mathit{flow}.\mathit{data}.\mathit{widths}|`$.

A read link is a current-heap fact, discarded by a write or a call that
changes the heap: a slot holding an earlier read is a snapshot, and its link
to the path expires. Dropping a root slot eliminates every term rooted at it.

**The steps stating them.** An operand is a slot $`x`$ with
$`\mathrm{int}(x)`$, of value $`x`$, or a literal that is a safe integer
$`i`$, of value $`i`$; $`r`$ is the result:

```math
\frac{\mathrm{SafeInt}(b,i)}{r\leftarrow\mathsf{num}\,b\dashv\mathrm{int}(r),\ r=i}\ \textsf{int-literal}
\qquad
\frac{\mathrm{int}(x)}{r\leftarrow x\dashv\mathrm{int}(r),\ r=x}\ \textsf{int-copy}
\qquad
\frac{\Gamma(s)\equiv_G\mathsf{list}(\tau)}{r\leftarrow\mathsf{lenOf}(s)\dashv\mathrm{int}(r),\ 0\le r\le 2^{32}-1}\ \textsf{length-range}
\qquad
\frac{\Gamma(s)\ \text{answers}\ \mathsf{isStr}}{r\leftarrow\mathsf{lenOf}(s)\dashv\mathrm{int}(r),\ r=\mathrm{strLength}(s)}\ \textsf{string-length}
\qquad
\frac{\Gamma(s),\Gamma(t)\ \text{answer}\ \mathsf{isStr}}
{r\leftarrow s+t\dashv\mathrm{strLength}(r)=\mathrm{strLength}(s)+\mathrm{strLength}(t)}\ \textsf{string-concat}
```

```math
\frac{K\vdash -(2^{53}-1)\le a\pm b\le 2^{53}-1}
     {K\vdash r\leftarrow a\pm b\dashv\mathrm{int}(r),\ r=a\pm b}\ \textsf{int-exact}
\qquad
\frac{}{K\vdash c\leftarrow a\lhd b\dashv (a\lhd b\ \text{if}\ c),\ (\neg(a\lhd b)\ \text{if}\ \neg c)}\ \textsf{int-compare}
\qquad
\frac{}{K\vdash c\leftarrow a\ \texttt{===}\ b\dashv (a=b\ \text{if}\ c),\ (a\ne b\ \text{if}\ \neg c)}\ \textsf{int-equal}
```

**A literal's value.** A slot whose type is one safe integer's literal
$`k`$, a module constant `const TEXT = 0` among them, holds $`k`$
(`IndexWrites.litSlot`, proved: `litSlot_sound`), so a read of it states
$`\mathrm{int}(r),\ r=k`$; the producer reads such a constant at its value
where a binding is assigned or declared it
(`literal-constant-value`; negative `invalid-literal-constant-value`, run
under Node).

**A sum reaching $`2^{53}`$.** A string's length plus one, $`a`$ a slot the
knowledge states equal to $`\mathrm{strLength}(s)`$ and $`b`$ the constant
$`1`$, two safe integers $`a,b\ge 0`$ whose sum
the knowledge bounds by $`2^{53}`$, and not by $`2^{53}-1`$, add to their
exact sum or to the double $`2^{53}`$, the least integer past the safe
integers, $`\mathrm{past}(r)`$ (`IndexFact.pastSafe`): $`a+b<2^{53}`$ is
exact, and $`a+b=2^{53}`$ is exactly representable (proved:
`SafeIntegers.add_two53`). The step states each atom of `int-exact`'s
conclusion as a disjunction with $`\mathrm{past}(r)`$:

```math
\frac{K\vdash 0\le a\qquad K\vdash 0\le b\qquad K\vdash a+b\le 2^{53}\qquad K\nvdash a+b\le 2^{53}-1}
     {K\vdash r\leftarrow a+b\dashv\mathrm{int}(r)\lor\mathrm{past}(r),\ (r\le a+b)\lor\mathrm{past}(r),\ (r\ge a+b)\lor\mathrm{past}(r)}\ \textsf{int-sum-past}
```

The double $`2^{53}`$ is no safe integer (proved:
`SafeIntegers.pastSafe_not_safe`), so knowledge stating $`r`$ a safe integer
decides each disjunction for its left side (`releasePast`, applied where an
edge's target is checked and before a dropped slot is eliminated), and a
target $`F\lor\mathrm{past}(r)`$ follows where $`F`$ follows from the left
sides (`guardEntails`). A copy of $`r`$ restates the disjunctions
(`pastCopies`). A typed array's construction takes such a sum as its length
([the standard library's typed arrays](SOURCE-CONTRACTS.md#the-standard-librarys-typed-arrays)).

with $`K\vdash`$ the entailment from the step's knowledge
([entailment](#linear-facts), `value-range` included), $`\lhd`$ one of `<`,
`<=`, `>`, `>=`, and each branch's fact over the integers ($`\neg(a<b)`$ is
$`b\le a`$: two safe integers are never NaN). `int-equal` reads JavaScript's
`Number::equal`, which on two safe integers is their equality, the zeros
included (proved, with its converse: no safe integer's bits are a NaN's). A
comparison with a number literal lowers to a tag test $`\mathsf{numEq}\,b`$
of the compared value; where $`b`$ is the safe integer $`k`$, each branch
states, of every slot $`x`$ of the tested slot's alias class with
$`\mathrm{int}(x)`$, the same facts (proved, from the same two theorems):

```math
\frac{\mathrm{SafeInt}(b,k)\qquad x\in\mathrm{class}(s)\qquad \mathrm{int}(x)}
     {s\ \textsf{passes}\ \mathsf{numEq}\,b\dashv x=k
      \qquad s\ \textsf{fails}\ \mathsf{numEq}\,b\dashv x\ne k}\ \textsf{num-equal}
```

so `i === 0 || xs[i - 1]!` under $`0\le i\le|\mathit{xs}|`$ reads below the
length: `strengthen` turns $`i\ne 0`$ into $`1\le i`$. `length-range` reads
the store contract's bound ([arrays](POSITIVE-TYPES.md#arrays)). Proved, from
the exactness of safe-integer addition and subtraction and the order of two
doubles that are safe integers. A length atom $`\mathrm{length}(x,n)`$ also
states the store's length at most $`2^{32}-1`$, which `length-observed` reads
from the store contract. `string-length` holds on the read's normal return:
a string longer than $`2^{53}-1`$ code units throws there
([strings](SEMANTICS.md#operational-language)), and the length of any other
is a safe integer. The lowering reads `length` of a value whose type answers
the string test with no test of its own, so the step is `lenOf` of the
string's slot.

**A constant factor.** Multiplication by an integer constant states a linear
fact where the knowledge bounds its result within the safe integers. A slot
is constant here where two checked inequalities establish its equality to
the constant; this includes the slots holding literals during evaluation.

```math
\frac{\mathrm{int}(a)\qquad K\vdash b=c\qquad
      K\vdash -(2^{53}-1)\le c\,a\le 2^{53}-1}
     {K\vdash r\leftarrow a*b\dashv\mathrm{int}(r),\ r=c\,a}
     \ \textsf{int-scale}
```

with $`c`$ an integer constant and $`b`$ a safe-integer operand; the
symmetric form reads $`b*a`$. Where $`c=0`$ the fact is $`r=0`$, naming no
slot of $`a`$, so it outlives $`a`$'s slot (`-0` is the safe integer $`0`$,
`stateful-source/arithmetic`). The clause language's constant coefficients
therefore bound computed row offsets such as `row * 28 + 27`. Proved:
`SafeIntegers.mul_safe` establishes exact multiplication against the float
model, `IndexWrites.knownConstant_sound` establishes the operand's constant
value, and `IndexWrites.linearAtoms_holds` establishes the result's facts.
The source cases are `table-constant-stride` and
`invalid-table-constant-stride` (a row starting at the length).

**Bounded bitwise operands.** The linear postcondition extends
[index-mask](PROGRAM-TYPING.md#writes-at-a-checked-index) when the left operand is a safe integer
between zero and $`2^{31}-1`$ and the right operand is a checked constant.
For a shift count $`0\le k<32`$, writing $`q=2^k`$:

```math
\frac{\mathrm{int}(a)\quad K\vdash 0\le a<2^{31}\quad K\vdash b=k}
     {K\vdash r\leftarrow a\mathbin{\texttt{>>}}b
       \dashv\mathrm{int}(r),\ 0\le r,\ qr\le a\le qr+q-1}
```

For an integer mask $`0\le m<2^{31}`$:

```math
\frac{\mathrm{int}(a)\quad K\vdash 0\le a<2^{31}\quad K\vdash b=m}
     {K\vdash r\leftarrow a\,\&\,b
       \dashv\mathrm{int}(r),\ 0\le r\le m,\ r\le a}
```

Both right operands are safe integers. Proved:
`SafeIntegers.toInt32_safe_nonneg` establishes the conversion boundary;
`SafeIntegers.shr_safe` and `SafeIntegers.bitAnd_safe` establish the numeric
results; `IndexWrites.bitAtoms_holds` connects them to the linear facts.
The quotient inequalities retain the relation to the input, so an input
bound of 222 entails a result at most 27 for a shift by three.

**Dropping a slot.** Where a step's output drops a slot, or an edge's mapping
retains no slot of a fact's class, the slot is first eliminated from the
unconditional linear facts by Fourier–Motzkin elimination: each pair of
facts of opposite signs on it is combined to cancel it, each combination a
`combine` step the checker decides, and the derived facts naming no dropped
slot are retained (proved). The facts conditional on a retained slot's value
are eliminated alike, together with the unconditional ones, and the derived
facts retained under the same condition; an edge establishes such a target
atom where the source's unconditional facts and those conditional on a slot
of its condition's class, on the same branch, entail it. So a test evaluated
again from saved operands retains, on each branch, what it states of the
slots that remain, and `const answer = base + 2`, computed from copies of
`base` and of the literal, retains `answer = base + 2` once the copies are
dropped.

**A comparison with a length.** A strict comparison of a safe integer $`k`$
with a slot $`n`$ a length atom names states, on the branch where $`k<n`$,
facts of $`k`$ alone, which remain once $`n`$ is dropped (proved):

```math
\frac{\mathrm{int}(k)\quad \mathrm{length}(x,n)\in\Sigma\quad K\vdash 0\le k}
     {c\leftarrow k<n\dashv (k\le 2^{32}-2\ \text{if}\ c),\ (\mathrm{bound}_<(x,k)\ \text{if}\ c)}\ \textsf{length-compare}
```

with the mirrored forms `n > k`, and `k >= n`, `n <= k` on the false branch;
without $`K\vdash 0\le k`$ only the first fact. A loop's test is evaluated
twice, its value and then, as a tested Boolean, again from its saved operands
for the dispatch's refinement; the edge into the dispatch retains the test's
result and drops the operands' re-read slots, so a fact of the comparison
over them reaches the branch only through slots it retains. A copy of a slot
restates the atoms conditional on it as conditional on the copy.

**A write bounded by linear facts.** `setElem-bounded` reads
$`\mathrm{bound}(x,k)`$, stated by a bound atom or by the linear facts
(proved), and a read below the length reads $`\mathrm{bound}_<(x,k)`$ alike;
a length atom $`\mathrm{length}(x',n)`$ states $`|x'|`$ defined and equal to
$`n`$:

```math
\frac{x'\in[x]\quad |x'|\ \text{defined}\quad \mathrm{int}(k)\quad
      K\vdash 0\le k\le |x'|\quad K\vdash k\le 2^{32}-2}
     {\mathrm{bound}(x,k)}\ \textsf{bound-linear}
\qquad
\frac{x'\in[x]\quad |x'|\ \text{defined}\quad \mathrm{int}(k)\quad
      K\vdash 0\le k\le |x'|-1}
     {\mathrm{bound}_<(x,k)}\ \textsf{bound-linear-strict}
```

String-only addition of two slots establishes its length equality on normal
return. Concatenation past the string bound throws; its exceptional edge has
no result length. `IndexWrites.linearAtoms_holds` proves the equality from
`concatString` and the UTF-16 expansion of string append. Native method
postconditions use the [audited string contracts](SOURCE-CONTRACTS.md#string-method-postconditions).

**Implementation.** Linear facts are `Linear.Fact`, normal forms
`Linear.normalize`; the certificate check is `Linear.check` (proved:
`Linear.check_sound`), the search `Linear.entails` (proved:
`Linear.entails_sound`) and `Linear.entailsWith`, the strict bound
`Linear.strengthen` (proved: `strengthen_holds`). The index facts are
`IndexFact.int` and `IndexFact.linear`, terms `HeapKnowledge.Term`, the
length `lengthOf` (the length `Step.lenV` gives), the typed-array length
`viewLengthOf` at `Calculus.viewLengthKey`, the string's length `strLengthOf`
(the length `Step.lenStr` gives, at most `maxStringLength`), the path read
`IndexFacts.readPath`, the key never copied by `copiedKey`. A fact reading
only the environment is `IndexFact.envOnly`; the heap extension's proof is
`readPath_extend`. $`\mathrm{lin}(\Sigma)`$ is `HeapKnowledge.linearFacts`
with `lengthRange` and `viewRange` (a string's length's too, `strRange_holds`); entailment is
`HeapKnowledge.entailsKnown` with `valueRanges` (proved:
`entailsKnown_sound`, from `valueRange_holds`); the safe integers are
`SafeIntegers.SafeInt`; the edge rule is `linearFollows` (proved:
`linearFollows_sound`). The read link is `HeapLinks.Holds` and the bridge
`HeapKnowledge.readBridge`; restating toward the root is `liftTerm` (proved:
`liftTerm_eq`), with `bridgedDefined` and `lengthBoundVia`; the read's
restatement is `readAtoms` (proved: `readAtoms_holds`) and
`HeapExpressionRules.linkedOutput` (proved in `linkedRead_sound`); the
dropped slot's is `restateReads` (proved: `restateReads_holds`). The steps
are a layer of `Checker.indexing` (`IndexWrites.linearAtoms`; proved:
`IndexWrites.linearAtoms_holds`, from `SafeIntegers.add_safe`, `sub_safe`
and `doubleOrder_safe`; `string-length` from `stringSlot_sound` and
`len_str_run`); `int-equal` is proved by
`SafeIntegers.numberEqual_safe` and `numberEqual_of_safe`, `num-equal` by
`HeapKnowledge.numEqIndices` (proved: `numEqIndices_holds`), which every tag
observation reads. Elimination is `HeapKnowledge.eliminateIndices` over
`Linear.eliminateAll` (proved: `eliminateIndices_holds`). The comparison with
a length is `IndexWrites.lengthAtoms` (proved: `lengthAtoms_holds`), the
loop test's second evaluation `compileConditionAtom`, the copy's restatement
`IndexWrites.copiedAtoms`, the bound from linear facts
`HeapKnowledge.lengthBound` (proved: `lengthBound_sound`).

## Terms for bindings held in cells

A binding an update inside an expression writes, or a closure captures, is
held in a cell (`SourceFacts`, "Bindings held in cells"): an object whose
field `value` holds the binding's value. A linear fact or guard over such a
binding $`x`$, held in the cell at slot $`c`$, names the path term rooted at
the cell, its path starting with `value`; a binding whose cell may hold the
uninitialized marker (an early one) names none:

```math
\frac{x\ \text{held in the cell at}\ c}
     {⟦x.p⟧_{\rho,h}=⟦c.\mathsf{value}.p⟧_{\rho,h},\quad ⟦|x.p|⟧_{\rho,h}=⟦|c.\mathsf{value}.p|⟧_{\rho,h},\quad ⟦\mathrm{view}(x.p)⟧_{\rho,h}=⟦\mathrm{view}(c.\mathsf{value}.p)⟧_{\rho,h}}\ \textsf{cell-term}
```

These are path terms of [linear facts](#linear-facts), so the rules there
state them and the [frame conditions](PROGRAM-TYPING.md#frame-conditions) preserve them. An
update $`\texttt{++}x`$, $`x\texttt{++}`$, $`x\texttt{ += }n`$ or
$`x\texttt{ -= }n`$, $`n`$ a safe-integer literal, is a read of
$`c.\mathsf{value}`$ into a slot $`r`$, whose link restates the cell's facts
of $`r`$; the sum $`r'=r\pm d`$, a safe integer by `int-exact`; and the write
$`c.\mathsf{value}:=r'`$, a number field's write, whose change drops the
facts over the field and whose read link restates the facts of $`r'`$ of it
(`write-link`, `read-bridge`). The update's value is $`r'`$ for a prefix
update and $`r`$ for a postfix one, so `xs[at++]!` reads at
$`r=c.\mathsf{value}-1`$ while the cell holds $`r'`$, and `++at` reads at
$`r'`$. No rule is added for cells: a cell is an object allocated by the
lowering, and these steps are the field read, sum and write rules above. A
cell's facts are preserved across a field write where a separation fact keeps
the written field apart from the cell's `value` (`first`; the producer
proposes this for a field of a parameter's object, allocated before the
cell), and across a call as its frame condition preserves a path's.

The producer reads an expression updating a cell against the facts after the
update: each fact of the binding restated of its old value, the write's
change applied, the new value stated the old one plus the step, the old one
eliminated; a binding the expression updates twice, reads elsewhere, or steps
by a non-literal is forgotten. An entry claim's facts lower to atoms each
stated once: a cut's knowledge is its assertion exactly, and two claimed
facts over a cell's value can lower to one atom.

**Implementation.** The cell's root is `Lowering.termRoot`, the read's
restatement `readAtoms`; the producer's reading is
`Linear_facts.after_cell_updates`, the lowering of entry claims
`Lowering.Flow`, a cut's check `checkAssertions`.

## The clause language

A clause is a JSDoc tag of a declaration's or a loop's leading comment,
read from the source text by the front end (`tools/bound-annotations.mts`)
and elaborated to index facts; Lean reads them from the Fragment. A clause
runs no code: it is no expression of the program and executes no property
read, so the JavaScript emitted for a module is the same with and without
its clauses.

**Where clauses are written.**

| Tag | Written on | Names | Meaning |
| --- | --- | --- | --- |
| `@requires C` | a function declaration, an arrow or a function expression, or the statement binding a function initializer | the parameters, and the receiver `this` where the function declares it | [preconditions](#preconditions) |
| `@ensures C` | a synchronous module function declaration with one signature and named non-rest parameters | `result` and the parameters its body does not reassign | [postconditions](#postconditions) |
| `@invariant C` | a type alias or an interface | `this`, a value of the type | [type invariants](#type-invariants) |
| `@representation T` | beside an `@invariant`, on an opaque type | the record type `T` the clause's paths resolve through | [sealed handles](#type-invariants) |
| `@invariant C` | the comment immediately before a `while`, `do` or `for` loop | the bindings in scope at the loop's head | [loop invariants](#loop-invariants) |

Several tags of one kind state their conjunction.

**The grammar.**

```math
\begin{aligned}
K &::= G\ \texttt{||}\ K \mid C\\
G &::= P\ \texttt{===}\ \mathtt{null} \mid P\ \texttt{===}\ \mathtt{undefined} \mid P\ \texttt{===}\ \mathtt{true} \mid P\ \texttt{===}\ \mathtt{false}\\
C &::= A \mid C\ \texttt{\&\&}\ C \mid C\ \texttt{||}\ C \mid \texttt{!}C \mid (C) \mid \mathtt{forall}\ x\ \mathtt{in}\ P\texttt{:}\ B \mid \mathtt{forall}\ x\ \texttt{<}\ P\ \mathtt{of}\ P\texttt{:}\ B\\
A &::= \mathtt{safeInteger}(P) \mid E\ \mathit{rel}\ E \mid P\ \texttt{!==}\ P\\
E &::= n \mid P \mid P.\mathtt{length} \mid n\cdot P \mid n\cdot P.\mathtt{length} \mid E + E \mid E - E \mid -E \mid (E)\\
P &::= x \mid P.f\\
B &::= A' \mid B\ \texttt{\&\&}\ B \mid B\ \texttt{||}\ B\\
E' &::= E \mid x \mid P[x] \mid P[x+d] \mid P[x].p \mid P[x].p.\mathtt{length} \mid n\cdot E'
\end{aligned}
```

with $`\mathit{rel}`$ one of `<`, `<=`, `>`, `>=`, `===`, $`n`$ and $`d`$
integer literals ($`d\ge 0`$), $`x`$ a parameter (`result` in an
`@ensures`, `this` in a type invariant, a binding in a loop invariant) or a
quantified atom's index, $`f`$ a field name, and $`A'`$ an atom over terms
$`E'`$, `safeInteger(P[x])` among them. A clause starts with its
[guards](#guarded-clauses); a [quantified atom](#quantified-clauses) is its
last, its body extending to the clause's end, and states no quantified atom
of its own; a `!` or an `||` among atoms states a
[linear disjunction](#guarded-clauses). A guard against `true` or `false`
tests a Boolean result ([postconditions](#postconditions)).

**Reading a clause.** A path $`P = x.f_1\ldots f_k`$ reads the fields from
its root in turn, each a required field of the record type the path before
it has, an alias followed to its equation and an intersection to the one
part stating the field; a path whose field no type resolves is refused.
After a guard, a path is resolved where the guards before it fail
([guarded clauses](#guarded-clauses)). A path $`P`$ as a term is its
value, which the clause states $`\mathrm{int}`$; `P.length` is the length
$`|P|`$ where $`P`$'s type is an array, the typed-array length
$`\mathrm{view}(P)`$ where it is a view of bytes the overlay of library
types states, the string's length $`\mathrm{strLength}(P)`$ where it is
`string`, and the field `length` read from $`P`$ otherwise. The type
decides only which term a clause names: a clause's facts are proved as
stated where they are established, so a term misread would be unprovable,
never assumed.

**Meaning.** Each atom elaborates to index facts:
`safeInteger(x)` to $`\mathrm{int}(x)`$, `safeInteger(P)` of a nonempty path
to $`P\le 2^{53}-1`$, which holds exactly where $`P`$ reads a safe integer; a
comparison $`E_1\ \mathit{rel}\ E_2`$ to the linear fact over the integers
its terms denote ([linear facts](#linear-facts)), with, for every sum,
difference and product $`e`$ it computes, the range
$`-(2^{53}-1)\le e\le 2^{53}-1`$, each bound of which is clamped at
$`2^{53}-1`$ (a stronger fact). Where those facts hold, JavaScript computes
each side exactly, so the comparison of the two safe integers answers as the
fact states: the facts imply the clause's value under the
[operational semantics](SEMANTICS.md#operational-language). An atom
$`P\ \texttt{!==}\ Q`$ of two paths whose types are arrays elaborates to a
[store separation](#store-separation); one of a path whose type may be a
typed array, or is no array, is refused.

**Integrality.** A value term is an integer only where a clause states it:
a comparison names a path's value, or an element, only where its
conjunction or an unconditional clause states it a safe integer
(`safeInteger(P)`, `safeInteger(P[x])`), and the clause
`0 <= from && from <= to` alone admits `from = 0.5`. A length, a typed-array
length and a string's length are integers by their terms' ranges
([linear facts](#linear-facts)). A clause whose constants leave the safe
integers is refused.

**`result` and entry values.** In an `@ensures`, `result` names the
returned value and its paths, read in the heap of the normal return; a
parameter names its entry value ([postconditions](#postconditions)).

**Refused forms**, each with the clause's location: a form outside the
grammar, a computed key among them, and `old(…)` ([postconditions](#postconditions)); a parameter named
`undefined` in a clause testing `undefined`; a quantified atom's index
named as a parameter; more than 64 alternatives, or a distribution into more
than 1024 facts. Written contracts beyond this language (entry values of
paths, named predicates, contracts over a closure's captures) are the
design of the [checked bound annotations](drafts/checked-bound-annotations.md) draft.

## Preconditions

A function's signature may state a precondition on the call's values
(`pre`, [reads below the length](PROGRAM-TYPING.md#reads-below-the-length)); its code is
checked assuming it, and every call establishes it (`call-requires`). The
arrow's meaning assumes it of each call, so the safety it gives is
conditional on it:

```math
f\in⟦(\vec A)\Rightarrow_{\phi}^{P}R⟧\iff\forall r\,\vec a\,h.\ \vec a\in⟦\vec A⟧\land P[0\mapsto r,\ i+1\mapsto a_i](h)\Rightarrow f(r,\vec a)\ \text{safe at}\ R\ \text{within}\ \phi
```

**Code.** Graph code of arity $`n`$ binds its receiver and its first $`n`$
parameters at the call's positions, so a precondition naming positions up to
$`n`$ is read in the frame as the call passed it (proved). The code is
checked from an entry whose knowledge may state the precondition's facts at
those slots, and its specification assumes them; invoking it supplies them
from the arrow's precondition. Code collecting a rest assumes none.

**Units.** A unit's request carries the index facts it assumes of its inputs,
as it carries their separation; its entry may know them, and its safety
assumes them (in the conclusion of `checkUnitJson_safe`):

```math
\mathrm{EnvOk}(\Gamma_{\mathit{in}},\rho)\land\mathrm{Sep}(\rho)\land\mathrm{IndexHolds}(\mathit{entryIndices},\rho,h)\Rightarrow\text{the unit runs safely from }\rho,h
```

The facts a unit assumes are its function's precondition; every call of the
function at its declared signature establishes the same facts. That a
declaration's signature and its unit's request state the same precondition is
a property of the front end, which reads both from the one clause.

**The clause.** A function declaration, arrow or function expression states
its precondition in its leading JSDoc comment, `/** @requires C */`, in
[the clause language](#the-clause-language) over its parameters. A
function initializer may use its binding statement's leading comment. The
front end elaborates it to index facts at the call's positions; Lean reads
them from the Fragment into the unit's request and into the signature its
callers see, and callers prove the facts as stated. A precondition is
refused on an async function; on one whose parameters are not plain required
names; and on one naming the receiver without declaring it.

**Exported functions.** An exported function's precondition is its
signature's in every module that imports it: the front end elaborates the
clause from the declaration TypeScript resolves the import to, over the
declaration's parameter types, as its own module elaborates it, and states it
on every form of the imported signature. Where the import is certified, Lean
reads the signature at its unit's footprint only where its precondition is
the one the unit is checked assuming, so `call-requires` checks every call of
the analyzed sources, an importer's included. A caller outside the analyzed
sources is trusted to establish it, a stand-in until applications are
analyzed too ([trust surface](DESIGN.md#trust-surface)).

**Calls the producer types.** A call selects a signature stating a
precondition where the producer's own facts at the call's statement establish
it: the bounds and linear facts of its analysis, each actual read as a linear
expression or as a path, a binding and the fields read from it; in an arm of
`c ? a : b`, with what the arm's branch of `c` states. Its facts naming a
length, a typed-array length or a path are preserved by a statement writing
no heap, a call leaving the heap unchanged
([`call-keep`](PROGRAM-TYPING.md#a-call-that-keeps-the-heap)) included, as Lean preserves
them, and forgotten by every other, a test's evaluation, its branches' facts
included, alike; a binding declared at a path's read (`const b = p.f`,
`const { f: b } = p`) restates of the binding each fact over a path through
it. Lean decides at the call (`call-requires`).

**Implementation.** The arrow's meaning is `PromiseWith` and
`ConstructPromise`. Graph code's frame is `codeFrame`, with `Effect.below`
(proved: `Effect.pre_frame`); the entry is `GraphCode.codeEntryIndices` and
`ControlFlow.entryKnows`, the specification `TypingBasics.PreAt` and
`GraphCodeSpec`, the invocation `graph_invoke`. A unit's facts are
`Request.entryIndices`, its safety `RequestsSafe`. The front end's
elaboration is `tools/bound-annotations.mts`, with `fieldType`,
`recordShape` and `namesView`; Lean reads `Fragment.Fn.requires` into the
request and into `moduleArrow`. A closure's `requires` bounds the facts each
claimed signature may assume (`lambdaSetup`, `preCovers`); its body and calls
use `GraphCode.codeChecked_sound` and `preconditionHolds_sound`. Evidence
search seeds the same entry facts that graph-code checking consumes
(`CodeRequest.asRequest`, `produceGraphUsing`). An import's precondition is
`writtenPrecondition` and `writtenImport`, Lean's certified read
`importedArrow` and `qualifiedRead`.

**Cases.** Positive: `closure-precondition` (const-bound and local arrows),
`precondition`, `precondition-lengths`
(`i + 1 < xs.length`, and `xs.length === ys.length` established by a test).
Negative, each run under Node: `invalid-closure-precondition-call` (a local
arrow called at its array's length), `invalid-precondition-call` (a call at
`xs.length`), `invalid-precondition-body` (a body reading past what
its clause bounds), `invalid-precondition-lengths` (a call with no
length equality), `invalid-precondition-lengths-shrunk` (an equality
a `pop` changed) and `invalid-precondition-literal-index` (a literal
index past the clause's bound). Exported: positive
`precondition-exported` and `precondition-value-import` (an
importer's calls of `imports-project/bounded.ts`'s functions); negative, run
under Node, `invalid-precondition-value-import` (an importer's call
at the length). Refused operand: `precondition-disjunction-refused` (the comparison's value is not stated a safe integer).
Over paths: positive `field-path-reads`; negative, each run under Node,
`invalid-field-path-read-at-length` (a call at the flags' typed-array
length), `invalid-field-path-read-other-record` (a read bounded by another
record's field) and `invalid-field-path-read-replaced` (a field replaced
after its test); a gap, `field-path-precondition-unestablished` (an exported
parameter's cursor, of whose index nothing states a safe integer).

## Postconditions

A signature's postcondition `ensures` is a list of index facts at the
return's positions: `0` the result, $`i+1`$ the call's position $`i`$. A
normal return leaves a heap where each holds. A trusted signature, an
intrinsic's or a declaration's, states one, and so does a module function's
signature where it writes `@ensures` or its result's type or a parameter's
names a type invariant ([type invariants](#type-invariants)), which its unit
proves at each return; other code states none. A binding carries none, a signature covers another
only where its facts include each of the other's, the meet of two signatures
states both lists, and a variadic call's selected signature states none, its
actuals not being its positions' values. At a call whose selected signature
$`\mathcal F_\epsilon`$ states one, the knowledge after a normal return
gains each fact renamed from positions to slots, the result to $`r`$, the
receiver to $`x`$ and the $`i`$-th actual to $`y_i`$, where each position the
fact names is a slot:

```math
\frac{\Gamma;\Pi;\Sigma\vdash_G r\leftarrow \mathrm{invoke}(f,x,\vec y):A\dashv \Pi\;;\;\Sigma'\qquad
      \text{at a signature}\ \mathcal F_\epsilon}
{\Gamma;\Pi;\Sigma\vdash_G r\leftarrow \mathrm{invoke}(f,x,\vec y):A\dashv \Pi\;;\;\Sigma',\ \epsilon.\mathsf{ensures}[0\mapsto r,\ 1\mapsto x,\ i+2\mapsto y_i]}\ \textsf{call-ensures}
```

Its premise is the step any other rule checks, `call-requires` included; the
renamed facts hold on its normal return (proved, joining the two
postconditions of the one run).

**Written clauses.** A synchronous module function declaration with one
signature and named non-rest parameters writes `@ensures C` in its leading
JSDoc comment, in [the clause language](#the-clause-language), with `result`
naming the return value and its paths. A leading guard `result === false || C` states `C` on a true return. An unguarded `safeInteger` clause in `@requires` also
permits that value term in `@ensures`; every postcondition fact remains a
return obligation. Array, typed-array and string lengths use their respective
terms. For example:

```ts
/** @requires safeInteger(count) && 0 <= count && count <= 4294967295
 * @ensures result.length === count
 */
export function zeros(count: number): number[] {
  const out: number[] = [];
  for (let i = 0; i < count; i++) out.push(0);
  if (out.length !== count) throw new Error("length mismatch");
  return out;
}
```

A named parameter denotes its entry value; the clause may name it only when
it is a plain required parameter and its binding is unchanged throughout the
body (`parameterKept`). Its paths
read the heap at normal return. `old(...)` is refused: the written language
has no entry-heap snapshots. `result` is reserved, so a function with a
parameter of that name cannot state a postcondition. Async, nested and
overloaded declarations, rest parameters and parameter patterns are refused.
Defaulted and optional parameters may occur when the clause does not name them.

A written postcondition is a contract of the declaration's signature, as its
precondition is. The declaring unit proves it: its unit establishes each
clause at every normal return through [return-ensures](#type-invariants).
Callers assume it: the signature stating it enters a caller's environment
exactly as a precondition's signature does, for module calls and analyzed
importing calls alike, and `call-ensures` gives the caller its facts, of a
binding a declaration or an assignment binds the result to, in each arm of a
conditional (`assignment-call-postcondition`; negative
`invalid-assignment-call-postcondition`, run under Node). A
caller's accepted unit is safe given its callees' signatures:
`checkUnitJson_safe` concludes its safety under `EnvOk` of its inputs at
their signatures, postconditions included. The caller is
[deep verified](DESIGN.md#function-coverage-and-release-thresholds) only when
its callees' units are accepted too. A postcondition adds no trust
assumption.
The front end's shared `postcondition` elaboration supplies both the
function's `ensures` and every imported signature's `ensures`.

**Cases.** `written-ensures` checks an array builder and its bounded caller,
a string-length allocation and a result path; the builder's explicit length
check establishes its return fact. `written-ensures-push-refused` records
the unchecked loop's unproved exact length. `written-ensures-value-import` checks a
caller across an analyzed import. `invalid-written-ensures-body` returns an
array shorter than its contract, and `invalid-written-ensures-unstated`
reads below a count absent from its callee's contract (under Node:
`undefined` and `NaN`). `written-ensures-reassigned-refused` and
`written-ensures-old-refused` exercise the entry-value restrictions;
`written-ensures-default-refused` checks a defaulted parameter reference. A control
in `pipeline/test.mts` forges the unstated result bound after the call; its
incoming edge must establish it.

**Implementation.** The positions are `CallEffects.ensuresEnv`, the meaning
the last conjunct of `CallEffects.Effect.post`, which takes the call's
actuals. A module function's postcondition is stated by `moduleArrow` and
`importedArrow`, other code's is excluded by `Effect.below`; carrying,
covering, meeting and forgetting are `Effect.keeps`, `ensuresCovers`,
`Effect.meet` and `Effect.forgetEnsures`. `call-ensures` is proved by
`PromiseCalls.ensuresCall_sound` and `ensuresAtoms_holds`; the step checker
`Checker.ensuringCalls` joins the two postconditions by
`HeapObservations.cross_upto`.

## Type invariants

A type alias or an interface `R` states a **type invariant** in its leading
JSDoc comment, `/** @invariant C */`, in [the clause language](#the-clause-language)
over the paths of `this`: values, array lengths and
typed-array lengths, `safeInteger(this.f)`, conjunctions of comparisons. Its
meaning is a predicate of a value $`o`$ in a heap, $`I_R(o,h)`$, the clause
with `this` read as $`o`$. Each path is resolved, for its kind (a value, an
array's length, a typed-array length), through the fields `R` declares, or,
where `R` is a sealed handle, through its representation.

**Sealed handles.** A **sealed handle** is an opaque (branded) type, one
declaring no field the clause reads, whose `@representation T` tag beside the
invariant names its underlying record, such as pretext's branded
`PreparedText`. TypeScript resolves `T` where `R` is declared: a record type,
or an alias of an intersection of record types
$`T=T_1\mathbin{\&}\cdots\mathbin{\&}T_m`$, each part a record type or such
an alias, pretext's `PreparedLineData = PreparedLineBreakData & { items?:
ParagraphSegmentData }`. A value of the intersection is a value of every
part, so a path's field resolves through the one part declaring it. A path
reads the value's fields in the heap, whatever its static type, so $`I_R`$ is
a predicate of the handle's object either way. A path no field resolves, a
field several parts of an intersection declare, and a representation of
another type, a union among them, are refused where an annotation names
`R`. A value of the handle's type is a value of its representation
([a handle means its representation](PROGRAM-TYPING.md#a-handle-means-its-representation)),
so a cast into the handle states no fact, and a boundary requiring the
invariant proves it.

**Boundary obligations.** An annotation **names** `R` where it is a reference
to `R` without type arguments, a reference to an alias whose equation names
it, an intersection with a part naming it, or a union each of whose arms
names it; an optional type, a union with an arm naming none, and a generic
reference name none. The invariant is a contract of the boundaries of
function declarations of the module, elaborated by the front end to the facts
of [preconditions](#preconditions) and [postconditions](#postconditions):

```math
\frac{f(\ldots,p_i:T_i,\ldots):T\qquad T_i\ \text{names}\ R}
     {\mathsf{pre}_f\ \ni\ I_R[\mathtt{this}\mapsto i+1]}\ \textsf{invariant-requires}
\qquad
\frac{f(\ldots):T\qquad T\ \text{names}\ R}
     {\mathsf{ensures}_f\ \ni\ I_R[\mathtt{this}\mapsto 0]}\ \textsf{invariant-ensures}
```

```math
\frac{f(\ldots,p_i:T_i,\ldots):T\qquad T_i\ \text{names}\ R\qquad \text{the body of}\ f\ \text{writes no binding named}\ p_i}
     {\mathsf{ensures}_f\ \ni\ I_R[\mathtt{this}\mapsto i+2]}\ \textsf{invariant-returns}
```

for a declaration of the module that is not async, the first for each
parameter $`p_i`$ that is a plain required name (no rest, default, `?` or
pattern: its input slot holds the actual at its position, whatever the other
parameters are), at the call positions a `this` parameter shifts as a
precondition's. So a body assumes the invariant of each value it receives,
and each call establishes it (`call-requires`); a caller gains it of each
value a call returns, and of each value it passes to a parameter the callee's
body writes no binding of, at the actual's slot (`call-ensures`, position
$`i+2`$ the $`i`$-th actual). Which bindings a body writes is read off its
syntax: an assignment, an update or a `for` head naming the parameter
anywhere in the body, a nested scope's same-named binding included; Lean
checks the facts at each return whatever the front end states.

**Between boundaries.** The facts are preserved by the steps whose frame
conditions preserve what they read ([frame conditions](PROGRAM-TYPING.md#frame-conditions)): a
`push` to one array of a received value changes a length, and the next call
requiring the invariant is refused, while an object literal's allocation and
a parameter's default change no old location and preserve them. A value given
type `R` otherwise, by a cast into it, a spread, a native or a read of
another structure's field, carries no fact, and a call requiring the
invariant of it is refused. An importer reads an imported declaration's
invariants as its own module does, over the imported signature's types; the
certified import's signature and its unit state the same facts. A union
result's fact is one every arm's type states, so a return of any arm proves
it.

**Proving postconditions.** A unit's request states its declaration's
postcondition, position `0` the result and $`q+1`$ the entry value of input
slot $`q`$, renamed from the signature's call positions. Which slots hold an
input's entry value is a table of pairs $`(s,q)`$ per node, untrusted: the
entry's pairs are $`(q,q)`$, and an edge carries a pair to each target slot
its mapping reads from the pair's slot, a value it binds shifting the slots;
a pair reaches a node where every edge into it carries it. The check reads
the table, and three conditions decide it: the entry's pairs are $`(q,q)`$;
every edge out of a node the table reaches carries its pairs, the target's
each read through the mapping from one of the source's, so a reassigned
parameter's slot, which no mapping reads from the input's, holds no pair
after the assignment; and each return node the table reaches admits no value,
has an empty result type, or its output knowledge entails each fact, an
input's position read at the slot after the result its pair names, by the
check of index atoms through the return's mapping, the read bridge included;
a fact naming an input no pair holds is refused:

```math
\frac{\forall\,\ell\mapsto(e,\mathsf{ret})\in P.\ \ \Gamma_\ell\ \text{empty}\ \lor\ A_\ell=\emptyset\ \lor\ \Sigma^{\mathit{out}}_\ell\vdash F[0\mapsto 0,\ q+1\mapsto s+1\ \text{for}\ (s,q)\in T_\ell]\ \ (F\in\mathsf{ensures})}
     {P\ \text{returns}\ \mathsf{ensures}}\ \textsf{return-ensures}
```

Every value a normal run returns then meets the facts in the heap it returns
in, with the inputs' entry values (proved, by an invariant of the run's
states beside the safety proof's: at each node the table's pairs hold, and
each edge's target's pairs hold after it; for units, a conjunct of the
conclusion of `checkUnitJson_safe`). A literal's allocation states the read
links of its fields (proved), so the bridge restates a fact over an
initializer's slot as one over the result's path: a return of
`{ widths, segmentFlags }` establishes
$`\mathrm{view}(0.\mathit{segmentFlags})=|0.\mathit{widths}|`$ from the facts
over `widths` and `segmentFlags`. A failing return is refused at its
statement.

**The excluded forms**, refused with the clause's location: a clause outside
the language, as a precondition's; guards are
[guarded clauses](#guarded-clauses). Closures, methods, overloaded and nested
declarations state no invariant facts.

**Implementation.** The declaration graph
(`tools/declaration-graph.mts`) reads the tags of each declaration it
collects, and `recordInvariants` in
`tools/fragment-statements.mts` elaborates them; which parameters a body
writes is `parameterKept` in `tools/bound-annotations.mts`. Lean's
allocation output is `HeapExpressionRules.allocOutput`; an importer's
invariants are `writtenImport`, their agreement with the unit
`Claims.Imports`. A request's postcondition is `SourceRequest.ensures`,
renamed by `extractNormalizedFn`; the table is `GraphCode.trackTable`, the
check `GraphCode.returnsEnsure` with `trackFollows` and `returnEntails` (by
`indicesCheckBy` through `returnMapping`). Proved: `GraphCode.goto_ensures`,
by `EnsState`, `TracksAt` and `NextTracks`, with `edgesTrack_sound`; for
units, `SourceRequests.checkRequests_ensures_at`, a conjunct of
`RequestsSafe`. A literal's read links are `HeapExpressionRules.freshLinks`
(proved in `alloc_sound`); a failing return's refusal is `ensuresRefusal`.

**Cases.** Positive: `bounds-quantified-invariant` (pretext's `createLine`
flow record, with a quantified index bound at its input and return), and
`type-invariant-walker` (pretext's `line-break.ts`
shape: a constructor building `widths` and a view allocated at its length,
walkers reading `prepared.segmentFlags[i]!` below `prepared.widths.length`).
Negative, each run under Node: `invalid-bounds-quantified-invariant` (an
index at the array length), `invalid-type-invariant-constructor` (a
return of a view one element short), `invalid-type-invariant-push` (a
`push` before passing the value on) and `invalid-type-invariant-cast` (a
value typed by a cast). Forged controls in `pipeline/test.mts`: the
invariant claimed of the cast value at the call's entry, refused there, and a
postcondition forged into the parser's document, refused at the return. A
parameter's invariant at its returns: positive
`cursor-invariant-after-writing-call` (pretext's `countSteppedLines` shape:
a loop calling a cursor-writing helper, then reading at the cursor's index);
negative, run under Node, `invalid-cursor-invariant-step-back` (a helper
stepping the cursor below 0, refused at its return); positive
`cursor-invariant-view-path` (a typed-array length read through a field,
preserved at a number field's write, `view-path-stable`) and negative, run
under Node, `invalid-view-path-field-replaced` (the field itself replaced); a
forged control, a parameter's fact the front end does not state forged into
the document, refused at a return. Sealed handles:
`sealed-handle-value-import` (the handle and its casts in and out, `seal` and
`open`, in `imports-project/handle.ts`; a builder establishing the
representation's invariant at `seal`, walkers opening the handle and reading
below `widths.length`, a write of a field the clause does not read, a union
result); negative, each run under Node,
`invalid-sealed-handle-builder-value-import` (a view one element short,
refused at `seal`), `invalid-sealed-handle-resize-value-import` (a `push`
after opening, refused at the next walker's call) and
`invalid-sealed-handle-forged-value-import` (a handle cast from an unrelated
object, refused at the cast); a representation by intersection, positive
`sealed-handle-intersection-representation` and negative, run under Node,
`invalid-sealed-handle-intersection-builder` (a view one element short,
refused at the builder's return); refused gaps
`sealed-handle-no-representation-refused` and
`sealed-handle-union-representation-refused`; a forged control: the handle's
invariant claimed at the walker's entry after the resize, refused there. A
cast into or out of a handle is itself an obligation of the operand at the
handle's or the record's type, which these casts do not meet
(`blocker-pretext-opaque-handle-cast`).

## Guarded clauses

A [precondition](#preconditions) or a [type invariant](#type-invariants) may
start with **guards** ([the grammar](#the-clause-language)'s $`G`$), each a
test that its path reads `null` or `undefined`; `undefined` names the
primitive value. Each path after a guard is
resolved where the guards before it fail: the type at a guarded prefix is its
type without the tag's arm, and an optional field is read where `undefined`
is excluded of it, or, at a guard's own path, where the guard tests
`undefined`. So `this.items === undefined || this.items.hyphenWidths === null
|| this.items.hyphenWidths.length === this.widths.length` reads `items` past
the first guard and `hyphenWidths`'s length past the second. Each fact the
conjunction elaborates to, with every safe-integer obligation of its
arithmetic, is wrapped in a **guarded fact** of each guard, the first
outermost.

**Linear disjunctions.** A clause also admits `A || B`, conjunctions in
parentheses, and `!A` where `A` contains linear comparisons. Negation reverses
each comparison and exchanges conjunction and disjunction; equality's
negation is the disjunction of the two strict orders. Every branch states
the safe-integer obligations of its arithmetic. A comparison's value terms
must be stated safe integers by its conjunction or an unconditional clause.
Thus `!(end > 0) || index < widths.length` expresses an implication over
safe integers.

A disjunction is an index fact with the ordinary disjunctive meaning:

```math
⟦A \lor B⟧_{\rho,h} \iff ⟦A⟧_{\rho,h} \lor ⟦B⟧_{\rho,h}
```

Conjunctions on either side distribute into conjuncts of disjunctions.
Renaming, heap extension and preservation of both arms preserve the fact
(proved). Entailment introduces a disjunction by either arm and uses a
source disjunction by proving the target from each arm (proved). The search
permits eight nested case splits and refuses an exhausted search.

**Implementation of linear disjunctions.** The fact is `IndexFact.either`;
`caseEntails_sound` proves case splitting and `guardEntails_sound` proves
introduction. `guardFollows_sound` connects them to the edge and contract
checks. Entry claims carry recursive `either` arms over guarded linear
claims. The producer carries these facts across statements, retains common
facts at joins, and proposes a surviving arm where its linear search refutes
the other. Each proposed entry is checked by Lean.

**Meaning.** A guard's path reads a value with each field the object's read
of a string key: the location's value where the object owns the key,
`undefined` where it owns neither the key nor a prototype; a missing
intermediate object reads nothing. With $`g`$ the guard's tag, `null` or
`undefined`, and $`\overline g`$ its value:

```math
\mathrm{guarded}(x.p,g,B)(\rho,h) \iff \exists v.\ \mathrm{readGuard}(h,\rho(x),p)=v\land\bigl(v=\overline g\lor B(\rho,h)\bigr)
```

A matching guard requires nothing of the body's terms; a failed read
establishes no disjunction. A numeric term reads an absent field as nothing,
so a guard admits an absent `items` without reading its length as `0`.
Renaming, heap extension and slot congruence carry a guarded fact as they
carry its body (proved).

**Elimination.** An observation excluding the tag of a guard whose path reads
the observed value removes the guard (proved): a failed `null`, `undefined`
or nullish test, or a truthy branch (proved); the path is a slot of the
observed slot's alias class, or one field a current read link, optional or
not, gives as one (proved):

```math
\frac{\mathrm{guarded}(x.p,g,B)\in\Sigma\qquad \mathrm{reads}_\Sigma(x.p)=y\qquad o\ \text{excludes}\ \overline g\ \text{of}\ y}
     {\Sigma\vdash y\ \text{observed}\ o\dashv\Sigma,\ B}\ \textsf{guard-eliminate}
```

So `const { contexts } = prepared; if (contexts !== null) … contexts[i]!`
reads below the length the invariant states: the destructuring's read link
restates the guard of `prepared.contexts` as one of `contexts`, and the
dispatch's failed `null` test frees the body. A conditional's arm reads it
alike: in `items.f === null ? 0 : items.f[i]!` the test's read link answers
the arm's read of `items.f`, which restates the freed fact of the read's
value ([the read bridge](#linear-facts)).

**Introduction.** A guarded target atom, unconditional, on an edge, at a
call's precondition or at a return, is renamed into the source's slots and
entailed (proved): its path is restated toward its root by read links and
toward its end (proved), its body's terms by the read bridge, and it holds
where

```math
\frac{\mathrm{tag}_\Sigma(x.p)=\overline g}{\Sigma\vdash\mathrm{guarded}(x.p,g,B)}\ \textsf{guard-tag}
\qquad
\frac{\mathrm{guarded}(x'.p',g,B')\in\Sigma\qquad \mathrm{lift}(x'.p')=\mathrm{lift}(x.p)\qquad \Sigma,B'\vdash B}
     {\Sigma\vdash\mathrm{guarded}(x.p,g,B)}\ \textsf{guard-match}
\qquad
\frac{\mathrm{lower}(x.p)=y\qquad \Sigma\vdash B}{\Sigma\vdash\mathrm{guarded}(x.p,g,B)}\ \textsf{guard-body}
```

with $`\mathrm{tag}_\Sigma`$ a value fact of the path's slot, or a cell fact
of its one field, holding the tag's value alone (proved), and
$`\mathrm{lower}(x.p)=y`$ the path restated to a slot alone, whose read is
defined. An edge reads the value a slot's type states of each slot its
target's guarded atoms test alone. So a builder's `return { widths, contexts:
null }` proves the invariant by its field's value and `return { widths,
contexts }` after `if (contexts !== null && contexts.length !==
widths.length) throw …` by its two edges, one entering where `contexts` is
`null`, the other where the lengths are equal.

**Joins.** A merge of the search, untrusted, retains a guarded candidate,
each predecessor's guarded atom also restated through its read links, where
every predecessor's knowledge entails it; each edge is checked. The search
retains the value a slot's type states where it admits `null` alone or
`undefined` alone, which an edge widening the slot's type would otherwise
lose. So `const hyphenWidths = items === undefined ? null :
items.hyphenWidths` states `hyphenWidths === null || hyphenWidths.length ===
widths.length` on each arm.

**Frame conditions.** A change preserves a guarded fact where it preserves
its guard's read, a slot alone or one field whose location it preserves
($`\mathrm{first}(x,f)`$), and its body (proved):

```math
\mathrm{kept}_\chi(\mathrm{guarded}(x.p,g,B)) \iff (p=[\,]\lor(p=[f]\land\mathrm{first}(x,f)))\land\mathrm{kept}_\chi(B)
```

A guard read through a longer path, whose locations may hold any value, is
preserved by no change. A guarded fact over a slot alone reads the
environment where its body does (proved).

**The read bridge through an optional key.** A read link through a key the
object may lack bridges terms too: where the key is absent, the read gave
`undefined`, of which no term denotes an integer, as none does of the path
through the absent key (proved).

**The producer** carries guarded facts as it carries linear facts: from a
precondition and a call's postcondition; restated at a path's read and a
destructuring; preserved by a heap change where its guards read slots alone
and the change preserves its fact; a test's branch excluding a guard's tag
adds its body, at a statement's edges and in a conditional's arm; the false
branch of `a && b`, where `a` tests a path against one tag, states `b`'s
branch guarded by that tag; a conditional with a `null` or `undefined` arm
states the other arm's restated guarded facts. Entry claims carry each fact's
ordered guards, each a binding's name, a path and a tag; the lowering wraps
the fact in them.

**Limits.** An object literal with no field `items` has a prototype, so its
read of `items` is the prototype's, which no rule reads: a builder returning
`{ widths }` does not establish `this.items === undefined`. A guard of two
fields or more is introduced by a matching guard or its value's cell facts,
and is preserved by no heap change.

**Implementation.** Path resolution is `clauseParameter` and `withoutTags`
in `fragment-statements.mts`; a guarded fact is `IndexFact.guarded`, the
guard's read `HeapFacts.ReadGave` and `readGuard`, an absent field's term
`readPath`; carrying is proved by `IndexFact.holdsAt_mapM`,
`holdsAt_extend` and `holdsAt_congr`. Elimination is
`HeapKnowledge.unguardIndices`, applied by `observe` (proved:
`unguardIndices_holds`), with `excludesTag` (proved: `excludesTag_ne`) and
`readsClass` (proved: `readsClass_eq`). Introduction is `guardFollows` and
`guardEntails` (proved: `guardEntails_sound`, `guardFollows_sound`, within
`indicesCheckWith_sound`), with `liftGuard` (proved: `liftGuard_eq`),
`lowerGuard` (proved: `lowerGuard_eq`) and `guardTags` (proved:
`guardTags_sound`); an edge's typed values are `typeValues` and
`ControlFlow.withTypedCells`. The join is in `CertificateProducer`, the
tag values `withTagValues`. Preservation is `guardKept` and
`IndexFact.keptBy` (proved: `readGuard_kept`, `holdsAt_kept`), the
environment-only fact `IndexFact.envOnly` (proved: `holdsAt_envOnly`), the
optional-key bridge `readBridge`. The producer is `linear_facts.ml`: each
guarded fact a pseudo-binding (`gfact_key`), elimination `geliminate` and
`with_test`, the conjunction's false branch `gtest`; entry claims carry
`LinearClaim.guards`, which `Lowering/Flow.lean` wraps.

**Cases.** Positive `guarded-invariant-nullable` (pretext's
`discretionaryHyphenContexts`: two builders, a destructured walker,
`returnsFromUnfitHyphen`'s shape, a walker testing the path, two callers) and
`guarded-invariant-optional` (pretext's `items?.hyphenWidths` in
`walkPreparedComplexLines`) and `guarded-conditional-arm` (pretext's
`getItemTabAdvance`, each read in a conditional's arm); negative, each run
under Node, `invalid-guarded-invariant-short` (a builder returning untested
contexts, refused at its return), `invalid-guarded-invariant-other-field`
(the null test of another field, refused at the read) and
`invalid-guarded-conditional-other-field` (alike, in a conditional); forged
controls: the guard removed from a claimed fact, and a guard naming another
field, each refused at its entry.

## Quantified clauses

A [precondition](#preconditions) may end with a **quantified atom** over the
indices of an array or a typed array a path reads, `forall x in P: B` of
[the grammar](#the-clause-language), its body atoms over the parameters'
paths, the index `x`, the element `P[x]`, its data paths and their array,
typed-array or string lengths. An element is named in a comparison only
where the body states it a safe integer, as a path is. Its meaning is one
index fact: the path reads a value whose store of elements holds locations
$`\ell`$, the bound term denotes $`n`$, and for every index below it each
body fact holds, its variables denoting, the element only where it is
present and a safe integer:

```math
\mathrm{every}(x.p,\,t,\,\Phi)(\rho,h) \iff \mathrm{read}(\rho,h,x.p)=v\land\mathrm{elems}(v)=s\land h(s)=\mathsf{arr}\,\ell\land⟦t⟧_{\rho,h}=n\land
\forall i<n.\ \forall F\in\Phi.\ F\ \text{holds at}\ (i,\ \ell_i,\ ⟦\cdot⟧_{\rho,h})
```

with $`\mathrm{elems}(v)`$ an array's store, or, of a host object owning no
store, the location of its model key `[[viewElements]]`: a typed array's
elements ([typed arrays](SOURCE-CONTRACTS.md#stated-library-types)). A
clause `forall x in P: B` elaborates to it with $`t=|P|`$ of an array,
$`t=\mathrm{view}(P)`$ of a typed array, each comparison
of the body to a linear fact over the index, the element and terms, its
computed sums ranged as a clause's are. A hole denotes no element, so a body
naming the element holds of no index holding a hole. A projected term reads
the element's data path in the same heap and then its safe-integer value or
length. For example, `forall i in xs: xs[i].text.length < bounds.length`
bounds the string length read through each element's `text` field. A
numeric data path requires its own `safeInteger(xs[i].offset)` atom.
Projected terms are instantiated by `every-read` with the read value as
their root; mapping and heap extension preserve their meaning (proved).

A prefix clause `forall i < n of P: B` uses the same quantified fact with
its bound the term `n`. The clause states `safeInteger(n)` when `n` names a
value. Length paths are terms too. A bound is one term; a named successor
`const next = n + 1` supplies the bound for an extended prefix.

**Reading an element.** The bounded signature of
$`\%\mathsf{ElementAt}\%`$ ([reads below the length](PROGRAM-TYPING.md#reads-below-the-length))
states in its postcondition the element fact $`\mathrm{element}(0,2,3)`$: the
result is what the store of the array at position 2 holds at the index at
position 3, below its length, the present element's value or `undefined` at
a hole. That is the read's meaning in JavaScript on an ordinary array, whose
element read runs no code ([trust surface](DESIGN.md#trust-surface)), stated
in the intrinsic's trusted signature; `%ByteAt%`'s bounded signature states
the same of a typed array's element store ([typed arrays](PROGRAM-TYPING.md#typed-arrays)). Where a call's postcondition states an
element fact $`\mathrm{element}(r,a,k)`$ and the knowledge states a
quantified fact over an array of $`a`$'s alias class, each body fact holds of
$`k`$ and $`r`$ (proved):

```math
\frac{\mathrm{element}(r,a,k)\in\Sigma\quad \mathrm{every}(x,t,\Phi)\in\Sigma\quad x\in[a]\quad
      \mathrm{int}(k)\quad K\vdash 0\le k\quad K\vdash k\le t-1}
     {\Sigma,\ F[\mathrm{index}\mapsto k,\ \mathrm{elem}\mapsto r]\ \ (F\in\Phi)}\ \textsf{every-read}
```

so `itemSegments[index]!` under `forall i in itemSegments: safeInteger(itemSegments[i]) && 0 <= itemSegments[i] && itemSegments[i] <= data.widths.length`
states its value a safe integer between $`0`$ and $`|\mathit{data}.\mathit{widths}|`$.

An offset term `P[i+d]`, for a nonnegative constant `d`, denotes the
safe-integer value of the element at that index. Alternatives within a body
have the same disjunctive meaning as other clauses; each selected arm
requires its own terms to denote. Thus an ordering contract can state:

```ts
/** @requires forall i in xs: i + 1 >= xs.length || (safeInteger(xs[i]) && safeInteger(xs[i + 1]) && xs[i] <= xs[i + 1]) */
```

The read rule instantiates an offset with a second element read only when
linear entailment establishes that its index equals the first index plus
that offset. `offsetSlot_value` and `instantiateEvery_holds` prove that
substitution preserves the body's meaning. The producer proposes these
instances for reads within the same expression.

**Frame conditions.** A body containing an element projection or offset is preserved
across heap extension and unchanged heaps. The growth and element-write
checks require its projected terms to be re-established; their generic
preservation checks refuse them. Disjunctive bodies also require explicit
checking at an appended or overwritten element; the generic write checks
refuse these bodies.

A quantified fact and an element fact read the heap: a
step leaving the heap unchanged preserves them; a growth of a receiver's
store preserves a quantified fact as below, an exact element write of a
typed array as below, and a write at a checked index one over an array whose
[element region](FOOTPRINTS.md#element-regions) is apart from the written
one (`every-apart-write`); a scalar field write preserves a quantified fact
when it satisfies the rule below. Any other heap change preserves neither, a stated
limit. On an edge a target quantified fact follows from a
source one whose root slot the edge maps it to, of the same path, whose bound
and each body fact the target's follow term by term (proved), and a target
element fact from the same one renamed. A read of field $`f`$ from slot
$`c`$ into slot $`v`$ restates of $`v`$ a quantified fact whose root, bound
or body terms read through $`c.f`$ (proved), so `const { widths } = data`
retains the fact of $`|\mathit{widths}|`$.

**Empty arrays.** A quantified fact over an array of length zero holds for
any body (proved). Its body terms need no interpretation, since no index
is below the bound. The edge checker establishes that the length term is
defined and at most zero; array lengths are nonnegative.

```math
\frac{K\vdash |x.p|=0}
     {\Sigma,\ \mathrm{every}(x.p,|x.p|,\Phi)}\ \textsf{every-empty}
```

An array literal without spreads states its result's length equal to its
number of elements (proved: `IndexWrites.literalArrayAtoms_holds`). Its
lowering evaluates each element once, in source order, then the store and
the object holding it in one inspection. The postcondition records the
length and the allocation's fresh locations. An empty literal therefore
states zero length. The producer proposes the zero-length facts at the declaration
and the written quantified invariant at the loop head; each incoming edge
checks the invariant, including the entry from the empty literal.

**Empty prefixes.** An existing quantified fact witnesses the element store
of its array or view. Together with a defined bound at most zero, it
establishes any quantified body at that bound (proved by
`elementsKnown_sound` and `linearFollows_sound`). The numeric typed-array
constructor's contract states a quantified fact with an empty body over its
result, witnessing the store that represents the freshly allocated view.

**Linear facts across a push.** For value actuals, the append relation
states exactly $`|x|_{\mathrm{after}}=|x|_{\mathrm{before}}+n`$, where
$`n`$ is the number of actuals. For a plain linear fact, each occurrence of
$`|x|`$ therefore contributes its coefficient times $`n`$ to the bound in
the fact after the call. Every other term must be preserved by the
receiver growth's frame. The rule accepts fixed slot actuals, whose context
establishes they are values, and unconditional linear facts; spread actuals
state no count (proved: `PromiseCalls.appended_length`,
`append_fact_holds`, `linearAppendKept_holds`). This applies to equality as
its two inequalities, including the builder invariant `out.length === i`.

**Lengths kept across a push.** A constant holding an array literal's object has
its store field apart from the store field of every older slot's array, a
fresh constant's among them: a [separation fact](PROGRAM-TYPING.md#separation-facts)
the allocation establishes and each cut restates (`separationFacts`), which
names no heap and so survives every heap change, a typed array's write and
a call included. A push into either keeps the other's length
(`growFirst`, through `HeapSeparation.apart` in either orientation; proved:
`growFirst_kept`):

```math
\frac{x=[\,\vec e\,]\ \text{a constant}\qquad y\ \text{an older array slot}\qquad \Sigma\vdash |y|=n}
     {\Sigma\vdash x.\mathtt{push}(\vec v)\dashv\Sigma',\ |y|=n}\ \textsf{push-apart}
```

and symmetrically for a push into $`y`$. The producer keeps such a length at
each statement from the constants' declarations in the node's scope. Cases:
`push-keeps-fresh-lengths` (pretext's `segmentAtLineBreaks`: two literals
pushed around a typed array's write stay equally long); negative
`invalid-push-keeps-fresh-lengths-alias`, run under Node (a constant a
conditional initializes may hold the older array).

**Across a push.** A normal return of `push` changes no old location but its
receiver's store, which it extends: the old elements keep their indices, and
the $`j`$-th actual, where the actuals are values, is the present element at
the old length plus $`j`$ (the append relation of `push`'s trusted contract,
[native footprints](SOURCE-CONTRACTS.md#native-footprints)). So a
quantified fact's array is the receiver's, extended, or one the push keeps,
and each index below its bound keeps its element. A body fact is kept where
each of its terms is preserved by the growth $`\chi=(\bot,\bot,\mathsf{grow})`$
or, in a fact $`\sum_t c_t\,t\le d`$, grown with $`c_t\le 0`$
([frame conditions](PROGRAM-TYPING.md#frame-conditions)), the index and the element read
apart. Two rules follow (proved):

```math
\frac{\mathrm{every}(x.p,t,\Phi)\in\Sigma\quad \mathrm{kept}_\chi(t)\quad \forall F\in\Phi.\ \mathrm{kept}_\chi(F)}
     {\Sigma\vdash r\leftarrow y.\mathtt{push}(\vec a)\dashv\Sigma',\ \mathrm{every}(x.p,t,\Phi)}\ \textsf{every-grow}
\qquad
\frac{\mathrm{every}(x,|x|,\Phi)\in\Sigma\quad \mathrm{int}(a)\quad \forall F\in\Phi.\ \mathrm{kept}_\chi(F)\land K\vdash F[\mathrm{index}\mapsto|x|,\ \mathrm{elem}\mapsto a]}
     {\Sigma\vdash r\leftarrow x.\mathtt{push}(a)\dashv\Sigma',\ \mathrm{every}(x,|x|,\Phi)}\ \textsf{every-push}
```

with $`\mathrm{kept}_\chi(t)`$ of a length $`|z|`$ holding where
$`\mathrm{first}(z,[\,])`$, a separation fact keeping $`z`$'s store apart
from the receiver's. So `itemSegments.push(widths.length)` extends
`forall i in itemSegments: … itemSegments[i] <= widths.length`, and a push of
a value the body excludes, or into an array no separation keeps apart from
the quantified one, keeps no fact over the whole quantified array. A push of
several actuals extends none (`every-push` reads one).

**Across a typed array's element write.** `b[k] = v` of a view at a safe
integer $`0\le k<\mathrm{view}(b)`$ of a safe integer $`v`$ the view's
element type holds unchanged (from $`0`$ to $`255`$ of a `Uint8Array`, to
$`65535`$ of a `Uint16Array`, from $`-2^{31}`$ to $`2^{31}-1`$ of an
`Int32Array`, any of a `Float64Array`) is `%ByteSet%`'s exact signature
([typed arrays](SOURCE-CONTRACTS.md#stated-library-types)): the view's element
store lists the same entries after it but at $`k`$, where it lists a location
holding $`v`$, and every other location holding no store keeps its value,
every store its length. So each index but $`k`$ keeps its element, and the
element at $`k`$ is $`v`$ (proved):

```math
\frac{\mathrm{every}(x,t,\Phi)\in\Sigma\quad x\in[b]\quad \mathrm{int}(k)\quad
      (K\vdash t\le k\ \lor\ \forall F\in\Phi.\ K\vdash F[\mathrm{index}\mapsto k,\ \mathrm{elem}\mapsto v])}
     {\Sigma\vdash r\leftarrow \%\mathsf{ByteSet}\%(b,k,v)\dashv\Sigma',\ \mathrm{every}(x,t,\Phi)}\ \textsf{every-write}
```

with the terms of $`t`$ and $`\Phi`$ kept by the write
($`\chi=(\bot,\bot,\mathsf{length})`$, which keeps every term). A quantified
fact over any other array or view is dropped: views over one buffer share its
bytes, and the model holds each view's elements as a store of its own, so a
fact over a view does not transfer to a `subarray` of it either
(`typed-array-subarray-facts-gap`, a stated limit). An array's length is at
most $`2^{32}-1`$, so a value bounded by one alone is not known to fit an
`Int32Array`: the clause states the bound (`v <= 2147483647`).

**Extending a prefix.** An exact element write at index $`k`$ establishes a
prefix with bound $`m`$ where the old prefix has bound $`n`$,
$`k\le n`$, $`m\le k+1`$, and the written value satisfies every body fact
at $`k`$. The bound and body terms must survive the write. Every index
below $`m`$ is either $`k`$, holding the written value, or below $`n`$,
holding its previous element (proved: `PromiseCalls.every_written_prefix`).
The checker proposes a known term equal to $`k+1`$ as the extended bound;
the producer carries that fact across a value-binding assignment.

**Across a scalar field write.** A field write that keeps stores preserves
a prefix with a stable bound when its body does not name the index and the
new field value satisfies the body. Every unchanged element keeps its
value; an element location equal to the written location holds the new
value, which satisfies the same body (proved:
`HeapExpressionRules.fieldEvery_holds`). The body terms must be preserved
by the write. This rule establishes preservation even where separation
between the cell and element locations is unavailable.

For `items[n++] = v`, the counter read restates the prefix on the old value
of `n`; the field write preserves that prefix by the rule above; the exact
element write extends it to the new value of `n`. The field write's read
link restates that bound on `n`'s cell path (proved:
`HeapKnowledge.liftEvery_holds`). An inclusive body such as
`0 <= items[i] && items[i] <= size` admits the updated counter
where the loop establishes `n <= size`. Saving a length in `size` lets the
existing stable-length rule preserve `items.length === size` across the
counter write. A strict body may exclude
the updated counter; preserving it then requires separation between the
cell and the element locations, a stated limit.

**The producer** carries each precondition's quantified facts to the entries
it claims (an entry's `quantified`, [SOURCE-CLAIMS](SOURCE-CLAIMS.md)),
preserves them across a statement writing no heap and naming none of their
bindings, keeps them across a push as `every-grow` and `every-push` keep
them, where its own frame analysis keeps their bounds, restates them at a
path's read, each read of a destructuring in turn, and, at an element read at an index
its facts bound below the fact's bound, names the read's value with the body
facts instantiated, for the call typing and the linear facts of the
statement.

**Implementation.** The quantified fact is `IndexFact.every`, with
`boundValue` and `elementInt`; the front end's elaboration
(`tools/bound-annotations.mts`) states the body's variables `Bound.index`,
`Bound.elem` and `Bound.free`. The element fact is `IndexFact.element`,
stated in `tools/intrinsics.mts`; `every-read` is
`HeapKnowledge.instantiateEvery`, applied by `PromiseCalls.withEnsures`
(proved: `instantiateEvery_holds`, `withElements_holds`); the store of
elements is `HeapKnowledge.elementsOf`. Preservation is
`IndexFact.keptBy`; the edge rule is `HeapKnowledge.boundFollows` and
`bodyFactFollows` (proved: `every_follows`); the read's restatement is
`HeapKnowledge.readEvery`, in `readAtoms` (proved: `readEvery_holds`, from
`bridgeReads_path` and `bridgeReads_term`). The append relation is
`CallEffects.ReceiverAppends`, beside `ReceiverGrows`, in `Effect.post`;
`every-grow` and `every-push` are `PromiseCalls.everyGrown`, with
`HeapKnowledge.bodyKeptBy` and `appendedBody`, added by `appendKept` in
`withEnsures` (proved: `every_grown`, `every_appended`, from
`boundValue_grown` and `factAt_monotone`; `appendKept_holds`). `every-write`
is `PromiseCalls.everyWritten`, with `writtenBody`, added by `writeKept` in
`withEnsures` (proved: `every_written`, `writeKept_holds`), from the exact
write `CallEffects.ExactWrite`. The producer's
facts are `Linear_facts.efact`, its element reads `Linear_facts.with_reads`
and `element_facts`, its facts across a push `Linear_facts.egrown`.

`every-empty` is the `every` branch of `HeapKnowledge.linearFollows`
(proved: `linearFollows_sound`). `IndexWrites.emptyArrayAtoms` states an
empty literal's length (proved: `emptyArrayAtoms_holds`, by its finite
execution); `Checker.emptyArrays` adds those facts and fresh locations.

**Cases.** Positive: `quantified-element-reads` (a read at an element, a loop
to an element, pretext's `narrowsLine` through a destructured path). Negative,
each run under Node: `invalid-quantified-element-read-inclusive` (an element
at most the length), `invalid-quantified-element-read-alias-write` (a write
through an alias of the quantified array) and
`invalid-quantified-element-read-shrunk` (a `pop` of the bounding array).
Empty entry: positive `quantified-empty-builder` (an empty literal, push
under a written invariant, and a bounded consumer); negative
`invalid-quantified-empty` (`[7]` claimed bounded by a one-element array,
returning `NaN` under Node). Its forged control claims that quantified fact
at the entry immediately following `[7]`.
Across a push: positive `quantified-push-builder` (pretext's builder pushing
`widths.length`, then its `narrowsLine` consumer); negative, each run under
Node, `invalid-quantified-push-value` (a push of a value the body excludes),
`invalid-quantified-push-alias` (a push into an array that may be the
quantified one) and `invalid-quantified-push-shrunk` (a push, then a `pop`
of the bounding array). Over a typed array: positive `typed-array-element-facts`
(pretext's `getHyphenRooms`, a loop pushing an element-bounded read, and a
typed array read through a destructured record); negative, each run under
Node, `invalid-typed-array-element-read-inclusive` (a typed array's element
at most the length) and `invalid-typed-array-element-read-after-write` (a
write through a `subarray` view of the quantified view's bytes). Across an
element write: positive `typed-array-element-writes` (a checked write, then
reads at the written and another index; a loop clamping every element);
negative, each run under Node, `invalid-typed-array-element-write-int32-wrap`
(an `Int32Array` write of $`2^{31}`$), `invalid-typed-array-element-write-uint8-truncation`
(a `Uint8Array` write of 260) and `invalid-typed-array-element-write-value`
(a write of a value the body excludes), each refused where the fact the
producer proposes after the write is checked; a gap,
`typed-array-subarray-facts-gap`. Forged
controls in `pipeline/test.mts`: the inclusive and alias-write negatives'
reads claimed at `number` with the strict quantified fact claimed at the
return's entry, refused there, and alike the two typed-array negatives'; and the
strict fact claimed at the entry after the push of the value and alias
negatives, refused there. An array with a hole reaches no `number[]`: a readable store
holds a hole only where `undefined` meets its element type, and the fragment
makes none.

## Loop invariants

A **loop invariant** is a clause written in a `/** @invariant C */` comment
immediately before a `while`, `do` or `for` loop, in
[the clause language](#the-clause-language), its quantified atom
([quantified clauses](#quantified-clauses)) included, over the bindings in
scope at the loop's head. It holds at the head: every edge into the head, the
loop's entry and each back edge, establishes it, and the head's knowledge
assumes it; the loop's exit, the false branch of its test, starts from it.

```math
\frac{\Sigma_{\mathit{entry}}\vdash I\qquad \Sigma_{\mathit{back}}\vdash I}
     {\Sigma_{\mathit{head}}=\Sigma_{\mathit{claimed}},\ I}\ \textsf{loop-invariant}
```

with $`I`$ the clause's facts rooted at the bindings it names: a value
binding's slot, or an initialized cell's `value` field
([cell terms](#terms-for-bindings-held-in-cells)), including quantified
bounds and free body terms. A clause naming any other
binding is refused at the loop. A path's kind (an array's length, a typed-array length, a field) is
read through the type the binding's declaration has. The invariant states
what the loop needs that no fact of its entry names, such as `j <= 2 * i` of
two counters stepping by 2 and by 1.

**Implementation.** The front end reads the tag before the loop
(`loopInvariantTags`, `clauseRoots`, `loopBindings` in
`tools/bound-annotations.mts`), asks TypeScript the type of each named
binding's declaration (a static type request), and elaborates the clause
(`elaborateRequires`) to index facts at positions naming the bindings, the
`while` node's `invariant` (`LoopInvariant`, `tools/fragment.mts`;
`Fragment.Stmt.loop`). Lean asserts the facts at the head's cut, its
bindings resolved to the head's value slots or cell paths (`Lowering.Flow.invariantFact`), so the check
of each edge into the head (`checkAssertions`) decides it whatever the
producer proposes. The producer adds them to the head's state
(`Source.loop_invariants`, `Proposal_flow`), so the entries of the body claim
what follows from them.

**Cases.** Positive: `loop-invariant-reads` and `bounds-cell-invariant`
(an expression-updated counter). Negative, each run under Node:
`invalid-bounds-cell-invariant` (a false entry over a cell),
`invalid-loop-invariant-back-edge` (a back edge stepping `j` by 3) and
`invalid-loop-invariant-entry` (an entry with `j = 2`). Control in
`pipeline/test.mts`: the back-edge negative's read claimed at `number` with
every fact the producer proposes removed, refused at the loop's head.

## Store separation

A **store separation** $`P\mathrel{\#}Q`$ states that the arrays the paths
$`P = x.p`$ and $`Q = y.q`$ read hold different stores (`IndexFact.storeApart`,
`PathStoresApart`):

```math
h,\rho\models P\mathrel{\#}Q \iff \exists u\,w.\ \mathrm{read}_h(\rho\,x,p)=u \wedge \mathrm{read}_h(\rho\,y,q)=w \wedge
  \forall s\,t.\ \mathrm{store}(u)=s \wedge \mathrm{store}(w)=t \Rightarrow s\ne t
```

For two arrays it is `Footprints.StoreApart`. It is the clause atom
`P !== Q` of two paths whose types are arrays: an array's identity is its
store location ($`\mathrm{store}`$ reads the array object's own store field,
fixed at its allocation), so two distinct arrays never share a store. A
typed array is refused: two views are distinct objects that may share one
buffer. A precondition stating it lets a body keep facts across a call whose
frame changes one of the two stores
([store regions](SOURCE-ELABORATION.md#stated-effects); the central
example of [stated effects](drafts/stated-effects.md#61-the-central-example)):

```ts
/** @requires flags !== runs.openBrackets */
function measure(flags: number[], runs: Runs): number { … }
```

**Establishing it.** A call establishes a precondition's separation from
its knowledge (`call-requires`, `HeapKnowledge.storeFollows`): the paths,
read through the knowledge's read links, reach slots a region fact
([element regions](FOOTPRINTS.md#element-regions)) or a separation of the
slots themselves states apart:

```math
\frac{\Sigma\vdash x.p\leadsto u\qquad \Sigma\vdash y.q\leadsto w\qquad \Sigma\vdash \mathrm{apart}(u,w)\ \text{or}\ u\mathrel{\#}w}
     {\Sigma\vdash x.p\mathrel{\#}y.q}\ \textsf{store-apart-links}
```

with $`x.p\leadsto u`$ a chain of read links from $`x`$'s class through the
fields $`p`$ to $`u`$'s class (`pathReaches`). A fresh array literal is apart
from every older array (`region-alloc`), so `{ openBrackets: [] }` gives
its field's array a separation from every array parameter. Where a slot
leaves the knowledge, a region fact or a separation naming it is restated
through the read links from a kept slot (`restateStores`, beside the linear
facts' `restateReads`).

**Keeping it.** A separation reads no heap where both paths are empty
(`envOnly`). Otherwise it is kept across a step where each path is at most
one field whose location the step keeps (`IndexFact.keptBy` with
`guardKept`): across a call, a field every clause of its slot's type states
`@stable` (`HeapExpressionRules.stableFirst`, `stableFirst_frame`: a stable
location holds its value in every heap a normal return reaches):

```math
\frac{\Sigma\vdash x.p\mathrel{\#}y.q\qquad |p|,|q|\le 1\qquad \Gamma\vdash p,q\ \text{stable fields}}
     {\Sigma\vdash f(\vec a)\dashv\Sigma',\ x.p\mathrel{\#}y.q}\ \textsf{stable-first}
```

**Consuming it.** A call of a frame with store regions keeps the store of
a slot a separation places outside every region, and with it the facts
reading the slot's length (`region-call-keep`,
[store regions](SOURCE-ELABORATION.md#stated-effects)).

**Implementation.** The front end elaborates `P !== Q`
(`elaborateRequires`, `tools/bound-annotations.mts`) to
`{"storeApart": {slot, path, other, otherPath}}`; an entry claim's
`storesApart` proposes one at a statement entry. The producer proposes
those of a precondition, of a declaration of an object literal whose field
holds an empty array literal, and keeps them as Lean does
(`Linear_facts.sstatement`). Proved: `storeFollows_sound`,
`restateStores_holds`, `stableFirst_frame`, `regionFirst_kept`,
`effectKept_holds`.

**Cases.** Positive: `stated-argument-path` (`measure` and its caller) and
`stated-local-runs` (the array allocated in the looping function). Negative,
run under Node: `invalid-stated-alias` (one array as both sides, `NaN`).
Gap: `stated-distinct-view-refused`. Controls in `pipeline/test.mts`: a
separation forged at a caller's entry, and a fact forged across a frame that
may change its array's store, each refused.

## Designs that extend this document

Each draft below extends a mechanism of this document; its status is its
row in [WORK](../WORK.md#status).

- [Checked bound annotations](drafts/checked-bound-annotations.md): written
  contracts beyond [the clause language](#the-clause-language), entry values
  of paths (`old`), named predicates, an invariant opened by a builder, and
  contracts over a local closure's captures and a defaulted parameter.
- [Element facts](drafts/element-facts.md): quantified facts over a typed
  array's bytes shared by its views, across the natives that write them, and
  over a counted prefix a function returns.
- [String lengths](drafts/string-lengths.md): length contracts of further
  string natives (`replace`, `slice` at clamped arguments, `repeat`,
  `padStart`, `JSON`), and a string's element read below its length.
- [Record invariants](drafts/field-paths-and-record-invariants.md#2-record-invariants):
  a record invariant kept across the record's own mutation and through
  values stored in other structures.
- [Stated effects](drafts/stated-effects.md): a callee's frame at the
  locations its arguments' paths reach, so a caller keeps the lengths of
  arrays apart from them.
- [Keeping contract facts across calls](drafts/keeping-contract-facts-across-calls.md):
  frames for the calls a walker makes between two boundaries of a record
  invariant.
