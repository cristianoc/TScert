# Postconditions that say by how much a length changed

Two-state postconditions (`old(…)` in `@ensures`) and the length after a
write at the length: the capabilities P2 and P8 of the bounds analysis of
pretext's rewrites. The native posts P14 needs are a list for the owner
(trust decisions), outside this draft.

## The existing mechanism this extends

- **Postconditions** ([postconditions](../ARITHMETIC.md#postconditions)). A
  signature's `Effect.ensures` lists index facts at the return's positions
  (`0` the result, $`i+1`$ the call's position $`i`$), read in the heap a
  normal return leaves (`Effect.post`, `CallEffects.ensuresEnv`). A unit
  states them at its entry frame (`PassUnit.EnsuresClause`) and proves them
  at each return over the inputs' entry values (`returnCheck`, the slots
  holding them the given inputs of `trackTable`); a caller assumes them
  (`call-ensures`: `PromiseCalls.ensuresAtoms` inside `withEnsures`).
- **Exact changes across a call** ([linear facts](../ARITHMETIC.md#linear-facts),
  "Linear facts across a push"). Where a call states exactly how much a term
  changed, `linearAppendKept` translates each linear fact of the call's entry
  over that term and terms the call keeps by the change (`appendFact`,
  proved `append_fact_holds`). `push` states such a change
  ($`|x|_{\mathrm{after}}=|x|_{\mathrm{before}}+n`$).
- **Entry values in the pass** ([the pass's named
  state](../SINGLE-PASS-PROOF.md#the-passs-named-state)). The state's
  meaning values names by an existential $`\eta`$; each start name is pinned
  to the invocation's entry value ($`\mathit{start}[q]=x\Rightarrow\eta\,x=\mathit{entry}\,q`$),
  the start names held by no slot included. A heap-free fact over names stays
  in the store across every step.
- **The write at a checked index**
  ([writes at a checked index](../PROGRAM-TYPING.md#writes-at-a-checked-index)).

`old` is the first and the third mechanism together: the entry value of a
term is a start name, pinned to the term's value in the entry heap. The
caller's rule is the second mechanism at the change a written
postcondition states. The write's post is the second mechanism at a write.

## 1. `old(P.length)` in a postcondition

**Grammar.** [The clause language](../ARITHMETIC.md#the-clause-language)
gains one term:

```math
E ::= \ldots \mid \mathtt{old}(P.\mathtt{length})
```

in `@ensures`, and in an `@invariant` of a loop of a function stating
`@ensures`. $`P`$ is a path rooted at a parameter, as a precondition reads
it; `P.length` is an array's, a typed array's or a string's length. Two
occurrences of one term are one entry value.

**Meaning.** $`⟦\mathtt{old}(T)⟧(\rho_0,h_0,\rho,h)=⟦T⟧(\rho_0,h_0)`$: the
length read at the call's positions in the heap the call starts in, a
natural below $`2^{53}`$, as the number `num (bitsOfNat n)`.

**Signature.** An effect states its entry terms `olds : List Term` over the
call's positions and its two-state facts `ensuresOld`, read at
$`\mathrm{oldEnv}`$: position $`p<|\mathit{olds}|`$ the entry value of
`olds[p]`, position $`p\ge|\mathit{olds}|`$ the return position
$`p-|\mathit{olds}|`$:

```math
\mathrm{post}_e(r,\vec a)(h_0,h,v)\iff\ldots\wedge\forall F\in e.\mathsf{ensuresOld}.\ F\ \text{holds at}\ \mathrm{oldEnv}_e(v,r,\vec a,h_0)\ \text{in}\ h
```

Every reader of `ensures` is unchanged. A meet concatenates the two lists
with the second's old positions shifted; covering asks equal entry terms;
forgetting drops both.

**Definedness.** Each entry term is a precondition fact $`T_j\le 2^{53}-1`$,
which holds exactly where $`T_j`$ is defined; Lean adds it to the
signature's precondition and the unit's entry facts from `olds` itself, so
a forged fragment cannot omit it.

### 1.1 The callee: entry values are start names

The unit is checked with one start name per entry term after its inputs'
($`w,\ldots,w+m-1`$), held by no slot and pinned to the entry values: the
entry environment is $`\rho_0`$ with $`\rho_0(w+j)`$ the entry value of
$`T_j`$. The start's given facts state

```math
\frac{T_j\ \text{an entry term}\qquad \Sigma_0\vdash T_j\le 2^{53}-1}
     {\Sigma_0\vdash g_j=T_j}\ \textsf{entry-value}
```

at slot $`w+j`$ past the start's slots, which the head entry names $`g_j`$.
A given invariant (`@invariant`) names $`g_j`$ at slot $`|\Gamma|+j`$ past
the head's context; the head query on an edge into the head reads the
source's $`g_j`$ there; a return reads old position $`j`$ at $`g_j`$. A
step reads no ghost name: a heap-free fact over $`g_j`$ (`base === old(T)`)
stays in the store across every step, and a heap fact over $`g_j`$
(`T === old(T) + k`) does not cross a write. So a loop changing $`T`$ binds
its entry value (`const base = T`) and states `base === old(T)` in its
invariant, with $`T`$ over `base`.

### 1.2 The caller: exact changes

A pair of facts of `ensuresOld` stating $`T=\mathtt{old}(T)+L`$, $`L`$ a
linear form over value positions, is an exact change of $`T`$ (renamed to
the caller's slots, $`T'`$):

```math
\frac{F\in\Sigma\ \text{linear, over}\ T'\ \text{and terms the call's effect keeps}\qquad e.\mathsf{ensuresOld}\vdash T=\mathtt{old}(T)+L}
     {\Sigma\vdash r\leftarrow\mathrm{invoke}(f,x,\vec y)\dashv\Sigma',\ F[\,T'\mapsto T'-L'\,]}\ \textsf{call-ensures-old}
```

$`L'`$ the change at the actuals; a term kept is one the effect's change
keeps (`effectKept`'s change and first fields). No other two-state fact
reaches the caller.

### 1.3 Soundness

- **Signature.** A new conjunct of `Effect.post`; the old conjuncts read as
  before.
- **Callee.** `StateHolds` is unchanged; its entry environment is the inputs'
  entry values followed by the entry values. `entry-value` holds at the start
  ($`\eta(w+j)=⟦T_j⟧(\rho_0,h_0)`$, defined by the precondition). The head
  entry reads slot $`|\Gamma|+j`$ at $`\eta(w+j)`$, which `headVal` gives
  every start name; the head query materializes the source with
  $`g_j`$ at that slot, whose value is the source's pinned $`\eta(w+j)`$. A
  return's facts hold at the result pushed onto the entry environment: the
  postcondition at the run's entry heap.
- **Caller.** As `append_fact_holds`, with the change $`L'`$: each other term
  of $`F`$ is kept by the call, and $`T'_{\mathrm{after}}=T'_{\mathrm{before}}+L'`$.

The headline theorems `mode8Accepted_sound` and `crossModule_safe` keep
their statements: they read `RequestSafe` and `RowSpec`, whose
postcondition is `Effect.post`.

## 2. The length after a write at the length

**Proposition** (the analysis's "Write at the length"). For an array $`x`$
and $`0\le k\le|x|`$, after `x[k] = v`: $`|x|=\max(|x|_{\mathrm{before}},k+1)`$
and the index $`k`$ is present.

The rules `write-bound` and `write-append` are
[writes at a checked index](../PROGRAM-TYPING.md#writes-at-a-checked-index)'s.
