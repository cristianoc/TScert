# Draft: tolerant frames, the separation theory of TScert's heap facts

A conceptual account of how TScert's middle layer decides that a heap fact
survives a step. A fact depends on observations of the heap, each with a
tolerance; a step bounds an observation by its effect or by an invariant,
and may state an exact relation from which new facts follow. The effect's
part is a frame theorem that covers disjointness and monotone interference
in one side condition. The statement that carries the theory is the
soundness of a node's knowledge transformer (section 9).

Each claim is labelled **proved** (with its Lean name on `main`),
**cited** (with the source and its scope) or **conjectured**.

## The existing mechanism this extends

- [Footprints](../FOOTPRINTS.md#changes-and-footprints) owns changes,
  regions, a footprint's two-state meaning `Post`, a fact's support and the
  check `stable K S Φ` (proved: `stable_sound`, `frame_sound`,
  `Post.compose`, `transport_sound`; `Footprints.lean`,
  `FootprintStability.lean`, `FootprintRebase.lean`).
- [Frame conditions](../PROGRAM-TYPING.md#frame-conditions) owns the
  preservation of index facts, term by term, from a class-level change
  $`\chi`$ and local evidence (`fact-kept`, `fact-grown`, `stable-first`,
  `view-stable`; proved: `keptIndicesWith_holds`).
- [Separation facts](../PROGRAM-TYPING.md#separation-facts),
  [store separation](../ARITHMETIC.md#store-separation) and
  [element regions](../FOOTPRINTS.md#element-regions) own the forms of
  disjointness knowledge.

The first two are parallel mechanisms joined by one proved abstraction
(`Changes.ofClosed`). The theory below states what they have in common;
section 11 says which parts of that statement are proved.

## 1. The patterns

From pretext's code and the pipeline cases. Each names a fact that must
hold after a step that writes the heap.

**P1. A lower bound under possible aliasing.**

```ts
for (let j = from; j < to; j++) out[j] = xs[j]!;   // needs to <= xs.length; out may be xs
```

An element write never shortens a store, so the bound survives a write
that may hit `xs` itself (`element-write-keeps-lengths`; an upper bound of
a length is lost, `invalid-element-write-upper-bound`).

**P2. A bound across a call that rewrites another array.**

```ts
/** @requires flags !== runs.openBrackets */
function measure(flags: number[], runs: Runs): number {
  let sum = 0;
  for (let i = 0; i < flags.length; i++) { readRuns(runs); sum += flags[i]!; }
  return sum;
}
```

`readRuns` splices `runs.openBrackets`, which may shorten it. The bound
`i < flags.length` survives because the spliced store is another store
(`stated-argument-path`; `invalid-stated-alias` reads `undefined` under
Node).

**P3. Storage the function allocated.** `(unspaced ??= []).push(g)`, or a
helper popping an array its caller built locally. A change to a location
allocated after a function's entry is no part of that function's effect
(`stated-region-fresh`, `stated-region-lazy`), and a fresh array is apart
from every older one (`region-alloc`).

**P4. A write-once cache.** `cached ??= build()` in a helper called inside
a loop: the cell moves from `null` to a value once, and the caller's facts
over lengths and paths survive (`lazy-cache-keeps-facts`).

**P5. Reliance while callbacks run.** `xs.map(f)` reads `xs.length` once
and tests presence at each index between calls of `f`; its result is dense
when `xs` stays dense below the captured length throughout
(`map-stable-push`; `invalid-map-unstable-pop`).

**P6. A quantified element fact across a write to another array.**
`every(z, t, Φ)`, every element of `z` below `t` satisfies `Φ`, across
`a[k] = v` (`quantified-freshness-write`;
`invalid-quantified-freshness-field-alias`).

**P7. Structures built in step.** `count === flags.length` across
`texts.push(…)`; two arrays pushed once each per iteration, their lengths
equal at the loop head (`push-keeps-apart-lengths`;
`invalid-push-keeps-apart-lengths-alias`).

**P8. Separation where a value exists.**
`const chosen = use ? runs : null` gives
`chosen === null || xs !== chosen.open` (`stated-region-nullable-apart`).

**P9. Facts and effects through a field.** `to <= analysis.flags.length`
across helpers that write other fields and other arrays; an effect
`"runs.openBrackets[*]"` naming a store through a field. Both need the
field to denote one array throughout the invocation.

**P10. A length no step changes.** `i < widths.length` for a typed array.

**P11. Exceptional exits.** A fact at a `catch` handler holds in the heap
the throw left, which a callee's normal-return effect does not bound.

**P12. A record replaced on each pass.**

```ts
let r = { n: 0 };
for (const x of xs) r = { n: x };
```

The loop head needs the current record separated from the loop's
iterator, on the entry edge and on the back edge, where `r` names a
different object each time (`blocker-for-of-fresh-record`, open).

**P13. A fact about a field of each element.** `rows[i].n >= 0` for every
`i`, across a write `rows[0].n = -1` or a write to another record: a
quantified fact whose body reads through the element (`Bound.project`).

**P14. Overlapping views.** `const tail = bytes.subarray(1); tail.fill(0)`
changes `bytes[1]`: two views are distinct objects over one buffer.

**P15. A callback writing what it captured.**
`walk(prepared, x => out.push(x))`, with a fact of `prepared` needed
after: the effect of `walk` is its callback's, which captures `out`.

Not treated here: a counted prefix a filler function returns and later
calls extend (`fillEnds`), the arithmetic of generated tables (strides,
products, bit fields), and facts across the ordered evaluation of
parameter defaults.

## 2. The model

### 2.1 Two layers and admissible transitions

The heap is a finite sequence of values indexed by locations; a step may
extend it and removes no location.

**Layer 1, invariants.** A world $`W`$ assigns each location a storage
contract; worlds grow by extension and revise no contract. Types denote
step-indexed, world-monotone predicates, and $`\mathrm{HeapOk}(n,W,h)`$
says every location meets its contract. A write within a location's
contract preserves every typing judgment, whatever aliases exist: the
Kripke model of general references
([SEMANTICS](../SEMANTICS.md#computations-and-recursive-types); cited:
[Ahmed 2004](../REFERENCES.md#ahmed-2004)). Three consequences of fixed contracts are used below:

- a location's class, `store` or `value`, is fixed;
- a location whose contract admits one value holds it in every reachable
  heap (a `@stable` field, a typed array's `[[viewLength]]`);
- an object's own keys and their locations are fixed at its allocation.

A transition $`(\rho,h)\leadsto h'`$ is **admissible** when it is a run of
safely typed code: $`|h|\le|h'|`$, and $`\rho`$, $`h`$ meet a world that
$`h'`$ meets an extension of, at a positive budget. Every statement below
quantifies over admissible transitions only; that restriction is the
whole interface between the layers, and it carries the environment's
typing, the world extension and the budget, not $`\mathrm{HeapOk}`$ alone.

**Layer 2, current-content facts.** The meaning of every fact kind takes
an environment and a heap and neither a world nor a step index (proved by
inspection of the definitions: `FactKind.Holds`, `IndexFact.Holds`,
guarded facts included). Facts are freely duplicable and confer no
permission.

### 2.2 Observations and facts

An **observation** is a partial function
$`o : \mathit{Env}\times\mathit{Heap}\rightharpoonup D_o`$ with a preorder
$`\preceq_o`$ on $`D_o`$, its **tolerance**: a slot's value (equality), the
value a path of fields reads (equality), a store's length (equality, or
$`\le`$), a store's dense prefix ($`\le`$), a typed array's length
(equality), whether a cell's kind lies in a set $`R`$ (equality of the
Boolean). An observation is **bounded** across $`(\rho,h)\leadsto h'`$
when $`o(\rho,h){\downarrow}`$ implies $`o(\rho,h'){\downarrow}`$ and
$`o(\rho,h)\preceq_o o(\rho,h')`$.

A fact's truth in a state depends on a set of observations that varies
with the state. A **dependency** for $`F`$ assigns to each state
satisfying $`F`$ a set $`\mathrm{dep}_F(\rho,h)`$ of observations such
that

```math
F(\rho,h) \;\wedge\; \bigl(\forall o\in\mathrm{dep}_F(\rho,h).\ o\ \text{bounded across}\ (\rho,h)\leadsto h'\bigr) \;\Rightarrow\; F(\rho,h').
```

- A linear fact $`\sum_t c_t\,t\le d`$ depends on each of its terms: a
  length term at $`\le`$ where $`c_t\le 0`$ and at equality otherwise,
  its definedness and its bound by $`2^{32}-1`$ part of the observation
  (proved: `Term.grownBy`, `termValue_grown`).
- $`\mathrm{dense}(x,n)`$ depends on $`x`$'s dense prefix at $`\le`$.
- A guarded fact $`g\vee F`$ depends on the guard's read in every state
  (the read must stay defined), on its value where the guard holds, and
  on the body's observations where it does not; where the guard holds the
  body's reads may be undefined.
- A quantified fact $`\mathrm{every}(z,t,\Phi)`$ depends on a family
  indexed by the state: its stop, and for each index below the stop in
  that state the observations of $`\Phi`$ at that element, at an offset
  and through a projection where the body has them (P13). The family's
  size is the stop's value, not a constant of the formula.
- A separation depends on what its paths read, at equality.

The tolerance a fact kind states is uniform in the fact's constants. The
particular fact $`5\le|x|`$ survives a change of length from 10 to 9; the
kind "lower bound of a length" states $`\le`$, sound for every constant.

Some preservation is not a conjunction of bounds on single observations.
$`\mathrm{apart}(x,y)`$ survives the growth of one store by fresh cells
and not the growth of both, which may list the same fresh cell
(`grownRegions_holds`); and $`\mathrm{every}(x,|x|,\Phi)`$ across an
append needs the old instances bounded and the new index established
(`every_appended`). The first is a joint tolerance of two observations;
the second is preservation together with an exact post (section 5).

### 2.3 Where a bound comes from

A step bounds an observation in one of two ways.

1. **The frame**: the step's effect does not interfere with what the
   observation reads, or interferes within its tolerance (section 3).
2. **An invariant**: the observation reads only locations whose contents
   layer 1 fixes, so every admissible transition bounds it at equality:
   a typed array's length, a path through `@stable` fields (`view-stable`,
   `stable-first`; proved: `stableFirst_frame`, `StablePath.transfer`, on
   normal return).

The frame's pairwise test is not the only way an effect bounds an
observation: a change may be known to leave a location alone by what the
location holds (`init` alters no location holding an object), which the
arithmetic change records and the pairwise test does not (P4).

A step may also state an **exact post** for an observation. That is not a
bound: it may falsify the fact that held before, and it yields a different
fact after (section 5).

## 3. The frame

### 3.1 Changes

A **change** $`\delta`$ is a family of preorders $`\delta_b`$ on values,
indexed by the length $`b`$ of the heap a step starts from, with
$`\delta_{b'}\subseteq\delta_b`$ for $`b\le b'`$: a later step's change is
a change from the earlier base (proved: `Change.Holds.lower`; used by
composition, section 4). Two sets of named changes are in use, at
different precision:

```math
\textit{footprints:}\quad \mathsf{keep} \sqsubseteq \mathsf{init} \sqsubseteq \mathsf{scalar} \sqsubseteq \mathsf{grow} \sqsubseteq \mathsf{any}
\qquad\qquad
\textit{arithmetic, on a store:}\quad \mathsf{keep} \sqsubseteq \mathsf{length} \sqsubseteq \mathsf{grow}^{a} \sqsubseteq \mathsf{any}
```

`init` is the write-once protocol of a nullable cell. The footprint's
`grow` keeps every dense prefix, shortens no store, keeps the bound
$`2^{32}-1`$ and lists as new element cells only locations at or above
$`b`$. The arithmetic $`\mathsf{grow}^{a}`$ states that the length does not
decrease and stays within $`2^{32}-1`$ where it was, and `length` that it
is equal. On stores $`\mathsf{grow}\sqsubseteq\mathsf{grow}^{a}`$, and the
footprint's `grow` and `length` are incomparable. The first chain is proved a chain of
preorders (`Change.Holds.refl`, `.mono`, `.trans`); a footprint's change
maps to an arithmetic one by a proved weakening (`Changes.ofClosed`,
`ofClosed_holds`). The theory needs of the named changes only that each
is such a family and that their order is decidable. A single lattice
containing both chains is conjectured: the meet of `length` and `grow`
(length-preserving rearrangements that keep dense prefixes) is none of
the named elements.

### 3.2 Regions, actions, supports

A **region** $`r`$ denotes a set of locations $`r(\rho,h)`$, taken here
within the allocated ones, $`l<|h|`$ (Lean's `all` is every index, and
`Post` and `Supported` restrict to allocated locations): a field of a slot's object, an
object's own locations, the cells a store lists, the locations of a class,
a path of fields from a slot. It is read in the heap a step starts in, as
a dynamic frame is (cited: [Kassios 2006](../REFERENCES.md#kassios-2006)). A **footprint** $`\Phi`$ is a
finite set of pairs $`(r,\delta)`$ and denotes an **action**:

```math
⟦\Phi⟧_\rho = \bigl\{(h,h') \bigm| |h|\le|h'| \;\wedge\; \forall l<|h|.\ h'(l)=h(l) \;\vee\; \exists (r,\delta)\in\Phi.\ l\in r(\rho,h)\wedge\delta_{|h|}(h(l),h'(l))\bigr\}
```

(`Post`, `Allowed`). A location no entry covers is unchanged; allocation
is free. The judgment $`c:\Phi`$, every normal run of $`c`$ from
$`(\rho,h)`$ ends in some $`h'`$ with $`(h,h')\in⟦\Phi⟧_\rho`$, is the
effect system's (proved for graph code: `checkRequests_footprint_at`,
`checkRequests_regional_at`).

A **support** $`S`$ has the shape of a footprint and the dual reading: the
regions an observation reads, each with a change under which the
observation is bounded. It denotes a rely,

```math
R^S_\rho = \bigl\{(h,h') \bigm| \forall (r,\delta)\in S.\ \forall l\in r(\rho,h).\ l<|h'| \wedge \delta_{|h|}(h(l),h'(l))\bigr\}
```

(`Supported`), and $`o:S`$ states that every admissible transition in
$`R^S_\rho`$ bounds $`o`$. The proved supports
(`FactKind.support_sound`): a slot's value and an alias link,
$`\emptyset`$; a cell's kind and a read link,
$`(\mathsf{field}\,x\,f,\mathsf{keep})`$; a dense prefix,
$`(\mathsf{store}\,x,\mathsf{grow})`$; the kinds of an array's elements,
$`(\mathsf{store}\,x,\mathsf{keep}),(\mathsf{elems}\,x,\mathsf{keep})`$.
For a length $`|x.p|`$ the support is the fields of $`p`$ at `keep` and
the store at $`\mathsf{grow}^{a}`$ or `length` by its tolerance
(conjectured as a support; proved as `Term.grownBy`, `termValue_grown`).

### 3.3 The tolerant frame theorem

Let $`K`$ be separation knowledge with a sound judgment
$`K\vdash r\mathrel{\#}r'`$: in every state where $`K`$ holds, the two
regions' denotations are disjoint. A footprint **respects** a support:

```math
\Phi \mathrel{\triangleleft_K} S \iff \forall (r,\delta)\in S.\ \forall (r',\gamma)\in\Phi.\ \ \gamma \sqsubseteq \delta \;\vee\; K \vdash r \mathrel{\#} r'
```

**Theorem (tolerant frame; proved: `stable_sound`).** If $`K`$ holds at
$`(\rho,h)`$, $`(h,h')\in⟦\Phi⟧_\rho`$ and
$`\Phi\mathrel{\triangleleft_K}S`$, then $`(h,h')\in R^S_\rho`$.

*Proof.* Take $`(r,\delta)\in S`$ and $`l\in r(\rho,h)`$, so $`l<|h|`$. By
the action, $`h'(l)=h(l)`$, and $`\delta`$ is reflexive; or some
$`(r',\gamma)\in\Phi`$ has $`l\in r'(\rho,h)`$ and
$`\gamma_{|h|}(h(l),h'(l))`$. Then $`K\vdash r\mathrel{\#}r'`$ contradicts
$`l`$ lying in both, so $`\gamma\sqsubseteq\delta`$. ∎

**Corollary.** If $`c:\Phi`$, $`o:S`$ and
$`\Phi\mathrel{\triangleleft_K}S`$, every normal run of $`c`$ from a state
satisfying $`K`$ bounds $`o`$.

With every tolerance `keep`, the side condition is disjointness of what
$`c`$ writes from what the fact reads: the frame rule of region logic
(cited: [Banerjee, Naumann and Rosenberg 2013](../REFERENCES.md#banerjee-naumann-and-rosenberg-2013), for first-order programs
with read effects of formulas). Where no pair is separated (class disjointness is intrinsic and needs no
stated knowledge) it is $`\gamma\sqsubseteq\delta`$ at every pair: stability of an assertion under
an interfering action (cited: [Jones 1983](../REFERENCES.md#jones-1983)). The theorem decides between the
two per pair of entries, which is what a loop invariant mixing both kinds
of fact needs.

**Bounds at the read location.** The index-fact mechanism carries, beside
a step's class-level change, direct evidence that one read location holds
the same value after the step (`FirstKept`, `ViewsKept`). Its sources:
the field is `@stable`, an invariant; the step is a field write and the
read field is apart from it or a sibling; the step changes only its
receiver's own locations (`call-own`) or its receiver's store
(`receiverGrows`) and the read location is apart from that region. The
field write and the receiver-local calls are instances of the corollary
at the region the step states (the written field, the receiver's own
locations, the receiver's store) in place of the class-level footprint (conjectured as a derivation; proved directly:
`keptIndicesWith_holds`).

**Reliance over many steps.** A construct that relies on a fact while it
runs callbacks applies the corollary at each callback's return, in the
state that callback started in (proved: `rely_chain`, `map_rely`,
`elems_rely`). No transitivity of the rely is used.

## 4. Composing effects

A body's footprint is stated at its entry state $`(\rho_0,h_0)`$; each
step's is read where the step starts, at $`(\sigma,h)`$. Composition
rebases the step's regions to the entry:

```math
\frac{(h_0,h)\in⟦\Phi⟧_{\rho_0} \qquad (h,h')\in⟦\Psi⟧_\sigma \qquad \mathrm{RebaseOk}\ \mathit{ev}\ \sigma\ \rho_0\ h_0\ h \qquad \Phi \cup \mathrm{rebase}_{\mathit{ev}}(\Psi) \sqsubseteq \Phi}
     {(h_0,h')\in⟦\Phi⟧_{\rho_0}}
```

(proved: `Post.compose_at`, `rebase_sound`). $`\Phi`$ is its own bound, so
it is an invariant through loops. The evidence $`\mathit{ev}`$ is checked
provenance: which entry path each step position's value was read from,
that a path read at $`h`$ reads the same at $`h_0`$, which element cells
were listed at $`h_0`$, and which positions hold storage allocated at or
above $`|h_0|`$. This is the self-framing obligation of dynamic frames in the
form of a containment: each location the step's region selects at $`h`$
must lie in the rebased region read at $`h_0`$, or be covered by an entry
of $`\Phi`$ at `any`, or be no location of $`h_0`$. Where the inclusion
uses the classes of locations it also needs their evidence at $`h_0`$
(`ClassOk`). The containment is discharged by layer 1 for a path through `@stable` fields
(`StablePath.transfer`, `read_stable`); a location at or above $`|h_0|`$
lies in no region read at $`h_0`$ and rebases to the empty footprint
(`checkFresh_sound`); any other region widens to a class or to all locations.

**Freshness bounds effects, not facts.**

```ts
function shrink(xs: number[]): Modifies<{ values: "any"; "xs[*]": "any" }, void> { xs.pop(); }
function f(): number { const xs = [1]; shrink(xs); return xs[0]!; }
```

`xs` is allocated after `f`'s entry, so the call's store region rebases
to nothing: for `f`'s callers the pop does not exist, and `f`'s effect
keeps of the call only its `values: any`. Inside `f`, the
fact $`0<|\mathit{xs}|`$ is an observation of the current heap, and the
call's footprint, read at the call, covers its store at `any`. The
corollary does not apply, and the fact is lost, as it must be. Rebasing
serves section 4; the frame of section 3 is always read at the step.

## 5. Exact posts

Beside its footprint, a step may state an exact relation between one
observation after it and the state before: a field write's read link
(`write-link`), a push's append (`ReceiverAppends`: the new length and the appended
contents; `ReceiverGrows`, its bound, keeps the old indices), a typed array's element
write. A fact over that observation after the step is derived by substitution
from the facts before it; the fact that held before may be false after. This is a strong update on shared state, sound without
ownership because it constrains only the written location: any other
observation survives the step through section 3, where aliasing is
accounted for. An array that may alias a pushed receiver keeps its lower
bounds and loses its equalities.

A write that redirects a path, `x.f = ys`, is of this kind for the facts
that read through `x.f`: they are facts of the new referent only where
the post's read link and the facts of `ys` re-derive them. Framing the
old referent's store says nothing of the new one.

## 6. Separation in use

Separation enters only as $`K\vdash r\mathrel{\#}r'`$ between two named
regions. The forms $`K`$ states:

| Form | Statement | Used for |
| --- | --- | --- |
| field locations | two objects' field locations differ (`HeapSeparation`) | cell facts and read links across a field write |
| stores | $`P\mathrel{\#}Q`$: the arrays two paths read hold different stores (`StoreApart`) | length facts across a call or write changing a store (P2, P7, P8, P9) |
| element regions | $`\mathrm{apart}(x,y)`$: two arrays share neither store nor cell (`RegionsApart`) | facts reading element contents (P6) |
| classes | a location of class `store` is no location of class `value` (layer 1) | every length fact against `values: any` |

**Depth.** The fact language has no recursively defined predicate. Each
formula traverses paths of a length fixed by the formula, at an index
offset and under at most one quantifier over an array's indices, so the
locations a fact reads are given by finitely many path schemas, each
instantiated at the indices below a stop, together with class regions.
Their number depends on the state; their depth does not. No pattern asks
for the disjointness of two reachability closures. P13 needs a region the
present forms lack, a path from each object a store lists.

**Separation facts are facts**, with dependencies of their own:

- a separation of two slots' own locations has no observation of the
  heap: identity is fixed at allocation;
- $`x.p\mathrel{\#}y.q`$ reads the fields of $`p`$ and $`q`$ at equality;
  through `@stable` fields it is bounded by layer 1 (`stable-first`);
- a guarded separation has the conditional dependency of section 2.2;
  where the guard reads a slot alone, only the body needs a bound (P8);
- $`\mathrm{apart}(x,y)`$ reads the cells the two stores list. Its
  proved support keeps both stores; its useful preservation is the joint
  one of section 2.2 (`grownRegions_holds`, from `ReceiverGrows` with
  `ReceiverAppends`; `writeAtoms_holds` at a checked index).

**Where separation comes from.** Inside a unit, allocation: a fresh
object's locations differ from every older one's (`sep-alloc`,
`region-alloc`). At a unit's entry, a stated precondition each caller
establishes (`call-requires`, `store-apart-links`), and module cells,
apart by construction. P12 is the case where allocation is not enough:
the separation must be re-established for a new object on each back edge.

**Cost of the pairwise form.** $`n`$ mutually distinct stores are
$`n(n-1)/2`$ facts. Two compact forms: an $`n`$-ary atom
$`\mathrm{distinct}(P_1,\ldots,P_n)`$ of the same meaning (conjectured),
and separation by allocation order, one slot's storage lying after a heap
mark another's lies before, which implies distinctness and is stronger
(proved in the model for own and field locations: `stamps_separate`;
reached from no source request).

## 7. The patterns, derived

| Pattern | Observation at its tolerance | The step | Source of the bound |
| --- | --- | --- | --- |
| P1 | $`|\mathit{xs}|`$ at $`\le`$ | `out[j] = v` : every store at `grow` | frame, $`\mathsf{grow}\sqsubseteq\mathsf{grow}^{a}`$; no separation |
| P2 | $`|\mathit{flags}|`$ at $`\le`$ | `readRuns(runs)` : `values: any`, the store of `runs.openBrackets` at `any` | frame, $`K\vdash\mathit{flags}\mathrel{\#}\mathit{runs}.\mathit{openBrackets}`$ |
| P3 | a caller's observation | a body writing storage it allocated : $`\emptyset`$ after rebasing | frame, no pair to check |
| P4 | a length, a path | `cached ??= build()` : `values: init` | a bound by contents: `init` alters no location holding an object, a number or a store. The pairwise test of section 3.3 does not give it ($`\mathsf{init}\not\sqsubseteq\mathsf{keep}`$ at an overlapping region); the arithmetic change, which classifies a location by what it holds, does (`Changes.ofClosed`) |
| P5 | $`x`$'s dense prefix at $`\le`$ | each callback : stores at most `grow` | frame, at each return (`rely_chain`) |
| P6 | the elements of $`z`$ below $`t`$ | `a[k] = v` : $`a`$'s store and cells | frame, $`K\vdash\mathrm{apart}(a,z)`$ |
| P7 | $`|\mathit{flags}|`$ at equality | `texts.push(…)` : the store of `texts` | frame, $`K\vdash\mathit{texts}\mathrel{\#}\mathit{flags}`$ |
| P8 | an observation of `xs` | a call with region `chosen.open[*]` | frame, by cases on the guard |
| P9 | $`|a.\mathit{flags}|`$ at $`\le`$ | a helper : `values: any`, `stores: grow` | invariant for the path, frame for the store |
| P10 | a view's length | any step | invariant |
| P11 | any | a call that throws | frame at the effect's bound on a throw, where it states one |
| P12 | the separation of `r` from the iterator | the back edge | establishment by allocation on each pass; open |
| P13 | $`\mathit{rows}[i].n`$ for each $`i`$ | a field write | frame against a region of element fields, which no form states |
| P14 | an element of `bytes` | `tail.fill(0)` | needs regions of buffer cells with offsets; not covered |
| P15 | an observation of `prepared` | `walk(prepared, cb)` | needs the callback's effect, captured roots included, in `walk`'s; not covered |

**P1 and exclusive points-to.** A specification of the write by
$`\mathit{out}\mapsto\_`$ frames a fact of $`\mathit{xs}`$ only where the
two are separated, or after a case split on their equality. The program
provides neither. The bound is closed under everything the write can do
to any store, so the frame asks nothing about aliasing.

**P2 in full.** The body's entry carries $`i<|\mathit{flags}|`$ and
$`K=\{\mathit{flags}\mathrel{\#}\mathit{runs}.\mathit{openBrackets}\}`$.
`openBrackets` is `@stable`, so the path is bounded by an invariant across
the call, and with it $`K`$. The observation $`|\mathit{flags}|`$ has
support $`(\mathsf{store}\,\mathit{flags},\mathsf{grow}^{a})`$. Against
the call's entry $`(\mathsf{store\ of}\ \mathit{runs}.\mathit{openBrackets},\mathsf{any})`$
the pair is decided by $`K`$; against
$`(\mathsf{cls\ value},\mathsf{any})`$ by the classes. The caller
establishes the precondition from `region-alloc` at
`{ openBrackets: [] }` through the field's read link.

**P9 with a mutable field.** Without `@stable`, the observation
$`|a.\mathit{flags}|`$ reads the field's location at equality, and a
helper stating `values: any` covers that location at `any`: the pair is
neither within tolerance nor separated, and the fact is lost. With
`@stable` the field's read is an invariant, the observation reduces to a
length of a fixed store, and `stores: grow` is within its tolerance. The
annotation moves one observation from the frame to the invariant layer;
nothing else in the derivation changes.

**P7 when both arrays are pushed.** $`|a|=|b|`$ does not survive
`a.push(x)`, and no bound is sought for it. The push's exact post gives
$`|a|'=|a|+1`$ on normal return, $`|b|`$ is bounded by the frame where
$`a\mathrel{\#}b`$, and the fact after the step is $`|a|=|b|+1`$; after
`b.push(y)` the equality holds again for the loop head. The intermediate
assertion differs from the invariant: this is reasoning by exact posts,
with the frame used only for the array not pushed.

## 8. Which separation logic, and how much

**Region-based effect framing with assertion-specific stability, over a
Kripke model of types.** What it takes from each line of work, and where
it stops:

- **Dynamic frames and region logic** (cited: [Kassios 2006](../REFERENCES.md#kassios-2006); [Banerjee, Naumann and Rosenberg 2013](../REFERENCES.md#banerjee-naumann-and-rosenberg-2013)): effects and read footprints are
  location-set expressions read in the pre-state; framing is a
  disjointness judgment between two of them; region expressions carry a
  self-framing obligation. TScert's regions are a fixed vocabulary of
  path-shaped expressions and no first-class region values.
- **Stability under interference** (cited: [Jones 1983](../REFERENCES.md#jones-1983)): a step's
  footprint is a guarantee, and a fact tolerates an action. The relies are
  derived from each fact kind and are never composed or stated by the
  program, so this is the stability check of rely/guarantee and not its
  calculus.
- **Monotone state** (cited: [Ahmed, Dreyer and Rossberg 2009](../REFERENCES.md#ahmed-dreyer-and-rossberg-2009); [Dreyer, Neis and Birkedal 2010](../REFERENCES.md#dreyer-neis-and-birkedal-2010); [Ahman et al. 2018](../REFERENCES.md#ahman-et-al-2018)): a location evolving along a
  preorder, with assertions closed under it surviving. `init` and `grow`
  are such protocols. They are enforced by the effect system's judgment
  $`c:\Phi`$ at each step and by no resource discipline.
- **Kripke semantics of types** (cited: [Ahmed 2004](../REFERENCES.md#ahmed-2004)): layer 1.

From separation logic proper the theory takes the frame principle and the
allocation rule (sections 4 and 6), and neither the separating conjunction nor a
resource model. The design is duplicable assertions together with checked
effects: disjointness is a judgment between a fact's read region and a
step's write region, and no assertion carries a permission. Whether the
model is an instance of an abstract separation logic or of Views
([Calcagno, O'Hearn and Yang 2007](../REFERENCES.md#calcagno-ohearn-and-yang-2007); [Dinsdale-Young et al. 2013](../REFERENCES.md#dinsdale-young-et-al-2013)), with
supports as the resource and section 3.3 as locality, is open: it would
need a composition on supports and the frame and safety-monotonicity
properties proved for it.

**How much separation.** In the patterns above and the present
vocabulary: pointwise disjointness of path-shaped regions of fixed depth,
pairwise, established by allocation or assumed at a unit's entry.
Tolerance and invariants decide P1, P4, P5, P9's path and P10 with no
separation. The additions the patterns ask for are regions along a path
from each element (P13), buffer cells with offsets (P14) and effects
parametric in a callback's (P15). This describes what the patterns use;
it is not a completeness result for the programs TScert may meet.

## 9. The knowledge transformer and the forward pass

The statement that carries the theory is about a node and its exits.
Knowledge $`\Sigma`$ is a set of facts over the node's input environment
$`\rho`$, with separation knowledge $`K\subseteq\Sigma`$. A node has a
checked effect $`\Phi`$ on normal return and exact posts $`Q`$ relating
its result and the locations it writes to the state before; on a throw it
has a checked effect $`\Phi^{e}`$ where it states one and the unrestricted
effect otherwise, and no post. Each exit has an environment transport: the
normal exit extends $`\rho`$ by the result,
$`\rho'=\rho[r\mapsto v]`$, and the exceptional exit gives the handler
$`\rho`$ extended by the thrown value.

A **checked transformer** for an exit is a set $`\Sigma'`$ of facts over
the exit's environment with a derivation for each $`F'\in\Sigma'`$, of
one of two shapes:

- *kept*: $`F'`$ is some $`F\in\Sigma`$ not mentioning the result, and the
  derivation gives, for $`\mathrm{dep}_F`$, bounds by the frame at the
  exit's effect under $`K`$ or by an invariant, jointly where $`F`$ needs
  it;
- *derived* (normal exit only): $`F'`$ follows from $`Q`$ together with
  facts of $`\Sigma`$, each of which is itself kept across the node. In
  P7 the fact $`|a|=|b|+1`$ after `a.push(x)` is derived from the append
  post and $`|a|=|b|`$, with $`|b|`$ bounded by the frame.

**Theorem (transformer soundness).** Let $`\Sigma'`$ be a checked
transformer of $`\Sigma`$ for an exit of a node. For every admissible
transition of the node through that exit from $`(\rho,h)`$ to
$`(\rho',h')`$, meeting the exit's effect and, on normal return, $`Q`$:
if $`\Sigma`$ holds at $`(\rho,h)`$ then $`\Sigma'`$ holds at
$`(\rho',h')`$.

The cases of its proof are those of this document: a bound by the frame
(section 3.3), a bound by an invariant or by contents, the conditional
dependencies of guarded facts, the state-indexed family of a quantified
fact and its extension at an appended index, the joint preservation of
`apart`, and derivation from exact posts. It is proved for the rules of
the present checker, rule by rule, in their own statements
(`keptIndicesWith_holds`, `frame_sound`, `writeAtoms_holds`,
`grownRegions_holds`, `every_appended`, `write-link`); as one statement
over one definition of derivation it is conjectured.

**Graphs.** With knowledge $`\Sigma_l`$ at each program point, soundness
of a forward pass follows from the theorem and three checks: the entry
state establishes the entry knowledge; on every edge, a checked
transformer of the source's knowledge, renamed along the edge, entails
the target's; and every loop head is such a target, on its back edges
too. A pass that computes transformers forward and intersects at merges
produces the $`\Sigma_l`$ of acyclic regions; at a loop head the
knowledge is given and checked. The proved check discharges these
obligations edge by edge; for the single forward pass they are
conjectured.

## 10. Limits

- **Joint tolerances** have no general form: `apart` under growth is a
  rule of its own (section 2.2).
- **Element-field regions** (P13) and **buffers** (P14).
- **Frame variables** (P15): a footprint is closed, so a higher-order
  function states a bound for every callback it admits (cited for the
  general problem: [Birkedal, Torp-Smith and Yang 2005](../REFERENCES.md#birkedal-torp-smith-and-yang-2005)).
- **Suspension.** Across an `await` the step's footprint is the
  environment's, which no judgment bounds.
- **Invariants broken across a call.** A relation a callee is expected to
  restore has no form: at each step a fact is bounded or re-derived.
- **Type-changing updates.** Contracts are fixed; layer 1 has no strong
  update.

## 11. Proof status

| Statement | Status |
| --- | --- |
| The footprint changes; actions; supports; the tolerant frame theorem; the supports of value, cell, link, density and element-kind facts | proved (`Change.Holds.*`, `Post`, `Supported`, `stable_sound`, `frame_sound`, `FactKind.support_sound`) |
| Composition with rebasing; stable paths; store freshness | proved (`Post.compose_at`, `rebase_sound`, `StablePath.*`, `checkFresh_sound`) |
| Reliance during callbacks | proved (`rely_chain`, `map_rely`, `elems_rely`) |
| Preservation of index facts, quantified facts and separations, from a class-level change and local evidence | proved (`keptIndicesWith_holds`, `termValue_grown`, `stableFirst_frame`, `writeAtoms_holds`, `grownRegions_holds`) |
| Transformer soundness as one statement over one definition of derivation, with both mechanisms as instances | conjectured |
| Bounds at the read location (`FirstKept`, `ViewsKept`) derived from the frame at the region a step states | conjectured |
| One change lattice containing `length` and the footprint's `grow` | conjectured |
