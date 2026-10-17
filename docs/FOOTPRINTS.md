# Footprints: one framing mechanism for heap-dependent facts

A design for keeping facts about the heap across writes, calls and callbacks
by one check. It states the vocabulary (regions, changes, footprints, facts
and provenance), the stability check, how footprints compose through graphs
and calls, the natives as instances, what the producer proposes and what
Lean decides, how the design treats the checker's existing mechanisms, how it
decides seven example programs, and its increments.

Each claim is labelled **proved** (with its Lean name), **audited** (with
its row in [native footprints](SOURCE-CONTRACTS.md#native-footprints)) or
**conjectured**. Proved lemmas are in `lean/Verification/Semantics/`
(`Footprints.lean`, `ClosedFootprints.lean`, `FootprintProvenance.lean`,
`FootprintStability.lean`, `FootprintNatives.lean`) and `lean/Verification/Programs/FootprintTyping.lean`;
their counterexample controls are in
`lean/Verification/Tests/FootprintControls.lean`, which also checks that every
theorem of the `Footprints` namespace rests on `propext`, `Classical.choice`
and `Quot.sound` alone. A rule without a proof or an audit is a proof
obligation of the design. [WORK](../WORK.md#footprints) tracks the work.

## The problem

Type safety rests on storage contracts that never change: a location keeps
its contract for the whole execution, so a write meeting the contract
preserves typing, as in ML. A write breaks no typing judgment.

A write or a call can break a **heap-dependent fact**: something the checker
relies on beyond the declared types, such as a cell's observed contents
(`HeapFacts.Fact`), a read link (`HeapLinks.Link`), or the density `map`
relies on to return a dense array. `Array.prototype.map` reads the length
`len` once, then for each `k < len` tests whether index `k` is present and
skips it when it is not, leaving a hole in its result
([ECMA-262](REFERENCES.md#ecma-262), `Array.prototype.map`). Its result is
dense when every index below `len` is present at each test.

The mechanism: **a heap-dependent fact is kept across an action when the
action's footprint provably preserves it.** Every construct (field writes,
element writes, allocations, native calls, defined calls, callback
boundaries, edges, loops) states its action as a footprint and keeps facts
through one check. The mechanism frames facts; typing, promise
establishment, refinement, shape analysis and lowering produce them by their
own rules.

## Regions

The calculus heap is a list of values indexed by locations. An object value
`.objAt fs c oid` maps keys to locations, a map fixed in the value. An array
object holds its store under the key `[]`; the store location holds `.arr ls`,
a list of optional element locations whose length is the array's length.

A **region** names a set of locations relative to an assignment `ρ` of values
to roots and a heap `h`. Roots are a graph point's slots, or a call contract's
operands: `self` (the callee value), `receiver` and `arg i`, and for a code
entry `cap i`, its closure value's `i`-th capture.

| Region | Denotation $`[\![r]\!]_{\rho,h}`$ | Depends on |
| --- | --- | --- |
| `field(x, k)` | the location `ρ x` maps key `k` to | `ρ` |
| `store(x)` | `field(x, [])` | `ρ` |
| `own(x)` | every location `ρ x` maps a key to | `ρ` |
| `elems(x)` | the element locations `h[store(x)]` lists | `h` |
| `class(store)` | every `l < h.length` with `h[l] = .arr _` | `h` |
| `class(value)` | every `l < h.length` with `h[l]` other than `.arr _` | `h` |
| `all` | every location | – |

Regions depending only on `ρ` are **timeless**. A footprint reads every
region at the heap before its action. The two classes partition the
locations below `h.length` by their contents. Regions name locations, the
location of a field rather than the object stored in it; an object read from
the heap is a new slot, with only the provenance below.

## Changes and footprints

A **change** is a reflexive, transitive relation on a location's contents,
parameterised by the length `b` of the heap it starts from:

```math
\begin{aligned}
\mathsf{keep}_b(v, v') &\iff v' = v\\
\mathsf{grow}_b(v, v') &\iff v' = v \lor \bigl(v = \mathsf{arr}\,ls \land v' = \mathsf{arr}\,ls' \land (\forall n.\ D_n\,ls \to D_n\,ls') \land \forall l.\ \mathsf{some}\,l \in ls' \to \mathsf{some}\,l \in ls \lor b \le l\bigr)\\
\mathsf{any}_b(v, v') &\iff \top
\end{aligned}
```

with $`D_n\,ls \iff n \le |ls| \land \forall i < n.\ ls[i] \ne \mathsf{none}`$,
the first `n` indices present. `grow` keeps every dense prefix and lists no
old element location the store did not list; it permits rearranging element
locations and removing indices beyond the first hole. The changes form the
chain $`\mathsf{keep} \sqsubseteq \mathsf{grow} \sqsubseteq \mathsf{any}`$
(proved: `Change.Holds.refl`, `.mono`, `.trans`, `.seq`; `.lower`: a larger
starting heap only strengthens `grow`; `.same_class`: only `any` changes a
location's class; `.grow_value`: on a non-store, `grow` is `keep`).

A **footprint** $`\Phi`$ is a finite list of entries $`(r, \delta)`$. A
location no entry covers keeps its contents; the change allowed at `l` is the
join of the entries covering it. Its meaning relates the heap `h` its regions
are read at to a later heap `h'`, constraining old locations only:

```math
\mathsf{Post}_\Phi(\rho)(h, h') \iff |h| \le |h'| \land \forall l < |h|.\ \mathsf{allowed}_\Phi(\rho,h,l)_{|h|}(h[l], h'[l])
```

(`Post`, which states the change at `l` as within one covering entry, the
same relation since changes form a chain.) Its extremes:
$`\mathsf{Post}_\emptyset`$ is `IsPrefix`, heap preservation (proved:
`Post.empty_iff`), and $`\mathsf{Post}_{\{(\mathsf{all},\mathsf{any})\}}`$
is $`|h| \le |h'|`$ (proved: `Post.all_iff`), which every run meets (proved:
`steps_grow`). `postB` decides `Post` on concrete heaps (proved: `postB_iff`).

**Order.** $`\Phi \sqsubseteq_{cl} \Psi`$ (`Footprint.le`) holds when every
entry of $`\Phi`$ lies in an entry of $`\Psi`$ with at least its change:
`field(x,k) ⊆ own(x)`, every region in `all`, each in itself, and
`field(x,k) ⊆ class(c)` where the class evidence `cl` names `c` for that
field. It is sound at a heap where the evidence holds (`ClassOk`; proved:
`Post.mono`).

**Closed footprints** mention only the classes and `all`. On `class(value)`,
`grow` is `keep`, so a closed footprint is a change for `class(value)` (`keep`
or `any`) and one for `class(store)` (`keep`, `grow` or `any`): six in all,
`Closed`. Their entrywise order is exactly the semantic order (proved:
`closed_order_exact`, with a one-location heap witnessing each failure).
Rewriting `grow` to `keep` in a footprint that is not closed needs class
evidence for the region at the heap the footprint is read at.

**Call effects.** A call signature's effect (`CallEffects.Effect`) is a
closed footprint and an optional promise, a type guard's or an assertion
function's; its postcondition is the footprint's, `Closed.Holds`, which
reads no slot (proved: `Closed.post_iff`). The empty closed footprint is
heap preservation and `all: any` is growth (proved: `Closed.holds_empty`,
`Closed.holds_top`), which every safe run meets (proved: `Closed.top_safe`).
One signature covers another at a footprint within its own and the same
promise (`Effect.covers`, proved: `Effect.covers_sound`); two signatures of
one call meet at the meet of their footprints (proved: `Closed.holds_meet`);
binding keeps the footprint (`Effect.drop`). The wire spells a closed
footprint `{"value": v, "store": s}`, `v` one of `keep` and `any`
([source claims](SOURCE-CLAIMS.md#quantified-callables-and-their-eliminations),
[request protocol](REQUEST-PROTOCOL.md#request-fields)).

## Facts

A **fact kind** has a meaning at a heap and a **support**: the regions it
reads, each with the largest change it tolerates. Its **support lemma**:

```math
\mathsf{Holds}_F(\rho,h) \land \bigl(\forall (r,\delta) \in S_F.\ \forall l \in [\![r]\!]_{\rho,h}.\ \delta_{|h|}(h[l],h'[l])\bigr) \implies \mathsf{Holds}_F(\rho,h')
```

(`Supported`; proved for every kind below: `FactKind.support_sound`.)
Locations outside the support may change arbitrarily. Separation by class
needs, besides, a **class theorem** for the support entry it uses.

| Fact | Meaning | Support | Class theorem |
| --- | --- | --- | --- |
| `value(x, atoms)` | `ρ x` meets a primitive predicate | none | – |
| `alias(x, y)`, `distinct(x,k, y,k')` | slot equality; two fields at different locations | none | – |
| `cell(x, k, atoms)` (`HeapFacts.Fact`) | `h[field(x,k)]` meets `atoms`, an absent key reading `undefined` | `field(x,k): keep` | `class(value)` from a source-valued contract of the field (proved: `classOk_of_contracts`); the atoms alone give none, since `nonNull` holds of a store (`nonNull_admits_store`) |
| `read(x, k, y)` (`HeapLinks.Link`) | `h[field(x,k)] = ρ y` | `field(x,k): keep` | as for `cell` |
| `dense(x, n)` (`Dense`) | `h[store(x)] = .arr ls` with $`D_n\,ls`$ | `store(x): grow` | `class(store)` by its meaning (proved: `dense_class`, `dense_classOk`) |

The density fact depends on its store's location alone (proved:
`dense_support`; a change no footprint keeping the store within `grow`
states leaves it holding: `dense_survives_outside_support`). Its footprint
form is `dense_stable`. Typing judgments stay outside the framed knowledge:
contracts are invariant.

## Provenance

Freshness is stated against **marks**: a valuation $`\mu`$ of mark indices by
ghost heap lengths, monotone, with mark 0 the length of the invocation's
entry heap and every mark at most the current heap's length (`MarksOk`).
Mark 0 is fixed for the invocation; the valuation is existentially
quantified at each point. Each slot carries at most two **stamps**
(`Stamps`, `StampsHold`):

- `after(x) = m`: every own location of `x` is at least $`\mu_m`$;
- `before(y) = m`: every **typed field** location of `y` is below $`\mu_m`$.

A slot's **typed fields** are the keys every alternative of its type gives
as an invariant field or as a readonly view other than `length`, whichever
each alternative uses (`typedFields`, `typedOperand`): a writable array's
store, a readonly array's and a union's of the two. Each has a world
contract (proved: `typedOperand_contract`, `typedField_contract`; a view by
`viewT`), and a location with a world contract lies below the heap's length
(proved: `typed_below`), so at a new mark equal to the heap's length every
slot's typed fields lie below it (proved: `before_typedFields`). A
source-typed value may name any location (`source_names_any_location`), so
hidden fields and every location of a value typed only `unknown` get no
`before`.

`after(x)` comes from allocation: `makeAt`, which allocates closures too,
places fields at the heap's length and beyond (proved: `alloc_after`), and a
new last mark at that length keeps the valuation sound (proved:
`MarksOk.push`). An array literal's element locations are fresh as well
(proved: `arrLit_fresh`). A native's fresh result is the other source
(audited: native footprints, "Fresh results"). Entry slots, captures among
them, get `before(·) = 0`; a slot a heap read defines gets no stamp. Stamps
never cross an invocation: a callee's operands start old, and a caller gets
`after(result)` only from a fresh-result guarantee, at a new mark equal to the
heap's length at the call.

**Separation by stamps** covers the regions they bound: with
`before(y) ≤ after(x)`, `field(x,k)` and `own(x)` are apart from every typed
field of `y` (proved: `stamps_separate`). A fresh store may list old element
locations, so `elems(x)` is apart from nothing by `after(x)`
(`elems_separation_false`, `stamps_separate_excludes_elems`).

**Edges rename marks** by a sorted map `σ` from target marks to source
marks with `σ(0) = 0`; the target valuation is $`\mu \circ \sigma`$ (proved:
`MarksOk.rename`). A target `after(j) = m'` needs a source
`after(slot j) = m` with `σ(m') ≤ m`, and a target `before(j) = m'` a source
`before(slot j) = m` with `m ≤ σ(m')` and the target's typed keys among the
source's (`stampEdgeOk`; proved: `stamps_transport`). Merging two marks that
bound the two sides of a separation is refused, as each such merge is false
(`merged_marks_unsound`), and so are a reordering and a moved mark 0. Each
incoming edge of a join supplies its own witness valuation, so a join may
state the least `after` and greatest `before` every edge justifies. One
`after` and one `before` per slot keep knowledge linear in slots and marks.
A mark created in a loop body is rebound on every iteration.

## The stability check

Separation $`K \vdash r \mathbin{\#} s`$ (`SepKnowledge.apart`) holds by:

1. **class**: `class(c)` against a field whose class evidence states
   `c' ≠ c`;
2. **provenance**: stamps, as above;
3. **link**: a distinct pair of fields.

A slot without provenance is apart from nothing (proved: `Sep.sound`). The
**stability check** of a fact under a footprint:

```math
\mathsf{stable}_K(F, \Phi) \iff \forall (r,\delta_F) \in S_F.\ \forall (s,\delta) \in \Phi.\ \delta \sqsubseteq \delta_F \lor K \vdash r \mathbin{\#} s
```

gives the fact's support premise from the footprint's postcondition (proved:
`stable_sound`), and the **frame** keeps exactly the facts that pass it
(proved: `frame_sound`). The check runs after every graph node against its
footprint, at every call against the callee's footprint at the call's
operands, at a native's callback boundary against the native's rely, and on
every edge, where the transported knowledge is justified as
`HeapKnowledge.check` justifies it.

**Classes from contracts**, at a step index where `HeapOk` constrains
contents:

- a location whose contract admits only source values holds no store, and
  one whose contract admits only stores holds one, at `HeapOk (n+1)` (proved:
  `contract_class`, `contract_store`); the same holds at the invocation's
  entry heap for a location it has, when the current world extends the
  truncated entry world (proved: `contract_class_entry`);
- the element locations of an array whose element contract admits only
  source values hold no store, at `HeapOk (n+2)`: the store's contract
  relates each element's contract to its family one level down (proved:
  `elems_class`; at level 1 the relation is vacuous,
  `elems_class_needs_two_levels`).

The one consumer of `elems_class` is transport at a node's start, state
`.at p` at step index `m`; its obligations, the node's return postcondition
at `m − 1` and the next point's invariant, are vacuous unless `m ≥ 2`
(conjectured; the graph lemma states it).

**Footprints of the actions.** Lean computes each action's footprint from
its term and evidence; regions are rooted at the node's slots. Each
operation keeps its evidence and its gains; the footprint frames the rest.

| Action | Footprint | Facts gained by the operation's rule |
| --- | --- | --- |
| read, test, arithmetic | $`\emptyset`$ | the read's `read` and `cell` facts |
| allocation (`makeAt`, `arrLit`, closure creation) | $`\emptyset`$ | `after(result)` at a new mark; `before(y)` where it improves |
| field write `writeAt k x v` | `field(x,k): any` | `cell(x',k,·)` for every alias `x'` of `x` |
| element write at a present index | `elems(x): any`, closed to `class(value): any` by `elems_class` | – |
| element write at a hole or the end | the above, and `store(x): grow` | – |
| call at a signature with footprint $`\Phi`$ | $`\Phi`$ at the call's slots | `after(result)` for a fresh result |
| exceptional edge of a call, `%Await%` | `all: any` | – |

A write to a field with a source-valued contract is within
`class(value): any` (`contract_class`); so a write to a captured cell closes
to a closed footprint.

## Composition

A **step footprint** is read at the heap its action starts in; an **entry
footprint**, describing an invocation so far, at the invocation's entry heap
`h₀`. Entry footprints use **entry-stable** regions: timeless regions rooted
at the point's slots, the classes read at `h₀`, and `all`. A heap-dependent
region does not compose by union: with `Φ = {store(x): any, elems(x): any}`,
$`\mathsf{Post}_\Phi`$ holds from `[arr [1], 0, 0]` to `[arr [2], 0, 0]` and
from there to `[arr [2], 0, 1]`, and fails across both
(`union_composition_false`).

**Transport** $`\alpha`$ (`transport`) maps a step region at the current heap
`h` to entry regions at `h₀`, given the slots whose own locations are at
least `|h₀|` (`FreshOk`) and the slots whose listed elements hold no store at
`h` (`ElemsValueOk`, from `elems_class`):

| Step region | Transport | Why |
| --- | --- | --- |
| timeless, rooted at a slot with `after(x) = m` | nothing | its locations are at least $`\mu_m \ge \mu_0 = |h_0|`$ |
| timeless, otherwise | itself | its denotation is heap-independent |
| `class(c)` | `class(c)` | only `any` changes a location's class |
| `elems(x)` with `elems_class` | `class(value)` | by `elems_class` at `h`, then as `class(value)` |
| `elems(x)`, otherwise | `all` | – |

Every location of `h₀` in a step region is in its transport at `h₀`, unless
the entry footprint already lets it change arbitrarily (proved:
`transport_sound`). **Composition**, with the inclusion justified by class
evidence valid at the entry heap:

```math
\mathsf{Post}_{\Phi_p}(\rho)(h_0,h) \land \mathsf{Post}_{\Phi_n}(\rho)(h,h') \land \Phi_p \mathbin{+\!\!+} \alpha(\Phi_n) \sqsubseteq_{cl} \Phi_q \land \mathsf{ClassOk}(cl, \rho, h_0) \implies \mathsf{Post}_{\Phi_q}(\rho)(h_0,h')
```

(proved: `Post.compose`). Evidence valid only at `h` does not suffice: a field
holding a store at `h₀` and a value at `h` admits evidence true at `h` under
which the composition fails (`current_heap_compose_false`), and applied to
that witness `Post.compose` shows no evidence valid at `h₀` justifies the
inclusion (`compose_needs_entry_evidence`). The entry-valid evidence comes
from contracts by `contract_class_entry`.

**Graphs.** Each point `p` of an invocation carries an entry footprint
$`\Phi_p`$ over its slots, $`\emptyset`$ at entry, meaning
$`\mathsf{Post}_{\Phi_p}(h_0, h)`$. A node with step footprint $`\Phi_n`$ and
successor `q` checks $`\Phi_p \mathbin{+\!\!+} \alpha(\Phi_n) \sqsubseteq_{cl} m^{*}\Phi_q`$
and that the knowledge at `q` is justified by the node's gains and the frame
of the knowledge at `p`. Lean computes $`\Phi_n`$ and $`\alpha`$; the
producer proposes $`\Phi_q`$, the marks and the mark map. Every edge, back
edges included, makes these checks; a loop head's $`\Phi`$ is a
producer-proposed invariant in a finite lattice. A cell allocated in the
invocation keeps its `after` through every iteration, so writes to it stay
out of $`\Phi`$. A slot an edge drops has its entries replaced by their class
containment at `h₀`, or by `all`. A return point checks
$`\Phi_{ret} \sqsubseteq \Phi_{decl}`$, the row's footprint at the entry
slots. A call's exceptional edge carries `all: any`, which reaches a normal
return only along paths from the handler to one; a node that cannot call
carries its own footprint on its exceptional edge. The graph state invariant
generalises `PreservingState`:

```
FootprintState h₀ n h : State → Prop
  | .at p .. | .done _   => Post Φ_p (h₀, h)
  | .eval t _ _ handler  => ReturnsPost (fun h' _ => Post (Φ_p ⊔ α Φ_node) (h₀, h')) n h t
                              ∧ handler's Φ ⊒ Φ_p ⊔ all:any
  | .raised _            => True
```

Its preservation step is `preserving_step` with `IsPrefix.trans` replaced by
`Post.compose` (conjectured).

**Calls and code entries.** A call instantiates its signature's footprint at
its slots (`receiver`, `arg i`, `self`). Binding keeps an entry only when it
mentions no saved operand, shifting the remaining argument positions; an entry
rooted at a saved operand becomes its closed coarsening. An intersection of
signatures keeps their footprints as a conjunction. A code entry's row states
a footprint over `receiver`, `arg i`, `self` and `cap i`; its arrow type
closes the `cap i` entries by their class containments, else to `all`.

## Natives

Each native's footprint is a footprint of this vocabulary. The footprints,
fresh results, state and sharing of every native the examples use are the
rows of [native footprints](SOURCE-CONTRACTS.md#native-footprints), with their
Node controls in `tests/node-runs.mts`. What the design proves of them:

- **Array mutators**, modelled by their specification steps on the store's
  list of element locations (`Arr`: `Set` of an index, `Delete`, a length
  change, in the order [ECMA-262](REFERENCES.md#ecma-262) gives them).
  `push`, `unshift` (with its final length step), a longer length, and `sort`
  over the whole call change the store by `grow` (proved: `Arr.push_grow`,
  `Arr.unshift_grow`, `Arr.setLength_grow`, `sort_grow` from `sort_dense` and
  `itemCount_ge`, given a comparator that keeps the store's locations among
  the entry's and fresh ones). `pop`, `shift`, `reverse` with a trailing hole
  and a shorter length do not (controls). A store change by `grow`, with
  element contents the only other old locations changed, meets the footprint
  `store(x): grow, class(value): any` (proved: `array_native_post`; for `any`,
  `array_native_post_any`). That a mutator changes nothing else is audited
  (native footprints, "Audited").
- **Relies.** A native that calls a callback may rely on a fact holding at
  every observation between callbacks. A fact holds across a sequence of
  steps each of whose footprints the stability check accepts (proved:
  `rely_chain`). For `map`, density below the captured length holds at every
  presence test when every step's footprint passes the closed check of its
  bound (proved: `map_rely`), and that check is the stability check with the
  class density gives its store (proved: `denseCheck_stable`). A
  postcondition on each callback's normal return therefore suffices: a
  reentrant call is part of the callback, a throw leaves `map`, and an async
  callback's continuation runs at a later `%Await%`, never inside the
  synchronous `map`. That `map` observes presence only between callbacks is
  audited.

**Footprint binders.** A native's callback parameter and own result are
stated at a binder `ε` over the six closed footprints; the declaration reader
expands it into one signature per footprint, exact quantification over a
finite domain. `bound(R)` holds the closed footprints the stability check
accepts for a rely `R` (proved for density: `stableDenseClosed_sound`, the
four footprints whose `class(store)` change is at most `grow`; outside it a
closed footprint lets a non-empty dense store become empty). Lean admits a
signature stating a relied result only at a footprint in its bound:

```
map: <U, ε ∈ bound(dense(receiver))>
       (callback: (value: T, index: number, array: readonly T[]) =>{ε} U) =>{ε} U[]   // receiver dense
map: <U, ε>
       (callback: (value: T, index: number, array: readonly T[]) =>{ε} U) =>{ε} U[] with holes
```

The binder states each callback member's own footprint as its callback's:
`forEach`, `every`, `some`, `filter` and `flatMap` with no rely, `find` and
`findIndex` relying on density to pass `T`.

**State and sharing.** A native object's state is its own locations in every
row the examples use: a Set's data and its `size` view, a regex's
`lastIndex`, an iterator's position. An iterator holds its collection through
an immutable hidden field and reads the collection's state at every step; its
step changes only its own position. A match iterator's state is its own
locations and its regex clone's, which needs a region over a hidden field.

**The rule users see** is a sufficient condition the checker checks:

> `xs.map(f)` has type `U[]` with no holes when `xs` has none and, as far as
> the checker can tell, `f` removes no index from an array it did not create
> itself: it calls no `pop`, `shift` or `reverse` on such an array, nor any
> function that may. `push`, `unshift`, `sort`, element writes, and writes to
> variables, object fields, sets, maps and regexes are allowed. An array
> reached through an object, such as `box.items`, is an array the callback did
> not create. Otherwise the checker gives the result a type that permits holes.

`push` followed by `pop` on the iterated array, `reverse` of an array that
stays dense, and a helper whose footprint the producer cannot narrow are safe
and refused. The diagnostic, an obligation diagnostic of kind
`callback-footprint`, names the native, the bound, the offending entry and the
source operation that contributed it:

```
error: xs.map(...) has a type that permits holes: its callback calls xs.pop() at 5:5,
which may remove an index of an array the callback did not create.
map's callback may not remove an index of such an array (pop, shift, reverse).
```

When the producer is bypassed, Lean's refusal is located at the graph node
whose footprint leaves the selected signature's bound.

## The acceptance theorem

The design adds no plan constructor and leaves `CertifiedPlan` as it is.
`SourceClaimJson.checkJson_safe` keeps its premise (the CLI success
condition) and its conclusion (safety of every accepted function), and states
that each unit whose declaration claims a footprint other than `all: any`,
run as its graph, returns with a heap its footprint relates to its entry heap
(proved: `SourceExtraction.checkRequests_footprint_at`). Such a claim, a
unit's or a code entry's, is established by heap preservation, which covers
every footprint (proved: `Closed.Holds.of_prefix`), and only for a plain
result; the graph lemmas of [composition](#composition) establish the others.
Footprints reach it through certified code entries
(`ProgramCertificates.CodesSound`, with a footprint version of
`codeChecked_sound`) and through trusted native contracts whose signatures
carry footprints (audited). Framed knowledge is consumed by the graph checker
whose soundness the theorem uses. The increment that changes the accepted path
reviews the theorem's premise and conclusion.

## The producer and Lean

The producer proposes, untrusted: each declaration's and closure's footprint,
by abstract interpretation over its body (footprints join, slots carry
stamps, loops and recursive declarations iterate from $`\emptyset`$ to a
fixpoint, calls consume the callee's footprint); each point's $`\Phi_p`$, marks
and mark maps; each call's selected signature, a native's binder instance the
least closed footprint covering the callback's; and the located
`callback-footprint` diagnostic.

Lean decides each node's step footprint, every edge's transported inclusion
and knowledge, marks and stamps, every frame, each exit against the row's
footprint, and each relied native signature against its rely, by the same
check.

Forged-claim controls, each through evidence production and consumption: a
captured or input cell claimed fresh; a `before` stamp claimed for an untyped
region; fresh storage confused with an old object read from it; a join or
back edge replacing a fresh slot by an old one; a mark map merging marks,
reordering them or moving mark 0; an escaped closure claimed to keep its
creator's freshness; an identity function claimed to return a fresh result; a
narrowed footprint on an unrestricted or structural native; a dropped
footprint entry; `elems` claimed entry-stable; mutation followed by a caught
throw that reaches a return; a wrong operand mapping at a call or a bind; and
a relied signature selected at a callback footprint outside its bound.

## The checker's existing mechanisms

| Mechanism | In the design | Why |
| --- | --- | --- |
| World contracts: `CtrAdm`, `ArrayPresence`, `StorePresence`, `CoversPresence`, `Implication`/`ImpliesOk`, `fieldAnswers`/`fieldSlice`, `persistentObservation`/`entryFacts` | kept, separate | Contracts are invariant; typing, promise establishment and refinement keep their rules. The class theorems read them. |
| `HeapFacts.Fact`, `Holds`, `check` | the `cell` fact kind | Its class comes from a field's contract. |
| `HeapLinks.Link` | one link type with an explicit kind (`alias`, `read`, `readOptional`, `distinct`), alias and distinct canonically ordered | Read links are the `read` fact kind. |
| `HeapLinks.alloc_frames`, `HeapKnowledge.alloc_frame(s)`, `HeapLinks.stable` | instances of `frame` | An allocation's footprint is $`\emptyset`$; `stable` is `frame` under `all: any`. |
| `HeapLinks.aliases`, `distinctFrom` | kept | Alias lookup gives a write's gains; separation goes through the check. |
| `HeapKnowledge.Knowledge`, `meet`, `check` | kept, with marks and stamps | – |
| `observeBoolean`, `observeTag`; `PromiseCalls.fieldYield` | kept | Refinement gains; a read link survives every action the check accepts. |
| `StepEvidence`, `checkStepResult` | kept | Operation evidence and its gains; their framing part is `frame(k, Φ_n)`. |
| `readFrame`, `read_frame`, `pure_frame`, the framing part of `pureOutput`; `ordinaryOutput`; `writeOutput`'s `distinctFrom` filter; `ControlFlow.handlerFacts`, `checkYields` | instances of `frame` | Under $`\emptyset`$, the call's footprint (`all: any` for `ordinaryOutput`), `{field(x,k): any}`, and the exceptional edge's or promise signature's footprint. |
| `allocOutput`'s product of distinct links, `Observations.distinctLinks`, `Bindings.mutableBinding`'s `apart` | stamps | `contractFields` is the typed fields' invariant part, with the same proof role (`typedField_contract`). |
| `Observations.checkpoint` | kept, with marks and $`\Phi_p`$ | – |
| `CallEffects.Effect` | a footprint and an optional promise | The heap effects are $`\emptyset`$ and `all: any`. |
| `Effect.post`, `PromiseWith`, `covers`, `call_safe`, `prefix_safe`, `pure_safe` | `Post`, footprint order, a footprint `call_safe` | – |
| `Purity.pureTerm`, `inspectTerm` and their runs | kept | A sufficient syntactic subset of the empty-footprint computations. |
| `ExpressionEffects.inspect_safe`, `selectedCallPreserves`; `GraphCode.NodePreserves`, `PreservingState`, `goto_preserving`, `compositionalCheckedResult`, `effectCheckedResult` | their footprint versions | The preserving versions are the instance at $`\emptyset`$. |
| `codeChecked_sound`, `SourceRequests.effect`, `effectResult` | kept, stating the row's footprint | – |
| The overlays' `effect` fields and preserving–unrestricted pairs | footprint rows and binders | `stateless` and `restoring` regex members share the footprint $`\emptyset`$ and keep their audits. |
| Producer `heap_preserving_*`, `declaration_footprint`, `infer`, `member_effects`, `retain_call_effects` | footprint inference | The same fixpoint over a larger lattice. |
| Producer `environment.widen_locals` | kept | It assigns and widens slots. |
| Producer `forget`, `execution.impact`, `loosen` | their heap-framing parts the producer's copy of `frame` | Proposals and checks agree. |
| `analysis_state` local holders; `SourceFacts` storage and growth | kept, separate | Shape analysis and lowering. |
| `ExpressionPlan.Effect` | the node's footprint | – |

## Seven example programs

Each runs a callback inside `xs.map(cb)`; the question is which `map`
signature the callback's footprint reaches. Under Node, programs 1 to 6
return dense arrays and program 7 a hole (the controls of
`tests/node-runs.mts` cover each operation). The decisions are conjectured
until the graph lemmas hold; programs 3 and 4 also rest on audited rows.

1. **A local counter**, `let n = 0; for (let i = 0; i < s.length; i++) n = n + 1;`
   in the callback. Lowering keeps `n` and `i` in slots (conjectured), so
   every node has the empty footprint and $`\Phi = \emptyset`$. Were they
   cells, each carries `after` and its writes transport to nothing. `map`
   applies at `ε = ∅`: verified.
2. **A fresh array**, `const a: number[] = []; a.push(x); a.push(x);`.
   `after(a)` from the allocation; each `push`, `store(a): grow`, transports
   to nothing: verified.
3. **A fresh regex**, `s.replace(/&/g, "&amp;")`. The literal's fresh result
   gives `after(re)`; the global `[Symbol.replace]`'s `own(re): any`
   transports to nothing: verified.
4. **A fresh set**, `const seen = new Set<string>(); for (const y of ys) seen.add(y); return seen.size;`.
   The set and the array iterator are fresh; `add` and each step change only
   their own state; `size` reads: verified.
5. **A helper**, the counter of program 1 in a declaration the callback calls.
   The declaration's footprint is $`\emptyset`$ and the call composes:
   verified.
6. **An outer cell**, `total = total + x` with `total` a cell of the
   enclosing function. The cell is old in the callback; its write,
   `field(cap total, value): any`, closes to `class(value): any` by its
   `number` contract. That footprint is in `bound(dense)`: `class(value)` is
   apart by class from the receiver's store. `map` applies at
   `ε = {class(value): any}`: verified. The enclosing function's own
   footprint is `class(value): any`, which relational regions would narrow
   to $`\emptyset`$.
7. **A shrink**, `xs.pop()` on the array being mapped. `store(xs): any` with
   `xs` captured and old closes to `class(store): any`, which fails the check
   for density. Only the signature with holes is in reach and the return
   needs `number[]`: refused, with the `callback-footprint` diagnostic at
   `xs.pop()`.

The same check admits an element write of the iterated array
(`class(value): any`) and a nested `map` whose callback pushes, and refuses
`push` then `pop`, `box.items.pop()` with `box` fresh (the array read from
`box.items` has no provenance), a nested `map` whose callback pops, and
`xs[5] = 6; xs.reverse()`.

## Increments

Each increment keeps `make test` and `make suite` green, adds its cases and
controls, and updates the documents that own its subject.

1. **Composition, class validity and provenance**: the lemmas of
   [composition](#composition), [the stability check](#the-stability-check)
   and [provenance](#provenance), with their controls.
2. **Native state and fresh results**: the
   [native footprints](SOURCE-CONTRACTS.md#native-footprints) rows, the array
   mutators' store relations and `map`'s rely, with Node controls.
3. **Closed footprints and the wire**: `CallEffects.Effect`'s heap part
   becomes a footprint, every proof consuming `Effect.post` is re-pointed
   through `Post.empty_iff` and `Post.all_iff`, and footprints go on the wire
   across TypeScript, OCaml and Lean, with identical outcomes.
4. **Definition summaries and relies**: `FootprintState` and its graph
   lemmas over `Post.compose`, with class evidence at the entry heap from
   `contract_class_entry` and transport's evidence at depth 2; producer
   footprint inference; binder expansion and relied native signatures; the
   seven programs as cases, with the forged-claim controls.
5. **Caller framing**: `frame` in place of `ordinaryOutput`, `writeOutput`'s
   filter, `handlerFacts` and `checkYields`; explicit link kinds; stamps in
   place of the distinct-link product.
6. **Relational regions**: `cap i` instantiated at calls of known closures,
   relies checked at the call site with the caller's separation, an
   entry-stable `elems₀` with its membership fact, the `freshElems` fact and
   its maintenance, `dense` as a point fact, and a region over a hidden field
   for the match iterator's state.

## Open questions

1. **Handlers.** A call's exceptional edge carries `all: any` along paths to
   a normal return; a throw postcondition on signatures would narrow it. None
   of the seven programs needs it.
2. **Relational callback footprints.** Closed footprints, with coarsening,
   express all seven programs and element writes through a callback's own
   operands. Footprints over operands substituted at the call need a
   Lean-native binder or call-site rely checks; how often a closed footprint
   refuses a safe callback is a census question.
