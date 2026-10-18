# Footprints: stable operations for the facts constructs rely on

A construct may rely on a heap fact across code it runs: `Array.prototype.map`
relies on the array it maps staying dense while its callback runs. The
mechanism has four parts:

1. **The fact** the construct relies on, with the locations it reads.
2. **The stable operations**: the operations proved to keep that fact,
   stated as the closed footprints within which they run.
3. **The checked contract**: Lean certifies that a callback, and every
   function it calls, runs within such a footprint, node by node.
4. **The construct's rule**: with the fact kept, the construct's simple rule,
   which ignores side effects, applies.

Each claim is labelled **proved** (with its Lean name), **audited** (with
its row in [native footprints](SOURCE-CONTRACTS.md#native-footprints)) or
**conjectured**. The lemmas are in `lean/Verification/Semantics/`
(`Footprints.lean`, `ClosedFootprints.lean`, `FootprintProvenance.lean`,
`FootprintStability.lean`, `FootprintNatives.lean`) and
`lean/Verification/Programs/` (`ExpressionEffects.lean`, `GraphCode.lean`);
their counterexample controls are in
`lean/Verification/Tests/FootprintControls.lean`, which also checks that every
theorem of the `Footprints` namespace rests on `propext`, `Classical.choice`
and `Quot.sound` alone. [WORK](../WORK.md#footprints) tracks the work.

## The fact

Type safety rests on storage contracts that never change: a write meeting a
location's contract breaks no typing judgment. A write or a call can break a
fact the checker relies on beyond the declared types. `Array.prototype.map`
reads the length `len` once, then for each `k < len` tests whether index `k`
is present and skips it when it is not, leaving a hole in its result
([ECMA-262](REFERENCES.md#ecma-262), `Array.prototype.map`). Its result is
dense when every index below `len` is present at each test.

The calculus heap is a list of values indexed by locations. An array object
holds its store under the key `[]`; the store location holds `.arr ls`, a
list of optional element locations whose length is the array's length. The
density fact `dense(x, n)` (`Dense`) says the store of `x` holds a list whose
first `n` indices are present:

```math
D_n\,ls \iff n \le |ls| \land \forall i < n.\ ls[i] \ne \mathsf{none}
```

It reads the store's location alone (proved: `dense_support`), and that
location holds a store (proved: `dense_class`).

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

`grow` keeps every dense prefix and lists no old element location the store
did not list. The changes form the chain
$`\mathsf{keep} \sqsubseteq \mathsf{grow} \sqsubseteq \mathsf{any}`$
(proved: `Change.Holds.refl`, `.mono`, `.trans`).

The locations below a heap's length fall into two classes by their contents:
`class(store)`, those holding a store, and `class(value)`, the others. A
**closed footprint** $`\Phi = \{\mathsf{value}{:}\,\delta_v,\ \mathsf{store}{:}\,\delta_s\}`$
(`Footprints.Closed`) states a change for each class, `keep` or `any` for
values (on a non-store, `grow` is `keep`) and `keep`, `grow` or `any` for
stores: six footprints. Its meaning relates the heap `h` a run starts in to a
later heap `h'`:

```math
\Phi.\mathrm{Holds}(h, h') \iff |h| \le |h'| \land \forall l < |h|.\ \delta_{\mathrm{class}(h[l])\,|h|}(h[l], h'[l])
```

(`Closed.Holds`, through `Closed.holds_iff`). Its extremes: the empty
footprint `{value: keep, store: keep}` is heap preservation and
`{value: any, store: any}` is growth (proved: `Closed.holds_empty`,
`Closed.holds_top`), which every safe run meets (proved: `Closed.top_safe`).
Runs compose: two runs within $`\Phi`$ are a run within $`\Phi`$ (proved:
`Closed.Holds.trans`). The entrywise order is exactly the semantic order
(proved: `closed_order_exact`, with a one-location heap witnessing each
failure; `Closed.Holds.mono`).

**Call effects.** A call or construct signature's effect
(`CallEffects.Effect`) is a closed footprint, an optional promise, a type
guard's or an assertion function's, and two Booleans: a fresh result, and the
receiver's store excepted ([fresh array storage](#fresh-array-storage)). A
signature promises that its normal return meets the footprint from the heap
the call starts in (`PromiseWith`, `ConstructPromise`). One signature covers another when its footprint is within
the other's and their promises are equal (`Effect.covers`, proved:
`Effect.covers_sound`); two signatures of one call meet at the meet of their
footprints (proved: `Closed.holds_meet`). The wire spells a closed footprint
`{"value": v, "store": s}`
([source claims](SOURCE-CLAIMS.md#quantified-callables-and-their-eliminations),
[request protocol](REQUEST-PROTOCOL.md#request-fields)).

## The stable set for density

Density reads only a store, and only a store change beyond `grow` can remove
a present index below `n`. The closed footprints that keep it are the four
whose store change is at most `grow` (`stableDenseClosed`; proved:
`stableDenseClosed_sound`; outside them a closed footprint lets a non-empty
dense store become empty, controls in `FootprintControls.lean`):

| Footprint | Keeps density |
| --- | --- |
| `{value: keep, store: keep}` | yes |
| `{value: any, store: keep}` | yes |
| `{value: keep, store: grow}` | yes |
| `{value: any, store: grow}` | yes |
| `{value: keep, store: any}` | no |
| `{value: any, store: any}` | no |

`map` relies on density between callbacks. For callbacks each of whose
normal returns meets a footprint of the stable set, density below the
captured length holds at every presence test (proved: `map_rely`, from
`rely_chain`; `denseCheck_stable` shows the set to be the general stability
check's instance for density, `stable_sound`). A reentrant call is part of
the callback, a throw leaves `map`, and an async callback's continuation runs
at a later `%Await%`, never inside the synchronous `map`. That `map` observes
presence only between callbacks is audited.

## The checked callback contract

A body is certified within a closed footprint $`\Phi`$ when every node of its
graph runs within $`\Phi`$, from the heap the node starts in, on the
locations below the heap the body started in; the runs compose by
`Closed.Holds.trans_on` into the body's (`GraphCode.BoundState`,
`goto_bounded`). Lean accepts a node (`compositionalChecked`,
`nodeWithin_of_checked`) when it is:

- an **inspection**: a read, test, arithmetic or allocation, an array
  literal's spread parts included, which read their stores' elements in
  place, which preserves the heap (`ExpressionEffects.check`,
  `Purity.inspectTerm`; proved: `inspect_safe`, from `inspect_step`);
- a **typed write** of a field whose contract, at the written object's type,
  admits only source values, within `{value: any, store: keep}`: the written
  location holds no store, by its contract (`writeWithin`; proved:
  `write_within`, from `sourceField_sound`). A variable's cell is such a
  field;
- an **element write** at a literal index, within `{value: any, store: grow}`,
  or `{value: any, store: keep}` at a required position
  ([element writes](#element-writes));
- a **selected call or construction** whose signature's footprint is within
  $`\Phi`$, its operands values (`selectedWithinAt`; proved:
  `ExpressionEffects.selected_sound`, through `CallEffects.call_safe` and
  `CallEffects.construct_safe`): a fixed call, a variadic call and a
  construction, each at the signature the evidence selects; a variadic
  call's spreads read their stores in the heap the call starts in
  (`spread_values_post`, `spread_head_post`). A signature excepting its
  receiver's store is within $`\Phi`$ where the receiver is a slot holding a
  fresh store, or $`\Phi`$ lets everything change
  (`Effect.within_below`).

A node with an exceptional handler is refused: a handler could turn a
throwing call into a normal return after mutation the bound does not track.
A function's guarantee comes only from its checked body: a declaration's
claimed footprint is checked against its graph (proved:
`SourceExtraction.checkRequests_footprint_at`), a closure's against its code
entry (`codeChecked_sound`), a class's construct signatures against its
constructor's code (`ctorGraph`). A callable value carries its footprint
through ordinary signature checking, substitution and application; an unknown
function states `{value: any, store: any}`.

The producer proposes each footprint, untrusted: a body's is the join of its
nodes' (`footprint_expr`, `footprint_stmts` in `ocaml-producer/source.ml`),
a variable write `{value: any, store: keep}`, a call or construction the join
of every signature its callee may take; declarations are proposed at the least
fixpoint from the empty footprint (`ocaml-producer/proposal.ml`). Lean decides
every node.

## Natives

Each native signature states its closed footprint; the rows, with what is
proved of each and what is audited, are
[native footprints](SOURCE-CONTRACTS.md#native-footprints). Within the
stable set are `push` and `unshift` (`{value: any, store: grow}`), a native
regex's members, the array iterator, `new Set` and `new Map`, and the
collections' and dates' mutators (each at most `{value: any, store: keep}`);
outside it are `pop`, `shift`, `reverse` and every native stated
unrestricted. `forEach`, `every`, `some`, `filter`, `find`, `findIndex` and
`flatMap` have one signature per closed footprint, each within its callback's.
`pop`, `shift` and `reverse` state `{value: any, store: keep}` with their
receiver's store excepted, so outside a fresh receiver they bound a call by
the footprint letting everything change; `filter`, `map`, `flatMap`,
`slice` and a string's `split` state a fresh result.
`map` has five signatures: one per footprint `ε` of the stable
set, which takes a dense receiver and a callback within `ε`, gives a dense
result and states `ε` as its own; and an unrestricted one, which takes any
receiver and any callback, gives a result that may hold holes and states no
footprint. So a callback changing stores beyond `grow`, such as one within
`{value: keep, store: any}`, or a sparse receiver gives a `map` call with no
footprint.

## Fresh array storage

A destructive operation on a store allocated after a run began changes no
store the run's entry heap held. `GraphCode` tracks, at each node, the slots
of the node's entry holding a value whose array store lies at or above the
entry heap's length (`FreshAt`, `FreshOk`). The fact reads no heap: an
object's fields are fixed at its allocation.

- **Facts along edges.** A destination's facts follow from the source's
  through the edge's slot map, and slot 0 of a binding continuation holds a
  fresh value where the node's value is fresh: a slot copy of a fresh slot,
  or a call at a selected signature stating a fresh result (`edgesFresh`,
  `varFresh`, `callFresh`; proved: `edgesFresh_sound`). The entry has none.
  Lean infers the facts (`inferFresh`, untrusted) and checks every edge; a
  join keeps a fact where every incoming edge establishes it, and a slot a
  write changes is a cell, which holds no fact.
- **Fresh-receiver calls.** A call at a signature excepting its receiver's
  store, at a receiver holding a fresh store, is within the signature's
  footprint on the locations below the entry heap's length
  (`Closed.HoldsOn.below_fresh`); runs compose with the body's by
  `Closed.Holds.trans_on`.
- **Fresh results.** Code claiming a fresh result is checked node by node,
  whatever its footprint, and each return returns a fresh value; its
  postcondition then states it (`effectChecked`, `codeChecked_sound`). A
  declaration states no fresh result.

`pop`, `shift` and `reverse` change only their receiver's store and element
contents, and `filter`, `map`, `flatMap`, `slice` and `split` allocate their
result's store (audited: [native footprints](SOURCE-CONTRACTS.md#native-footprints)).
Controls (`map-stable-fresh-store`'s negatives and `pipeline/test.mts`): an
alias of the mapped array, a join of a fresh and an old array, a reassigned
variable and a helper's parameter, each also at a result type admitting holes
(`map-fresh-controls-sparse`), where a callback forged within
`{value: any, store: keep}` is refused in search and in checking; a pop of the
mapped array before a throw its handler catches (`invalid-map-handler-after-pop`);
and a fresh result forged onto code returning its parameter. A fresh array
popped inside `try` is refused with every node a handler covers, though its
result is dense (`map-fresh-handler-refused`, a gap).

## Element writes

`a[b] = v`, at a literal index, lowers to one node: `setElem` on the store
`a` holds at its store field, then the write of the store it returns back to
that field. At an index the store lists, `setElem` writes `v` into the
element's location, which holds a source value by the position's contract,
a location of `class(value)`, and returns the store unchanged; at a hole or
past the end it allocates a fresh location, at or above the entry heap's
length, and returns the store with it listed there (`placeAt`). Either way
every old dense prefix stays and the store lists no old element location it
did not list (proved: `placeAt_dense`, `placeAt_mem`). Lean accepts the node
(`elemWriteWithin`; proved: `elem_write_core`, through `elem_present_holds`
and `elem_grow_holds`) where the object's slot type gives its store field a
tuple contract whose position at the index holds source values:

```math
\frac{\Gamma(o).\mathtt{[]} = \mathsf{list}(T)\qquad T_{b}\ \text{source-valued}}
     {o[b] = v\ \text{within}\ \{\mathsf{value}{:}\,\mathsf{any},\ \mathsf{store}{:}\,\mathsf{grow}\}}\ \textsf{elem-write}
\qquad
\frac{\Gamma(o).\mathtt{[]} = \mathsf{list}(T)\qquad b < |T.\mathsf{required}|\qquad T_{b}\ \text{source-valued}}
     {o[b] = v\ \text{within}\ \{\mathsf{value}{:}\,\mathsf{any},\ \mathsf{store}{:}\,\mathsf{keep}\}}\ \textsf{elem-write-present}
```

A required position is listed in every store its contract admits, so the
write there takes the present case. A length alone proves no presence,
since a hole may lie below it, and no other presence evidence is read. The
node raises nothing after its first step, so its footprint holds where it
raises too. A store write through any other operation (`length` assignment,
`delete` of an element) is outside the rule. The producer proposes
`{value: any, store: grow}` for an element write at a literal index and for
a compound or logical assignment of a variable `{value: any, store: keep}`
(`footprint_expr`). `map-stable-element-write` is the case; controls in
`pipeline/test.mts` certify `keep` claimed at a required position and refuse
it at an optional one.

## The rule users see

> `xs.map(f)` has type `U[]` with no holes when `xs` has none and `f`, with
> everything it calls, uses only operations that keep every array's dense
> prefixes: reads (optional chains included), tests, arithmetic, allocation
> (array literals with spreads included), writes to variables and to fields
> holding values, writes of array elements at literal indices, `push` and `unshift`, `for...of` and spreads over arrays,
> strings, sets, maps and regex matches, the readers and mutators of `Set`,
> `Map`, `Date` and regex literals, the array members taking callbacks
> (`map`, `filter`, `forEach`, `find`, ...) whose callbacks keep the same
> rule, calls of functions checked the same way, and `pop`, `shift` and
> `reverse` of an array whose storage the callback created, through `filter`,
> `map`, `flatMap`, `slice`, `split` or a function stating a fresh result,
> held in a constant. Other `pop`, `shift` and `reverse` calls, and calls of
> functions the checker cannot bound, are refused. Otherwise the checker
> gives the result a type that permits holes.

`pop` on an array literal the callback allocated, `push` followed by `pop`,
and a `pop` on an array unrelated to the mapped one are safe and refused: the
rule does not separate arrays beyond fresh storage
([deferred](#deferred-extra-precision)).

## The seven programs

Each runs a callback inside `xs.map(cb)` and returns the result at a type
without holes. Each is a pipeline case, with its Node run in
`tests/node-runs.mts`:

| Program | Case | Outcome | Why |
| --- | --- | --- | --- |
| 1. a local counter in a loop | `map-stable-local-counter` | verified | variable writes, `{value: any, store: keep}` |
| 2. a fresh array and `push` | `map-stable-push` | verified | `push`, `{value: any, store: grow}` |
| 3. a global regex replacement | `map-stable-regexp-replace` | verified | `[Symbol.replace]` through the dispatch, `{value: any, store: keep}` |
| 4. a fresh `Set` filled by `for...of` | `map-stable-set` | verified | `new Set`, the iterator's step and `add`, each within `{value: any, store: keep}` |
| 5. a helper counting in a loop | `map-stable-helper` | verified | the declaration's checked footprint, consumed at its call |
| 6. a captured outer counter | `map-stable-outer-cell` | verified | a cell holding a number, `{value: any, store: keep}` |
| 7. `xs.pop()` on the mapped array | `invalid-map-unstable-pop` | refused | `pop`, `{value: any, store: any}`: only the signature with holes applies, refused at the return contract |

Forged-claim controls run through evidence production and consumption
(`pipeline/test.mts`): a callback claimed within a footprint its body leaves,
a declaration claimed within one its loop leaves, a class's construct
signature claimed within one its constructor leaves, a dispatch claimed below
its member's footprint, and an exhausted check reported as exhausted.

## The acceptance theorem

`SourceClaimJson.checkJson_safe` keeps its premise (the CLI success
condition) and its conclusion (safety of every accepted function), and states
that each unit whose declaration claims a footprint other than
`{value: any, store: any}`, run as its graph, returns with a heap its
footprint relates to its entry heap and a value meeting its goal, a guard's
promise included (proved:
`SourceExtraction.checkRequests_footprint_at`). Footprints reach it through
certified code entries (`ProgramCertificates.CodesSound`, `codeChecked_sound`)
and through trusted native contracts (audited).

## Deferred: extra precision

The rule separates arrays only by fresh storage, so it refuses safe
callbacks that change another array beyond `grow`: `pop` on an array literal
the callback allocated, on an array a callback parameter names that is not
the mapped one, or `push` then `pop`. Admitting them needs
footprints over regions rooted at a call's operands (`own(x)`, `store(x)`,
`elems(x)`), effects relative to operands, allocation-sensitive summaries, composition of regional
footprints along a graph (transport to the entry heap), and framing of the
caller's knowledge by a call's footprint. The regional lemmas proved so far
are in `Footprints.lean` (`Post`, `Post.compose`, `transport_sound`) and
`FootprintStability.lean` (`stable_sound`, `frame_sound`). None of the seven
programs, nor the repository code measured, needs them; a retained program
refused for this reason is the trigger.

**Provenance stamps** (`FootprintProvenance.lean`: marks, `after` and
`before` stamps, `stamps_separate`) are the candidate replacement for the
distinct links the checker keeps between pairs of fields, which grow
quadratically with the fresh objects a body allocates. A version that
replaces them must keep the separation the pairwise links keep at two
points:

- a join intersects stamps by literal mark number, which loses separation
  pairwise links keep;
- a step treating a slot copy `.var i` as a shift only loses separation
  through copied slots.

The motivating program is one allocating many fresh objects, whose distinct
links grow quadratically.
