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
**conjectured**. The lemmas of `FootprintNatives.lean` (`Arr.push_grow`,
`Arr.unshift_grow`, `Arr.setLength_grow`, `sort_grow`, `array_native_post`,
`map_rely`, `denseCheck_stable`, `elems_rely`) are proved in a model of the
natives' specification steps and read by no acceptance theorem; the native
footprints they argue for are trusted input. The lemmas are in `lean/Verification/Semantics/`
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
parameterised by the length `b` of the heap it starts from. With
$`\mathrm{init}(v,v')`$ an initialization, $`v`$ `null` or `undefined` and
$`v'`$ no store, and $`\mathrm{scalar}(v,v')`$ a scalar's step, $`v`$ neither
an object nor a store and $`v'`$ no store:

```math
\begin{aligned}
\mathsf{keep}_b(v, v') &\iff v' = v\\
\mathsf{init}_b(v, v') &\iff v' = v \lor \mathrm{init}(v, v')\\
\mathsf{scalar}_b(v, v') &\iff v' = v \lor \mathrm{scalar}(v, v')\\
\mathsf{grow}_b(v, v') &\iff v' = v \lor \bigl(v = \mathsf{arr}\,ls \land v' = \mathsf{arr}\,ls' \land (\forall n.\ D_n\,ls \to D_n\,ls') \land \forall l.\ \mathsf{some}\,l \in ls' \to \mathsf{some}\,l \in ls \lor b \le l\bigr) \lor \mathrm{scalar}(v, v')\\
\mathsf{any}_b(v, v') &\iff \top
\end{aligned}
```

`init` lets a location holding `null` or `undefined` take a value, the change
of a lazy initialization `x ??= e`; `scalar` lets a location holding neither an
object nor a store take a value, the change of a `Map`'s `set` to its `size`;
`grow` keeps every dense prefix and lists no old element location the store
did not list, or takes a scalar's step. The changes form the chain
$`\mathsf{keep} \sqsubseteq \mathsf{init} \sqsubseteq \mathsf{scalar} \sqsubseteq \mathsf{grow} \sqsubseteq \mathsf{any}`$
(proved: `Change.Holds.refl`, `.mono`, `.trans`). A change other than `any`
keeps an object, `keep` and `init` keep contents neither `null` nor
`undefined`, and on a store `init` and `scalar` are `keep` (proved:
`Change.Holds.object_kept`, `.defined_kept`, `.init_store`, `.scalar_store`).

The locations below a heap's length fall into two classes by their contents:
`class(store)`, those holding a store, and `class(value)`, the others. A
**closed footprint** $`\Phi = \{\mathsf{value}{:}\,\delta_v,\ \mathsf{store}{:}\,\delta_s\}`$
(`Footprints.Closed`) states a change for each class, `keep`, `init`,
`scalar` or `any` for values (on a non-store, `grow` is `scalar`) and `keep`,
`grow` or `any` for stores (on a store, `init` and `scalar` are `keep`): twelve
footprints. Its meaning relates the
heap `h` a run starts in to a later heap `h'`:

```math
\Phi.\mathrm{Holds}(h, h') \iff |h| \le |h'| \land \forall l < |h|.\ \delta_{\mathrm{class}(h[l])\,|h|}(h[l], h'[l])
```

(`Closed.Holds`, through `Closed.holds_iff`). Its extremes: the empty
footprint `{value: keep, store: keep}` is heap preservation and
`{value: any, store: any}` is growth (proved: `Closed.holds_empty`,
`Closed.holds_top`), which every safe run meets (proved: `Closed.top_safe`). The entrywise order is exactly the semantic order
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
a present index below `n`. The closed footprints that keep it are the eight
whose store change is at most `grow` (`stableDenseClosed`; proved:
`stableDenseClosed_sound`; outside them a closed footprint lets a non-empty
dense store become empty, controls in `FootprintControls.lean`):

| Footprint | Keeps density |
| --- | --- |
| `{value: keep, store: keep}` | yes |
| `{value: init, store: keep}` | yes |
| `{value: scalar, store: keep}` | yes |
| `{value: any, store: keep}` | yes |
| `{value: keep, store: grow}` | yes |
| `{value: init, store: grow}` | yes |
| `{value: scalar, store: grow}` | yes |
| `{value: any, store: grow}` | yes |
| `{value: keep, store: any}` | no |
| `{value: init, store: any}` | no |
| `{value: scalar, store: any}` | no |
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

A body is certified within a closed footprint $`\Phi`$ when every node outside
a checked region with no normal exit runs within $`\Phi`$, from the heap the node starts in, on the
locations below the heap the body started in; the runs compose by
`Closed.Holds.trans_on` into the body's (`GraphCode.BoundState`,
`goto_bounded`). Lean accepts a node (`compositionalChecked`,
`nodeWithin_of_checked`) when it is:

- an **inspection**: a read, test, arithmetic or allocation, an array
  literal's spread parts included, which read their stores' elements in
  place (an operand that is one of several arrays reads the store of the
  one its slot holds, the read derived at each alternative by `unionVar`:
  `arrayStoreAt`), a merge, which reads its operands' own properties and steps to
  the allocation of their copy, and a key's record (`makeKey`), which converts
  a primitive key and steps to the allocation of a record of the key, each
  preserving the heap (`ExpressionEffects.check`, `Purity.inspectTerm`;
  proved: `inspect_safe`, from `inspect_step`, whose merge case is
  `mergeParts_vals`: every copied value is a value). A write at a string key
  of a module binding holding a record lowers to these and the binding's
  cell write, within `{value: any, store: keep}`
  (`module-dictionary-keeps-lengths`);
- a **typed write** of a field whose contract, at the written object's type,
  admits only source values, within `{value: any, store: keep}`: the written
  location holds no store, by its contract (`writeWithin`; proved:
  `write_within`, from `sourceField_sound`). A variable's cell is such a
  field, and so is a named field an assignment or a logical assignment
  writes (`field-write-refinement`);
- an **element write** at a literal index, within `{value: any, store: grow}`,
  or `{value: any, store: keep}` at a required position
  ([element writes](#element-writes));
- a **selected call or construction** whose signature's footprint is within
  $`\Phi`$, its operands values (`selectedWithinAt`; proved:
  `ExpressionEffects.selected_sound`, through `CallEffects.call_safe` and
  `CallEffects.construct_safe_exc`): a fixed call, a variadic call and a
  construction, each at the signature the evidence selects; a variadic
  call's spreads read their stores in the heap the call starts in
  (`spread_values_post`, `spread_head_post`). A signature excepting its
  receiver's store is within $`\Phi`$ where the receiver is a slot holding a
  fresh store, or $`\Phi`$ lets everything change
  (`Effect.within_below`);
- a node **without a normal return**: its term, by the node's own checked
  ordinary typing, has a type no value meets, so its run is within every
  $`\Phi`$ on normal return (rule below).

```math
\frac{\Gamma_l\vdash t_l:B\ \text{(the node's checked ordinary typing)}\qquad \mathrm{expand}_G(B)=\varnothing}
     {\text{node } l \text{ within } \Phi \text{ on normal return}}\ \textsf{no-return}
```

$`B`$ is the result type of the node's evidence, at which its ordinary
safety holds, after instantiation; its emptiness is the decision that makes
a slot of a type no value meets an unreachable entry: a type of clause rows
expanding to no clause (`ExpressionEffects.emptyType`; proved:
`emptyType_sound`, and `noReturn_sound`, by `of_value_property` from the
node's safety, every normal postcondition holding vacuously). `never` and a
generic call instantiated at `never` are empty; `Promise<never>` and a
guard's `boolean` are not.

For a normal-return guarantee, a checked region $`D`$ may contain nodes whose
paths cannot return normally. Every node in $`D`$ has either an empty result
type by the rule above, or a non-return continuation whose destinations all
lie in $`D`$; every exceptional handler of a node in $`D`$ also lies in $`D`$.
The region may contain cycles. Its nodes retain ordinary safety and may
change the heap without satisfying $`\Phi`$. A handler outside $`D`$ requires
the throwing node to meet the footprint on its throw too. A body claiming
`onThrow` uses an empty $`D`$.

Proved: `GraphCode.bounded_step` preserves the bound outside $`D`$ and the
absence of a normal exit inside it; `goto_bounded` gives the body's footprint.
The checker computes a candidate region (`inferDead`) and checks each member's
normal and exceptional exits (`deadNode`), so stopping the computation early
cannot admit an unchecked exit. The region is derived from the graph and its
ordinary certificate and adds no claim field. A rethrowing handler can belong
to $`D`$; an outer handler or finalizer returning normally keeps any path to
that return outside $`D`$.

A node whose exceptional handler lies outside $`D`$ is within the bound on a
throw as well: its throw is an inspection, a typed write, or a call whose
signature bounds its throws (`onThrow`), and the handler's facts follow from
the node's, the thrown value never fresh (proved:
`GraphCode.throwsWithin_sound`, `handlerFresh_sound`).
A signature stating `onThrow` bounds the throws leaving the invocation too
([effect-qualified contracts](SEMANTICS.md#effect-qualified-call-contracts)).
A function's guarantee comes only from its checked body: a declaration's
claimed footprint is checked against its graph (proved:
`SourceExtraction.checkRequests_footprint_at`), a closure's against its code
entry (`codeChecked_sound`), a class's construct signatures against its
constructor's code (`ctorGraph`); a [statement](SOURCE-ELABORATION.md#stated-effects)
in a definition's annotation is certified from its code at the definition. A callable value carries its footprint
through ordinary signature checking, substitution and application; an unknown
function states `{value: any, store: any}`.

An async definition's footprint is `{value: any, store: any}`. An async
call returns a promise where its body throws, so a footprint its body meets
on normal return bounds no run of the call; the model reads the body's
throw as a throw ([async functions](SOURCE-CONTRACTS.md#async-functions-and-await)).
The Fragment states every callable definition's completion kind, `sync` or
`async`, from its own `async` modifier (`completion`,
[FRAGMENT-FORMAT](FRAGMENT-FORMAT.md)); Lean refuses an async declaration
unit, async graph code and a qualified read of an async unit claiming any
other footprint, before any certification is tried (`RequestJson.asyncEffects`;
proved: `SourceExtraction.checkRequests_async`):

```math
\frac{\mathrm{completion}(d)=\mathsf{async}\qquad \mathrm{claim}(d)=\Phi}
     {\Phi=\{\mathsf{value}{:}\,\mathsf{any},\ \mathsf{store}{:}\,\mathsf{any}\}}\ \textsf{async-effect}
```

The producer proposes each footprint, untrusted: a body's is the join of its
nodes' (`footprint_expr`, `footprint_stmts` in `ocaml-producer/source.ml`),
a variable write `{value: any, store: keep}`, the empty footprint in a
declaration's body where the variable is a local its activation holds in a
slot, which no location holds (a parameter or a binding of the body, no cell
of it, `cellLocals`, and no name the module declares; `Source.slot_local`),
and a field write `{value: any, store: keep}` where its
object's claim gives every alternative the field as a required writable one
holding source values (`Type_queries.source_field_write`, as Lean's typed
write reads it), a call or construction the join
of every signature its callee may take, a call its own typing claims at
`never` the empty footprint, a `throw` in a closure not proposed on a throw
the empty footprint, outside a `try` whose handler may return normally (the
throw and its operand's nodes lie in the checked region with no normal
exit; `map-throw-operand-footprint`, `invalid-map-throw-operand-caught`),
an async definition none, and a method call,
in a function's or a closure's body, on an object whose claim has several
alternatives once each declaration it names is unfolded, with actuals that
are names or literals none: the lowering may read and invoke its member in one
node dispatched on the object (`Lowering.dispatchesCall`), which no bounded node rule above admits.
A method call on a union of arrays none of which owns the member, the member
claimed at one type, is not dispatched (each alternative reads it from the
array prototype), nor is one on a union of hosts each holding the member as a
method, generic (a scheme whose signatures take the declaration as receiver,
as `forEachChild`) or not (`unionMemberHosts`); each is proposed as a call; declarations are proposed at the least
fixpoint from the empty footprint (`ocaml-producer/proposal.ml`). Lean decides
every node.

## Natives

Each native signature states its closed footprint; the rows, with what is
proved of each and what is audited, are
[native footprints](SOURCE-CONTRACTS.md#native-footprints). Within the
stable set are `push` and `unshift` (`{value: any, store: grow}`), `sort`
at a comparator within one of its footprints (`{value: any, store: grow}`,
`sort_grow`), a native
regex's members, the array iterator, `new Set` and `new Map`, and the
collections' and dates' mutators (each at most `{value: any, store: keep}`,
the mutators `{value: scalar, store: keep}`);
outside it are `pop`, `shift`, `reverse`, `splice` and every native stated
unrestricted. `forEach`, `every`, `some`, `filter`, `find`, `findIndex`,
`flatMap`, `reduce` and `reduceRight` have one signature per closed
footprint stating `keep` or `any` for values, each within its callback's; a
callback within `{value: init, …}` or `{value: scalar, …}` takes the one
stating `any`.
`pop`, `shift`, `reverse` and `splice` state `{value: any, store: keep}` with their
receiver's store excepted, so outside a fresh receiver they bound a call by
the footprint letting everything change; `filter`, `map`, `flatMap`, `flat`,
`slice`, `splice` and a string's `split` state a fresh result.
`map` has five signatures: one per footprint `ε` of the stable
set stating `keep` or `any` for values, which takes a dense receiver and a callback within `ε`, gives a dense
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

`pop`, `shift`, `reverse` and `splice` change only their receiver's store and element
contents, and `filter`, `map`, `flatMap`, `flat`, `slice`, `splice` and `split` allocate their
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

`a[b] = v`, at a literal index, lowers to one node whose operands are slots:
`setElem` on the store the object in slot `a` holds at its store field, at
the number `b`, of the value in slot `v`, then the write of the store it
returns back to that field. The operands' own evaluation is earlier nodes,
each checked within the footprint on its own. `setElem` steps only at an
array index, a number `indexOfBits` reads as one: a finite integer from 0 to
$`2^{32}-2`$, `-0` included as 0, as ECMAScript's array indices are. At an
index the store lists, it writes `v` into the element's location, which
holds a source value by the position's contract, a location of
`class(value)`, and returns the store unchanged; at a hole or past the end
it allocates a fresh location, at or above the entry heap's length, and
returns the store with it listed there (`placeAt`). Either way every old
dense prefix stays and the store lists no old element location it did not
list (proved: `placeAt_dense`, `placeAt_mem`).

Lean accepts the node (`elemWriteWithin`) where the object's slot type gives
its store field a tuple contract whose position at the index holds source
values:

```math
\frac{\Gamma(o).\mathtt{[]} = \mathsf{list}(T)\qquad T_{b}\ \text{source-valued}}
     {o[b] = v\ \text{within}\ \{\mathsf{value}{:}\,\mathsf{any},\ \mathsf{store}{:}\,\mathsf{grow}\}}\ \textsf{elem-write}
\qquad
\frac{\Gamma(o).\mathtt{[]} = \mathsf{list}(T)\qquad b < |T.\mathsf{required}|\qquad T_{b}\ \text{source-valued}}
     {o[b] = v\ \text{within}\ \{\mathsf{value}{:}\,\mathsf{any},\ \mathsf{store}{:}\,\mathsf{keep}\}}\ \textsf{elem-write-present}
```

The theorem (`elem_write_core`, through `elem_present_holds` and
`elem_grow_holds`) assumes the node's ordinary safety, `Safe` of its term at
the node's type from an environment meeting its slot types and a heap
meeting its world, and concludes the footprint of every heap the node
returns in, and, in the calculus, of every heap it raises in: once its first
step has read the store, no step of the term raises. A required position is
listed in every store its contract admits, so the write there takes the
present case. A length alone proves no presence, since a hole may lie below
it, and no other presence evidence is read. A store write through any other
operation (`length` assignment, `delete` of an element) is outside the
rule.

**Writable arrays.** The calculus's `setElem` always succeeds at an array
index, where JavaScript's assignment to a frozen, sealed or non-extensible
array throws in strict code: the rule rests on the host assumption that
every array the program writes is writable and extensible
([ordinary array construction](SOURCE-MODEL.md#exact-contracts-and-native-effects)).

A write at a key the program computes, its index a slot
([writes at a checked index](PROGRAM-TYPING.md#writes-at-a-checked-index)),
is within the same `grow` footprint where every position of the store's
contract holds source values, a tuple of no required or optional position
whose rest does (`elemVarWriteWithin`, proved: `elem_var_write_core`): where
the write steps, its index decodes to some position, and the rest's contract
gives that position's.

```math
\frac{\Gamma(o).\mathtt{[]} = \mathsf{list}(\langle[\,],[\,],E\rangle)\qquad E\ \text{source-valued}}
     {o[k] = v\ \text{within}\ \{\mathsf{value}{:}\,\mathsf{any},\ \mathsf{store}{:}\,\mathsf{grow}\}}\ \textsf{elem-write-slot}
```

The producer proposes `{value: any, store: grow}` for an element write at a
literal index or at a computed key every claim types as a number
(`element_key`), and for a compound or logical assignment
of a variable `{value: any, store: keep}` (`footprint_expr`). `map-stable-element-write`
is the case; controls in `pipeline/test.mts` certify `keep` claimed at a
required position, through search and checking, and refuse it at an
optional one.

## Element regions

The existing mechanism this extends is the index fact of
[quantified clauses](ARITHMETIC.md#quantified-clauses): a region fact is
one more `IndexFact`, carried by the same edge renaming and cut assertions,
and framed by the same change $`\chi`$ of
[frame conditions](PROGRAM-TYPING.md#frame-conditions).

**Regions.** The region of a value in a heap $`h`$ is the set of locations
its elements occupy: of a raw store $`\mathsf{arr}\,\ell`$, its listed cells;
of an array object, the location $`s`$ of its store field and the cells
$`h(s)`$ lists. A region fact $`\mathrm{apart}(x,y)`$ states that the
regions of the values in slots $`x`$ and $`y`$ are disjoint
(`IndexFact.apart`, `RegionsApart`). An array slot, one whose type is one
record clause with a store field (written or read only) of one list
contract, has its region in the heap: its store field's location and every
listed cell are locations of the world (`arraySlot_region`, proved).

**Rules.** An array literal's store, of slots, and the empty literal's object
are apart from every array slot of the context; an array object built from
the raw store in slot 0 is apart from every array slot that store is apart
from (`region-alloc`, `regionAtoms`, proved). A fact is kept by a change
keeping every store ($`s=\mathsf{keep}`$), whose store cells hold the same
stores. A write at a checked index of $`a`$'s store keeps a fact whose one
side is $`a`$ and other an array slot apart from it, or both of whose sides
are apart from it (`region-write`); a call growing its receiver's store
keeps a fact between two array slots (`region-grow`), each appended cell
lying past the old heap ([native footprints](SOURCE-CONTRACTS.md#native-footprints),
the append relation of `push`). Both proved (`writeAtoms_holds`,
`grownRegions_holds`):

```math
\frac{\mathrm{apart}(x,y)\in\Sigma\quad (x\in[a]\land \mathrm{apart}(a,y)\in\Sigma\land \mathrm{array}(y))\lor(\mathrm{apart}(a,x),\mathrm{apart}(a,y)\in\Sigma)}
     {\Sigma\vdash a[k]:=v\dashv\Sigma',\ \mathrm{apart}(x,y)}\ \textsf{region-write}
```

**Quantified facts across a write.** A write at a checked index of $`a`$'s
store keeps $`\mathrm{every}(z,t,\Phi)`$ where $`\mathrm{apart}(a,z)`$ and
the bound and every free body term read nothing of $`a`$'s region: a slot's
value, a string's length, or the length of a slot $`w`$ with
$`\mathrm{apart}(a,w)`$ (`every-apart-write`, proved: `writeAtoms_holds`, through
`IndexFact.every_frame`). Across a growth of $`a`$'s store, the length of a
slot apart from $`a`$ is kept (`growFirst`), so `every-grow` keeps such a
fact too.

```math
\frac{\mathrm{every}(z,t,\Phi)\in\Sigma\quad \mathrm{apart}(a,z)\in\Sigma\quad \mathrm{apart}_a(t)\quad \forall F\in\Phi.\ \mathrm{apart}_a(F)}
     {\Sigma\vdash a[k]:=v\dashv\Sigma',\ \mathrm{every}(z,t,\Phi)}\ \textsf{every-apart-write}
```

The producer states $`\mathrm{apart}(x,y)`$ at a declaration of an array
literal for every older array binding of the unit, and carries it across a
statement writing no heap, a bounded write and a push of actuals writing no
heap, as the rules keep it; Lean checks each entry's region facts on every
edge into it. A fact naming a binding the statement assigns is dropped.
Across a push, the producer translates a linear fact by the append relation
where each other length it names is of an array apart from the receiver
(`growFirst`). Cases: positives
`quantified-freshness-write` and `quantified-freshness-builder` (a fresh
array written and pushed while a precondition's quantified fact is kept),
`push-keeps-apart-lengths` (pretext's texts loop: `count === flags.length`
across `texts.push(…)`);
negatives, run under Node, `invalid-quantified-freshness-field-alias`,
`invalid-quantified-freshness-free-term` and
`invalid-push-keeps-apart-lengths-alias` (a push into a parameter that may
be the counted array); a forged control claims an alias
apart from its array and is refused at the first entry claiming it.

**Store fields apart.** A constant holding an array literal's object has
its store field apart from the store field of every older slot's array, a
[separation fact](PROGRAM-TYPING.md#separation-facts) the allocation
establishes; the lengths a push into either keeps are
[lengths kept across a push](ARITHMETIC.md#quantified-clauses).

## The elements fact

A second instance of the mechanism. `xs.every(g)` at a guard `g` promising
`string` answers `true` only where every present element of `xs` is a
string, and `xs.map(f)` relies on that between its callbacks as it relies
on density, so `f` may take its parameter at `string`
(`blocker-every-promise`, `every-elements-map-join`).

**The fact.** $`\mathrm{elems}(x,R)`$ says that the array slot $`x`$ holds
has a store, and that every element location the store lists holds a value
whose kind is in $`R`$, a set of the kinds null, undefined, boolean, number,
string, bigint, symbol and object (`CallEffects.ElemsAt`,
`CallEffects.ElemPred`):

```math
\mathrm{elems}(x,R)(\rho,h)\iff\exists\,\ell\ ls.\ \mathrm{store}(\rho(x))=\ell\land h[\ell]=\mathsf{arr}\,ls\land\forall l.\ \mathsf{some}\,l\in ls\Rightarrow\exists v.\ h[l]=v\land v\in R
```

A hole lists no location, so the fact is about present elements; the store
exists, so a heap extension keeps it (proved: `HeapKnowledge.elemsAt_extend`).
It is a fact kind of the stability check (`FactKind.elems`), its support the
store's location and the element locations, each kept (proved:
`elems_support`); a footprint keeping every location passes the check
(`elemsCheck_stable`), so the fact holds at every visit of a native whose
steps and callbacks keep the heap (proved: `elems_rely`, from `rely_chain`).
$`R`$ reads no world, so the fact is an atom of heap knowledge, compared along
edges and kept or dropped by the knowledge rules.

**The signatures' two parts.** A call signature's effect states two more
optional predicates about its receiver, as `receiverStore` and `receiverOwn`
are about it: `requires R`, a precondition, $`\mathrm{elems}(r,R)`$ in the
heap the call starts in; and `elements R`, a promise, $`\mathrm{elems}(r,R)`$
in the heap a normal return of `true` leaves (`Effect.requires`,
`Effect.elements`, in `PromiseWith` and `Effect.post`). One signature covers
another where its precondition is weaker and its promise stronger
(`Effect.covers`, proved: `covers_sound`); two signatures of one call combine
only where both state the same parts (`PromiseWith.combine`); an ordinary
arrow erases only a signature without a precondition (`Effect.plain`,
`PromiseWith.erase`); binding keeps neither part (`Effect.keeps`), since a
bound call does not pass the receiver the parts are about; graph code stating
either is refused (`effectChecked`). `Array.prototype`'s members are invoked
with the array as their receiver (`xs.every(g)` reads the member and calls it
with `xs`), so the parts are about the array.

**The natives.** The overlay states, for each predicate of the fixed set
{`string`, `number`, `boolean`}, `every` at a guard within the empty
footprint promising the predicate's type, with the elements promise, and
`map` at a callback within the empty footprint taking the predicate's type,
with the precondition, at a dense receiver with a dense result and at any
receiver with a result that may hold holes (`native-guard-every`,
`native-map-elems`, audited rows of
[native footprints](SOURCE-CONTRACTS.md#native-footprints)):

```math
\frac{f:(T,\ \mathsf{number},\ \mathsf{ReadonlyArray}(T))\Rightarrow_{\emptyset} R\,[\mathsf{guards}\ 0]}
     {\mathit{xs}.\mathsf{every}(f):\mathsf{boolean}\,[\mathsf{true}\Rightarrow\mathrm{elems}(\mathit{xs},R)]\;!\;\emptyset}\ \textsf{native-guard-every}
\qquad
\frac{\mathit{xs}:\mathsf{ReadonlyArray}^{\pi}(T)\qquad\mathrm{elems}(\mathit{xs},R)\qquad f:(R,\ \mathsf{number},\ \mathsf{ReadonlyArray}(T))\Rightarrow_{\emptyset} U}
     {\mathit{xs}.\mathsf{map}(f):\mathsf{Array}^{\pi}(U)\;!\;\emptyset}\ \textsf{native-map-elems}
```

where $`\pi`$ is `dense` for the dense signature and `sparse` for the other.

**The rules.** A call keeping the heap at a signature promising its
receiver's elements, its result a Boolean, adds the atom on its receiver's
slot conditional on the result's truthiness (`call-elements`, proved:
`PromiseCalls.elementsCall_sound`). A truthiness or Boolean answer on a
branch's edge makes an atom conditional on the tested slot's class
unconditional (`HeapKnowledge.observe`, `ControlFlow` on `.branch` edges,
proved: `promoteTruthy_holds`, `observeBoolean_holds`). A negation
`if x then false else true` restates the atoms conditional on `x` on its
result with the opposite answer (`not-elements`, proved:
`Checker.negatingSlots`'s soundness, from `negation_run` and
`negation_test_run`). A call at a signature stating `requires R` is accepted
where its receiver slot's class has an unconditional atom with a predicate
within $`R`$ (`call-requires`, proved: `requiresTree_sound`, through
`call_local_sound` with the precondition), and each fact of a precondition on
the call's values its signature states follows from the knowledge at the call
([reads below the length](PROGRAM-TYPING.md#reads-below-the-length)); a write, a call beyond the empty
footprint and a throw drop every atom, as they drop every heap fact. The
search carries the atoms along edges, meets them at merges and seeds a cut
with the atoms every entering edge carries; Lean checks every edge.

**Cases.** Positive: `blocker-every-promise`, `every-elements-map-join`,
`every-elements-number`, `every-elements-sparse` (a receiver admitting
holes, its result keeping them, run under Node). Negative, each run under Node: `invalid-every-elements-callback-call` and
`invalid-every-elements-guard-call` (a callback or a guard beyond the empty
footprint) and `invalid-every-elements-escape` (the fact gives the array no
type). Forged controls in `pipeline/test.mts`: the declarations without the
elements promise or at another predicate, a guard closure's claim stating
either part, and the atom forged unconditional in the evidence.

## Index facts

A third instance: footprints are how the frame conditions of index facts
are stated and checked. An index fact (a length, a typed-array length, a
field path's value) reads the locations its terms read, each holding an
object, a store or a number. A closed footprint preserves the locations of
the classes it keeps, `grow` on a value being `keep`
(`HeapKnowledge.Changes.ofClosed`, proved: `ofClosed_holds`), so a call at a
signature within `{value: any, store: keep}` preserves every length, and
`grow` preserves the lower bounds of a length; a field write, an element
write below the length and a call changing only its receiver's own locations
state their own change. The preservation rules and their proofs are
[frame conditions](PROGRAM-TYPING.md#frame-conditions).

## The rule users see

> `xs.map(f)` has type `U[]` with no holes when `xs` has none and `f`, with
> everything it calls, uses only operations that keep every array's dense
> prefixes: reads (optional chains included), tests, arithmetic, allocation
> (array and object literals with spreads included), writes to variables and to fields
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

`SourceClaimJson.checkUnitJson_safe` keeps its premise (the CLI success
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
callbacks that change another array beyond `grow`, such as `pop` on an array
literal the callback allocated. Admitting them needs footprints over regions
rooted at a call's operands (`own(x)`, `store(x)`, `elems(x)`), composed
along a graph and framing the caller's knowledge; the regional lemmas are
proved (`Post.compose`, `transport_sound`,
`stable_sound`, `frame_sound`, namespace `Footprints`).

### Argument-path store regions

This extends the receiver-store exception, stable field links and store
separation. A region $`(i,p)`$ names a call position ($`0`$ is the receiver)
and a path of own data fields. In the entry heap $`h_0`$, it selects the
array store reached from that position's value. The footprint bounds every
other old location, including element cells. A failed path read selects no
store. An empty receiver path has the receiver-store effect's scope.

Writing $`R_{i,p}(h_0,\rho_0)`$ for that optional store location, the relation is:

```math
\begin{aligned}
\mathrm{within}(h_0,h') \iff{}& |h_0|\le |h'|\ \land{}\\
 &\forall l<|h_0|.\quad
   (\forall(i,p)\in S.\ R_{i,p}(h_0,\rho_0)\ne l)
   \Rightarrow \Phi_{\mathrm{class}(h_0[l])}(h_0[l],h'[l]).
\end{aligned}
```

The location is fixed at entry. A mutable path could later select a different
array through an alias or a call. A path through required stable fields
keeps its entry value by each field's singleton contract
([records](POSITIVE-TYPES.md#records)). This restricts the field references;
the final array's store can change. External values need a checked boundary
or an explicit contract establishing those same stable fields.

The semantic framing theorem requires separation from every selected store.
Distinct slots or distinct field names do not establish that premise. With
that separation, `store: keep` retains another array's exact length and
`store: grow` retains its dense prefixes. An alias of the selected array
cannot meet the separation premise. Framing on a throw additionally requires
a footprint guarantee on that throw.

**Proof scope.**
[`ArgumentStoreRegions.lean`](../lean/Verification/Semantics/ArgumentStoreRegions.lean)
defines `ArgumentStoreRegionsWithin`, `StoreApart` and `StablePath`.
Proved: `ArgumentStoreRegionsWithin.trans` composes at unchanged selected
stores; `.nested` composes with a nested call's selected entry or fresh
stores; `.receiver` embeds the receiver-store exception; `.frame_length`
and `.frame_densePrefix` give caller framing. `StablePath.transfer`, `.read`
and `.frame` retain the path through world extension and safe execution,
including a throw. `StoreApart.stable_path_frame` retains separation and
`.not_alias` excludes the alias case.

[`ArgumentPathTracking.lean`](../lean/Verification/Programs/ArgumentPathTracking.lean)
proves entry, slot-map, normal-edge and handler checks sound
(`checkEntry_sound`, `checkMap_sound`, `checkEdges_sound`,
`checkHandler_sound`). `stableField_path` obtains a path witness from a
checked stable-field type and a successful own-field read; `copy`,
`read_stable` and `receiver_call` establish provenance and its store effect.
`checkReceiver_sound` connects a checked receiver origin to the existing
receiver-store call effect.
[`ArgumentRegionGraph.lean`](../lean/Verification/Programs/ArgumentRegionGraph.lean)
proves `bounded_step`, `bounded_safe_of_sim` and `goto_bounded`: ordinary graph
safety, regional node obligations, and checked provenance transfers imply the
regional bound on every finite return. The invariant covers cycles and caught
throws; a caught throw requires a bound even without an exceptional guarantee
on the enclosing invocation. `nodeWithin_of_closed` embeds existing closed
node bounds. `checkReceiverCall_sound` validates a selected receiver-store
invocation against a tracked origin and its existing checked call effect,
including calls with checked preconditions. An escaping throw needs an
effect bound only when the enclosing invocation promises one.

A caller's separation of a region's store from another array is a fact of
its knowledge, a [store separation](ARITHMETIC.md#store-separation) or a
region fact, which `region-call-keep` consumes
([stated effects](SOURCE-ELABORATION.md#stated-effects)).

[`ArgumentRegionCertificates.lean`](../lean/Verification/Programs/ArgumentRegionCertificates.lean)
checks a provenance table at entry, every normal edge and every handler.
`checkNodes_sound` discharges the regional node obligations for closed-bound
nodes, slot copies and receiver-store calls on tracked entry values.
`checkEntry_sound` proves the regional bound from the executable check and
ordinary code and summary soundness. Its premises contain no unchecked
regional node obligations. `checkEntry_reassign` preserves the check under
type-parameter assignments; `firstRefusedNode_sound` identifies a failing
node at its program label for source diagnostics. Field-read provenance, fresh stores and nested
argument-path calls are outside this checker's supported nodes.

The regional graph and caller-separation checks do not participate in CLI
acceptance. The call-effect wire has no argument-path field. The source-level
argument-path effect therefore lies outside these theorems' proof scope.

`GraphCodeSpec` states a code's effect at the receiver and actuals matching
its entry frame (`FrameValues`), including the optional rest-store slot.
The invocation proofs supply that match (`graph_invoke`, `graph_invoke_at`,
`graphRest_invoke`).

**Provenance stamps** (`FootprintProvenance.lean`: marks, `after` and
`before` stamps, proved: `stamps_separate`) state a slot's separation against
heap marks rather than against each older slot, as
[separation facts](PROGRAM-TYPING.md#separation-facts) do; they need a mark
valuation below the current heap's length, carried through every heap
change. [WORK](../WORK.md#footprints) tracks both.
