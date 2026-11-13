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
\mathsf{grow}_b(v, v') &\iff v' = v \lor \bigl(v = \mathsf{arr}\,ls \land v' = \mathsf{arr}\,ls' \land (\forall n.\ D_n\,ls \to D_n\,ls') \land (\forall l.\ \mathsf{some}\,l \in ls' \to \mathsf{some}\,l \in ls \lor b \le l)\\
&\qquad \land |ls| \le |ls'| \land (|ls| \le 2^{32}-1 \to |ls'| \le 2^{32}-1)\bigr) \lor \mathrm{scalar}(v, v')\\
\mathsf{any}_b(v, v') &\iff \top
\end{aligned}
```

`init` lets a location holding `null` or `undefined` take a value, the change
of a lazy initialization `x ??= e`; `scalar` lets a location holding neither an
object nor a store take a value, the change of a `Map`'s `set` to its `size`;
`grow` keeps every dense prefix, lists no old element location the store
did not list, and leaves the store no shorter and at most $`2^{32}-1`$ long
(`maxArrayLength`) where it was (`LengthGrows`), or takes a scalar's step. The changes form the chain
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
`goto_bounded`). The pass accepts a node (`SinglePass.footprintCheck`; proved:
`TolerantFrames.footprintCheck_sound`, `nodeWithin_of_checked`) when it is:

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
`PassUnit.ordinary_requestSafe`), a closure's against its code
entry (`PassUnitCodes.codeSpec_of_guarantee`), a class's construct signatures against its
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

The walk proposes each footprint, untrusted (`declarationWalks`,
`FragmentFront.lean`): a body's is the join of the changes its writes and
its calls' instances make, by class of location (`Walk.valueChange`,
`Walk.storeChange` in `Synthesis.lean`, as a function literal's effect is
found): an assignment of a binding a cell holds `{value: any, store:
keep}`, a binding its activation holds in a slot none (`cellLocals`); a
field write `{value: any, store: keep}` where the field is a source field
(`ExpressionEffects.sourceField`), a `length` write `{value: any, store:
any}`; an element write `{value: any, store: grow}` (`targetWrite`); a call
or construction its selected instance's footprint, everything where the
instance excepts a receiver's store that is not fresh, and none where the
instance's result is the empty type, outside a handler and an async body: on
a normal return it changes nothing, its throw its signature's
(`Synthesis.callChanges`; proposed so under a handler too,
`TSCERT_FORCE=no-return`, refused over the `invalid-async-throw-only-*`
cases and `invalid-method-effect-throw-caught`); a call of an unknown
callee, an iteration and a finalizer change anything or bound no throw. It
bounds the throws where none of
its calls, iterations or finalizers leaves one unbounded. Callees are
walked first, each caller reading the footprint found for it; a
self-recursive function is walked with itself at `{value: keep, store:
keep}`, then at what that walk found, until a walk finds no more than it
assumed, three walks at most. An async function, a generic one, one with a
rest parameter and one with a written effect keep what `fragmentClaims`
gives them. A method call on an object whose type has several
alternatives once each declaration it names is unfolded, with actuals that
are names or literals, may be lowered to one node dispatched on the object
(`Lowering.dispatchesCall`), which no bounded node rule above admits; a
method call on a union of arrays none of which owns the member, the member
at one type, is not dispatched (each alternative reads it from the array
prototype), nor is one on a union of hosts each holding the member as a
method, generic (a scheme whose signatures take the declaration as
receiver, as `forEachChild`) or not (`unionMemberHosts`). Lean decides
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
  postcondition then states it (`SinglePass.footprintCheck`'s `outFresh`,
`PassUnitCodes.codeSpec_of_guarantee`). A
  declaration states no fresh result.

**In a regional body.** A body certified at stated store regions
([argument-path store regions](#argument-path-store-regions)) tracks, at
each node, two lists of slots against $`b=|h_0|`$, the invocation's entry
heap's length, fixed through the whole run, loops included: the slots $`F`$
holding a fresh value and the slots $`C`$ holding a fresh cell
([ArgumentRegionFresh.lean](../lean/Verification/Programs/ArgumentRegionFresh.lean)):

```math
\begin{aligned}
\mathrm{FreshValue}_b(v) &\iff \neg\,\mathrm{isArr}(v)\ \land\ \forall s.\ \mathrm{store}(v)=s \Rightarrow b\le s\\
\mathrm{CellFresh}_b(h,c) &\iff \exists\, l\,v.\ c.\mathtt{value}=l\ \land\ h[l]=v\ \land\ \mathrm{FreshValue}_b(v)
\end{aligned}
```

A fresh value is conditional: `null`, a number and an object with no store
field meet it, and an array meets it where its store was allocated during
the run. It reads no heap. A fresh cell is an invariant of its contents,
read at each heap: a cell is the object a `let` a closure writes lowers to
([slot or cell](SOURCE-ELABORATION.md#slot-or-cell)), its contents at its
field `value`. A `let` held in a slot is rebound by each write, one nested
in an expression included, and a slot's fresh value is a fact of the value,
which no step changes. A node's value is fresh, and a node
keeps its cells, by these rules, with $`\Gamma`$ the node's slot types,
$`i \in F`$ and $`j \in C`$:

```math
\frac{}{x_i\ \text{fresh}}
\quad
\frac{k\ \text{a constant}}{k\ \text{fresh}}
\quad
\frac{\mathtt{[]} \in \mathit{ns}}{\mathsf{new}\{\mathit{ns}\}\ \text{fresh}}
\quad
\frac{}{x_j.\mathtt{value}\ \text{fresh}}
\quad
\frac{\text{the selected signature states}\ \mathtt{Fresh}}{f(\bar x)\ \text{fresh}}
```

```math
\frac{}{x_j\ \text{a fresh cell}}
\qquad
\frac{\mathit{ns}\ \text{distinct}\qquad \mathit{ns}_m=\mathtt{value}\qquad \bar x_m = x_i}
     {\mathsf{new}\{\mathit{ns}:\bar x\}\ \text{a fresh cell}}
```

```math
\frac{t\ \text{an inspection}}{t\ \text{keeps}\ C}
\qquad
\frac{}{x.f := x_i\ \text{keeps}\ C}
\qquad
\frac{\mathrm{Post}\,\Psi\,\sigma\,h\,h' \qquad
      \forall (r,\delta)\in\Psi.\ \delta=\mathsf{keep} \lor r \subseteq \mathsf{cls}\ \mathsf{store}}
     {t\ \text{keeps}\ C}
```

An inspection changes no old location; a write of a fresh value leaves a
fresh value wherever it writes; and a frame whose every entry keeps its
locations or holds only stores ($`\mathsf{cls}\ \mathsf{store}`$, a region's
part of class store) changes no cell's contents, a value of no store
(`keepsValues`, proved: `CellFresh.post`). `push`'s frame names its
receiver's store at its part of class store, which `ReceiverGrows` states.
The allocation rule holds of a run of the allocation with any initializers
or binding before it (`alloc_fresh`, from `alloc_step`: the store field's
location is past the heap the allocation starts in); the others are
`cellAlloc_fresh`, `cellRead_fresh` and `freshWrite_cells`. The facts along
edges and handlers are GraphCode's (`edgesFresh`, `handlerFresh`, proved
for any slot property: `edgesFresh_holds`, `handlerFresh_holds`): a
destination's facts follow from the source's through the edge's slot map,
slot 0 from the node's value; a handler's from the facts of every node it
catches, the thrown value never fresh, its cells kept on the node's throw.
The entry has none. Lean infers the facts (`freshTables`, untrusted) and
checks every node (`checkFresh_sound`) and every edge.

A fresh value's store region rebases to no region of the entry
([the step-frame rule](#argument-path-store-regions)), so a step growing or
popping an array the body allocated, directly or through a cell, needs no
region of the stated frame (`stated-region-fresh`, `stated-region-lazy`).
A fresh record holding the caller's array gives that array no fact; a slot
or a cell written with a value not fresh loses its fact, so a join of a
fresh array and an old one has none; a call's result is fresh only at a signature
stating `Fresh`, which the callee's own check establishes
(`invalid-stated-region-fresh-wrapper`, `invalid-stated-region-fresh-join`,
`invalid-stated-region-fresh-call`, each run under Node; a control forges
`Fresh` onto the callee of the last, refused at the callee). The rule
keeps a cell only across steps whose frames keep every location of class
value: a call whose frame changes values (`values: any`), or the step of a
`for...of` iterator, whose frame changes its receiver's own locations,
leaves its cells no fact. A slot keeps its fact across every step: a
slot holding `null` or an array the body allocates stays fresh
across calls whose frames state `values: "any"`, and a handler receives it
as the throwing node holds it (`stated-slot-collect`,
`stated-slot-conditional`, `stated-slot-handler`;
`invalid-stated-slot-handler`, where the throw precedes the write, run
under Node).

**The regional check as a second certificate.** A unit's claimed footprint
$`\Phi_c`$ has one entry point (`effectResult`), which tries its
certificates in order: $`\Phi_c = \mathsf{top}`$ with no throw or fresh
result promised; a pure graph; the pass's walk at the bound, node by node
(`SinglePass.footprintCheck`); and, for a unit promising no fresh result, the
regional check with no regions at $`\Phi_c`$ (`regionalChecked`), its
throws bounded where the unit claims $`\Phi_c`$ on a throw. A frame stating
a store region is `top` to the node-by-node check (`Effect.footprint`); the
regional check rebases its region on a store the body allocated to none, so
a body changing such a store through a callee stays within $`\Phi_c`$
(`stated-fresh-direct`). With no regions the regional check's postcondition
is the closed footprint itself:

```math
\frac{\mathrm{ArgumentStoreRegionsWithin}\ \Phi\ [\,]\ \rho\ h_0\ h}{\Phi.\mathrm{Holds}\ h_0\ h}\ (\text{no-regions})
```

(proved: `ArgumentStoreRegionsWithin.nil_holds`; acceptance:
`PassUnit.ordinary_requestSafe`). A unit an earlier
certificate accepts runs no regional traversal. A record the body receives
holds no fresh fact, so a region on its field is no store the body
allocated (`invalid-stated-fresh-parameter`, run under Node).

**Fresh fields.** A regional body tracks a third list at each node, pairs
$`(s, f)`$ of a slot and a field name, of the names the regions of the
body's calls read through one field
([ArgumentRegionFresh.lean](../lean/Verification/Programs/ArgumentRegionFresh.lean)):

```math
\mathrm{FieldFresh}_b(h,v,f) \iff \forall u.\ \mathrm{readPath}(h,v,[f]) = u \Rightarrow \forall s.\ \mathrm{store}(u)=s \Rightarrow b\le s
```

A value with no field $`f`$, `null` and `undefined` included, meets it. A
node's value has a fresh field, and a node keeps a pair, by these rules,
with $`i \in F`$, $`(j,f)`$ a pair of the node's entry and $`\Gamma`$ its
slot types:

```math
\frac{}{x_j\ \text{fresh at}\ f}
\quad
\frac{k\ \text{a constant}}{k\ \text{fresh at}\ f}
\quad
\frac{\mathit{ns}\ \text{distinct}\qquad \mathit{ns}_m=f\qquad \bar x_m = x_i}
     {\mathsf{new}\{\mathit{ns}:\bar x\}\ \text{fresh at}\ f}
\quad
\frac{\Gamma(j)\ \text{states}\ f\ \mathtt{@stable}\ \text{or is}\ \mathtt{null}\ \text{or}\ \mathtt{undefined}}
     {t\ \text{keeps}\ (j,f)}
```

A stable field's location has a stable contract in the world, which every
heap a run reaches keeps, its throws included, and a store's location is
part of the value the field holds (proved: `fieldAlloc_fresh`,
`fieldsHold_frame` from `stableLocations_exc`, `fieldOut_sound`,
`fieldsCheck_sound`). The facts along edges and handlers follow the slot
maps as the other two lists' do (`edgesFields_holds`,
`handlerFields_holds`); the entry has none. The rebasing maps a step's
region at a path of one field to no region where the step position's slot
has that field fresh:

```math
\frac{(s,f)\ \text{fresh at the step}}{\mathrm{rebase}(\mathsf{path}\ s\ [f]\ \mathsf{store}) = \varnothing}
```

(proved: `RebaseOk.fresh_path`, `rebase_sound`). Lean infers the pairs after
the values and cells, apart from them (`freshTables`, untrusted; without a
fixed point, none), and checks every node and edge (`checkNodes`). A body
that allocates a record holding an array it allocates and passes it to a
callee stating a region on that field changes no store of its entry heap
through the call (`stated-fresh-field`, `stated-fresh-field-local`,
`stated-fresh-field-nullable`, where the slot is the record or `null`;
`stated-fresh-field-escape`, `stated-fresh-field-alias`,
`stated-fresh-field-throw`). A fresh record holding the caller's array and a
join with such a record give no fact (`invalid-stated-fresh-old-array`,
`invalid-stated-fresh-join`, each run under Node). A region through a field
that is not `@stable` is refused at the callee's entry
(`invalid-stated-fresh-reassigned`, `invalid-stated-fresh-reassigned-throw`;
Node prints `NaN` for `console.log(total([1, 2, 3]))` in each).

The transport check (`fieldsKept` in `checkNode`) refuses a fresh-field
fact retained across replacement of the mutable field by the parameter's
array, also through a throwing call inside `try` and the subsequent
`catch`.

`pop`, `shift`, `reverse` and `splice` change only their receiver's store and element
contents, and `filter`, `map`, `flatMap`, `flat`, `slice`, `splice` and `split` allocate their
result's store (audited: [native footprints](SOURCE-CONTRACTS.md#native-footprints)).
Controls: `map-stable-fresh-store`'s negatives, an alias of the mapped
array, a join of a fresh and an old array, a reassigned variable and a
helper's parameter, each also at a result type admitting holes
(`map-fresh-controls-sparse`); a pop of the mapped array before a throw its
handler catches (`invalid-map-handler-after-pop`); and a fresh result
stated of an identity function, refused at its unit
("forged fragment: a fresh result stated of an identity function" in
`tests/single-pass-controls.mts`). A fresh array
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

Each rule's footprint is also the node's frame condition for index facts: the
node keeps every fact the change $`(\top,\top,\mathsf{grow})`$ keeps, the
lower bounds of every length, the written array's included
([index facts](#index-facts), `IndexWrites.growOutput`, proved:
`ExpressionEffects.writeStep_grow`).

The walk proposes `{value: any, store: grow}` for an element write
(`Synthesis.targetWrite`). `map-stable-element-write` is the case.

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

The separations at a unit's loop heads are inferred (`freshApartAt`,
`RegionInference.lean`): the pairs of slots whose regions an allocation
states apart, a literal's store apart from every array slot, carried along
every edge to the slots whose mappings read them, those every predecessor
carries; at each loop head, the pairs of array slots of an allocation whose
array the loop writes an element of. Each is a proposal: Lean checks each
loop head's region facts on every edge into it. A fact naming a binding the
statement assigns is dropped. Across a push, a linear fact is translated by
the append relation where each other length it names is of an array apart
from the receiver (`growFirst`). Cases: positives
`quantified-freshness-write` and `quantified-freshness-builder` (a fresh
array written and pushed while a precondition's quantified fact is kept),
`push-keeps-apart-lengths` (pretext's texts loop: `count === flags.length`
across `texts.push(…)`);
negatives, run under Node, `invalid-quantified-freshness-field-alias`,
`invalid-quantified-freshness-free-term` and
`invalid-push-keeps-apart-lengths-alias` (a push into a parameter that may
be the counted array); a forced proposal stating each side of such a pair
apart from itself (`TSCERT_FORCE=head-apart` over
`quantified-freshness-builder`, `tests/single-pass-control-inputs.mts`) is
refused at that unit.

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
either is refused (`PassUnitCodes.codeConditions`). `Array.prototype`'s members are invoked
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
pass carries the atoms along edges and meets them at merges; a loop head's
atoms are inferred candidates (`HeadInference.lean`), each an obligation
checked on every edge into the head.

**Cases.** Positive: `blocker-every-promise`, `every-elements-map-join`,
`every-elements-number`, `every-elements-sparse` (a receiver admitting
holes, its result keeping them, run under Node). Negative, each run under Node: `invalid-every-elements-callback-call` and
`invalid-every-elements-guard-call` (a callback or a guard beyond the empty
footprint) and `invalid-every-elements-escape` (the fact gives the array no
type).

## Index facts

A third instance: footprints are how the frame conditions of index facts
are stated and checked. An index fact (a length, a typed-array length, a
field path's value) reads the locations its terms read, each holding an
object, a store or a number. A closed footprint preserves the locations of
the classes it keeps, and `grow` on a store leaves every length no smaller
(`HeapKnowledge.Changes.ofClosed`, proved: `ofClosed_holds`). So a call at a
signature within `{value: any, store: keep}` preserves every length, and a
fact with a non-positive coefficient on each length it reads, its other
terms kept, survives a call
within `{value: any, store: grow}` (`Term.grownBy`, proved:
`termValue_grown`), and so does such a fact across an element write, within
that footprint at any index ([element writes](#element-writes)); a field
write, an element write below the length and a call changing only its
receiver's own locations state their own change. The preservation rules and their proofs are
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

A footprint check that runs out of subtype rounds is reported as exhausted
("exhausted footprint check" in `tests/single-pass-controls.mts`).

## The acceptance theorem

`SourceClaimJson.PassUnit.mode8Accepted_sound` (`PassUnitRun.lean`) takes
the condition under which mode 8 accepts a unit's group and concludes
`PassUnitSafe` of the group: each member's request is safe, and, where its
declaration claims a footprint other than `{value: any, store: any}`, an
on-throw bound or a fresh result, its graph, run from every entry meeting its
inputs, returns with a heap its footprint relates to its entry heap and a
value meeting its goal, a guard's promise included, and throws with a heap
its footprint relates where it claims `onThrow` (`FootprintClause`,
`PassUnit.lean`). Footprints reach it through
certified code entries (`ProgramCertificates.CodesSound`, `PassUnitCodes.codesAccepted_sound`)
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

**The step-frame rule.** A body certified at a stated frame $`\Phi`$ keeps
the invariant $`\mathrm{Post}\,\Phi\,\rho_0\,h_0\,h`$ at every node, where
$`\rho_0`$ and $`h_0`$ are the invocation's entry values and heap: $`\Phi`$
is the closed bound's two class entries and an entry
$`(\mathsf{path}\ x\ p\ \mathsf{store},\ \mathsf{any})`$ per region. Each
step has a local effect, a frame $`\Psi`$ read at the step's own positions
$`\sigma`$ in the heap $`h`$ it starts in: a call's is its signature's frame
at the call's actuals (`Effect.within`), a step within the closed bound has
the bound's two class entries, an element write has
$`\{(\mathsf{cls}\ \mathsf{value},\mathsf{any}),\ (\mathsf{field}\ i\ \mathsf{store},\mathsf{any})\}`$
at the array's slot $`i`$. The rule is

```math
\frac{\mathrm{Post}\,\Phi\,\rho_0\,h_0\,h \qquad \mathrm{Post}\,\Psi\,\sigma\,h\,h' \qquad
  \mathrm{RebaseOk}\ \mathit{ev}\ \sigma\ \rho_0\ h_0\ h \qquad
  \Phi \mathbin{+\!\!+} \mathrm{rebase}_{\mathit{ev}}(\Psi) \sqsubseteq \Phi}
  {\mathrm{Post}\,\Phi\,\rho_0\,h_0\,h'}
```

where $`\sqsubseteq`$ is `Footprint.le`. The evidence $`\mathit{ev}`$ links a
step position $`s`$ to an entry position and path $`(x,q)`$ with
$`\mathrm{readPath}\,h_0\,(\rho_0\,x)\,q=\sigma\,s`$, and says which
path $`p`$ read from $`\sigma\,s`$ at $`h`$ reads the same value at $`h_0`$
(`RebaseOk`), and which positions hold a fresh value, whose store, where it
has one, lies at or above $`|h_0|`$ ([fresh array
storage](#fresh-array-storage)). Rebasing maps the store region of a fresh
position, $`\mathsf{field}\ s\ \mathtt{[]}`$ or
$`\mathsf{path}\ s\ []\ \mathtt{[]}`$, to no region: a location it
selects is no location of $`h_0`$, so `rebase_sound`'s case of a location
below $`|h_0|`$ contradicts the evidence. It maps $`\mathsf{field}\ s\ k`$ and
$`\mathsf{path}\ s\ p\ k`$ to $`\mathsf{path}\ x\ (q\,p)\ k`$,
$`\mathsf{own}`$ and $`\mathsf{pathOwn}`$ alike, a class or a cell to
itself, the part of a region of class $`c`$ to its image's part of class
$`c`$, and any other region, or one without evidence, to $`\mathsf{all}`$.
A location an entry of $`\Phi`$ at `any` covers needs no rebasing
(`rebase_sound`'s second disjunct). The rule is `Post.compose_at`
([FootprintRebase.lean](../lean/Verification/Semantics/FootprintRebase.lean));
since $`\Phi`$ is the accumulated bound, it is an invariant through loops.
On a throw the step's raised frame takes $`\Psi`$'s place where the node may
throw: to a handler, or out of an invocation stating `onThrow`.

The evidence of a node comes from its tracked facts: a slot holding the
value an entry path reads links its position, and a one-field path
$`[f]`$ from a slot holding an entry value $`\rho_0\,x`$ agrees where
$`(x,[f])`$ is a stated region, by the entry world's witness. The witness
is conditional: where $`\rho_0\,x`$ has the field $`f`$, the field is
stable and its read fixed; where it has none (`null`, `undefined`), no heap
reads it, so the path selects no store. A parameter's type passes the entry
check where every alternative a field read succeeds on states $`f`$ present
and stable, and there is one (`entryField`).

Push's step frame is the one `ReceiverGrows` gives on normal return, every
old location kept but the receiver's store, which holds a store and which
`grownFrame` names at `any`, as its part of class store; its signature's closed bound `{value: any, store: grow}` is its frame
on a throw. A destructuring read, `const { f } = x`, is a stable read: an
empty frame and the result's provenance. A node's fresh positions are the
slots its fresh facts name (`nodeFresh`).

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
checked stable-field type and a successful own-field read; `copy` and
`read_stable` establish provenance. `checkEntryFields_sound` gives the
conditional entry witnesses and `StableNow.agree` their agreement.
[`ArgumentRegionGraph.lean`](../lean/Verification/Programs/ArgumentRegionGraph.lean)
proves `bounded_step`, `bounded_safe_of_sim` and `goto_bounded`: ordinary graph
safety, regional node obligations, and checked provenance transfers imply the
regional bound on every finite return. The invariant covers cycles and caught
throws; a caught throw requires a bound even without an exceptional guarantee
on the enclosing invocation. `nodeWithin_of_step` is the step-frame rule at a
node, its evidence from the node's facts (`nodeRebase_ok`).

A caller's separation of a region's store from another array is a fact of
its knowledge, a [store separation](ARITHMETIC.md#store-separation) or a
region fact, which `region-call-keep` and `region-call-grow` consume
([stated effects](SOURCE-ELABORATION.md#stated-effects)).

[`ArgumentRegionCertificates.lean`](../lean/Verification/Programs/ArgumentRegionCertificates.lean)
checks a provenance table at entry, every normal edge and every handler.
A node is a provenance step, a slot copy (`checkCopy_sound`) or a read
through a `@stable` field the slot's type states present (`checkRead_sound`),
or a step whose local effect the common check `stepWithin` includes:
`closedStep_ok`, `callStep_ok` (its frame, or `grownFrame` where the
signature states `receiverGrows`) and `writeStep_ok` (from
`writeStep_sound`, `ExpressionEffects.lean`, whose element-write cores
state the written store, `StoreWrite`). Each node also passes its
freshness check (`checkFresh_sound`, [fresh array
storage](#fresh-array-storage)). `checkNodes_sound` discharges every
node's obligation; `checkEntry_sound` proves the regional bound from the
executable check and ordinary code and summary soundness. Its premises
contain no unchecked regional node obligations. `checkEntry_reassign`
preserves the check under type-parameter assignments;
`firstRefusedNode_sound` identifies a failing node at its program label for
source diagnostics.

The regional graph check is part of CLI acceptance: a function
declaration's stated regions, `"x[*]"` and `"x.f[*]"` through a `@stable`
field, are certified by it (`RegionalClause` of `mode8Accepted_sound`'s
conclusion), and a call effect carries them (`regions`).

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
