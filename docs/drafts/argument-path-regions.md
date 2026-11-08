# Footprint regions rooted at argument paths

## The existing mechanism this extends

[Footprints](../FOOTPRINTS.md): a call's effect is a closed footprint
$`\Phi=\{\mathsf{value}{:}\delta_v,\ \mathsf{store}{:}\delta_s\}`$ bounding the
change of every old location (`Footprints.Closed`, `Effect.within`), with one
region excepted where `receiverStore` holds: the receiver's array store, which
the call may change arbitrarily ([fresh array storage](../FOOTPRINTS.md#fresh-array-storage),
`pop`, `shift`, `reverse`, `splice`). Region facts
$`\mathrm{apart}(x,y)`$ ([element regions](../FOOTPRINTS.md#element-regions))
and store-field separation facts keep a fact about one array across a
change of another. Read links through stable keys survive every step
(`stable-link`, [PROGRAM-TYPING.md](../PROGRAM-TYPING.md); stable keys,
[POSITIVE-TYPES.md](../POSITIVE-TYPES.md)). The regional lemmas
`Post.compose`, `transport_sound`, `frame_sound` (namespace `Footprints`) are
proved and unused: [deferred extra precision](../FOOTPRINTS.md#deferred-extra-precision).

This draft generalizes `receiverStore` from the receiver to an array reached
from any position through a path of fields, and states what the caller needs
to frame its facts across such a call.

## The form

An effect states a list of **argument regions** $`(i,p)`$: position $`i`$ of
the call (`0` the receiver) and a path $`p`$ of data fields. In the heap the
call starts in, $`(i,p)`$ denotes the region of the array object the path
reads from the position's value (`IndexHeaps.readPath`): its store field's
location and the cells that store lists (`RegionOf`). The effect's meaning:

```math
\mathrm{within}(h,h')\iff
  \forall l<|h|.\ l\notin\textstyle\bigcup_{(i,p)}R_{i,p}(h)\Rightarrow\delta_{\mathrm{class}(h[l])}(h[l],h'[l])
```

`receiverStore` is the region $`(0,[\,])`$.

**Callee.** A unit claims a region $`(i,p)`$ where every change its body
makes outside the closed footprint is a call or write whose own region is the
store of a slot $`z`$ that the knowledge links to the entry value of
$`p`$ from parameter $`i`$: a read at entry (`const {f} = x`) followed by no
write of the path's fields, or a stable link. pretext's `readScriptRuns`
reads `runs.openBrackets` once at entry and splices, pushes and writes only
that array; its runs' fields `read` and `scripts` take numbers (`scalar`).
So it claims `{value: any, store: grow}` (its other calls) with the region
$`(1,[\mathtt{openBrackets}])`$, and `spaceSharesScriptRun` and
`getUnspacedGraphemes` inherit it by passing their parameter at position 1.

**Caller.** At a call with region $`(i,p)`$, a fact naming the store of an
array slot $`y`$ is kept where the knowledge at the call states the path's
array: a chain of read links $`a_i.p\mapsto z`$ and $`\mathrm{apart}(z,y)`$ or a
store-field separation of $`z`$ and $`y`$, and the closed footprint keeps the
fact.

## The soundness question

Between pretext's script-run calls, `measureAnalysis` calls measurement
functions whose closed footprints state `value: any`. A closed footprint
names no reachability, so in the model such a call may write any old object
into `scriptRuns.openBrackets`, for instance the analysis's `flags`, and the
next script-run call would then splice `flags`' store. The caller's link
`scriptRuns.openBrackets ↦ z` therefore does not survive those calls, and
the region cannot be framed from it. The link survives every step only where
each field of the path is a **stable key** (`stable-link`): a location whose
contract admits one value, which every safe run keeps.

Stable keys exist only on host families. The general form here therefore
needs one of:

1. **Stable keys of program records.** A record type states a field stable
   (say `/** @stable */` on a `readonly` field); an object literal at that
   type allocates the field's location with the contract admitting only the
   value written there (the world's contracts are semantic predicates,
   `Worlds.Ctr`); no write of the key types (the location's contract refuses
   every other value); a record is below another only where it states every
   stable key the other does (as for host families). Allocation soundness
   (`alloc_sound`) needs the singleton contract.
2. **Reachability footprints.** A call changes no location unreachable from
   its actuals, its closure and the module bindings. This is a property of
   the calculus (no forged references), with no trust, but it needs a
   reachability invariant through every step.

Option 1 reuses the existing stable-key and stable-link mechanisms; option 2
is the deferred mechanism in general.

## Review (Astra, 2026-11-08)

- The regional effect is sound where every certified normal return keeps
  $`|h'|\ge b`$ and, for each $`l<b`$ outside $`R_0`$ (the regions in the
  entry heap $`h_0`$), $`\Phi(\mathrm{class}(h_0[l]))`$ holds of
  $`h_0[l],h'[l]`$; on a throw only with `onThrow`. The callee check must
  establish this along every returning path, loops, nested calls and caught
  exceptions included; a later reread of the path needs a proved link to
  the entry value, and "no write" includes writes through aliases and calls.
- `Effect.within` excepts only the receiver's store location, while
  `RegionOf` also holds element cells: $`(0,[\,])`$ with element cells weakens
  `receiverStore`. The first form is store-only; element-cell regions are a
  separate extension with transport obligations.
- The lost-link analysis holds: a contract admitting both arrays lets a
  `value: any` call replace the field and keep `HeapOk`; separation facts and
  provenance stamps describe locations of fixed slot values, not which value
  a mutable field holds.
- Stable keys of program records are sound with an allocation-time contract
  $`C(j,U,v)\iff A(j,U,v)\land v=v_0`$, chosen once from the allocation's
  policy and initializer (`AllocationWorlds.allocation_safe`, its policy and
  the creation typing rules, not `alloc_sound`); subtyping keeps every stable
  key and grants no writable view of the singleton location; spreads and
  copies allocate fresh singleton contracts for the values they copy; external
  code needs a checked boundary or an explicit assumption. `stable_frame` and
  `withStable_sound` carry the preservation.
- Recommended order: a store-only argument effect for empty paths, checked
  against the entry heap, with caller framing and forged-effect and alias
  controls; then required, own, readonly stable fields on explicit object
  literals, singleton allocation, and one-field paths through stable links.
  `store: grow` keeps lower bounds across the intervening calls, not
  equalities of lengths.
