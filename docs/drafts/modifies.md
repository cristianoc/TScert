# Draft: what a call may change

A design for stating and checking the locations a call may change. Base:
TScert main at 56e79063, and the Lean of local branch
`chain1-argument-regions` (05d9d1eb). Claims are labelled **proved** (with
the Lean name and where it lives), **cited** (with the document and its
scope) or **conjectured**.

## The existing mechanism this extends

The regional footprint of [footprints](../FOOTPRINTS.md#changes-and-footprints)
owns the concern (`Semantics/Footprints.lean`, `FootprintStability.lean`;
proved there):

- a `Footprint` is a list of a `Region` and a `Change`; `Post Φ ρ h h'`
  bounds each location of $`h`$ by the entries covering it, read in $`h`$,
  keeps every location no entry covers, and leaves allocation free;
- a fact's support is a `Footprint` of the regions it reads, each at the
  change it tolerates; `Supported S ρ h h'` is that tolerance, and
  `stable K S Φ` decides it from `Post Φ` and separation knowledge $`K`$
  (`stable_sound`);
- a sequence of steps composes into one footprint at the entry heap,
  transporting each step's regions there (`Post.compose`, `transport`).

An effect-qualified signature
([inferred call effects](../SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification);
cited) states its frame through this machinery at one region form: a
`Closed` footprint $`\{v,s\}`$ is `Post` of the two class regions
(`Closed.Holds`, `ClosedFootprints.lean`), and three flags of `Effect`
(`CallEffects.lean`) except the receiver's store (`receiverStore`) or own
locations (`receiverOwn`), or promise an append (`receiverGrows`). Branch
`chain1-argument-regions` adds store regions read through field paths
(`ArgumentStoreRegionsWithin`; proved there, not reached from acceptance).

This design makes an effect's frame one `Footprint` over the call's
positions, read by `Post`, and extends `Region` with paths and module cells.
A [stated effect](../SOURCE-ELABORATION.md#stated-effects) gains the regional
items, written `@modifies` on a declaration.

## 1. The meaning

**Regions.** A call's environment $`\rho`$ is `callEnv`: position $`0`$ the
receiver, $`i`$ the $`i`$-th actual. Regions are read in the heap $`h_0`$ the
call starts in. A path $`p=f_1\ldots f_k`$ reads own data fields from
position $`x`$ (`HeapKnowledge.readPath`); a read that fails denotes no
location.

| Region | Locations at $`(\rho,h_0)`$ | |
| --- | --- | --- |
| `field x k`, `own x`, `elems x`, `cls c`, `all` | as today | existing |
| `path x p k` | the own field $`k`$ of the object $`p`$ reads from $`x`$ | new; `field x k` at $`p=[]`$ |
| `pathOwn x p` | the own locations of that object | new |
| `pathElems x p` | the element cells its store lists | new; `elems x` at $`p=[]`$ |
| `cell b` | the cell of module binding $`b`$ | new |
| `inCls r c` | the locations of $`r`$ whose contents in $`h_0`$ are of class $`c`$ | new |

`path x p store` is the store-only region of chain1. The written form
$`P[*]`$ is the store and its cells, `path x p store` and `pathElems x p`;
the store-only region has no written form and serves the translations of §2.

**The frame.** An effect states a footprint $`\Phi_E`$ over these regions.
A normal return from $`h_0`$ to $`h'`$ meets $`\mathrm{Post}\,\Phi_E\,\rho\,h_0\,h'`$;
a throw meets it too where the effect states `onThrow`. A location covered
by several entries is allowed any one of their changes, which is their join
since changes form a chain (`Allowed`). The relational promises of `Effect`
stand beside the frame unchanged: `fresh`, `freshObject`, `elements`,
`ensures`, `receiverGrows`'s `ReceiverGrows` and `ReceiverAppends`,
`elementWrite`'s `ExactWrite`.

**Evaluation at entry.** `Post` reads every region in $`h_0`$. A later write
of a path's field changes which array the path reads, and the frame still
names the entry one; stability of a path's fields is a premise of transport
(§3), never of the meaning.

**Allocation.** A location at or above $`|h_0|`$ is unconstrained.

## 2. Existing effects, translated

Each translation is exact: the same relation on heaps.

| Existing effect | Frame | Evidence |
| --- | --- | --- |
| `Closed` $`\{v,s\}`$ | `cls value: v`, `cls store: s` | `Closed.Holds` is this `Post` (definition) |
| `receiverStore` with $`\{v,s\}`$ | the two, `path 0 [] store: any` | `HoldsOn` off the store, which is unconstrained |
| `receiverOwn` with $`\{v,s\}`$ | the two, `inCls (own 0) value: any` | on an own location the join is `ownChange` $`=\{\mathsf{any},s\}`$, since $`\{v,s\}\le`$ `ownChange` (`Effect.le_ownChange`; proved) |
| `receiverGrows`, `elementWrite` | the rows above for the effect's other fields | `ReceiverGrows`, `ReceiverAppends`, `ElementWrite.Holds` kept as promises |
| chain1 region $`(i,p)`$ with $`\{v,s\}`$ | the two, `path i p store: any` | `ArgumentStoreRegionsWithin` off the store |

`Effect.within` becomes `Post` of the frame at `callEnv r args`, replacing
`footprint`, `receiverStore` and `receiverOwn` by one field; `excPost` takes
the actuals. No translation weakens a promise.

## 3. Composition and preservation

Two judgments use a call's frame, and they differ.

**The enclosing function's obligation.** A body certified at a frame
$`\Phi`$ composes its steps into $`\mathrm{Post}\,\Phi`$ at its own entry heap
(`Post.compose`). A step's region of a slot whose object was allocated after
that entry transports to nothing (`FreshOk`): freshness discharges the
enclosing function's frame, and only that.

**Keeping a current fact.** A fact $`F`$ held before a call is kept where
`stable K F.support Φ_call` holds, $`\Phi_{call}`$ the callee's frame read at
the call's values and heap, $`K`$ the caller's separation knowledge
(`stable_sound`). Freshness relative to the caller's entry refutes nothing
here: in

```ts
/** @modifies xs[*] */ function shrink(xs: number[]): void { xs.pop(); }
function f(): number { const xs = [1]; shrink(xs); return xs[0]!; }
```

`xs` is fresh relative to `f`'s entry, so `shrink`'s write is outside `f`'s
frame obligation, but $`|xs|=1`$ is not kept: its support
`field xs store: grow` meets `path 0 [] store: any` at the call, and no
separation refutes it. Separation from the fact's support is the only
refutation: `StoreApart` (chain1), `RegionsApart` and `HeapSeparation.apart`,
each entering $`K`$.

**Transport premises.** `Post.compose` needs each step's region, read at the
step's heap $`h`$, inside regions read at the entry $`h_0`$:

- `path x p k`, `pathOwn x p`: the path reads the same object in $`h`$ and
  $`h_0`$, by `@stable` fields (`StablePath.read`, chain1; proved) or by the
  slot's provenance table naming the entry path (chain1
  `ArgumentPathTracking.lean`). Otherwise the region transports to `all`.
- `pathElems x p`, `elems x`: as the path, and **cell provenance**: every
  cell the store lists in $`h`$ was listed in $`h_0`$ or lies at or above
  $`|h_0|`$. `keep` and `grow` on the store give it (the last conjunct of
  `Change.Holds .grow`); `any` does not. The native mutators' store steps
  keep it (`Arr.Within`, `FootprintNatives.lean`; proved in the step
  model). Otherwise the region transports as `elems` does today (`cls value`
  under `ElemsValueOk`, else `all`).
- `cell b`: a cell's identity is fixed; it transports to itself.
- `inCls r c`: as $`r`$, intersected with `cls c` as `cls c` transports
  (`cls_back`: a location of class $`c`$ in $`h`$ had it in $`h_0`$ or lies
  in an entry at `any`).
- A nested call: its frame at its actuals, each position renamed to the
  caller's slot holding that value, then the premises above. Chain1's
  `.nested` covers store regions only.
- A callback call: the frame its type states, at its actuals. A closure is
  checked at a type whose frame its body's frame lies within, with each of
  the closure's captured roots named only through a class region, since the
  type names its parameters alone.
- A throw: a call node with an exceptional edge (to a handler or to the
  exit) uses its callee's frame on that edge only where the callee states
  `onThrow`; a normal-only summary gives the exceptional edge no bound, so a
  body stating `@modifies` with such an edge is refused. A handler is
  checked from the heap the throw leaves, related to the entry by the frame
  so far composed with the callee's exceptional frame
  ([exceptional footprints](../SOURCE-ELABORATION.md#exceptional-footprints);
  cited).

**Natives.** A native's frame is its own steps' footprint joined with the
frame, on both exits, of every callback and conversion it may invoke (a
comparator, a `map` callback, a conversion at its contract's frame).
`array_native_post` gives `[store x: grow, cls value: any]` and
`array_native_post_any` the same at `any` (proved): an element write may
change any value-class location, never confined to the receiver's cells. A
row stating `this[*]` needs a theorem from a narrower audited premise (the
native changes only its store and the cells its store lists in $`h_0`$, and
allocates the rest) with `Arr.Within`; its change on the cells is
`{value: any, store: grow}` for `push`, `unshift` and `sort`'s writeback
(`unshift` overwrites present cells), and `any` for `pop`, `shift`,
`reverse` and `splice`. Until that theorem, rows keep today's footprints.

## 4. The clause

A function declaration, arrow, function expression or method states its
frame in its leading JSDoc comment, beside `@requires`
([preconditions](../PROGRAM-TYPING.md#preconditions); cited):

```math
\begin{aligned}
M &::= \texttt{@modifies}\ I\ (\texttt{,}\ I)^{*} \mid \texttt{@modifies nothing}\\
I &::= L \mid L\ \texttt{:}\ c \mid L\ \texttt{: \{value:}\ c\texttt{, store:}\ c\texttt{\}}\\
L &::= b \mid P\texttt{.}f \mid P\texttt{[*]} \mid P\texttt{.*} \mid \texttt{values} \mid \texttt{stores}\\
P &::= x \mid \texttt{this} \mid P\texttt{.}f\\
c &::= \texttt{keep} \mid \texttt{init} \mid \texttt{scalar} \mid \texttt{grow} \mid \texttt{any}
\end{aligned}
```

An item without a change is at `any`; one change $`c`$ stands for
`{value: c, store: c}`, and `{value: v, store: s}` on $`L`$ for the entries
`inCls L value: v` and `inCls L store: s`. $`L`$ maps to `cell`, `path`,
`path store` with `pathElems`, `pathOwn`, `cls value`, `cls store`. A function type states a
frame as a `modifies` member of `Within`'s literal,
`Within<{ value: v; store: s; modifies: "I, I" }, T>`, its class bounds
joined with its items; one function reads both forms (`statedResult`,
`tools/type-term.mts`).

**Binding.** A root $`x`$ is a parameter's name, bound to its position; a
parameter with a default, a rest parameter and a pattern are refused as
roots, since their value in the body is not the call's. `this` is position
$`0`$, refused in an arrow. A module binding is identified by its
declaration's symbol through imports and aliases; its cell is the one the
module's activation allocates, reached by a function as a capture
([slot or cell](../SOURCE-ELABORATION.md#slot-or-cell); cited). At a call,
a callee's `cell b` is the caller's own capture of $`b`$ where it has one,
and its class region otherwise. `values` and `stores` are reserved in this
grammar; a parameter of either name is diagnosed.

**Refusals**, each where read: a path through a field no type resolves; a
traversed field of $`P`$ without `@stable`
([records](../POSITIVE-TYPES.md#records); cited), the final field of
$`P\texttt{.}f`$ excepted; a root of none of the forms above; a clause on a
definition the [stated-effect refusals](../SOURCE-ELABORATION.md#stated-effects)
refuse (async, overloaded, a constructor).

**Checking.** A frame written `@modifies` holds on both exits (`onThrow`
set); a `Within` statement keeps its written `onThrow`. A written clause is
certified by the definition's check over the whole declared domain
(`stated-declaration`, `stated-closure`), never at a call site. Coverage
$`E\le E'`$ is `Footprint.le` with the extended `Region.sub` on each exit:
$`E'`$ stating `onThrow` requires $`E`$ to. Where the body is visible the
producer proposes the frame and Lean checks it; a clause is written only
where no body is checked with the call: an export read by another module,
a function value's type, an import, a native's row.

## 5. Does `modifies` generalise?

The general object is the regional `Footprint` with `Post`. `modifies S` is
one footprint (`any` on $`S`$), a closed footprint another (the class
regions), and the flags, chain1's regions, native rows and caches are
others (§2). It bounds what a call changes; it does not replace the
relational promises (§1), which say how.

"Stable for many operations" is the existing support judgment: a fact
states its support once, each region at the change it tolerates, and every
operation whose frame passes `stable K S Φ` keeps it. The operations proved
stable for a structure are exactly those frames, and the effect-free rule
for a callback using only them is `stable` at its type's frame.

Other forms:

- **Effect polymorphism over callbacks.** A wrapper passing its callback's
  frame through needs frame variables, the callback's frame including its
  captured roots. Outstanding: the separated captured-output accumulation of
  [keeping contract facts across calls](keeping-contract-facts-across-calls.md#certifying-helpers-natives-and-callbacks)
  (`onLine` appending to a captured array) is not met by closed callback
  frames, nor by any frame a callback's type can state without frame
  variables.
- **Separation preconditions**, for an array and a loop in different
  functions (§6.1): atoms of `@requires`, `apart(P, Q)` (regions: store and
  cells, `RegionsApart`) and `storeApart(P, Q)` (stores, chain1
  `StoreApart`). The first gives the second; the converse is never
  inferred. Each enters the unit's entry separation and the signature's
  `pre`; a call establishes it from its knowledge (`call-requires`).
- **Read sets**: a caller computes its facts' supports. Not proposed.

## 6. The examples

### 6.1 The central example

```ts
type Runs = { /** @stable */ readonly openBrackets: number[] };
/** @modifies runs.openBrackets[*], values */
function readRuns(runs: Runs): void { runs.openBrackets.splice(0, 1); }
/** @requires storeApart(flags, runs.openBrackets) */
function measure(flags: number[], runs: Runs): number {
  let sum = 0;
  for (let i = 0; i < flags.length; i++) { readRuns(runs); sum += flags[i]!; }
  return sum;
}
```

`readRuns`: `splice` changes its receiver's store, which lies in
`path 0 [openBrackets] store`, and value-class locations
(`array_native_post_any`; `checkReceiverCall_sound`, chain1; proved). A
regional `splice` row (§3) drops `values`. `measure` keeps
$`i<|\mathit{flags}|`$, support `field flags store: grow`: the call's
store region is refuted by `storeApart`, kept along the loop since
`openBrackets` is stable (`StoreApart.stable_path_frame`, chain1; proved),
and `values: any` keeps every store. Without the precondition,
`measure(xs, { openBrackets: xs })` with `xs = [1, 2, 3]` reads `xs[1]` as
`undefined` and returns `NaN` under Node (run 2026-11-09).

### 6.2 Pretext's script runs (`tscert-bounds`, `src/prepare.ts`)

`ScriptRuns` is `{ read: number, scripts: number, openBrackets: number[] }`.
From the code (conjectured, read at `tscert-bounds`): `readScriptRuns`
reads `runs.openBrackets` once at entry, splices, pushes and writes elements
of that array, writes `runs.read` and `runs.scripts`, and calls
`getScriptFactsAt`, whose `getScriptFacts` initializes the module binding
`scriptClasses` with `??=`. Its frame, with today's native rows:

```text
runs.openBrackets[*], values, scriptClasses: init
```

and the items of `unpackClasses`'s frame. `spaceSharesScriptRun` and
`getUnspacedGraphemes` state the same items at their own `runs`; at
`runs = null` the paths read nothing. None is exported.

`measureAnalysis` allocates the runs itself:
`const scriptRuns: ScriptRuns = { read: 0, scripts: ANY_SCRIPT, openBrackets: [] }`.
The literal `[]` is apart from every older array slot (`region-alloc`;
cited), and the record's allocation gives `storeApart` of
`scriptRuns.openBrackets` from `flags`, `starts` and `texts`
(`ArgumentStoreSeparation.of_separation`, chain1; proved). This is
separation, not freshness: the call's region is read at the call and meets
no supported store. The one source change is `/** @stable */` on
`openBrackets`, which keeps the path across the loop's other calls, whose
frames state `values: any`
([the soundness question](argument-path-regions.md#the-soundness-question);
cited).

### 6.3 Class methods' effects ([method-effects.md](method-effects.md))

A `Within` statement is the class-region frame; D1 (a) holds as decided,
the `modifies` member one more part of the statement, certified by the same
rules and compared by the coverage of §4. D5's rewrites stand; the same
code is admitted as written with `@modifies this.typeParamScopes[*]` on a
stable field. D6 compares an override's frame with its base's by the same
coverage.

### 6.4 Module caches ([keeping-contract-facts-across-calls.md](keeping-contract-facts-across-calls.md))

`getEngineProfile`'s `cachedEngineProfile ??= build()` is
`cachedEngineProfile: init` joined with `build`'s frame. A caller's frame
collects these transitively; it may widen them soundly (`values: init`
covers every cache cell at once, losing which). A private cell of another
module appears in a caller's frame by its identity, or widened. A write to
an object reached through a cache needs its own region. `Map.set` is
`this.*: scalar` where the model places the map's table among the
receiver's own locations.

### 6.5 Footprints ([FOOTPRINTS.md](../FOOTPRINTS.md))

- **Value and store classes**: `values` and `stores`, the class regions.
- **Fresh array storage**: freshness discharges the enclosing obligation
  (§3; `FreshOk`, `Closed.HoldsOn.below_fresh`; cited).
- **Element writes**: `o[k] = v` is within
  `o[*]: {value: any, store: grow}` (`store: keep` at a required
  position) once its write is proved confined to the store's cells; the
  typed write today is a closed footprint.

## 7. Lean obligations

Paths relative to `lean/Verification/`; "chain1" names a file of branch
`chain1-argument-regions`.

- **O1 Regions.** `Region.path`, `pathOwn`, `pathElems`, `cell`, `inCls`, their
  `mem`, `Region.sub` and `transport` cases with the premises of §3
  (`StablePath`, provenance, cell provenance), and `Post.compose` over
  them. Chain1's `ArgumentStoreRegionsWithin` and its `.trans`, `.nested`,
  `.receiver`, `frame_length` become lemmas of `Post` at `path _ _ store`.
- **O2 Effect.** One field `frame : Footprint` replacing `footprint`,
  `receiverStore` and `receiverOwn`; `within` as `Post` at `callEnv`; the
  translations of §2 proved equal to today's `within`.
- **O3 Callee check.** Chain1's provenance table and graph bound
  (`ArgumentPathTracking.lean`, `ArgumentRegionGraph.lean`,
  `ArgumentRegionCertificates.lean`) with node cases for a field write at a
  `path`/`pathOwn` entry, an element write at `pathElems`, a cell write at
  `cell`, a nested call and a callback call (§3), and both exits.
- **O4 Separation.** `SepKnowledge.apart` for the new regions from
  `StoreApart`, `RegionsApart` and `HeapSeparation.apart`; `stable` then
  decides preservation unchanged.
- **O5 Coverage.** `Footprint.le` with the extended `Region.sub`, sound
  against `Post` under `ClassOk`, on both exits; used by `Effect.covers`,
  subtyping and D6.
- **O6 Native rows.** The confinement theorem of §3 from the narrower
  premise and `Arr.Within`.
- **O7 Preconditions.** `apart` and `storeApart` in `Effect.pre`, the
  unit's entry separation and `call-requires`.
- **O8 Acceptance.** `checkUnitJson_safe` keeps its premise and gains, for
  a unit stating a frame, that its runs meet it, beside
  `checkRequests_footprint_at`. The `FunctionPlan` to `CertifiedPlan`
  conversion is unchanged.
- **Wire.** `CallEffect` and the Fragment's `stated` carry the entries;
  decoders require them field by field.

## 8. Trust

A written clause is certified from the body it describes; an imported one is
read under the import assumption as a `Within` statement is. A regional
native row rests on a narrower audited premise than today's (its other
changes confined to the cells its store lists at entry), reviewed by the
owner with O6. A `@stable` field of a value external code builds needs the
checked boundary or explicit contract [records](../POSITIVE-TYPES.md#records)
states.

## 9. Cases

Positive: `modifies-argument-path` (§6.1), `modifies-local-runs` (runs
allocated in the looping function), `modifies-module-cache` (a `??=` cache
keeping a fact elsewhere), `modifies-callback-frame` (a callback type
stating a frame, called in a loop).

Negative, each run under Node: `invalid-modifies-alias` (§6.1 without
`@requires`, `NaN`), `invalid-modifies-fresh-shrink` (§3's `f`),
`invalid-modifies-unstated-write`, `invalid-modifies-path-reassigned` (a
traversed field without `@stable`, reassigned to the counted array between
calls), `invalid-modifies-throw` (a splice before a throw a caller catches),
`invalid-modifies-default-root` (a defaulted parameter's default an older
array the body shrinks).

Forged controls (`pipeline/test.mts`): a frame narrower than the body's
writes; an `apart` or `storeApart` forged at a call that cannot establish
it; an entry rooted at another position; a `cell` naming a same-named
binding of another module; a captured root's write claimed within a
callback type's parameter items; a rest or pattern root; a normal-only
nested summary on a path that throws to the exit, and on one caught by a
handler; an `unshift` row claiming `this[*]: grow`; a `sort` row omitting
its comparator's frame; a stated signature claimed over a narrower domain
than its declaration's; a coverage claim dropping `onThrow`.

## 10. Decisions and open questions

Decisions:

- **Join.** It is `Post`'s meaning (`Allowed`); `receiverOwn` translates
  exactly under it (`Effect.le_ownChange`).
- **One representation.** The frame replaces the three flags; the
  relational promises stay separate fields.
- **`@modifies`, one parser.** Both forms read by `statedResult`; class
  bounds join with items; names bound as in §4.
- **`[*]` is store and cells.** The owner's meaning; the store-only region
  serves exact translations; a cell region needs cell provenance to compose.
- **`@stable` on traversed fields**, refused otherwise; the final written
  field need not be stable.
- **Both exits** for `@modifies`; coverage compares exceptional frames.
- **Two separation atoms**, `apart` stronger, `storeApart` derived from it.
- **Frame variables** for propagation through wrappers, support judgments
  for preservation.
- **Transitive cache effects**, widened soundly where precision is not
  needed.

Open:

- **Q1.** Cell provenance across a store change at `any` (`splice`,
  `pop`): a change between `grow` and `any` that keeps cell provenance, or
  a heap invariant that no store lists an old cell it did not list
  (conjectured of every modelled step; `Arr.Within` proves it for the
  native mutators' store steps).
- **Q2.** The separated captured-output accumulation of `onLine` (§5),
  outstanding until frame variables.
