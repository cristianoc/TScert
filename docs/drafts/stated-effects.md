# Draft: stated effects

A design for one footprint language and one written form of it, `Within`'s
footprint extended with regions, so that every effect a call can have in
TScert can be stated where its function's body is not checked with the call.
Base: TScert main at 56e79063, and the Lean of local branch
`chain1-argument-regions` (05d9d1eb). Claims are labelled **proved** (with
the Lean name and where it lives), **cited** (with the document and its
scope) or **conjectured**.

## The existing mechanism this extends

**The footprint.** The regional footprint of
[footprints](../FOOTPRINTS.md#changes-and-footprints) owns what a step may
change (`Semantics/Footprints.lean`, `FootprintStability.lean`; proved
there):

- a `Footprint` is a list of a `Region` and a `Change`; `Post Φ ρ h h'`
  bounds each location of $`h`$ by the entries covering it, read in $`h`$,
  keeps every location no entry covers, and leaves allocation free;
- a fact's support is a `Footprint` of the regions it reads, each at the
  change it tolerates; `stable K S Φ` decides from `Post Φ` and separation
  knowledge $`K`$ that the fact survives (`stable_sound`);
- steps compose into one footprint at the entry heap, each step's regions
  transported there (`Post.compose`, `transport_sound`).

**The written form.** A [stated effect](../SOURCE-ELABORATION.md#stated-effects)
(cited) is a signature's result `Within<F, T>`, `Within` the declaration of
[`tools/resolvable.d.ts`](../../tools/resolvable.d.ts), with
$`F=\{\mathsf{value}{:}\,v,\ \mathsf{store}{:}\,s[,\ \mathsf{onThrow}]\}`$:
the closed footprint `Closed.Holds`, which is `Post` of the two class
regions (`ClosedFootprints.lean`). One function reads it for every reader
(`statedResult`, `tools/type-term.mts`); a program definition stating it is
certified from its code (`stated-declaration`, `stated-closure`); an
importer reads it under the import assumption; a statement outside the
program's sources (a declaration file, a package) is refused
([fragment boundary](../SOURCE-FRAGMENT.md)).

**Effects with no written form.** An `Effect` (`CallEffects.lean`) holds
more than $`F`$. Each item below works only where its source is: a trusted
native row, or a body TScert analyses, in the file or in an imported
module's run ([certified imports](../SOURCE-CONTRACTS.md#certified-imports);
cited). Across a boundary without a body (a declaration file, a package) it
has no carrier.

| Effect | Lean | Its source today |
| --- | --- | --- |
| the receiver's store excepted, the receiver's own locations | `receiverStore`, `receiverOwn` | native rows (`array-prototype.mts`, `intrinsics.mts`) |
| an append to the receiver's store | `receiverGrows`: `ReceiverGrows`, `ReceiverAppends` | `push`'s row |
| a typed array's element write, exact or not | `elementWrite` | typed-array rows (`intrinsics.mts`, `library-types.mts`) |
| a fresh result | `fresh`, `freshObject` | native rows, `compiler-api.mts`'s request entries |
| a module cell's write | a class bound, `value: init` or wider | the producer, inside the closed footprint |
| stores read through an argument's fields | `ArgumentStoreRegionsWithin` (chain1) | the producer, on chain1 |

A returned closure's footprint (`resultFootprint` of `FunctionClaims`) has
a written form already: the returned function type's own `Within`.
`ensures`, `requires` and `elements` are facts and element kinds rather
than changes; they stay rows of the trusted contracts, outside this design.

## 1. The language

**Regions.** A call's environment $`\rho`$ is `callEnv`: position $`0`$ the
receiver, $`i`$ the $`i`$-th actual. Regions are read in the heap $`h_0`$ the
call starts in. A path $`p=f_1\ldots f_k`$ reads own data fields from
position $`x`$ (`HeapKnowledge.readPath`); a read that fails denotes no
location.

| Region | Locations at $`(\rho,h_0)`$ | |
| --- | --- | --- |
| `field x k`, `own x`, `elems x`, `cls c`, `all` | as today | existing |
| `path x p k` | the own field $`k`$ of the object $`p`$ reads from $`x`$ | `field x k` at $`p=[]`$ |
| `pathOwn x p` | that object's own locations | `own x` at $`p=[]`$ |
| `pathElems x p` | the element cells its store lists | `elems x` at $`p=[]`$ |
| `cell b` | the cell of module binding $`b`$ the function captures | |
| `inCls r c` | the locations of $`r`$ whose contents in $`h_0`$ are of class $`c`$ | |

**The frame.** An effect states a footprint $`\Phi_E`$. A normal return
from $`h_0`$ to $`h'`$ meets $`\mathrm{Post}\,\Phi_E\,\rho\,h_0\,h'`$; a throw
meets it where the effect states `onThrow`, and is otherwise unbounded. A
location several entries cover may change as their join (`Allowed`;
changes form a chain). Regions are read at entry: a later write of a
path's field changes which array the path reads, and the frame still names
the entry one. A location at or above $`|h_0|`$ is unconstrained.

**Promises.** The relational promises stand beside the frame: `fresh`,
`freshObject`, `receiverGrows` (`ReceiverGrows`, `ReceiverAppends`) and
`elementWrite` (`ElementWrite.Holds`), each on normal return only
(`Effect.post`); `Effect.excPost` carries none of them onto a throw.

## 2. The written form

$`F`$ gains two kinds of optional member:

```math
\begin{aligned}
F &::= \texttt{\{ value:}\ v\texttt{; store:}\ s\ [\texttt{; onThrow: true}]\ [\texttt{; at: \{}\ (\texttt{"}L\texttt{":}\ C\texttt{;})^{+}\ \texttt{\}}]\ [\texttt{; }\mathit{promise}]^{*}\ \texttt{\}}\\
C &::= c \mid \texttt{\{ value:}\ c\texttt{; store:}\ c\ \texttt{\}}\\
L &::= b \mid P\texttt{.}f \mid P\texttt{[*]} \mid P\texttt{.*}\qquad P ::= x \mid \texttt{this} \mid P\texttt{.}f\\
\mathit{promise} &::= \texttt{fresh: true} \mid \texttt{freshObject: true} \mid \texttt{appends: true} \mid \texttt{writes: "stores"} \mid \texttt{writes: "exact"}\\
c &::= \texttt{"keep"} \mid \texttt{"init"} \mid \texttt{"scalar"} \mid \texttt{"grow"} \mid \texttt{"any"}
\end{aligned}
```

$`\{v,s\}`$ is `cls value: v`, `cls store: s`, as today; each `at` entry adds
its regions: $`b`$ is `cell b`, $`P.f`$ is `path`, $`P[*]`$ is `path store`
with `pathElems`, $`P.*`$ is `pathOwn`; $`L`$ at a pair
$`\{\mathsf{value}{:}\,c_v,\ \mathsf{store}{:}\,c_s\}`$ is `inCls L value`
at $`c_v`$ and `inCls L store` at $`c_s`$. `appends` is `receiverGrows`,
`writes` is `elementWrite`. A statement adds a guarantee where its frame is
below $`\{\mathsf{any},\mathsf{any}\}`$ or it states a promise; one that
adds none (both class bounds `any`, no promise, whatever its `at` items and
`onThrow`, which add nothing to that frame) is refused as today. A top frame
with a promise is admitted where its promise is (below).

```ts
function readRuns(runs: Runs): Within<{ value: "any"; store: "keep"; at: { "runs.openBrackets[*]": "any" } }, void>
```

**Why `Within` and not a JSDoc tag.** `Within` is a type, so it rides on
every signature TScert reads, a function type's included: a callback
parameter, a field's function, a returned closure, an interface member, a
declaration file's export. A JSDoc tag has no attachment point on a
function type written in a parameter. TypeScript binds `Within` by its
declaration, so recognition is by binding, never by spelling, and
`statedResult` already reads it for every reader, with the fragment's
refusals fencing its positions. Preconditions stay `@requires`
([preconditions](../PROGRAM-TYPING.md#preconditions); cited), which gains
the separation atoms of §5.

**Binding.** A root $`x`$ is a parameter's name, bound to its position; a
parameter with a default, a rest parameter and a pattern are refused as
roots, since their value in the body is not the call's. `this` is position
$`0`$, refused in an arrow. $`b`$ is a [module cell](../SOURCE-ELABORATION.md#module-cells)
of the declaring module, resolved through its declaration's symbol; a name
that resolves to none is refused where read. A traversed field of $`P`$
must be `@stable` ([records](../POSITIVE-TYPES.md#records); cited), the
final field of $`P.f`$ excepted; a path through a field no type resolves
is refused.

**Where a statement is admitted.**

- *A program definition* (its body visible): optional. Written, the whole
  statement is certified from the code over every environment its inputs
  admit (`stated-declaration`, `stated-closure`): the frame, the producer
  proposing it and Lean checking it; `fresh`, by the freshness facts the
  compositional check infers, every return a fresh value (`FreshAt` of the
  entry heap's length on normal return; `compositionalChecked` with `ret`,
  `GraphCode.lean`; proved for code entries). Unwritten, the producer
  infers the effect as today. `freshObject`, `appends` and `writes` have
  no rule certifying them from a body (`effectCheckedResult` refuses each)
  and are refused here and on a function type of the program; they are
  admitted in audited contracts only.
- *A function type of the program* (a parameter, a field, a returned
  closure): every value introduced at it meets it, by the existing
  introductions (closure certification, subtyping, field writes), `fresh`
  included.
- *An import from another module of the program*: read under the import
  assumption ([trust surface](../DESIGN.md#trust-surface)) as the exporting
  module's own run certified it, its promises included.
- *A declaration file or a package*: an **audited contract**. A statement
  there is read only where a reviewed overlay entry pins its declaration
  by origin, package version and heading text, the statement included, as
  [stated library types](../SOURCE-CONTRACTS.md#stated-library-types)
  pin theirs, and the owner has reviewed it against the package's code by
  [modeling a library](../SOURCE-CONTRACTS.md#modeling-a-library): its
  callbacks, conversions and both exits. An unpinned statement is refused
  as today. Each pinned statement is an item of the trust surface; the
  native rows of `tools/*.mts` become such entries written in this form.

## 3. Existing effects, translated

Each translation is the same relation on heaps.

| Existing effect | Frame | Evidence |
| --- | --- | --- |
| `Closed` $`\{v,s\}`$ | `cls value: v`, `cls store: s` | `Closed.Holds` is this `Post` (definition) |
| `receiverStore` with $`\{v,s\}`$ | the two, `path 0 [] store: any` | `HoldsOn` off the store, unconstrained there |
| `receiverOwn` with $`\{v,s\}`$, whether or not `receiverStore` is set | the two, `inCls (own 0) value: any` | on an own location the join is `ownChange` $`=\{\mathsf{any},s\}`$, since $`\{v,s\}\le`$ `ownChange` (`Effect.le_ownChange`; proved) |
| chain1 region $`(i,p)`$ with $`\{v,s\}`$ | the two, `path i p store: any` | `ArgumentStoreRegionsWithin` off the store |

`Effect.within` tests `receiverOwn` first, so with both flags set the
receiver's store, one of its own locations (`storeOf` $`r\in`$ `ownOf` $`r`$),
is bounded at $`s`$; translating `receiverStore` too would add
`path 0 [] store: any` and weaken it. `Effect.within` becomes `Post` of
the frame at `callEnv r args`, one field replacing `footprint`,
`receiverStore` and `receiverOwn`; `excPost` takes the actuals.

## 4. Composition and preservation

**The enclosing function's obligation.** A body certified at a frame
$`\Phi`$ composes its steps into $`\mathrm{Post}\,\Phi`$ at its entry
(`Post.compose`). A step's region of an object allocated after that entry
transports to nothing (`FreshOk`): freshness discharges this obligation,
and only this one.

**Keeping a current fact.** A fact held before a call is kept where
`stable K F.support Φ_call` holds, $`\Phi_{call}`$ the callee's frame at the
call's values and heap, $`K`$ the caller's separation knowledge
(`stable_sound`). In

```ts
function shrink(xs: number[]): Within<{ value: "any"; store: "keep"; at: { "xs[*]": "any" } }, void> { xs.pop(); }
function f(): number { const xs = [1]; shrink(xs); return xs[0]!; }
```

`xs` is fresh relative to `f`'s entry, so `shrink`'s change is within any
frame of `f`, but the fact $`0<|xs|`$, support `field xs store: grow`
(`grow` keeps a dense prefix and so a lower bound, never an exact length),
is not kept: it meets `path 0 [] store: any` and no separation refutes it.
Separation is the only refutation: `StoreApart` (chain1), `RegionsApart`,
`HeapSeparation.apart`, each entering $`K`$.

**Transport.** `Post.compose` needs each step's region, read at the step's
heap $`h`$, inside regions read at the entry $`h_0`$, or inside an earlier
entry at `any` (the second disjunct of `transport_sound`):

- `path x p k`, `pathOwn x p`: the path reads the same object in $`h`$ and
  $`h_0`$, by `@stable` fields (`StablePath.read`, chain1; proved) or the
  slot's provenance table (chain1 `ArgumentPathTracking.lean`); otherwise
  `all`.
- `pathElems x p`, `elems x`: the path's premise, and **cell provenance**:
  every cell the store lists in $`h`$ was listed in $`h_0`$ or lies at or
  above $`|h_0|`$. It is a relational obligation each step proves locally:
  `keep` and `grow` on the store give it (the last conjunct of
  `Change.Holds .grow`; proved); an element write gives it (`placeAt_mem`;
  proved); the native mutators' store steps give it (`Arr.Within`,
  `FootprintNatives.lean`; proved in the step model); it composes by
  transitivity, on both exits. A step with no such proof transports the
  region as `elems` does today: to `cls value` where the array's contract
  makes every element a source value, so each cell is of class `value`
  (`ElemsValueOk`), else to `all`.
- `cell b`: a cell's identity is fixed; it transports to itself.
- `inCls r c`: $`r`$'s transport intersected with `cls c`, keeping
  `cls_back`'s disjunct: a location of class $`c`$ in $`h`$ had it in $`h_0`$
  or lies in an earlier entry at `any`.
- *A nested call*: its frame at its actuals, each position renamed to the
  caller's slot holding that value. A callee's `cell b` is the caller's own
  capture of $`b`$ only under **module-cell agreement**: the module's
  initialization allocates one cell for $`b`$, and every closure of the
  module captures that cell, an invariant preserved by every invocation
  (captures are fixed at creation) and stated by
  [module composition](../../WORK.md#module-composition). Without that
  agreement, from another module, or where $`b`$ has no resolution, `cell b`
  at change $`c`$ widens to `cls value: c`: a cell holds a source value of
  its contract, never a store, so its location is of class `value`. It
  never becomes an empty region.
- *A callback call*: the frame its type states, at its actuals. A closure
  is checked at a type whose frame covers its body's, each captured root
  named only through a class region, since the type names its parameters
  alone.
- *A throw*: a call's exceptional edge (to a handler or to the exit) uses
  the callee's frame only where it states `onThrow`; otherwise the edge has
  no bound, and a body stating `onThrow` with such an edge is refused. A
  handler is checked from the heap the throw leaves
  ([exceptional footprints](../SOURCE-ELABORATION.md#exceptional-footprints);
  cited).

**Natives.** A native's frame is its own steps' footprint joined with the
frame of every callback and conversion it may invoke. Today's rows hold
on normal return only. `array_native_post` gives `[store x: grow, cls value: any]`
and `array_native_post_any` the same at `any` (proved): an element write
may change any value-class location. On normal return `push`'s
`ReceiverGrows` with `ReceiverAppends` gives the narrower
`path 0 [] store: grow` (conjectured; a lemma of O6), where its footprint
row is the global $`\{\mathsf{any},\mathsf{grow}\}`$. A row stating
`this[*]` needs a theorem from a narrower audited premise (the native
changes only its store and the cells its store lists in $`h_0`$, and
allocates the rest) with `Arr.Within`: `{value: any, store: grow}` for
`push`, `unshift` and `sort`'s writeback (`unshift` overwrites present
cells), `any` for `pop`, `shift`, `reverse` and `splice`.

## 5. Generality

The general object is the regional `Footprint` with `Post`: a closed
footprint, the receiver flags, chain1's regions, native rows and module
caches are footprints of it (§3). "Stable for many operations" is the
existing support judgment: a fact states its support once, and every
operation whose frame passes `stable K S Φ` keeps it. A callback using only
operations stable for a structure is effect-free for its facts by `stable`
at its type's frame.

- **Separation preconditions**: atoms of `@requires`, `apart(P, Q)`
  (stores and cells, `RegionsApart`) and `storeApart(P, Q)` (stores, chain1
  `StoreApart`); the first gives the second. Each enters the unit's entry
  separation and `Effect.pre`; a call establishes it from its knowledge
  (`call-requires`).
- **Frame variables**, for a wrapper passing its callback's frame through,
  are deferred. They need closure packaging (a callback's frame including
  its captured roots), substitution at the wrapper's call, and both-exit
  guarantees. Until then the separated captured-output accumulation of
  [keeping contract facts across calls](keeping-contract-facts-across-calls.md#certifying-helpers-natives-and-callbacks)
  (`onLine` appending to a captured array) is not met: no closed callback
  frame states it.

## 6. The examples

### 6.1 The central example

```ts
type Runs = { /** @stable */ readonly openBrackets: number[] };
function readRuns(runs: Runs): Within<{ value: "any"; store: "keep"; at: { "runs.openBrackets[*]": "any" } }, void> {
  runs.openBrackets.splice(0, 1);
}
/** @requires storeApart(flags, runs.openBrackets) */
function measure(flags: number[], runs: Runs): number {
  let sum = 0;
  for (let i = 0; i < flags.length; i++) { readRuns(runs); sum += flags[i]!; }
  return sum;
}
```

`splice` changes its receiver's store, inside `path 0 [openBrackets] store`,
and value-class locations (`array_native_post_any`;
`checkReceiverCall_sound`, chain1; proved), on normal return. `measure`
keeps $`i<|\mathit{flags}|`$, support `field flags store: grow`: the path's
store region is refuted by `storeApart`, kept along the loop since
`openBrackets` is stable (`StoreApart.stable_path_frame`, chain1; proved);
its cells are of class `value`, since `number[]` holds source values, so
they miss `flags`'s store location; `value: any` changes no store. Without
the precondition, `measure(xs, { openBrackets: xs })` with `xs = [1, 2, 3]`
reads `xs[1]` as `undefined` and returns `NaN` under Node (run
2026-11-09). Delivery needs stable-path evidence, the element-class
premise, the checked `storeApart`, actual-argument substitution and the
certified summary.

### 6.2 Pretext's script runs (`tscert-bounds`, `src/prepare.ts`)

Read from the code at `tscert-bounds` (conjectured until the producer
proposes it): `readScriptRuns(runs, …)` reads `runs.openBrackets` once at
entry, then splices it, pushes onto it and writes its elements at computed
indices; writes `runs.read` and `runs.scripts`; and calls
`getScriptFactsAt`, whose `getScriptFacts` evaluates
`scriptClasses ??= unpackClasses(…)` and calls `getClass`. With today's
rows its frame on normal return is

```text
value: any, store: grow, at { runs.openBrackets[*]: any }
```

joined with `unpackClasses`'s and `getClass`'s frames: `store: grow` from
the element writes (`elem-write-slot`, a closed footprint) and `push`'s
row; `value: any` from the element writes and `splice`, and it covers
`scriptClasses: init` and the two field writes, which then add no
precision. None of the native rows states `onThrow`, so the frame holds on
normal return only; `measureAnalysis` catches nothing, so its facts need
only normal edges. `spaceSharesScriptRun` adds `hasProperty`'s frame, and
`getUnspacedGraphemes` `findGraphemeEnds`'s and its fresh `Int32Array`'s
and fresh `unspaced` array's; each is its body's transitive frame, the
imports' at their certified or stated signatures. At `runs = null` the
paths read nothing.

`measureAnalysis` allocates the runs:
`const scriptRuns: ScriptRuns = { read: 0, scripts: ANY_SCRIPT, openBrackets: [] }`.
The literal `[]` is apart from every older array slot (`region-alloc`;
cited), so the record's allocation gives `storeApart` of
`scriptRuns.openBrackets` from `flags`, `starts` and `texts`
(`ArgumentStoreSeparation.of_separation`, chain1; proved). A loop fact on
those arrays' lengths, support at `grow`, is then kept: `store: grow`
tolerates it, `value: any` misses stores, the path region is apart, the
cells are value-class. The stable link from `scriptRuns` to its array is
`/** @stable */` on `openBrackets`, since the loop's other calls state
`value: any`, which covers the field
([the soundness question](argument-path-regions.md#the-soundness-question);
cited). It is the one source change this separation needs.

The loop's facts are kept only if the complete joined summaries of the
helpers it calls change the protected stores (those of `flags`, `starts`
and `texts`) at `grow` or less. Read from the code at `tscert-bounds`
(conjectured), each helper's frame meets it:

- `readScriptRuns`: `push` (`grow`), `splice` at the apart
  `runs.openBrackets[*]`, element writes (closed $`\{\mathsf{any},\mathsf{grow}\}`$),
  the fields `read` and `scripts` (value class).
- `getScriptFacts`, `unpackClasses`, `unpackClassRuns`, `getClass`: the
  cells `scriptClasses`, `classRuns`, `classRemaps` at `init`; writes and
  `fill` on typed arrays they allocate, discharged by freshness.
- `hasProperty`: the cell `bmpProperties` at `init`, element writes on that
  `Uint16Array`, `astralProperties.set`, and `lazyRegExp`'s closure, its
  cell `built` at `init` and `RegExp.prototype.test`.
- `findGraphemeEnds`: the field of the record `graphemeRules` and
  `getBreakRules`'s `breakRules` (value class), the typed arrays
  `parseGraphemeRules` allocates, element writes on `ends`, an `Int32Array`
  its caller allocates.
- `getUnspacedGraphemes`: the frames of `findGraphemeEnds` and
  `readScriptRuns`, and `push` onto its fresh `unspaced`.

Unverified: the producer's summaries of these bodies, Lean-checked, and
the native rows these frames rest on (`Map.prototype.set` with its table
among the map's own locations, §6.4; `RegExp.prototype.test`; typed
arrays' element writes, `fill` and `subarray`), each changing no store
beyond `grow`.

### 6.3 Class methods' effects ([method-effects.md](method-effects.md))

A method's `Within` is its frame; D1 (a) holds as decided, `at` one more
part of the statement, certified by the same rules and compared by the
coverage of O8. D5's code is admitted as written with
`at: { "this.typeParamScopes[*]": "any" }` on a stable field. D6 compares
an override's frame with its base's by that coverage.

### 6.4 Module caches ([keeping-contract-facts-across-calls.md](keeping-contract-facts-across-calls.md))

`getEngineProfile`'s `cachedEngineProfile ??= build()` is
`at: { "cachedEngineProfile": "init" }` joined with `build`'s frame. A
caller collects these transitively, or widens them (`value: init` covers
every cell at once). From another module a cell is the widened class
region (§4). A write to an object reached through a cache needs its own
region. `Map.set` is `this.*: scalar` where the model places the map's
table among the receiver's own locations.

### 6.5 Footprints ([FOOTPRINTS.md](../FOOTPRINTS.md))

- **Value and store classes**: $`\{v,s\}`$.
- **Fresh array storage**: freshness discharges the enclosing obligation
  (§4; `FreshOk`, `Closed.HoldsOn.below_fresh`; cited).
- **Element writes**: `o[k] = v` is within
  `o[*]: {value: any, store: grow}` (`store: keep` at a required position)
  once its write is proved confined to the store's cells; today it is the
  closed $`\{\mathsf{any},\mathsf{grow}\}`$
  ([element writes](../FOOTPRINTS.md#element-writes); cited).

## 7. Stating effects to save module runs

Conjectured (the owner's expectation, unmeasured): a caller in another file
that reads an import at its written effect needs no analysis of the
import's module, so a stated export makes checking its importers cheaper.
Today the parser lowers every module the checked file imports a function
from, transitively ([certified imports](../SOURCE-CONTRACTS.md#certified-imports)),
so a stated import saves the module's run only where the parser also
leaves out a module none of whose imports is read qualified. The
measurement that settles it: on pretext at `tscert-bounds`, with the
helpers `prepare.ts` imports (`unpackClasses`, `getClass`, `hasProperty`,
`findGraphemeEnds`) stated and not, the stage time per file and the stages
replayed and executed after a body-only edit of an imported module
(`invocations.jsonl`), with the verified function count unchanged.

## 8. Lean obligations

Paths relative to `lean/Verification/`; "chain1" names a file of branch
`chain1-argument-regions`.

- **O1 Regions.** `Region.path`, `pathOwn`, `pathElems`, `cell`, `inCls`:
  `mem`, `Region.sub`, and `transport` with §4's premises and the
  earlier-`any` disjunct of `transport_sound`; `Post.compose` over them.
  Chain1's `ArgumentStoreRegionsWithin` and its `.trans`, `.nested`,
  `.receiver`, `frame_length` become lemmas of `Post` at `path _ _ store`.
- **O2 Effect.** One field `frame : Footprint` replacing `footprint`,
  `receiverStore` and `receiverOwn`; `within` as `Post` at `callEnv`; §3's
  translations proved equal to today's `within`, `receiverOwn` first.
- **O3 Cell provenance.** A relation `CellsFrom h₀ h x p` and its proof for
  primitive writes, native steps and composition, on both exits; the
  `elems` fallback where it is missing.
- **O4 Module cells.** Module-cell agreement as an invariant of the module
  environment, within module composition; the widening to `cls value`
  where it is not established.
- **O5 Callee check.** Chain1's provenance table and graph bound
  (`ArgumentPathTracking.lean`, `ArgumentRegionGraph.lean`,
  `ArgumentRegionCertificates.lean`) with node cases for a field write at
  a `path`/`pathOwn` entry, an element write at `pathElems`, a cell write,
  a nested call and a callback call, on both exits.
- **O6 Natives.** `push`'s narrower normal-return frame from
  `ReceiverGrows` and `ReceiverAppends`; the confinement theorem of §4
  from the narrower premise and `Arr.Within`.
- **O7 Separation.** `SepKnowledge.apart` for the new regions from
  `StoreApart`, `RegionsApart` and `HeapSeparation.apart`, with the
  element-class premise for `pathElems`; `apart` and `storeApart` in
  `Effect.pre`, the unit's entry separation and `call-requires`.
- **O8 Coverage.** `Footprint.le` with the extended `Region.sub`, sound
  against `Post` under `ClassOk`, on both exits; used by `Effect.covers`,
  subtyping and D6.
- **O9 Acceptance.** `checkUnitJson_safe` keeps its premise and gains, for
  a unit stating a frame, that its runs meet it, beside
  `checkRequests_footprint_at`. The `FunctionPlan` to `CertifiedPlan`
  conversion is unchanged.
- **O10 Promises.** The whole statement checked and proved: `statedWithin`
  compares `fresh` and its "adds a guarantee" test replaces
  `s.footprint != .top`; a declaration stating `fresh` runs the
  compositional check with `ret`, and `checkRequests_stated_at` gains
  `FreshAt` of the entry heap's length on normal return over its full
  domain; closures as `effectCheckedResult` checks them; the export's
  certified signature carries `fresh` to importers; acceptance (O9)
  includes it. `freshObject`, `appends` and `writes` refused outside
  audited contracts.
- **Wire.** `CallEffect` and the Fragment's `stated` carry the entries and
  promises; decoders require them field by field.

## 9. Trust

A statement on a program definition is certified from its code; an
imported one is read under the import assumption. A statement in a
declaration file or a package is an audited contract, pinned and reviewed
by the owner (§2), and a trust-surface item; `freshObject`, `appends` and
`writes` are stated there only. A regional native row rests on
a narrower audited premise than today's (its changes confined to its store
and the cells its store lists at entry), reviewed with O6. A `@stable` field
of a value external code builds needs the checked boundary or explicit
contract [records](../POSITIVE-TYPES.md#records) states.

## 10. Cases

Positive: `stated-argument-path` (§6.1), `stated-local-runs` (runs
allocated in the looping function), `stated-module-cache` (a `??=` cache
keeping a fact elsewhere), `stated-callback-frame` (a callback type stating
a frame, called in a loop), `stated-package-contract` (a pinned statement
in a package's declaration file), `stated-top-fresh` (a builder stating
`fresh: true` at `{value: "any", store: "any"}`).

Negative, each run under Node: `invalid-stated-alias` (§6.1 without
`@requires`, `NaN`), `invalid-stated-fresh-shrink` (§4's `f`),
`invalid-stated-unstated-write`, `invalid-stated-path-reassigned` (a
traversed field without `@stable`, reassigned to the counted array between
calls), `invalid-stated-throw` (a splice before a throw a caller catches,
at a frame claiming `onThrow`), `invalid-stated-default-root`, and an
unpinned statement in a declaration file.

Forged controls (`pipeline/test.mts`): a frame narrower than the body's
writes; `apart` or `storeApart` forged at a call that cannot establish it;
an entry rooted at another position; a `cell` naming a same-named binding
of another module, and one substituted exactly without agreement; a
`pathElems` transported to `cls value` without the element-class premise;
both receiver flags translated independently; a captured root's write
claimed within a callback type's parameter items; a normal-only nested
summary on a path that throws to the exit, and one caught by a handler; a
function returning its input stated `fresh: true` within
`{value: "keep", store: "keep"}`, its claims forged to carry the promise; an
`unshift` row claiming `this[*]: grow`; a `sort` row omitting its
comparator's frame; `appends` and `freshObject` on a program definition; a
`{value: "any", store: "any"}` statement with no promise; a coverage claim
dropping `onThrow`.

## 11. Decisions and open questions

Decisions:

- **One language.** The regional `Footprint` read by `Post`; the frame
  replaces the three flags; the relational promises stay separate fields.
- **One written form.** `Within`'s $`F`$ with `at` and promise members,
  read by `statedResult`; preconditions in `@requires`.
- **Optional where a body is visible**, certified from it whole, `fresh`
  included; an audited, pinned contract where none is, and for
  `freshObject`, `appends` and `writes`.
- **Refused only without a guarantee**: a top frame with no promise.
- **`onThrow` as written**, normal return otherwise, as `Within` today.
- **`[*]` is store and cells**; the store-only region serves translations.
- **`@stable` on traversed fields**; the final field need not be.
- **Module cells**: exact under agreement, the class region otherwise.
- **Cell provenance**: a checked local obligation, the class fallback
  without it.

Open:

- **Q1.** Cell provenance across a store change at `any` (`splice`,
  `pop`) beyond the native steps `Arr.Within` covers.
- **Q2.** Frame variables, for the captured-output accumulation of §5.
- **Q3.** Whether stated imports save module runs (§7).
