# Draft: what a call may change

A design for stating and checking the locations a call may change, for
review with Astra. Base: TScert main at 56e79063, and the Lean of local
branch `chain1-argument-regions` (05d9d1eb). Claims are labelled **proved**
(with the Lean name and where it lives), **cited** (with the document and
its scope) or **conjectured**.

## The existing mechanism this extends

Two rows of [the general mechanisms](../DESIGN.md#general-mechanisms) own
the concern, and this design is one extension of both:

- **What a call may change** is an effect-qualified signature
  ([inferred call effects](../SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification);
  cited): proposed by the producer, proved from the callee's code, consumed
  at a call; written at a boundary as a
  [stated effect](../SOURCE-ELABORATION.md#stated-effects),
  `Within<F, T>`.
- **A fact kept across a call** is a [footprint](../FOOTPRINTS.md): the
  fact with the locations it reads, the closed footprints proved to keep it
  (`stable_sound`, `FootprintStability.lean`; proved), Lean certifying code
  within them node by node.

An effect's frame (`Effect.within`, `CallEffects.lean`) is a closed
footprint $`\Phi=\{\mathsf{value}{:}\,\delta_v,\ \mathsf{store}{:}\,\delta_s\}`$
over every old location, with three special cases written as flags: the
receiver's store excepted (`receiverStore`), the receiver's own locations
at their own change (`receiverOwn`), and the receiver's store grown by the
actuals (`receiverGrows`). The branch `chain1-argument-regions` adds a
fourth, stores reached from any call position through a path of fields
(`ArgumentStoreRegionsWithin`, `ArgumentStoreRegions.lean`; proved there,
not reached from acceptance). This design states all of them as one
object: a change for each location set a call names, every other old
location kept.

## 1. The meaning

**Location sets.** A location set $`L`$ is read in the heap $`h_0`$ and the
call's values $`\rho`$ (position $`0`$ the receiver, $`i`$ the $`i`$-th
actual) the call starts with. A path $`P=x.f_1\ldots f_k`$ reads the fields
from a root $`x`$ (a parameter, `this`) in $`h_0`$
(`HeapKnowledge.readPath`); a read that fails denotes no location.

```math
\begin{aligned}
⟦b⟧ &= \{\text{the cell of module binding } b\}\\
⟦P.f⟧ &= \{\text{the location of the own data field } f \text{ of the object } P \text{ reads}\}\\
⟦P[*]⟧ &= \{s\}\cup\{l \mid \mathsf{some}\,l\in ls\},\quad s=\mathrm{store}(P),\ h_0[s]=\mathsf{arr}\,ls\\
⟦P.*⟧ &= \mathrm{own}(P)\\
⟦\mathsf{values}⟧ &= \{l<|h_0| \mid \mathrm{class}(h_0[l])=\mathrm{value}\},\qquad
⟦\mathsf{stores}⟧ = \{l<|h_0| \mid \mathrm{class}(h_0[l])=\mathrm{store}\}
\end{aligned}
```

$`⟦P[*]⟧`$ is the region of [element regions](../FOOTPRINTS.md#element-regions)
(`RegionOf`; cited): the array's store location and the element cells it
lists.

**The frame.** An effect $`E`$ is a finite list of items $`L_k:\Phi_k`$, a
location set with a closed footprint. Each old location may change at most
as the join of the items containing it, and a location in no item keeps its
contents:

```math
\delta_E(l)=\bigsqcup\{\Phi_k \mid l\in⟦L_k⟧(\rho,h_0)\},\qquad \textstyle\bigsqcup\varnothing=\{\mathsf{value}{:}\,\mathsf{keep},\ \mathsf{store}{:}\,\mathsf{keep}\}
```

```math
\mathrm{Fr}_E(\rho,h_0,h') \iff |h_0|\le|h'|\ \land\ \forall l<|h_0|.\ \delta_E(l)_{\mathrm{class}(h_0[l])\,|h_0|}\bigl(h_0[l],h'[l]\bigr)
```

The join is entrywise, in the chain
$`\mathsf{keep}\sqsubseteq\mathsf{init}\sqsubseteq\mathsf{scalar}\sqsubseteq\mathsf{grow}\sqsubseteq\mathsf{any}`$
([changes](../FOOTPRINTS.md#changes-and-footprints); cited). The existing
effects are instances:

| Existing effect | Items |
| --- | --- |
| a closed footprint $`\{v,s\}`$, `Within<{value: v; store: s}, T>` | `values: v`, `stores: s` |
| `receiverStore` with $`\Phi`$ | $`\Phi`$'s two items, `this[*]: any` |
| `receiverOwn` with $`\Phi`$ and own change $`\chi`$ | $`\Phi`$'s two items, `this.*:` $`\chi`$ |
| an argument store region $`(i,p)`$ with $`\Phi`$ (chain1) | $`\Phi`$'s two items, $`x_i.p`$`[*]: any` |
| `@modifies runs.openBrackets[*]` | `runs.openBrackets[*]: any` |

The flags read a location in the specific item at its own change alone; the
join reads it at that change joined with $`\Phi`$'s for its class. The two
agree where the own change is at least $`\Phi`$'s (conjectured for every
signature stating `receiverOwn`; obligation O1).

**Evaluation at entry.** Every set is read once, in $`h_0`$. A later write
of a path's field changes which array the path reads, and the frame still
names the entry one. Stability of a path's fields is a requirement of the
rules (§5), never of the meaning.

**Allocation.** A location at or above $`|h_0|`$ is unconstrained. A fresh
result (`fresh`, `freshObject`) is a promise about the returned value,
unchanged by this design.

**Exceptions.** A frame stated with `@modifies` holds on normal return and
on a throw, from the entry heap (`SafePostExc`,
[exceptional footprints](../SOURCE-ELABORATION.md#exceptional-footprints);
cited): its `onThrow` is set. A `Within` statement keeps its written
`onThrow`.

**Callbacks.** A call of a function value is at the frame its type states,
read at that call's values; a frame whose items are rooted at the function
type's own parameters is substituted at the actuals the body passes. A
higher-order function's frame covers each callback call it makes. A native
taking a callback states closed footprints alone (§3).

## 2. The clause

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
`{value: c, store: c}`, `grow` on a location holding no store being
`scalar`.
A function type states a frame as a third member of `Within`'s literal,
`Within<{ value: v; store: s; modifies: "I, I" }, T>`, read by the same
item grammar, so a callback's type, a method field and `typeof f` carry it;
`@modifies` on a declaration is that statement of its result. One function
reads both (`statedResult`, `tools/type-term.mts`).

Refused, each where it is read: a path through a field no type resolves; a
path $`P`$ in $`P\texttt{.}f`$, $`P\texttt{[*]}`$ or $`P\texttt{.*}`$ any
field of which is not `@stable` ([records](../POSITIVE-TYPES.md#records);
cited); a root that is neither a parameter, `this` nor a module binding; a
clause on a definition the [stated-effect refusals](../SOURCE-ELABORATION.md#stated-effects)
refuse (async, overloaded, a constructor).

Where the body is visible the producer proposes the frame and Lean checks
it; a written clause is needed only where no body is checked with the call:
an export read by another module, a function value's type, an import, a
native's row.

## 3. Does `modifies` generalise?

**Recommendation.** The general object is the frame of §1: a change bound
for each entry location, an upper bound. `modifies S` is one frame (`any` on
$`S`$), a closed footprint another (constant on each class), and every
effect flag, native row and lazy cache below is one too; one meaning
replaces four special cases. "Stable for a fact" is a judgment about a
frame, decided by the caller, and needs no annotation of its own:

```math
\frac{F\in\Sigma\qquad K=\{k \mid ⟦L_k⟧\cap\mathrm{rd}(F)\neq\varnothing \text{ not refuted by }\Sigma\}\qquad \mathrm{stable}\bigl(F,\ \textstyle\bigsqcup_{k\in K}\Phi_k\bigr)}
     {F\ \text{holds after a call at}\ E}\ \textsf{frame-kept}
```

with $`\mathrm{rd}(F)`$ the locations $`F`$ reads and $`\mathrm{stable}`$
the existing stability check (`stable_sound`; proved). A set is refuted by
separation facts ([separation facts](../PROGRAM-TYPING.md#separation-facts),
`StoreApart`, `apart`), by class (an element cell is never a store) and by
freshness (a set read at a store allocated after the caller's entry).

Each candidate generalisation, and what it is for:

- **The dual, "preserves $`S`$" (a complement set).** Needed where the
  consumer names the fact and the callee is unknown: `map` keeping its
  receiver dense across a callback whose frame changes another array's
  store. Its callback's type would name the receiver of the call that
  receives it, a dependent signature. No site of chain 1 or of the drafts
  below needs it; `map`, `forEach` and the other natives keep one signature
  per closed footprint. Deferred (Q8).
- **Read sets.** A caller computes $`\mathrm{rd}(F)`$ of its own facts, so
  framing needs no read clause on the callee. Not proposed.
- **Effect polymorphism over callbacks.** A wrapper passing its callback's
  frame through (`forEach(f)` at "whatever $`f`$ changes") needs frame
  variables. Native wrappers enumerate closed footprints today; a
  program wrapper with a regional callback is the first need (pretext's
  `onLine`, which states no region). Deferred (Q8).
- **Separation preconditions.** Needed where the array and the loop are in
  different functions (§4.1). Proposed as an atom of `@requires`: the
  existing precondition mechanism and unit entry separation
  (`Request.entrySeparation`; cited).
- **Two-state facts** (`|xs|` unchanged by a pop followed by a push): beyond
  an upper bound on locations; a frame item `xs[*]: any` loses the length.
  No surveyed site needs it. Not proposed.

## 4. The examples

### 4.1 The central example

```ts
type Runs = { /** @stable */ readonly openBrackets: number[] };
/** @modifies runs.openBrackets[*] */
function readRuns(runs: Runs): void { runs.openBrackets.splice(0, 1); }
/** @requires apart(flags, runs.openBrackets) */
function measure(flags: number[], runs: Runs): number {
  let sum = 0;
  for (let i = 0; i < flags.length; i++) { readRuns(runs); sum += flags[i]!; }
  return sum;
}
```

`readRuns`: the body's one change is `splice` on the store of a slot read
from `runs.openBrackets` at entry, a call at the receiver-store effect
whose receiver's store is in $`⟦\mathtt{runs.openBrackets[*]}⟧`$
(`checkReceiverCall_sound`, chain1; proved). `measure` keeps
$`i<|\mathit{flags}|`$ across the call where the store of `flags` is not
in that set: `apart(flags, runs.openBrackets)` at entry, kept along the loop
since `openBrackets` is stable (`StoreApart.stable_path_frame`, chain1;
proved). Both `flags` and `runs` are parameters, so the fact crosses the
boundary as a precondition, and each caller establishes it. Without it,
`measure(xs, { openBrackets: xs })` with `xs = [1, 2, 3]` reads `xs[1]` as
`undefined` and returns `NaN` under Node (run 2026-11-09).

The atom: `apart(P, Q)`, $`P`$ and $`Q`$ paths of the clause grammar at
array types, states $`\mathrm{apart}`$ of their regions in the entry heap
([element regions](../FOOTPRINTS.md#element-regions); cited). It enters the
unit's entry separation and the signature's `pre`, and a call establishes
it from its knowledge (`call-requires`).

### 4.2 Pretext's script runs (`tscert-bounds`, `src/prepare.ts`)

`ScriptRuns` is `{ read: number, scripts: number, openBrackets: number[] }`.
From the code (conjectured, read at `tscert-bounds`): `readScriptRuns`
reads `runs.openBrackets` once at entry (`const { openBrackets } = runs`),
then splices, pushes and writes elements of that array, writes the number
fields `runs.read` and `runs.scripts`, and calls `getScriptFactsAt`, whose
`getScriptFacts` initializes the module binding `scriptClasses` with `??=`.
Its proposed frame is

```text
runs.read, runs.scripts, runs.openBrackets[*], scriptClasses: init
```

with the items of `unpackClasses`'s frame. `spaceSharesScriptRun` and
`getUnspacedGraphemes` call it with their own `runs`, so their frames are
the same items at their parameter; `getUnspacedGraphemes`'s `runs` is
`ScriptRuns | null`, and at `null` the path reads nothing and the sets are
empty. None of the three is exported, so none needs a written clause.

`measureAnalysis` allocates the runs itself (line 423):
`const scriptRuns: ScriptRuns = { read: 0, scripts: ANY_SCRIPT, openBrackets: [] }`.
The literal `[]` is apart from every older array slot, `flags`, `starts`
and `texts` read from `analysis` included (`region-alloc`; cited), and the
record's allocation gives $`\mathrm{storeApart}`$ of
`scriptRuns.openBrackets` from each (`ArgumentStoreSeparation.of_separation`,
chain1; proved); `read` and `scripts` are fresh fields, apart from every
older field (`sep-alloc`; cited). So separation does not cross a function
boundary at these calls, and the one source change is
`/** @stable */ readonly openBrackets: number[]` in `ScriptRuns`, which no
code reassigns. The stable field is what keeps the path across the loop's
other calls, whose frames state `values: any` (the measurement helpers): in
the model such a call may write any old object into
`scriptRuns.openBrackets`
([the soundness question](argument-path-regions.md#the-soundness-question);
cited).

### 4.3 Class methods' effects ([method-effects.md](method-effects.md))

A `Within` statement is the frame `values: v, stores: s`; D1 (a) holds as
decided, with the `modifies` member as one more part of the statement,
certified by the same rule (`stated-declaration`, `stated-closure`) and
compared by the same coverage: $`E\le E'`$ where every location's bound
under $`E`$ is within its bound under $`E'`$, decided item by item from
the sets' syntax (§5, O4). D5's rewrites (`Gate`'s `shift`s into field
writes) are the form this design would also admit as written,
`@modifies this.typeParamScopes[*]` on a stable field; the rewrites stand.
D6 (an override checked against its base's statement) reads frames by the
same coverage.

### 4.4 Module caches ([keeping-contract-facts-across-calls.md](keeping-contract-facts-across-calls.md))

`getEngineProfile`'s `cachedEngineProfile ??= build()` is
`cachedEngineProfile: init` with `build`'s items. Today's
`{value: init, store: keep}` keeps facts reading locations holding a
defined value; the item keeps every fact not reading that cell. A
measurement helper writing `measurement.spaceKerning` states that item.
`Map.set` is `this.*: scalar` where the model places the map's table and
size among the receiver's own locations, which the draft names as its
condition. `onLine` is a callback at a stated closed footprint; regional
accumulation is Q8. Default parameters are preconditions, outside this
design.

### 4.5 Native footprints ([native-footprints-from-steps.md](native-footprints-from-steps.md))

The audited premise "changes nothing but its store and element contents"
is the item `this[*]`, and the step sequences prove the change on it:
`push` and `unshift` `this[*]: grow`, `sort`'s writeback
`this[*]: {value: any, store: grow}` (`Arr.push_grow`,
`Arr.unshift_grow`, `sort_grow`, `FootprintNatives.lean`; proved in the
step model), `pop`, `shift`, `reverse`, `splice` `this[*]: any`. The
native's row then states its set; the derivation computes the item's
change.

### 4.6 Footprints ([FOOTPRINTS.md](../FOOTPRINTS.md))

- **Value and store classes**: `values` and `stores`, the closed
  footprints' own split.
- **Fresh array storage**: a receiver-store call on a fresh receiver is
  within the caller's frame because its set lies at or above the caller's
  entry length (`FreshOk`, `Closed.HoldsOn.below_fresh`; cited); a set read
  from a fresh slot is refuted the same way in `frame-kept`.
- **Element writes**: `o[k] = v` is within
  `o[*]: {value: any, store: grow}` (at a required position
  `store: keep`), a set narrower than `values: any, stores: grow`.
- **The vision** (operations proved stable for a structure make the
  effect-free rule sound for callbacks using only them): the stable
  operations for a fact $`F`$ are the frames for which `frame-kept` keeps
  $`F`$; closed footprints are the frames a native's callback signature can
  name without naming the receiver.

## 5. Lean obligations

Paths relative to `lean/Verification/`; "chain1" names a file of branch
`chain1-argument-regions`.

- **O1 Semantics.** `Frame` (a list of a location set and a `Closed`) with
  `Frame.Holds ρ h₀ h'` as §1, generalizing `ArgumentStoreRegionsWithin`
  (chain1 `Semantics/ArgumentStoreRegions.lean`) from store regions at
  `any` to the five set forms at any footprint. `Effect.within` reads the
  frame; lemmas show `receiverStore`, `receiverOwn` and plain footprints
  read as before (exactly, or the signatures where the join differs are
  listed). Reused: `.trans`, `.nested`, `.receiver`, `.frame_length`,
  `.frame_densePrefix`, `StablePath` and its `transfer`, `read`, `frame`.
- **O2 Callee check.** The provenance table of chain1
  `Programs/ArgumentPathTracking.lean` (slots holding an entry path's
  value) and the graph bound of `Programs/ArgumentRegionGraph.lean`
  (`bounded_step`, `goto_bounded`, cycles and caught throws) and
  `Programs/ArgumentRegionCertificates.lean` (`checkNodes_sound`,
  `checkEntry_sound`). New node cases: a typed field write through a
  tracked slot at a `P.f` or `P.*` item; an element write at a `P[*]`
  item; a module cell write at a `b` item; a nested call whose frame, read
  at its actuals, lies within the body's (chain1 lists field-read
  provenance and nested argument-path calls as unsupported); a callback
  call at its type's frame. `GraphCodeSpec` at the frame's values
  (`FrameValues`, `graph_invoke_at`, chain1 `GraphCode.lean`; proved).
- **O3 Caller frame.** `frame-kept` over the existing stability check,
  with refutation by `StoreApart` (chain1
  `Programs/ArgumentStoreSeparation.lean`: `checkFrame_sound`,
  `frame_length`, `of_separation`, `prepend`), `HeapSeparation.apart` for
  field sets, `RegionsApart` for `[*]` sets read by element facts, and
  freshness.
- **O4 Coverage.** $`E\le E'`$ decided syntactically (each item of $`E`$
  inside an item of $`E'`$ of a larger footprint, `values`/`stores`
  covering every set of their class), proved sound against `Frame.Holds`;
  used by `Effect.covers`, subtyping and D6.
- **O5 Preconditions.** `apart(P, Q)` in `Effect.pre`, the unit's entry
  separation and `call-requires`.
- **O6 Acceptance.** `checkUnitJson_safe` keeps its premise and gains, for
  a unit stating a frame, that its runs meet it, beside
  `checkRequests_footprint_at`. The `FunctionPlan` to `CertifiedPlan`
  conversion is unchanged: a frame is part of an effect, never a plan.
- **Wire.** `CallEffect` and the Fragment's `stated` carry the items;
  decoders require them field by field.

## 6. Trust

None added. A written clause is certified from the body it describes; an
imported one is read under the import assumption as a `Within` statement
is ([stated effects](../SOURCE-ELABORATION.md#stated-effects); cited). The
native rows restate their audited premise as a set (§4.5), the same
audit. A `@stable` field of a value external code builds needs the checked
boundary or explicit contract [records](../POSITIVE-TYPES.md#records)
states.

## 7. Cases

Positive: `modifies-argument-path` (§4.1), `modifies-local-runs` (the
pretext shape: runs allocated in the looping function, no precondition),
`modifies-module-cache` (a `??=` cache keeping a fact reading a `null`
location elsewhere), `modifies-callback-frame` (a callback type stating a
frame, called in a loop).

Negative, each run under Node:
`invalid-modifies-alias` (§4.1 without `@requires`, `NaN`),
`invalid-modifies-unstated-write` (a body writing `runs.read` under a
clause omitting it, refused at the definition),
`invalid-modifies-path-reassigned` (the path's field not `@stable`,
reassigned to the counted array between calls),
`invalid-modifies-throw` (a splice before a throw a caller catches).

Forged controls (`pipeline/test.mts`): a frame claimed narrower than the
body's writes, through search and checking; an `apart` entry fact forged
at a call that cannot establish it; a frame item rooted at a different
position.

## 8. Open questions

- **Q1.** Is the join of §1 the meaning, or does a specific item override
  a class item (the flags' reading)? The join is monotone and needs no
  order of sets; overriding states `receiverOwn` exactly.
- **Q2.** Does `Effect` replace `receiverStore`, `receiverOwn` and
  `receiverGrows`'s frame part by the item list in one change, or carry
  the list beside them?
- **Q3.** Spelling: `@modifies` on declarations and a `modifies` member of
  `Within`'s literal in types, both read by one function. Are `values` and
  `stores` the right words, refused where a parameter has that name?
- **Q4.** `P[*]` holds the element cells. Chain1 proves store-only regions,
  and Astra's earlier review names cell regions a separate extension with
  transport obligations. Does the first version state `[*]` as store and
  cells, or store only with cell writes at `values`?
- **Q5.** `@stable` on every field of a path: a refusal of the clause, or
  only a requirement of the caller's and callee's rules, with an unstable
  path stated but never framed through?
- **Q6.** Does `@modifies` always hold on a throw, or does it take
  `onThrow` as `Within` does?
- **Q7.** `apart(P, Q)` states the regions apart (store and cells). Length
  facts need only distinct stores. Is one atom right?
- **Q8.** Regional frames of callbacks: deferred until a site needs one.
  Is the dependent "preserves the receiver" signature for natives the
  right form then, or frame variables?
- **Q9.** The proposed frame of `readScriptRuns` lists `scriptClasses`
  and `unpackClasses`'s items. Does the producer's frame grow with every
  module cache a callee initializes, and does a caller need those items at
  all beyond `init`?
