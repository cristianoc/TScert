# Draft: abstract confined regions for user-defined heap abstractions

A design for framing heap mutations inside user-defined abstractions (classes
such as `FastMap<K, V>`, `LruCache<K, V>`, `Arena<T>`, and module-private
caches) and built-in collections (`Map`, `Set`, `WeakMap`) through one
mechanism, with zero collection-specific effect rules.

Base: TScert `single-pass` at `9440e5f13`; the Pretext copy lives in
`dev/paper-rules/pretext/src/`. Claims are labelled **proved** (with the Lean
name), **cited** (with the source document or file, exact scope, and whether
the source result transfers), **measured** (counted in this checkout at
`9440e5f13`), or **conjectured**. Every new definition, rule, and theorem in
this draft is **conjectured** until mechanized in Lean without `sorry` or
project axioms.

## Motivation: why collection-specific rules do not scale

In TScert's native overlay (`tools/array-prototype.mts:690-762`, cited),
`WeakMap.prototype.{set, delete}` carry the empty footprint because their
table lives in an internal slot (`[[WeakMapData]]`) outside the calculus heap,
and `Map.prototype.{set, delete, clear}` and `Set.prototype.{add, delete, clear}`
carry the global class footprint `{ value: "scalar", spine: "keep" }` because
their only modelled location is `size`. That treatment rests on an accident of
the host model: built-in collections hold no array spines or element cells in
the calculus heap.

User-defined heap abstractions hold their representation in ordinary heap
storage:

- A hash table `class FastMap<K, V>` owns `#buckets: Array<Entry<K, V> | null>`
  and `#count: number`. Updating an entry writes element cells of `#buckets`
  (`Kind.elem`) and, on growth or rehash, mutates or replaces `#buckets`'s
  array spine (`Kind.arraySpine`).
- An `LruCache<K, V>` owns doubly linked node objects (`#head`, `#tail`,
  `prev`/`next` fields) and a backing index.
- An `Arena<T>` owns a backing `Array<T>` or `Int32Array` (`Kind.arraySpine`
  or `Kind.viewSpine`, plus `Kind.elem`) and a cursor `#len: number`.
- Module-private caches such as Pretext's `graphemeEndCaches`
  (`dev/paper-rules/pretext/src/line-text.ts:12`, cited) and
  `cachedEngineProfile` (`dev/paper-rules/pretext/src/measurement.ts:438`,
  cited) hold persistent mutable state in unexported module bindings whose
  entries are loaded into local variables and mutated on demand.

In TScert's kinded world (`lean/Verification/Semantics/Worlds.lean:52-93`,
cited), `Role.key?` returns a property key only for `.field k` and `.cell k`,
and returns `none` for `.elem` and `.spine`. Element cells and array or view
spines carry no distinguishing property key. Consequently, key-disjointness
(`Footprints.Region.apart_of_keys`, proved in
`lean/Verification/Semantics/RegionBounds.lean:374-385`) and key-wide field
regions (`*.f`) cannot separate `#buckets`'s spine or element cells from an
unrelated caller array such as `prepared.widths: number[]`. Hardcoding `Map`
or `WeakMap` regions into the effect language leaves `FastMap`, `LruCache`,
and `Arena` unable to frame against caller arrays.

## The existing mechanism this extends

[The general mechanisms](../DESIGN.md#general-mechanisms) assign heap fact
preservation across calls to [footprints](../FOOTPRINTS.md) (cited): a fact's
support, the stable operations stated as footprints, Lean certifying code
within those footprints, and the tolerant frame rule. This design extends four
existing pieces directly:

1. **Regions, footprints, respect, and rebasing**
   (`lean/Verification/Semantics/Footprints.lean`,
   `lean/Verification/Semantics/FootprintRebase.lean`, proved):

   ```text
   Region ::= field x k | fields x | cells x | cls S | all
            | path x p k | pathFields x p | pathCells x p | spine x p

   Post Φ ρ h h'  ⟺  |h| ≤ |h'| ∧ ∀ l v, h[l]? = some v →
                       ∃ v', h'[l]? = some v' ∧
                       (v' = v ∨ ∃ (r, δ) ∈ Φ, r.mem ρ h l ∧ δ.Holds |h| v v')

   respects q S Φ  ⟺  ∀ (r, δ) ∈ S, ∀ (r', γ) ∈ Φ,  γ ⊑ δ ∨ q.disjoint r r'

   rebase ev r:
     field s k / path s p k  ↦  []            if k = arraySpineKey ∧ ev.fresh s p
                             ↦  [path x (q++p) k]  if ev.path s p = some (x, q)
                             ↦  [cls (keyClass k)] otherwise
     cells _ / pathCells _ _ ↦  [cls values]
     spine s p               ↦  [spine x (q++p)]   if ev.path s p = some (x, q)
                             ↦  [cls spines]       otherwise
   ```

   Every fact surviving a call is checked by `Footprints.respects` (proved:
   `respect_sound`, `frame_step`), and each step's frame is mapped back to the
   enclosing call's entry via `Footprints.rebase` (proved: `Post.compose_at`).

2. **Kind- and key-based separation queries**
   (`lean/Verification/Semantics/RegionBounds.lean`,
   `lean/Verification/Semantics/SeparationEvidence.lean`, proved):

   ```text
   Region.bound:
     field _ k / path _ _ k  ↦  arraySpine if k = arraySpineKey else fieldsAndCells
     fields _ / pathFields   ↦  fieldsAndCells
     cells _ / pathCells     ↦  elems
     spine _ _               ↦  spines
     cls S                   ↦  S.kinds
     all                     ↦  KindSet.all

   Region.key?:
     field _ k / path _ _ k  ↦  some k  if k ≠ arraySpineKey, else none
     _                       ↦  none

   boundQuery.disjoint r s  ⟺  (r.bound ∩ s.bound).isEmpty ∨ r.keysApart s
   ```

   `boundQuery_sound` proves `boundQuery` sound at every well-formed state
   (`HeapOk` and `RootsOk`), and `SepEvidence.query` combines `boundQuery`,
   freshness stamps, and explicit separation facts (`SepEvidence.query_sound`).

3. **No-forge local confinement**
   (`lean/Verification/Semantics/Confinement.lean`,
   `lean/Verification/Programs/LocalConfinement.lean`,
   `lean/Verification/Programs/TolerantFramesConfined.lean`,
   [local object confinement](local-object-confinement.md), proved):

   ```text
   NoPriv Priv v        ⟺  ∀ l, Leaves allC v l → ¬ Priv l
   ClosedOut h Priv     ⟺  ∀ m < |h|, ¬ Priv m → ∀ v, h[m]? = some v → NoPriv Priv v

   steps_confined_unreachable:
     ClosedOut h Priv ∧ (∀ x ∈ roots(t), NoPriv Priv x) ∧ Steps k h t h' t'
     ⟹ (∀ l, Priv l → h'[l]? = h[l]?) ∧ ClosedOut h' Priv ∧ (∀ x ∈ roots(t'), NoPriv Priv x)

   closedOut_of_keep_outside:
     HeapOk n W h ∧ ClosedOut h Priv ∧ (∀ m < |h|, ¬ Priv m → h'[m]? = h[m]?)
     ⟹ ClosedOut h' (Priv ∪ [|h|, |h'|))
   ```

   In the single pass, `LocalConfinement.ConfinedAt` maintains a per-activation
   set `Priv ⊆ [|h₀|, |h|)` of locally allocated objects and arrays, checked
   node by node by `LocalConfinement.checkNode` and composed with the pass by
   `TolerantFrames.nodesChecked_confined` with zero client trust.

4. **Effect variables, declared reach, and named effects**
   ([effect languages](effect-languages.md),
   `lean/Verification/Paper/EffectLanguage/Rules.lean`,
   `lean/Verification/Paper/EffectLanguage/Model.lean`):

   ```text
   BoundRule:  Within θ Φ s₀ ∧ Reaches s₀ s ∧ Anchored θ s₀ ∧ Same Φ s₀ s  ⟹  Incl θ Φ s
   AnchRule:   Anchored θ s₀ ∧ Reaches s₀ s                                 ⟹  Incl θ (old s₀) s
   MeetRule:   Incl E Φ₁ s ∧ Incl E Φ₂ s                                    ⟹  Incl E (meet Φ₁ Φ₂) s
   InstRule:   RenOk σ E ∧ Act E s s'                                       ⟹  Act (rename σ E) s s'
   ```

   The four rules are proved over the idealised heap model (`model_rules` in
   `Model.lean:221`) and conjectured for TScert's full calculus. A named
   effect $`N(x_1, \dots, x_n) \triangleq \Phi`$ abstracts a basic effect, and
   declared reach $`x.\ast\ast_T`$ collects the field, spine, and element-cell
   locations along all paths in $`\mathrm{Acc}(T)`$
   (`effect-languages-note/note.tex`, Definitions 4 and 11, cited).

### Dual relation to private representation

[Private representation](private-representation.md) (cited; conjectured) uses
ECMA-262 private names and lexical confinement in the *inward* direction:
protecting a class's private state $`R_C`$ from arbitrary external callbacks
running under effect $`\top`$, by bounding every outside step to the class's
reference-preserving protocol $`\Psi_C`$.

Abstract confined regions solve the *dual (outward)* direction: protecting
external caller state (such as `prepared.**`) from a class's or module's
private mutable implementation, by encapsulating every mutation of internal
objects, arrays, and typed arrays behind an opaque confined region (`m.@rep`
or `M.@state`) that callers separate from their own data without unfolding
the implementation. Unlike private representation, a confined abstraction in
the outward direction needs neither read-only views nor a reference-preserving
protocol: a `FastMap` may drop and replace its entire `#buckets` array during
a rehash.

### Concrete example: `FastMap` and Pretext W5 (`layoutWithLines` / `getGraphemeEnds`)

Consider a user-written hash table `FastMap<K, V>` backing a module-private
cache in the shape of Pretext's `getGraphemeEnds`
(`dev/paper-rules/pretext/src/line-text.ts:12-30`, cited) and `layoutWithLines`
(`dev/paper-rules/pretext/src/layout.ts:355-375`, cited):

```ts
type Entry<K, V> = { key: K; value: V };

class FastMap<K, V> {
  #buckets: Array<Entry<K, V> | null> = [null, null, null, null];
  #count = 0;

  get(k: K): V | undefined {
    const e = this.#buckets[hash(k) & (this.#buckets.length - 1)];
    return e !== null && e !== undefined && e.key === k ? e.value : undefined;
  }

  set(k: K, v: V): void {
    if (this.#count * 2 >= this.#buckets.length) this.#rehash();
    const idx = hash(k) & (this.#buckets.length - 1);
    this.#buckets[idx] = { key: k, value: v };
    this.#count++;
  }

  #rehash(): void {
    const next: Array<Entry<K, V> | null> = new Array(this.#buckets.length * 2).fill(null);
    // reinsert existing entries into next ...
    this.#buckets = next;
  }
}

// Module line-text.ts (mirroring dev/paper-rules/pretext/src/line-text.ts:12-30)
const graphemeEndCaches = new WeakMap<PreparedSegments, FastMap<number, Int32Array>>();

export function getGraphemeEnds(prepared: PreparedSegments, segmentIndex: number): Int32Array {
  let cache = graphemeEndCaches.get(prepared);
  if (cache === undefined) {
    cache = new FastMap<number, Int32Array>();
    graphemeEndCaches.set(prepared, cache);
  }
  let ends = cache.get(segmentIndex);
  if (ends === undefined) {
    const segment = prepared.segments[segmentIndex];
    if (segment === undefined) throw new RangeError("missing value");
    ends = new Int32Array(segment.length);
    findGraphemeEnds(getEngineProfile().graphemeTable, segment, 0, segment.length, ends);
    cache.set(segmentIndex, ends);
  }
  return ends;
}

// Module layout.ts (mirroring dev/paper-rules/pretext/src/layout.ts:355-375)
export function layoutWithLines(
  prepared: PreparedTextWithSegments, maxWidth: number, lineHeight: number,
): LayoutLinesResult {
  const lines: LayoutLine[] = [];
  const lineCount = walkPreparedLinesRaw<E_visitor>(
    getInternalPrepared(prepared),
    normalizeMaxWidth(maxWidth),
    (w, sSeg, sGraph, eSeg, eGraph) => {
      lines.push(createLayoutLine(prepared, w, sSeg, sGraph, eSeg, eGraph));
    },
  );
  return { lineCount, height: lineCount * lineHeight, lines };
}
```

#### Step-by-step through the existing mechanism (where it fails)

1. **`FastMap.prototype.set`:** The element write `this.#buckets[idx] = ...`
   has step frame `{ #buckets.spine: grow, #buckets.cells: any }`. The rehash
   write `this.#buckets = next` has step frame `{ this.#buckets: any }`, and
   `this.#count++` has `{ this.#count: scalar }`.
2. **Rebasing `FastMap.prototype.set`:** Because `this.#buckets` is reassigned
   during `#rehash`, the path `this.#buckets` is not rigid across the body.
   `Footprints.rebase` widens `#buckets.spine` to `cls(spines)` and
   `#buckets.cells` to `cls(values)`. Even without `#rehash`, `#buckets.cells`
   always rebases to `cls(values)` (`FootprintRebase.lean:246-247`), and the
   array spine `#buckets.spine` carries no property key.
3. **Rebasing `getGraphemeEnds`:** `cache` is loaded from
   `graphemeEndCaches.get(prepared)` — a local slot not linked by a rigid path
   from any parameter. `Footprints.rebase` widens every mutation through
   `cache` to `cls(spines)` and `cls(values)`. Likewise, `getEngineProfile()`
   writes the module cell `cachedEngineProfile` (`measurement.ts:1001`), which
   rebases to `cls(values)` at `init`.
4. **Checking `Inst` at `walkPreparedLinesRaw` in `layoutWithLines`:** The
   walker requires its visitor's effect `E_visitor` to satisfy
   $`E_{\text{visitor}} \sqsubseteq \{\mathit{prepared}.\ast\ast_{\mathit{PreparedLineData}} : \mathsf{keep};\ \mathsf{else}: \mathsf{any}\}`$.
   `prepared.widths` has spine kind `Kind.arraySpine` (`Category.array`) and
   element cells of kind `Kind.elem` (`Category.value`).
   - `boundQuery` tests `cls(spines)` against `prepared.widths.spine`
     (`spines ∩ arraySpine = arraySpine ≠ ∅`) and `cls(values)` against
     `prepared.widths.cells` (`values ∩ elems = elems ≠ ∅`).
   - `Region.key?` returns `none` for `.cls`, `.spine`, and `.cells`, so
     `Region.keysApart` is `false`.
   - Neither `graphemeEndCaches`, `cache`, `#buckets`, nor
     `cachedEngineProfile` is freshly allocated inside `layoutWithLines`, so
     freshness does not discharge them.
   - `Footprints.respects` fails, `Inst` refuses the call, and
     `layoutWithLines` is refused.

#### The proposed change, and the same example step-by-step

The design adds two orthogonal concepts to `Footprints.Region` and
`SepEvidence`: (1) opaque **abstract regions** (`m.@rep` on a class,
`M.@state` on a module), and (2) **confinement with fresh-only growth**
generalizing `Confinement.ClosedOut` from function locals to classes and
modules. Walking the same example through the change:

1. **Declaring the class region:** `FastMap<K, V>` declares a confined
   abstract region `@rep`, defined privately as its `#buckets` field, the
   spine and element cells of `#buckets`, the fields of every `Entry` node
   owned by `#buckets`, and `#count`. Notice that `Entry.key` and
   `Entry.value` are field locations *inside* `@rep` (holding references to
   `k` and `v`), while the objects `k` and `v` themselves lie *outside* `@rep`.
2. **Checking `FastMap` once, internally:**
   - `FastMap`'s constructor allocates `#buckets` freshly, establishing
     confinement (`ClosedOut` for the instance's rep set).
   - `get` performs only reads and returns `e.value` (a stored payload, not a
     rep object); its effect is `{}`.
   - `#rehash` allocates a fresh array `next`, copies entry references into
     `next`, and stores `next` into `this.#buckets`. Every old rep location
     modified lies in `this.@rep`, `next` is fresh (satisfying fresh-only
     growth $`R_m(h') \subseteq R_m(h) \cup [|h|, |h'|)`$), and neither
     `#buckets` nor `next` escapes.
   - `set` calls `#rehash`, allocates a fresh `{ key: k, value: v }` record
     (fresh-only growth; `k` and `v` are payload fields, not absorbed into
     `@rep`), stores it into `#buckets[idx]`, and increments `#count`. All
     writes to pre-existing locations lie in `this.@rep`, so `set` certifies
     at `Modifies<{ "this.@rep": "any" }, void>`.
3. **Declaring and checking the module regions:**
   - `measurement.ts` declares a confined module region `measurement.@state`
     covering `cachedEngineProfile` (and its private caches).
     `getEngineProfile()` certifies at
     `Modifies<{ "measurement.@state": "any" }, EngineProfile>` (the returned
     profile is read-only or fresh/outside `@state`; only the module cell
     `cachedEngineProfile` is in `@state`).
   - `line-text.ts` declares a confined module region `lineText.@state`
     covering `graphemeEndCaches.@rep` and the `@rep` of every `FastMap`
     instance stored in `graphemeEndCaches`. Because `graphemeEndCaches` is
     unexported and no `FastMap` instance ever escapes `line-text.ts`, every
     `cache` loaded from `graphemeEndCaches` is confined to `lineText.@state`,
     and `ends = new Int32Array(...)` is allocated fresh before being stored
     as a payload and returned. `getGraphemeEnds` certifies at
     `Modifies<{ "lineText.@state": "any"; "measurement.@state": "any" }, Int32Array>`
     (or `lineText.@state` alone if `measurement.@state` is composed into it).
   - `createLayoutLine` calls `buildLineTextFromRange` -> `getGraphemeEnds`
     and allocates a fresh `LayoutLine`, certifying at
     `Modifies<{ "lineText.@state": "any"; "measurement.@state": "any" }, LayoutLine>`.
4. **Checking `Inst` at `walkPreparedLinesRaw` in `layoutWithLines`:**
   - The visitor's effect is
     $`E_{\text{visitor}} = \{\mathit{lines}.\mathsf{spine} : \mathsf{extend},\ \mathit{lineText}.@\mathrm{state} : \mathsf{any},\ \mathit{measurement}.@\mathrm{state} : \mathsf{any}\}`$.
   - `lines` is fresh, so `lines.spine` is disjoint from `prepared.**`.
   - `lineText.@state` and `measurement.@state` are confined module regions,
     so by the disjointness theorem below they are disjoint from
     $`\mathit{prepared}.\ast\ast_{\mathit{PreparedLineData}}`$ without
     unfolding either region, even though `FastMap` mutates internal arrays.
   - `Inst` succeeds, and `layoutWithLines` verifies.

## The proposed design

The design rests on two orthogonal concepts and introduces zero
collection-specific rules.

### 1. Abstract regions (data groups)

Abstract regions extend named effects $`N(x_1, \dots, x_n) \triangleq \Phi`$
([effect languages](effect-languages.md), `note.tex` Definition 11, cited)
from transparent abbreviations to opaque region members on classes and
modules (the data-group abstraction in frame specifications, related in spirit
to [Leino 2010](../REFERENCES.md#leino-2010) and
[Kassios 2006](../REFERENCES.md#kassios-2006); those systems use binary write
sets and specification variables rather than TScert's change lattice and
kinded worlds, so their metatheory does not transfer directly).

- **Class abstract region (`m.@rep`):** A class $`C`$ may declare an abstract
  region member (written illustratively `@rep`, or named regions `@r` when a
  class separates independent pieces of state) together with a private
  representation definition inside $`C`$'s body,
  $`C.@\mathrm{rep}(\mathit{this}) \triangleq \bigcup_i r_i(\mathit{this})`$,
  where each $`r_i(\mathit{this})`$ is a concrete region over private fields
  of $`C`$, owned storage reachable through them (such as
  `this.#buckets`, `this.#buckets.spine`, `this.#buckets.cells`, owned node
  fields), optional public summary fields of $`C`$ (such as `this.size`), or
  abstract regions `this.#sub.@rep` of owned sub-abstractions.
- **Module abstract region (`M.@state`):** A module $`M`$ may declare a
  confined module region $`M.@\mathrm{state}`$ defined privately over its
  unexported `let`/`const` bindings, their owned storage, and the `@rep`
  regions of unexported confined instances held in those bindings.
- **Opacity at callers:** Outside the defining class $`C`$ (or module $`M`$),
  $`m.@\mathrm{rep}`$ (or $`M.@\mathrm{state}`$) is an opaque `Footprints.Region`
  constructor. Callers never unfold its definition; they check inclusion and
  disjointness purely through the region's owner identity, confinement
  status, and declared types.
- **Checking inside the owner:** Every method and constructor of $`C`$ (and
  every function of $`M`$) checks its body against its stated effect by
  unfolding $`\mathit{this}.@\mathrm{rep}`$ (or $`M.@\mathrm{state}`$) to its
  concrete representation set, using the ordinary `Footprints.Post` and
  `Fresh-Eff` rules.

### 2. Confinement with fresh-only growth

Opacity alone does not imply disjointness: if `FastMap` stored a caller's own
array inside `#buckets` and mutated it, `m.@rep` could collide with
`prepared.widths`. Disjointness follows from a persistent **confinement
invariant** generalizing `Confinement.ClosedOut`
(`lean/Verification/Semantics/Confinement.lean:39-40`, proved for
function-local sets) from one activation to the lifetime of an instance or
module, paired with dynamic-frames self-framing
([Kassios 2006](../REFERENCES.md#kassios-2006), cited for the self-framing
idea; binary frames there do not transfer directly to TScert's change
lattice).

For each confined owner $`o`$ (an instance of a confined class $`C`$, or a
confined module $`M`$), write $`R_o(h) \subseteq \{0, \dots, |h|-1\}`$ for the
set of locations denoted by $`o.@\mathrm{rep}`$ (or $`M.@\mathrm{state}`$) in
heap $`h`$, partitioned into its *interior* $`R_o^{\mathrm{int}}(h)`$
(private fields, module cells, and all owned internal arrays, spines, element
cells, and records) and any declared *public summary fields*
$`R_o^{\mathrm{pub}}(h)`$ directly on $`o`$ (such as `o.size` on a collection;
always empty for a module region $`M.@\mathrm{state}`$).

The persistent confinement invariant `OwnerConfined` (conjectured) consists of
four conditions.

**1. Boundary closure (`ClosedOut` on the interior).** Every allocated
location $`m \notin R_o^{\mathrm{int}}(h)`$ outside $`o`$'s interior holds
a value whose direct location references stay outside
$`R_o^{\mathrm{int}}(h)`$, except that the owner object $`o`$ itself holds
its private-name slots $`\sigma_{C.\#f}`$ (for a class) and the module's
unexported bindings hold its top-level cells (for a module):

```math
\forall m < |h|.\ m \notin R_o^{\mathrm{int}}(h) \;\land\; h[m] = v \;\implies\;
  \forall l.\ \mathrm{Leaves}_{\mathrm{pub}}(v, l) \implies l \notin R_o^{\mathrm{int}}(h)
```

where $`\mathrm{Leaves}_{\mathrm{pub}}`$ excludes private-name slots of $`C`$
on $`o`$ and unexported module bindings of $`M`$.

**2. Owner disjointness.** Distinct confined owners $`o_1 \neq o_2`$ have
disjoint interiors, $`R_{o_1}^{\mathrm{int}}(h) \cap R_{o_2}^{\mathrm{int}}(h) = \emptyset`$
(unless $`o_2`$ is explicitly nested inside $`o_1`$'s representation, in
which case $`R_{o_2}(h) \subseteq R_{o_1}^{\mathrm{int}}(h)`$).

**3. Payload outward-only flow.** Stored caller objects (`k`, `v`) may be
referenced *from* locations inside $`R_o^{\mathrm{int}}(h)`$ (for example,
`entry.key` and `entry.value`), and `get` may return those payload
references. Those target objects remain *outside* $`R_o(h)`$: only the
container fields holding the references belong to $`R_o^{\mathrm{int}}(h)`$.
Consequently, mutating a payload object `v.x = 1` is not covered by
`this.@rep` and is refused unless declared explicitly.

**4. Fresh-only growth (self-framing).** Every operation of $`o`$ taking
pre-heap $`h`$ to post-heap $`h'`$ satisfies:

```math
R_o(h') \;\subseteq\; R_o(h) \cup [\,|h|,\ |h'|)
```

An operation may drop old interior objects (e.g., discarding the old
`#buckets` array during `#rehash`) and absorb freshly allocated internal
objects (e.g., a new `next` array or new `Entry` records), while never
absorbing any pre-existing location outside $`R_o(h)`$.

#### Local obligations checked once on the owning class or module

Each obligation is checked statically when certifying the defining class $`C`$
or module $`M`$, with zero caller burden:

- **Lexical boundary:** A confined class has no `extends` clause and is
  declared where its private names are evaluated once (matching
  [private representation](private-representation.md#the-class-shape-the-rule-requires),
  cited). A confined module region covers only unexported module bindings.
- **Fresh acquisition:** Any reference written into a rep-owned field (such as
  `this.#buckets`, `this.#buckets[i]`, or a nested rep field) must be freshly
  allocated in the current method or already rep-owned. References to external
  parameters (`k`, `v`) may only be written into fields explicitly marked as
  payload references (excluded from the rep expansion).
- **No representation escape:** No rep-owned reference (any value whose direct
  references lie in $`R_o^{\mathrm{int}}`$) may be returned, thrown, passed to
  unverified or external code, or written into non-rep storage. Payload values
  read from payload fields (such as `e.value` returned by `FastMap.get`) are
  not rep-owned and may be returned freely.
- **Method effect soundness:** Every write performed by a method of $`C`$ (or
  function of $`M`$) touches only locations in $`R_o(h)`$ or freshly allocated
  locations $`l \ge |h|`$, establishing both `Post` at `{ this.@rep: δ }` (or
  `{ M.@state: δ }`) and preservation of `OwnerConfined` (by generalizing
  `Confinement.closedOut_of_keep_outside`).
- **Exception safety:** Every throw path leaving a method preserves
  `OwnerConfined` (never leaking a rep object in the thrown value) and, when
  `onThrow` is claimed, satisfies the stated effect on throw as well.

### 3. Disjointness theorem (conjectured)

Let $`\mathrm{Types}(\mathrm{Acc}(T))`$ be the set of types reachable from
type $`T`$ along the finite access paths $`\mathrm{Acc}(T)`$ of declared reach
([effect languages](effect-languages.md), `note.tex` Definition 4, cited),
with declared reach $`x.\ast\ast_T`$ defined so that when a confined class
$`C`$ is reached at path $`a \in \mathrm{Acc}(T)`$, $`x.\ast\ast_T`$ includes
$`(x\,a).@\mathrm{rep}`$ (or any public summary fields of $`C`$).

**Conjecture (Disjointness of confined abstract regions from declared reach).**
At every well-formed state $`(\rho, h)`$ (`HeapOk`, `RootsOk`) satisfying
`OwnerConfined`, two disjointness equations hold without unfolding any
abstract region.

**Class instance form.** For any confined class $`C`$, slot $`m : C`$, and
slot $`x : T`$, if no type in $`\mathrm{Types}(\mathrm{Acc}(T))`$ can
inhabit $`C`$ ($`C \notin \mathrm{Types}(\mathrm{Acc}(T))`$), then:

```math
⟦m.@\mathrm{rep}⟧(\rho, h) \;\cap\; ⟦x.\ast\ast_T⟧(\rho, h) \;=\; \emptyset
```

This holds regardless of what internal `Array`s, `TypedArray`s, or records
$`m.@\mathrm{rep}`$ contains, without unfolding $`C.@\mathrm{rep}`$.

**Module form.** For any confined module region $`M.@\mathrm{state}`$ and
any external root $`x : T`$ (of any type $`T`$):

```math
⟦M.@\mathrm{state}⟧(\rho, h) \;\cap\; ⟦x.\ast\ast_T⟧(\rho, h) \;=\; \emptyset
```

**Proof sketch (conjectured).** Every location $`l \in ⟦x.\ast\ast_T⟧(\rho, h)`$
is reached from $`\rho(x)`$ by traversing public declared fields and array
spines along $`\mathrm{Acc}(T)`$. By boundary closure (1), no path of public
fields and array spines starting outside $`R_o^{\mathrm{int}}(h)`$ can enter
$`R_o^{\mathrm{int}}(h)`$, because private names of $`C`$ are never public
keys ([ECMA-262](../REFERENCES.md#ecma-262), Private Names, cited) and
unexported bindings of $`M`$ are unreachable from any object reference. Thus
$`R_o^{\mathrm{int}}(h) \cap ⟦x.\ast\ast_T⟧(\rho, h) = \emptyset`$ holds
unconditionally for both instances and modules. For a class instance $`m : C`$,
any public summary field $`l \in R_m^{\mathrm{pub}}(h)`$ (such as `m.size`)
lives directly on an instance of $`C`$; the type condition
$`C \notin \mathrm{Types}(\mathrm{Acc}(T))`$ rules out landing on an instance
of $`C`$ along $`\mathrm{Acc}(T)`$, so
$`R_m^{\mathrm{pub}}(h) \cap ⟦x.\ast\ast_T⟧(\rho, h) = \emptyset`$ as well.
When $`C \in \mathrm{Types}(\mathrm{Acc}(T))`$ (for example, when `prepared`
itself owns a field `cache: FastMap<K, V>`), disjointness does not follow from
types alone and falls back to explicit separation evidence (freshness of `m`
or object inequality `m !== prepared.cache` with owner disjointness).

#### Rebasing, composition, and anchoring (conjectured)

Two further properties make abstract confined regions compose cleanly with
`Seq-Eff`, `Loop-Eff`, and effect polymorphism (`Bound`, `Anch`, `Meet`,
`Inst`):

- **Self-framing rebasing:** Because fresh-only growth guarantees
  $`R_o(h') \subseteq R_o(h) \cup [|h|, |h'|)`$, a step bounded by
  $`\{o.@\mathrm{rep} : \delta\}`$ after a prior step from $`h_0`$ to $`h`$
  changes no location of $`[0, |h_0|)`$ outside $`R_o(h_0)`$. Therefore
  `o.@rep` rebases to `o.@rep` at $`h_0`$ across `Seq-Eff` and is transitive
  for `Loop-Eff`, even when `#rehash` replaces `#buckets` on every iteration.
- **Generalized anchoring for `Anch`:** In `Model.lean:81-83`, `Model.Anchored`
  requires an effect instance $`\theta`$ to satisfy
  $`\mathrm{bnd}\ \theta\ h\ l = \mathsf{keep}`$ for *every* location
  $`l \ge |h_0|`$. An instance containing `{ m.@rep: any }` (for a captured
  `const m: FastMap`) may allocate new `#buckets` inside `m.@rep` during
  iteration 1 of a walker and mutate those newly allocated `#buckets` during
  iteration 2, so its bound is not `keep` on `m`'s own post-$`h_0`$
  allocations. However, `m.@rep` never absorbs locations allocated outside `m`
  (such as `walk`'s local `cursor`). Weakening `Anchored` to require
  preservation of every location outside the callee's confined owners' fresh
  allocations (or pairing `Anch` with `OwnerConfined`) keeps `BoundRule`,
  `AnchRule`, `MeetRule`, and `InstRule` sound while admitting
  `{ m.@rep: any }` and `{ M.@state: any }` as anchored effect instances
  (conjectured).

### 4. Unification across built-ins, user abstractions, and module caches

All three kinds of mutable abstraction become instances of this single
mechanism, with zero collection-specific rules in the effect language:

| Abstraction | Owner & region | How obligations are established | Effect of mutators |
| --- | --- | --- | --- |
| Built-in `Map<K, V>`, `Set<T>`, `WeakMap<K, V>` | Host class `Map`/`Set`/`WeakMap`, region `this.@rep` | Audited host contract (`tools/array-prototype.mts`, ECMA-262 internal slots + `size`) | `Modifies<{ "this.@rep": "any" }, ...>` (replaces global `changesValues = { value: "scalar", spine: "keep" }`) |
| User `FastMap<K, V>`, `LruCache<K, V>`, `Arena<T>` | Class `C` with `#private` fields, region `this.@rep` | Checked once on `C`'s constructor and methods (no host trust beyond ECMA-262 private names) | `Modifies<{ "this.@rep": "any" }, ...>` |
| Module caches (`graphemeEndCaches`, `cachedEngineProfile`) | Module `M`, region `M.@state` | Checked once on `M`'s unexported bindings and module functions | `Modifies<{ "M.@state": "any" }, ...>` |

**Boundary with functional content predicates (explicit scope limit).**
Abstract confined regions establish *framing*: mutating `m.@rep` or
`M.@state` leaves disjoint caller facts (such as `prepared.widths.length`)
unchanged. They do *not* express functional properties of the stored contents,
such as `m.set(k, v)` implying `m.get(k) === v`, `m.has(k)` implying
`m.get(k) !== undefined`, or `m.size` increasing by 1. Functional content
predicates require abstract state / ghost maps
([correctness specifications](correctness-specs.md)) and remain outside this
mechanism.

### 5. Upgrade path from near-term receiver-scoped `this.size` and key/cell regions (Option A)

In the near term, Pretext's pattern W5 (`layoutWithLines`, `getGraphemeEnds`,
`getEngineProfile`) is addressed by a smaller change (Option A):
scoping `Map`/`Set` mutators to receiver `{ "this.size": "scalar" }` in
`tools/array-prototype.mts` and adding key-wide field regions (`*.f`) and
module cell regions (`cells` of `Kind.cell`) to `Footprints.Region`. That
works for native `Map`/`Set` and module `let` cells specifically because
built-in collections have no heap-allocated arrays in the model and
`cachedEngineProfile` lives in a `Kind.cell` location disjoint from
`PreparedLineData`.

Abstract confined regions (Direction B) are compatible with Option A and
generalize it without rework:

- Key-wide field regions (`*.f`) and module cell regions remain general
  `Footprints.Region` constructors useful for non-confined mutable structures
  and open-object writes.
- Under abstract confined regions, `Map`, `Set`, and `WeakMap` declare `@rep`
  in their overlay entries, subsuming receiver-scoped `this.size`, while
  user-defined `FastMap`, `LruCache`, `Arena`, and nested module caches gain
  the same framing power for internal arrays and typed arrays.
- No annotation syntax or Lean soundness theorem introduced by Option A
  conflicts with Direction B.

## What this duplicates

Per [designs start from an existing mechanism](../../AGENTS.md#designs-start-from-an-existing-mechanism),
each modelled concern sits beside its existing owner:

| Concern | Existing model in TScert | How this design relates to it |
| --- | --- | --- |
| Natives | `tools/array-prototype.mts` (`interfaceOverlay` for `Map`, `Set`, `WeakMap`), [native footprints](../SOURCE-CONTRACTS.md#native-footprints) | Reads the same overlay mechanism; replaces global `changesValues` on `Map`/`Set` with `this.@rep`. Duplicates nothing. |
| Outside values & trust | [Trust surface](../DESIGN.md#trust-surface), `tools/builtin-trust.mts` (`stores`, `callsArgs`, `passesOwnAllocations`), ECMA-262 private-names row in [private representation](private-representation.md#trust) | Reuses existing built-in trust rows and the single ECMA-262 private-names row; verified user classes and modules add zero new caller trust. |
| Module bindings | [Module cells](../SOURCE-ELABORATION.md#module-cells), `Role.cell` / `Kind.cell` in `Worlds.lean` | `M.@state` groups existing module cell locations and owned storage reachable from them; no duplicate module-binding lowering. |
| Initialization | Module initialization order and class construction (`FragmentFront.lean`, `Lowering.lean`, [modules and code units](../DESIGN.md#modules-and-code-units)) | Reuses existing constructor and module-init checking, adding the initial confinement obligation (`OwnerConfined`) on completion. |
| Effects & regions | `Footprints.Region`, `Footprints.Post`, `Footprints.Supported`, `Footprints.respects`, `Paper.EffectLanguage.Rules` | Adds abstract-region constructor(s) directly to `Footprints.Region` and extends `SepEvidence.query`; no parallel effect language or prototype-only string region. |
| Kinds of step | `Step`, `Steps` (`Calculus.lean`), `ExpressionEffects`, `SinglePass` | Zero new operational step forms; confinement preservation uses the existing no-forge lemmas (`Reach.step_reach`, `Reach.step_noForge`, `Reach.step_writes`). |
| Confinement vs `LocalConfinement` | `Semantics/Confinement.lean` (`ClosedOut`, `NoPriv`, `steps_confined_unreachable`, `closedOut_of_keep_outside`), `Programs/LocalConfinement.lean` (`ConfinedAt`, `checkNode`), `TolerantFramesConfined.lean` | Generalizes `ClosedOut` / `NoPriv` from a single function activation's `Priv` to persistent class/module owners with fresh-only growth and payload separation. |
| Confinement vs `private-representation.md` | [Private representation](private-representation.md) ($`R_C`$, $`\Psi_C`$, read-only views, reference-preserving protocol) | Shares the lexical private-name boundary and no-inheritance restriction, solving the dual (outward) framing direction without read-only views or a reference-preserving protocol. |

## What must be proved in Lean

Every item below is **conjectured** until mechanized in Lean with zero
`sorry`, zero project axioms (`Verification.Tests.AxiomCheck` and
`Verification.Paper.TolerantFrames.Tests.AxiomCheck`), and unchanged
acceptance-soundness structure (`SourceClaimJson.PassUnit.mode8Accepted_sound`
via exhaustive `FunctionPlan.certify`):

1. **Abstract regions in `Footprints.Region`:** Add abstract region
   constructors (instance `@rep` on a slot/path, module `@state`) and a
   semantic region map interpreting each abstract region to its owner's
   concrete location set at $`(\rho, h)`$, keeping `Region.mem`, `Post`,
   `Supported`, and `respects` unified.
2. **Persistent `OwnerConfined` invariant:** Generalize `Confinement.ClosedOut`
   to `OwnerConfined h O` (boundary closure on interior locations, owner
   disjointness, payload outward-only references) and prove:
   - external steps preserve `OwnerConfined` and leave every interior location
     unchanged (from `Reach.step_reach`, `Reach.step_noForge`,
     `Reach.step_writes`);
   - owner steps passing the checked confinement obligations preserve
     `OwnerConfined` and satisfy fresh-only growth
     $`R_o(h') \subseteq R_o(h) \cup [|h|, |h'|)`$.
3. **Type-directed disjointness theorem:** Prove that under `HeapOk`,
   `RootsOk`, and `OwnerConfined`,
   - $`C \notin \mathrm{Types}(\mathrm{Acc}(T)) \implies ⟦m.@\mathrm{rep}⟧(\rho, h) \cap ⟦x.\ast\ast_T⟧(\rho, h) = \emptyset`$, and
   - $`⟦M.@\mathrm{state}⟧(\rho, h) \cap ⟦x.\ast\ast_T⟧(\rho, h) = \emptyset`$
     for every external root $`x : T`$.
   Wire both into `SepEvidence.query` and prove `SepEvidence.query_sound`.
4. **Self-framing rebasing and loop composition:** Prove that fresh-only
   growth rebases `m.@rep` and `M.@state` to themselves in `FootprintRebase`
   (`Post.compose_at`) and makes `{ m.@rep: δ }` and `{ M.@state: δ }`
   transitive for `LoopEvidence.loop_sound`.
5. **Generalized anchoring in `EffectLanguage`:** Relax `Model.Anchored` to
   preserve external post-entry allocations (outside confined owners' fresh
   allocations), prove `PaperRules` (`BoundRule`, `AnchRule`, `MeetRule`,
   `InstRule`) in `Verification/Paper/EffectLanguage/Model.lean`, and prove the
   corresponding theorems for TScert's calculus.
6. **Checked confinement obligations on classes and modules:** Extend
   `LocalConfinement` / `ModuleInterfaces` / `Plans.lean` to check fresh
   acquisition, payload separation, no representation escape, and method
   effects at `FunctionPlan.certify`, with `mode8Accepted_sound` covering
   confined classes and modules.
7. **Negative controls:** Add counterexample controls in
   `Verification/Tests/FootprintControls.lean` and negative pipeline cases
   verifying refusal of: (a) returning or leaking `#buckets` from a method,
   (b) storing a caller-passed array into `#buckets` as rep storage,
   (c) mutating a stored payload object `v.x = 1` under `this.@rep`, and
   (d) claiming `m.@rep # prepared.**` when `FastMap` is reachable in
   `Acc(Prepared)` without separation evidence.

### Measured code touchpoints

The existing files that this design reads or would extend have the following
sizes (measured via `wc -l` in this checkout at `9440e5f13`; implementation
diff size is not measured):

| Area | File | Lines (measured) | Role in this design |
| --- | --- | ---: | --- |
| Footprint core | `lean/Verification/Semantics/Footprints.lean` | 1,261 | `Region`, `Post`, `Supported`, `respects` |
| Region bounds & separation | `lean/Verification/Semantics/RegionBounds.lean` | 431 | `Region.bound`, `boundQuery` |
| Separation queries | `lean/Verification/Semantics/SeparationEvidence.lean` | 649 | `SepEvidence.query`, `query_sound` |
| Rebasing | `lean/Verification/Semantics/FootprintRebase.lean` | 423 | `rebase`, `Post.compose_at` |
| Semantic confinement | `lean/Verification/Semantics/Confinement.lean` | 1,122 | `ClosedOut`, `NoPriv`, `steps_confined_unreachable` |
| Checked confinement | `lean/Verification/Programs/LocalConfinement.lean` | 1,512 | Per-node confinement checking |
| Pass confinement soundness | `lean/Verification/Programs/TolerantFramesConfined.lean` | 417 | `nodesChecked_confined` |
| Single pass | `lean/Verification/Programs/SinglePass.lean` | 4,220 | Call framing and step checks |
| Effect language rules/model | `lean/Verification/Paper/EffectLanguage/{Rules,Model}.lean` | 305 | `PaperRules`, generalized `Anchored` |
| Source boundary & plans | `lean/Verification/Source/{Fragment,Lowering}.lean`, `Claims/{FragmentFront,ModuleInterfaces,Plans}.lean` | 3,360 | Wire, class/module region checks, `FunctionPlan.certify` |
| Node front end & overlays | `tools/{array-prototype,type-term,fragment-classes}.mts` | 4,325 | Annotation syntax, class/module parsing, `Map`/`Set`/`WeakMap` `@rep` overlays |
