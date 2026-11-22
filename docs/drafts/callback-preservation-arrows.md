# Draft: support-parametric callback arrows

A design for verifying higher-order functions whose loops preserve heap
invariants across calls to a callback parameter — and whose callers pass
closures that mutate fresh local state or forward to another callback — by
adding caller-checked **callback demands** to `CallEffects.Effect`.

Base: branch `single-pass` at `536133477`. Evidence labels follow the
conventions of [the callback frames dossier](callback-frames-dossier.md):
**proved** (an existing Lean theorem at the base), **to prove** (a theorem this
design adds, with its proof outline), **observed** (a file, line, grep count, or
test output at the base), **cited** (another document and its scope), and
**trust** (an assumption about unanalyzed external code).

## The existing mechanism this extends

This design extends three existing mechanisms listed in
[the general mechanisms](../DESIGN.md#general-mechanisms):

1. **Footprints, supports, respect, and separation evidence**
   ([footprints](../FOOTPRINTS.md#support-and-respect),
   [separation queries](../FOOTPRINTS.md#separation-queries); cited).
2. **Effect-qualified callable contracts and inferred call effects**
   ([inferred call effects](../SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification),
   [the checked callback contract](../FOOTPRINTS.md#the-checked-callback-contract); cited).
3. **Regional argument-path and freshness tracking**
   (`ArgumentRegionGraph.lean`, `ArgumentRegionFresh.lean`,
   `ArgumentRegionCertificates.lean`; observed).

### How the existing mechanism works

At the base, every function arrow carries an effect (`EffectSignatures.lean`,
`CallEffects.lean`, `PromiseCalls.lean`, `Support.lean`,
`SeparationEvidence.lean`, `SurvivalSeparation.lean`, `PassUnitRealize.lean`;
observed):

```text
-- Verification.CallEffects (EffectSignatures.lean, CallEffects.lean)
structure Effect where
  exits    : Exits ExitSchema          -- normal & optional onThrow frames + postconditions
  promise  : Promise                   -- promise kind
  requires : List IndexFact            -- precondition at call entry (callEnv r args)
  pre      : List Fact                 -- cell precondition at call entry

def PromiseWith (P : ... -> Prop) (eff : Effect) (r : Tm) (args : List Tm)
    (n : Nat) (W : WorldT n) (h : Heap) (t : Tm) : Prop :=
  eff.Requires r args h ->             -- caller establishes precondition
  P ... (fun h' v => eff.callPost r args h h' v) ...

-- Verification.Footprints (Support.lean, SeparationEvidence.lean, SurvivalSeparation.lean)
def respects (q : SepQuery) (S Phi : Footprint) : Bool :=
  S.all fun e => Phi.all fun f => f.2.le e.2 || q.disjoint e.1 f.1

def knowledgeEvidence (k : Knowledge) : SepEvidence :=
  { links := k.links, facts := knowledgeSeps k ++ separationFacts k.separation }
  -- stamps and typed are currently left at their empty defaults

def knowledgeQuery (k : Knowledge) : SepQuery := (knowledgeEvidence k).query

-- Verification.GraphCode.PromiseCalls (PromiseCalls.lean)
def callerFrame (eff : Effect) (t : Tm) : Footprint :=
  (eff.frame.renameM (actualSlot t)).byClass

def frameKeeps (stable : Nat -> String -> Bool) (eff : Effect) (t : Tm)
    (k : Knowledge) (a : IndexAtom) : Bool :=
  a.fact.keeps (knowledgeQuery k) (.ofFirst stable) (callerFrame eff t)

def effectKept (stable : Nat -> String -> Bool) (eff : Effect) (t : Tm)
    (k : Knowledge) : List IndexAtom :=
  if keepsHeap eff then []
  else shiftIndices (k.indices.filter fun a => !a.fact.envOnly && frameKeeps stable eff t k a)
```

Soundness flows through one proved chain:

- `Footprints.knowledgeQuery_sound` (**proved**, `SurvivalSeparation.lean`):
  when `HeapKnowledge.Holds k ε ρ h`, `HeapOk n W h`, and `RootsOk W ρ`,
  `(knowledgeQuery k).Sound ρ h`.
- `Footprints.respect_sound` and `Footprints.frame_step` (**proved**,
  `Support.lean`): if `respects q S Φ = true`, `q.Sound ρ h`, and
  `Post Φ ρ h h'`, then `Supported S ρ h h'` holds, so every assertion
  supported by `S` holds in `h'`.
- `PromiseCalls.effectKept_holds` (**proved**, `PromiseCalls.lean`): every
  index atom retained by `effectKept` holds after the call's normal return.
- `PassUnit.rowSpec_of_requestSafe` (**proved**, `PassUnitRealize.lean`),
  `PassUnit.receiverDropSound` (**proved**, `PassUnitRealize.lean`),
  `PassUnit.passFile_safe_kinds` (**proved**, `PassUnitInterfaces.lean`),
  `PassUnit.crossModule_safe` (**proved**, `PassUnitCross.lean`), and
  `SourceClaimJson.PassUnit.mode8Accepted_sound` (**proved**,
  `PassUnitRun.lean`): accepted units satisfy `RowSpec` (hence `PromiseWith`)
  across single-file and multi-module boundaries.

### Running a small example through the existing mechanism

Consider a walker with a local cursor `c` and a visitor parameter `visit`,
called by two callers:

```ts
type Visitor = (i: number) => void;

function walk(xs: number[], visit: Visitor): number {
  const c = { i: 0 };
  let sum = 0;
  while (c.i < xs.length) {
    visit(c.i);
    sum += xs[c.i]!;
    c.i = c.i + 1;
  }
  return sum;
}

function sumAndTrace(xs: number[]): number {
  const visited: number[] = [];
  return walk(xs, (i) => { visited.push(i); });
}

function sumAndAlias(xs: number[]): number {
  return walk(xs, (_i) => { xs.pop(); });
}
```

Through the existing mechanism, step by step:

1. At `walk`'s entry, `visit` has an unrestricted arrow effect (or, with
   `Modifies<{ values: "any"; spines: "grow" }, void>`, class entries
   `values: any` and `spines: grow`).
2. Before `visit(c.i)`, the loop holds `0 <= c.i` and `c.i < xs.length`. Their
   supports (`IndexFact.support?`) require `(field c "i", keep)` and
   `(field xs arraySpineKey, grow)`.
3. At `visit(c.i)`, `effectKept` calls `frameKeeps` with `callerFrame eff t`.
   - Under an unrestricted arrow, `callerFrame` contains `(all, any)`.
     `respects` fails on both `(field c "i", keep)` and
     `(field xs arraySpineKey, grow)`, so both facts are dropped.
   - Even under `Modifies<{ values: "any"; spines: "grow" }, void>`,
     `(cls values, any)` overlaps `(field c "i", keep)` because `values` covers
     every field location of the heap; `0 <= c.i` and `c.i < xs.length` are
     dropped anyway (observed in
     [the callback frames dossier](callback-frames-dossier.md#1-p22s-two-forms)).
4. At `xs[c.i]!`, the verifier refuses `walk` because neither `0 <= c.i` nor
   `c.i < xs.length` is in scope.
5. `sumAndTrace` and `sumAndAlias` are never distinguished: `walk`'s signature
   cannot express that `visit` must preserve `xs`'s spine while remaining free
   to push to its own fresh array `visited`.

### The proposed change

Keep `Footprints`, `Respect`, `SinglePass`, `ArgumentRegionGraph`,
`ModuleInterfaces`, and `PassUnit` as the single pipeline, and add four small
extensions inside them:

1. **Callback demands on `CallEffects.Effect`.** Add one field
   `demands : List CallbackDemand := []` to `CallEffects.Effect`, where each
   demand names a callback parameter position and the support it must respect,
   rooted at the outer call's `callEnv` positions (`0` receiver, `1..arity`
   actuals):

   ```text
   structure CallbackDemand where
     param   : Nat                                  -- callback position in callEnv (1 + i)
     support : Exits Footprints.Footprint           -- normal & optional onThrow support in callEnv
     actuals : List (Option (Nat × List String))    -- optional outer-call paths passed to param
   ```

   An ordinary arrow has `demands = []`. Subtyping (`Effect.Covers`) is
   contravariant in `demands`, matching `requires` and `pre`: a function
   requiring fewer callback demands covers a signature allowing more.

2. **Outer-entry support preservation (`SupportedAt`) in `PromiseWith`.**
   Extend `PromiseWith` with a premise `eff.DemandsHold r args n W h`: for
   every `d ∈ eff.demands`, whenever `f := callEnv r args d.param` is invoked
   in any future world `W' ≥ W` and heap `h₁` on arguments matching `d.actuals`
   and exits normally to `h₂`, every location `l` selected by
   `d.support.normal` at `(callEnv r args, h)` (the outer call's entry heap)
   undergoes at most its allowed change from `h₁` to `h₂` (written
   `SupportedAt d.support.normal (callEnv r args) h h₁ h₂`), and symmetrically
   for `d.support.onThrow` on exceptional return.

   Evaluating `d.support` at the outer entry heap `h` makes `DemandsHold`
   monotone under `WorldExt` and lets the caller discharge `d` once at the
   outer call site using fixed location inequalities (`l ≠ l'`). Inside the
   producer, every `.field x k` entry of `d.support` is heap-independent, and
   every `.path x p k` entry matches `(callEnv r args, h₁)` whenever the
   producer preserves the prefix fields along `p` from `h` to `h₁` (tracked by
   the existing `FirstKept` / `EntryState` prefix preservation).

3. **Local confinement for unescaped allocations (Form (a)) and path provenance
   stamps in `SepEvidence` (Form (b)).**
   - **Producer side (local cursor `c`).** A local allocation `c` inside `walk`
     whose address is never passed to `visit` and never stored into any
     location reachable from the entry heap or `visit`'s arguments cannot be
     read or written by `visit` (a general operational lemma on `Step`). Its
     support entries `(field c f, keep)` are discharged locally at `visit(...)`
     and omitted from the published `CallbackDemand`. When `walk` passes `c` to
     a helper (such as Pretext's `normalizePreparedLineStart(prepared, cursor)`),
     confinement persists provided the helper's effect does not store `c` into
     a non-confined object.
   - **Caller side (path provenance stamps).** Populate `SepEvidence.stamps` in
     `knowledgeEvidence` (`SurvivalSeparation.lean`) and generalize
     `Stamps.before` from single fields (`FootprintProvenance.lean`) to paths
     `pathBefore y p m` (every field location along `p` from `y` and every own
     or spine location of the target value lies strictly below mark $`\mu(m)`$).
     At any allocation mark `m` with $`\mu(m) = |h_m|`$, `HeapOk` and `RootsOk`
     establish `pathBefore y p m` for every live slot `y` and path `p`, while
     the new allocation `x` gets `after x = some m`. A path-level `before`
     stamp is preserved by every step whose frame keeps the fields along `p`.

4. **Parametric closure effects for adapting callbacks.** When synthesizing
   and checking a closure literal `cb` inside a function `g`, record its effect
   as a pair `(Φ_local, calls_cb)`:
   - `Φ_local`: the closure's own footprint (inferred by `ArgumentRegionGraph`
     over its captures and parameters, with fresh local allocations discharged
     by `FreshValue` / `nodeFresh`);
   - `calls_cb`: direct invocations inside `cb` of callback parameters `q` of
     the enclosing function `g`, together with the mapping from `g`'s parameter
     positions to `q`'s call.

   At a call `h(a₁, …, cb)` inside `g` where `h` demands `d_h` on `cb`:
   - `Φ_local` is checked directly against `d_h.support` (renamed into `g`'s
     slots) by `Footprints.respects (knowledgeQuery k)`;
   - each invocation of `g`'s own callback parameter `q` in `calls_cb` forwards
     the renamed demand `d_h.support` into `g`'s own `CallbackDemand` on `q`.

### Running three concrete programs through the proposed change

#### Example 1: `walk` with `sumAndTrace` and `sumAndAlias`

1. **Checking `walk(xs, visit)` (producer).**
   - `c = { i: 0 }` is allocated at mark `m_c` inside `walk`. Its address is
     never passed to `visit` (which receives the number `c.i`) and never stored
     into `xs` or any pre-existing object, so `c` is locally confined.
   - At `visit(c.i)`, the live loop facts `0 <= c.i` and `c.i < xs.length` have
     supports `(field c "i", keep)` and `(field xs arraySpineKey, grow)`.
   - `(field c "i", keep)` is discharged by local confinement of `c`.
   - The residual parameter-rooted support `[(field 1 arraySpineKey, grow)]`
     becomes `walk`'s inferred callback demand
     `d_walk = { param := 2, support := { normal := [(field 1 arraySpineKey, grow)] }, actuals := [none, none] }`.
   - Under `d_walk`, `SinglePass` verifies `visit(c.i)` retains `0 <= c.i` and
     `c.i < xs.length`, so `xs[c.i]!` verifies. `walk` publishes `d_walk` on
     its arrow `Effect`.

2. **Checking `sumAndTrace(xs)` (accepted caller).**
   - `const visited: number[] = []` allocates `visited` at mark `m₁`
     (`after visited = some m₁`, `pathBefore xs [] m₁`).
   - Closure `cb = (i) => { visited.push(i); }` has inferred parametric effect
     `(Φ_local := [(field visited arraySpineKey, extend)], calls_cb := [])`.
   - At `walk(xs, cb)`, `d_walk.support.normal` instantiates to
     `S = [(field xs arraySpineKey, grow)]`.
   - `respects (knowledgeQuery k) S Φ_local` checks whether `extend ⊑ grow`
     (true already, since `extend` grows a spine!) and also whether
     `visited`'s spine is disjoint from `xs`'s spine (`after visited = m₁ ≥ m₁ = before xs`,
     also true). Both checks succeed; `sumAndTrace` **verifies**.
   - Even if `walk` required `(field xs arraySpineKey, keep)` (for example, to
     keep `xs.length <= n`), `extend ⊑ keep` is false, and `SepEvidence.fresh`
     still discharges disjointness via `after visited = m₁ ≥ m₁ = before xs`,
     so `sumAndTrace` still **verifies**.

3. **Checking `sumAndAlias(xs)` (refused caller).**
   - Closure `cb = (_i) => { xs.pop(); }` has `Φ_local = [(field xs arraySpineKey, any)]`.
   - At `walk(xs, cb)`, `S = [(field xs arraySpineKey, grow)]`.
   - `any ⊑ grow` is false, and `xs`'s spine is not disjoint from `xs`'s spine.
     `respects` returns `false`, so `sumAndAlias` is **refused**.

#### Example 2: `collectDirect` (nested path preservation, resolving PR 330's root-only failure)

```ts
interface PreparedData {
  widths: number[];
  segmentFlags: number[];
}

/** @requires prepared.widths.length === prepared.segmentFlags.length */
function walkRaw(
  prepared: PreparedData,
  onEntry: (width: number, flag: number) => void,
): void {
  const c = { i: 0 };
  while (c.i < prepared.widths.length) {
    const w = prepared.widths[c.i]!;
    const f = prepared.segmentFlags[c.i]!;
    onEntry(w, f);
    c.i = c.i + 1;
  }
}

/** @requires prepared.widths.length === prepared.segmentFlags.length */
function collectDirect(prepared: PreparedData): number[] {
  const walked: number[] = [];
  walkRaw(prepared, (w, _f) => { walked.push(w); });
  return walked;
}

/** @requires prepared.widths.length === prepared.segmentFlags.length */
function appendToProtected(prepared: PreparedData): void {
  walkRaw(prepared, (w, _f) => { prepared.widths.push(w); });
}
```

Step by step:

1. **Checking `walkRaw(prepared, onEntry)` (producer).**
   - `c = { i: 0 }` is locally confined.
   - Across `onEntry(w, f)`, the loop invariant keeps `0 <= c.i`,
     `prepared.widths.length === prepared.segmentFlags.length`, and
     `c.i < prepared.widths.length`.
   - The non-confined supports are:
     - `(field 1 "widths", keep)`,
     - `(field 1 "segmentFlags", keep)`,
     - `(path 1 ["widths"] arraySpineKey, keep)`,
     - `(path 1 ["segmentFlags"] arraySpineKey, keep)`.
   - `walkRaw` never writes `prepared.widths` or `prepared.segmentFlags`, so
     both path prefixes stay identical to outer entry `h₀` at every iteration.
     `walkRaw` verifies and publishes this four-entry `CallbackDemand` on
     `onEntry` (`param := 2`).

2. **Checking `collectDirect(prepared)` (accepted caller).**
   - `const walked: number[] = []` creates mark `m₁` with:
     - `after walked = some m₁`,
     - `pathBefore prepared [] m₁`, `pathBefore prepared ["widths"] m₁`,
       `pathBefore prepared ["segmentFlags"] m₁` (all proved from `HeapOk` and
       `RootsOk` at `h_{m₁}`).
   - Closure `cb = (w, _f) => { walked.push(w); }` has
     `Φ_local = [(field walked arraySpineKey, extend)]`, `calls_cb = []`.
   - At `walkRaw(prepared, cb)`, `respects (knowledgeQuery k) S Φ_local` checks
     every entry of `S` against `(field walked arraySpineKey, extend)`:
     - `(field prepared "widths", keep)` vs `(field walked arraySpineKey, extend)`:
       disjoint by `Region.keysApart` (`"widths" ≠ arraySpineKey`) and by
       `SepEvidence.bound` (value vs spine) and by freshness stamps.
     - `(field prepared "segmentFlags", keep)`: disjoint by the same checks.
     - `(path prepared ["widths"] arraySpineKey, keep)`: both are spines, so
       bounds overlap, and `extend ⊑ keep` is false. `SepEvidence.fresh` checks
       `after walked = some m₁` against `pathBefore prepared ["widths"] m₁`:
       `m₁ ≤ m₁` holds, so `disjoint` returns `true`.
     - `(path prepared ["segmentFlags"] arraySpineKey, keep)`: disjoint by
       `pathBefore prepared ["segmentFlags"] m₁`.
   - Every entry succeeds; `collectDirect` **verifies**.

3. **Checking `appendToProtected(prepared)` (refused caller).**
   - Closure `cb = (w, _f) => { prepared.widths.push(w); }` has
     `Φ_local = [(path prepared ["widths"] arraySpineKey, extend)]`.
   - Against `(path prepared ["widths"] arraySpineKey, keep)`, `extend ⊑ keep`
     is false, and no separation fact or stamp separates `prepared.widths` from
     itself. `respects` returns `false`; `appendToProtected` is **refused**.

#### Example 3: `walkLines` with adapting closure (modeling Pretext's `walkRichInlineLineRanges`, resolving PR 330's wrapper failure)

```ts
interface Line { width: number; flag: number; }

/** @requires prepared.widths.length === prepared.segmentFlags.length */
function walkLines(
  prepared: PreparedData,
  visit: (line: Line) => void,
): void {
  walkRaw(prepared, (w, f) => {
    visit({ width: w, flag: f });
  });
}

/** @requires prepared.widths.length === prepared.segmentFlags.length */
function collectAdapted(prepared: PreparedData): number[] {
  const walked: number[] = [];
  walkLines(prepared, (line) => { walked.push(line.width); });
  return walked;
}
```

Step by step:

1. **Checking `walkLines(prepared, visit)` (forwarding wrapper).**
   - The adapting closure `adapter = (w, f) => { visit({ width: w, flag: f }); }`
     allocates a fresh object `{ width: w, flag: f }` (discharged from
     `Φ_local` by `FreshValue` / `nodeFresh` — empty effect on pre-existing
     locations) and invokes `walkLines`'s callback parameter `visit` (`param := 2`).
   - Its parametric effect is `(Φ_local := [], calls_cb := [(param := 2)])`.
   - At `walkRaw(prepared, adapter)`:
     - `Φ_local = []` trivially respects `d_walkRaw.support` (`respects_empty`,
       **proved** in `SurvivalSeparation.lean`).
     - Because `calls_cb` invokes `visit` (`param := 2`) and `walkLines` has
       not modified `prepared.widths` or `prepared.segmentFlags` since entry,
       `walkRaw`'s demand `S` (renamed to `walkLines`'s `callEnv` where
       `prepared` is position `1`) is forwarded directly as `walkLines`'s own
       `CallbackDemand` on `visit`.
   - `walkLines` **verifies** and publishes the same four-entry demand on
     `visit`.

2. **Checking `collectAdapted(prepared)` (accepted caller).**
   - `walked = []` establishes `after walked = some m₁` and `pathBefore` for
     `prepared`'s paths at `m₁`.
   - `line => { walked.push(line.width); }` has
     `Φ_local = [(field walked arraySpineKey, extend)]`, `calls_cb = []`.
   - Checking against `walkLines`'s forwarded demand succeeds by the exact same
     path-stamp check as `collectDirect`; `collectAdapted` **verifies**.

### What this duplicates

| Concern | Existing owner in TScert | How this design uses it | What is duplicated |
| --- | --- | --- | --- |
| Regions, changes, footprints, respect | `Footprints.lean`, `Support.lean` (`Region`, `Change`, `Footprint`, `respects`, `frame_step`) | Reused directly as the payload of `CallbackDemand.support` and for caller verification | None |
| Separation evidence & freshness marks | `SeparationEvidence.lean`, `FootprintProvenance.lean`, `SurvivalSeparation.lean` (`SepEvidence`, `Stamps`, `knowledgeQuery`) | Populates the existing `SepEvidence.stamps` field and extends `Stamps.before` from single fields to paths | None |
| Callable contracts & subtyping | `EffectSignatures.lean`, `CallEffects.lean` (`Effect`, `Arrow`, `PromiseWith`, `Effect.Covers`) | Adds one field `demands : List CallbackDemand := []` to `Effect` and one contravariant check in `Effect.Covers` | None |
| Natives & external library contracts | `tools/intrinsics.mts`, `tools/library-globals.mts`, `CallEffects.Effect` | Unchanged; native higher-order functions (e.g. `Array.prototype.forEach`) can carry `demands` on their ordinary `Effect` if desired | None |
| Outside values & world invariants | `Semantics` (`WorldT`, `HeapOk`, `RootsOk`, `builtinInvariant`) | `SupportedAt` uses the existing `WorldExt` and `HeapOk`; no separate client-protocol world or component region | None |
| Module bindings & initialization | `PassUnitFile.lean`, `ModuleInterfaces.lean` (`RowTable`, `matchStores`) | `demands` rides on `CallEffects.Effect` inside `RowSpec` and `ModuleInterfaces` | None |
| Expression & step effects | `ArgumentRegionGraph.lean`, `ArgumentRegionFresh.lean`, `PromiseCalls.lean` | Closure `Φ_local` reuses `ArgumentRegionGraph.stepWithin` / `nodeRebase`; producer fact retention reuses `frame_step` | None |
| Acceptance / soundness path | `PassUnitRealize.lean`, `PassUnitInterfaces.lean`, `PassUnitCross.lean`, `PassUnitRun.lean` (`mode8Accepted_sound`) | One acceptance path; no new `FunctionPlan` or `CertifiedPlan` constructor | None |

## Semantic model and soundness

### Definitions

Define outer-entry support preservation (`SupportedAt`) on two heaps `h₁`, `h₂`
with regions evaluated at an earlier entry heap `h₀`:

```math
\mathrm{SupportedAt}(S, \rho_0, h_0, h_1, h_2) \iff
\forall (r, \delta) \in S,\; \forall l\, v,\;
\mathrm{mem}(r, \rho_0, h_0, l) \land h_1[l] = \mathrm{some}\; v
\implies \exists v',\; h_2[l] = \mathrm{some}\; v' \land \delta.\mathrm{Holds}(|h_1|, v, v')
```

Notice that when $`h_1 = h_0`$, $`\mathrm{SupportedAt}(S, \rho_0, h_0, h_0, h_2)`$
is definitionally `Footprints.Supported S ρ₀ h₀ h₂` (**proved** by `rfl` once
defined). More generally, if every path prefix appearing in $`S`$ reads the
same value in $`h_1`$ as in $`h_0`$, then
$`\mathrm{SupportedAt}(S, \rho_0, h_0, h_1, h_2) \implies \mathrm{Supported}(S, \rho_0, h_1, h_2)`$
(**to prove**, direct induction on `Region`).

A `CallbackDemand` holds at outer entry $`(r, \bar{a}, h_0)`$ in world
$`W_0`$ at budget $`n`$ when for every $`k \le n`$, future world
$`W \ge W_0`$, heap $`h_1`$ with `HeapOk k W h₁` and $`|h_0| \le |h_1|`$, and
invocation of $`f := \mathrm{callEnv}(r, \bar{a}, d.\mathrm{param})`$ at
arguments matching $`d.\mathrm{actuals}`$:

- on normal return to $`(h_2, v)`$,
  $`\mathrm{SupportedAt}(d.\mathrm{support.normal}, \mathrm{callEnv}(r, \bar{a}), h_0, h_1, h_2)`$;
- when $`d.\mathrm{support.onThrow} = \mathrm{some}\; S_{\mathrm{exc}}`$, on
  exceptional return to $`h_2`$,
  $`\mathrm{SupportedAt}(S_{\mathrm{exc}}, \mathrm{callEnv}(r, \bar{a}), h_0, h_1, h_2)`$.

`Effect.DemandsHold eff r args n W₀ h₀` is the conjunction of
`CallbackDemand.Holds` over `d ∈ eff.demands`.

### Key theorems

1. **World monotonicity of `DemandsHold`** (**to prove**): because
   `CallbackDemand.Holds` quantifies over all future worlds `W ≥ W₀` and
   budgets `k ≤ n`, `WorldExt W₀ W₁` preserves `DemandsHold` immediately.
2. **Contravariant subtyping in `Effect.Covers`** (**to prove**): if
   `eff₁.demands` is implied by `eff₂.demands` (every demand of `eff₁` is
   covered by a demand of `eff₂` at the same `param` whose support is at least
   as strong and whose `actuals` constraint is at least as general), then
   `eff₂.DemandsHold → eff₁.DemandsHold`, so `PromiseWith` is preserved by
   `Effect.Covers` (preserving `CallArrow` and `checkArrowWith_sound`).
3. **Producer transfer at a callback call** (**to prove**): at a call to
   callback parameter `d.param` inside the producer in heap `h₁`:
   - `DemandsHold` yields `SupportedAt d.support.normal ρ₀ h₀ h₁ h₂`;
   - prefix preservation from `h₀` to `h₁` converts `SupportedAt` into
     `Supported d.support.normal ρ₀ h₁ h₂`;
   - `Footprints.frame_step` (**proved**, `Support.lean`) preserves every
     assertion whose non-confined support is subsumed by `d.support.normal`.
4. **Local confinement operational lemma** (**to prove**): define
   `Reachable h roots` as the transitive closure of heap pointers reachable
   from `roots` in `h`. For any operational transition `Step h t h' t'` (or
   multi-step execution `Steps`), if location `l` is not in
   `Reachable h (locsOf t)`, then `h'[l]? = h[l]?` and `l ∉ Reachable h' (locsOf t')`.
   Applying this to a callback invocation `visit(a₁, …)` where locally
   allocated `c`'s own locations are disjoint from
   `Reachable h (locsOf visit ∪ locsOf a₁ ∪ …)` proves
   `Supported [(field c f, keep)] ρ h₁ h₂` directly from the operational
   semantics, with no assumption on `visit`'s body.
5. **Caller discharge via `SepEvidence` and `PathBefore`** (**to prove**):
   - **Establishment**: at `HeapOk n W h` and `RootsOk W ρ`, every location
     along `readPath h (ρ y) p` and every own/spine location of its target
     value satisfies `l < h.length` (induction on `p` using `HeapOk` and
     `RootsOk`).
   - **Future-heap respect**: if `respects (knowledgeQuery k) S Φ_cb = true` at
     outer call entry `h₀`, and every entry of `Φ_cb` is heap-independent
     (`.field`, `.fields`, `.cls`, `.all`) or a path region whose prefix is
     preserved between `h₀` and `h₁`, then `Post Φ_cb ρ_cb h₁ h₂` implies
     `SupportedAt S ρ₀ h₀ h₁ h₂` for every future world `W ≥ W₀` and heap `h₁`
     with `HeapOk k W h₁`.
   - **Parametric forwarding**: if closure `cb` has checked local effect
     `Φ_local` respecting `S` and invokes outer callback parameter `q` whose
     demand in `g` covers `S` (with matching prefix agreement between `g`'s
     entry and `h`'s call site), then by transitivity of `SupportedAt` across
     steps of `cb`, `cb` satisfies `CallbackDemand.Holds` for `S`.
6. **End-to-end acceptance soundness** (**proved** architecture, extended in
   place): because `demands` is a field of `CallEffects.Effect`, `RowSpec`,
   `rowSpec_of_requestSafe`, `receiverDropSound`, `passFile_safe_kinds`,
   `crossModule_safe`, and `SourceClaimJson.PassUnit.mode8Accepted_sound`
   continue to cover every accepted unit with no new `FunctionPlan` or
   `CertifiedPlan` variant.

## Restrictions and trust

### Explicit language restrictions

Each restriction is chosen by the behaviour it excludes, not by a list of
examples:

1. **Direct callback parameter and parametric forwarding.** Demand inference
   and discharge apply where a callback parameter is called directly or
   forwarded through a closure literal whose body invokes the parameter
   directly. Storing a callback parameter in a mutable heap cell and calling it
   indirectly through the heap falls back to the callback's stated effect.
2. **Acyclic demand inference.** Within a module, callback demands are inferred
   in reverse topological order of the call graph. Mutually recursive
   higher-order functions that forward callbacks to each other infer no cyclic
   demand and use their stated effects instead.
3. **Local confinement boundary.** A local allocation is discharged as confined
   only where it is never stored into a non-confined object, never captured by
   a closure passed out, and passed only to helpers whose checked contract
   does not let that parameter escape.
4. **Normal-exit demands first.** `CallbackDemand.support` carries both
   `normal` and `onThrow : Option Footprint` on day one so the wire format has
   one shape; Stage 2 infers `normal` demands first and keeps `onThrow = none`
   unless a `try`/`catch` handler crosses the callback call.
5. **No wrapper annotation required.** Plain TypeScript callback parameters
   `(x: A) => B` with no explicit `Modifies<...>` participate in demand
   inference automatically (matching upstream Pretext's unannotated signatures
   in [the callback frames dossier](callback-frames-dossier.md#3-what-the-api-exposes)).
   An explicit `Modifies<P, T>` on a callback parameter continues to fix its
   closed effect as today.

### Trust surface

For every call between analyzed functions (single-file or cross-module through
`ModuleInterfaces`), `demands` adds **zero** trust: the caller's check
discharges `DemandsHold` and `PassUnit` proves soundness end to end.

For an **exported function with nonempty `demands`** called by unanalyzed
external code, one explicit trust row is added to
[the trust surface](../DESIGN.md#trust-surface):

- **Trust**: an external caller of an exported function whose signature carries
  a `CallbackDemand` passes a callback that respects that demand (on the same
  footing as the existing trust rows for exported `@requires` preconditions and
  stated `Modifies<...>` callback parameters).

## Size estimate and stages

### Measured footprint at the base

Exact file counts measured on `single-pass` (`536133477`) via `rg` (**observed**):

| Symbol / area | Files reading it | Impact of adding `demands : List CallbackDemand := []` |
| --- | --- | --- |
| `CallEffects.Arrow` | 35 | Unaffected (`demands` lives inside `Effect`, with default `[]`) |
| `CallEffects.Effect` | 32 | Default `[]` keeps existing constructors valid; `Effect.Covers`, `PromiseWith`, `ModuleInterfaces`, and `EffectSignatures` encoders/decoders update |
| `ExitSchema` | 22 | Unaffected (`CallbackDemand` reuses `Exits Footprints.Footprint`) |
| `PassUnit.RowSpec` | 2 | Reuses `Effect` directly; `rowSpec_of_requestSafe` threads `DemandsHold` |
| `ModuleInterfaces` | 2 | Encodes/decodes `Effect.demands` alongside `exits` and `requires` |
| `SepEvidence` / `FootprintProvenance` / `SurvivalSeparation` | 3 | Adds `pathBefore` to `Stamps`, populates `stamps` in `knowledgeEvidence`, updates `SepEvidence.fresh` |

Estimated total new Lean code across all four stages: ~1,500–2,500 lines
(not yet built; measured from the module counts above and the size of
`ArgumentRegionFresh.lean` at 425 lines and `SeparationEvidence.lean` at 717
lines).

### Staged implementation plan

Each stage lands as an independent, passing PR on `single-pass`:

- **Stage 1 — Semantic `Effect.demands`, `SupportedAt`, `PromiseWith`, and
  `Effect.Covers`.**
  Add `CallbackDemand`, `SupportedAt`, `Effect.demands` (default `[]`),
  `DemandsHold` in `PromiseWith`, and contravariant demand checking in
  `Effect.Covers` / `checkArrowWith_sound`. All existing tests pass unchanged
  because every existing arrow has `demands = []`.
- **Stage 2 — Producer demand inference, `SupportedAt` transfer, and local
  confinement.**
  Prove the operational local-confinement lemma on `Step`; discharge confined
  local allocations (Form (a)) and project residual parameter-rooted supports
  at callback call sites into `Effect.demands`; wire `SupportedAt` into
  `SinglePass` and `PassUnit` (`rowSpec_of_requestSafe`). Validates `walk`
  (producer) and `bounds-pattern-unreachable-field`.
- **Stage 3 — Path provenance stamps, caller discharge, and parametric adapting
  closures.**
  Extend `Stamps` with `pathBefore`, populate `knowledgeEvidence.stamps`, prove
  future-heap `SupportedAt` from `respects`, and add parametric
  `(Φ_local, calls_cb)` closure checking and demand forwarding. Validates
  `sumAndTrace` / `sumAndAlias`, `collectDirect` / `appendToProtected`, and
  `walkLines` / `collectAdapted` (positive and negative Node-checked cases).
- **Stage 4 — Cross-module interfaces and Pretext validation.**
  Serialize `Effect.demands` in `ModuleInterfaces` (with round-trip and
  `json-field-names` checks), update [the trust surface](../DESIGN.md#trust-surface)
  for exported demands, and run the Pretext walkers (`walkPreparedLinesRaw`,
  `walkPreparedComplexLines`, `walkLineRanges`, `walkRichInlineLineRanges`,
  `layoutWithLines`) under restored bounds.

## Comparison with Read-Only Frames and PR 330/331

| Dimension | Read-Only Frames (`single-pass`) | PR 330 / PR 331 (`InferPreserves<T>`) | Support-parametric callback arrows (this design) |
| --- | --- | --- | --- |
| Measured Lean size (**observed**) | 35,356 lines across 70 files | 8,408 lines across 53 `Callback*.lean` files | ~1,500–2,500 lines (estimated) inside existing modules |
| Soundness scope | General component rule, still unlanded in `PassUnit` (Phase 1 step 1.3.5.2; **observed** in `WORK.md`) | PR 331 proves two hardcoded shapes (`CallbackTypicalEntry.lean`, `TypicalPair`, `PrefixPlan`; **observed**) | General `CallEffects.Effect` + `PromiseWith` + `PassUnit` (`mode8Accepted_sound`), no shape-specific proofs |
| Mutable arrays / fork handles | Requires `readonly` handles + component protocol $`\Psi_C`$ + client obligation $`\Theta_C`$ (**cited**: [read-only handles](readonly-handles.md#trust)) | Works on mutable arrays; fails on `collectDirect` (root-only separation) and `walkLines` (adapting closures; **observed** in PR 330's `callback-preservation-inference.mts`) | Works on mutable arrays, nested paths (`collectDirect` via `pathBefore`), and adapting closures (`walkLines` via parametric forwarding) |
| Source annotations required | `readonly` handle types + sealed representations | `InferPreserves<T>` wrapper on callback parameters | Plain TypeScript callback types `(x: A) => B` (explicit `Modifies<...>` still respected) |
| Cross-module support | Component-wide protocol | Shared-store `PrefixPlan` only (PR 331; **observed**) | Ordinary `ModuleInterfaces` + `PassUnitCross.crossModule_safe` |
| External caller trust | Client obligation $`\Theta_C`$ on every handle | Assumed `InferPreserves` contract | One row on `DESIGN.md#trust-surface` for exported functions with nonempty `demands` |
