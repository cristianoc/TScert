# Extending `IndexFact.every`: interval bounds, shifted parallel arrays, and bitmask guards (#396, #397, #398)

This draft analyses three expressive-power limits of quantified array facts (`IndexFact.every`):

1. **#396 — Interval quantification** ($`\mathit{lo} \le i < \mathit{hi}`$), motivated by lazy mid-loop parallel-array allocation ([quantified-suffix-null-gap.ts](../../pipeline/examples/quantified-suffix-null-gap.ts), [prepare.ts](../../dev/paper-rules/pretext/src/prepare.ts)).
2. **#397 — Shifted parallel indexing** ($`q[i + \Delta]`$), motivated by sub-range builders copying a 0-indexed list into a base-shifted destination ([quantified-offset-parallel-gap.ts](../../pipeline/examples/quantified-offset-parallel-gap.ts), [rich-inline.ts](../../dev/paper-rules/pretext/src/rich-inline.ts)).
3. **#398 — Bitmask-guarded body clauses** ($`(f[i] \mathbin{\&} m) = c`$), motivated by patching an array entry under a `Uint8Array` kind-bit guard ([quantified-bitmask-guard-gap.ts](../../pipeline/examples/quantified-bitmask-guard-gap.ts), [rich-inline.ts](../../dev/paper-rules/pretext/src/rich-inline.ts)).

Each section starts from the existing mechanism, gives a general extension rather than a special case, walks its self-contained gap example through the verifier before and after the change, lists its soundness obligations and measured code footprint, and compares it against the Pretext-side source alternative.

## The existing mechanism this extends

This design extends [quantified clauses](../ARITHMETIC.md#quantified-clauses) and [supports of index facts](../FOOTPRINTS.md#supports-of-index-facts), within the [Arithmetic](../ARITHMETIC.md) general mechanism ([general mechanisms](../DESIGN.md#general-mechanisms)).

### Existing data structures and rules (read from code)

**Syntax and semantics** ([IndexFacts.lean](../../lean/Verification/Semantics/IndexFacts.lean)):

```lean
-- IndexFacts.lean
structure Term where
  kind : Term.Kind              -- .value | .length | .view | .strLength
  slot : Nat
  path : List String
  atEntry : Bool := false

inductive GuardTag where
  | null | undef | tru | fls | notNull | notUndef | notTru | notFls

inductive Bound where
  | index
  | elem
  | offset (delta : Nat)
  | project (kind : Term.Kind) (path : List String)
  | parallel (slot : Nat) (path : List String) (kind : Term.Kind) (elemPath : List String)
  | free (t : Term)

inductive ElemTarget where
  | self (elemPath : List String)
  | parallel (slot : Nat) (path : List String) (elemPath : List String)

inductive BodyClause where
  | clause (c : LinearClause Bound)
  | guarded (target : ElemTarget) (tag : GuardTag) (body : BodyClause)

inductive IndexFact where
  ...
  | every (slot : Nat) (path : List String) (stop : Term) (body : List BodyClause)
```

`IndexFact.HoldsAt` interprets `.every s p stop body` over the half-open prefix $`[0, n)`$ where $`n`$ is `termValue ε ρ h stop`:

```math
(\forall i < \mathit{stop}.\ \Phi)(\rho, h) \iff
  \exists w\,\mathit{st}\,\ell\,n.\;
  \mathrm{readPath}\,h\,(\rho\,s)\,p = \mathsf{some}\,w \land
  \mathrm{elementsOf}\,w = \mathsf{some}\,\mathit{st} \land
  h[\mathit{st}]?\mathbin{.\mathrm{bind}}\mathrm{spineEntries} = \mathsf{some}\,\ell \land
  \mathrm{termValue}\,\varepsilon\,\rho\,h\,\mathit{stop} = \mathsf{some}\,n \land
  \forall i : \mathbb{N}.\; i < n \to \forall B \in \mathit{body}.\; B.\mathrm{HoldsAt}\,\varepsilon\,\rho\,h\,\ell\,i
```

`ElemTarget.read ρ h ls i` reads `.self ep` at `ls[i]?` and `.parallel s' p' ep` at `ls'[i]?` (the same index `i`), applying `readGuard h v ep`; it does not take `ε`. `boundValue ε ρ h ls i` evaluates `.index` as `i`, `.elem` as `elementInt h ls i`, `.offset d` as `elementInt h ls (i + d)`, `.project k p` on `ls[i]?`, `.parallel s' p' k ep` on `ls'[i]?` (the same index `i`), and `.free t` as `termValue ε ρ h t`. `BodyClause.HoldsAt` evaluates `.guarded t g b` as $`\exists w.\; t.\mathrm{read}\,\rho\,h\,\ell\,i = \mathsf{some}\,w \land (g.\mathrm{holds}\,w \lor b.\mathrm{HoldsAt}\,\varepsilon\,\rho\,h\,\ell\,i)`$.

**Supports and survival** ([Survival.lean](../../lean/Verification/Semantics/Survival.lean)):

```lean
-- Survival.lean
def parallelCells (c : ReadContext) (s' : Nat) (p' : List String) : Footprint :=
  pathReads c s' .grow [] p' ++
    [(if c.arrayPath s' p' then .path s' p' arraySpineKey else .spine s' p', .keep),
     (.pathCells s' p', .keep)]

def bodyClauseSupport (c : ReadContext) (s : Nat) (p : List String) (B : BodyClause) : Footprint :=
  B.targets.flatMap (fun | .parallel s' p' [] => parallelCells c s' p' | _ => []) ++
  B.vars.flatMap fun
    | .free t => t.support c .keep
    | .project .length [] => [(.elemSpines s p, .keep)]
    | .parallel s' p' k [] => parallelCells c s' p' ++ if k == .length then [(.elemSpines s' p', .keep)] else []
    | _ => []

def everySupport (c : ReadContext) (s : Nat) (p : List String) (stop : Term) (body : List BodyClause) : Footprint :=
  pathReads c s .grow [] p ++ everyCells c s p stop (body.any BodyClause.needsKeep) ++
    stop.support c .keep ++ bodySupport c s p body
```

`ElemTarget.supported` and `Bound.supported` admit `elemPath = []` and refuse deeper element paths. `FactSupport.check_sound` (proved) establishes survival via `IndexFact.every_frame` and `IndexFact.keeps_sound`.

**Entailment, instantiation, and heap steps** ([HeapKnowledge.lean](../../lean/Verification/Semantics/HeapKnowledge.lean), [PromiseCalls.lean](../../lean/Verification/Programs/PromiseCalls.lean), [IndexWrites.lean](../../lean/Verification/Programs/IndexWrites.lean), [HeapExpressionRules.lean](../../lean/Verification/Programs/HeapExpressionRules.lean)):

```lean
-- HeapKnowledge.lean
def everyPrefix (K) (M) (m) (a) (t) : Bool :=
  -- matches target .every s' p stop' body' against source .every x p st b
  -- when termDefined a (pick stop'), bodyClauseFollows for each clause, and K ⊢ stop' ≤ st

def parallelSlot (K) (ls) (as) (s' p' k) : Option Nat :=
  -- finds unconditional .element r' y j in as with readsPath ls s' p' y and K ⊢ j = k

def instantiateEvery (K) (ls) (as) (cls) (r x k) : IndexAtom → List IndexAtom :=
  -- for unconditional .every s p st body with readsPath ls s p x, intSlot k, termDefined st,
  -- K ⊢ 0 ≤ k and K ⊢ k ≤ st - 1: maps each BodyClause through instantiateBodyClause
  -- (.guarded (.self ep) g b ↦ .guarded r ep g b';
  --  .guarded (.parallel s' p' ep) g b ↦ let r' ← parallelSlot ...; .guarded r' ep g b')
```

- Empty array and empty prefix: `linearFollowsIn` derives `.every s p stop body` when `stop == |s.p|` and `K ⊢ |s.p| ≤ 0`, or when `elementsKnown` and `K ⊢ stop ≤ 0` (proved: `linearFollowsIn_sound`).
- Push and exact typed-array writes: `PromiseCalls.every_grown`, `every_appended`, `every_written`, and `every_written_prefix` handle unguarded scalar bodies (`bodyClauseKeptBy` returns `false` for `.guarded`, `.project`, `.parallel`, `.offset`). `every_written_prefix` searches `definedTerms` for a slot equal to `i + 1`.
- Element writes on another array and scalar field writes: `IndexWrites.writeAtoms` (`every-apart-write`) and `HeapExpressionRules.fieldEvery` handle unguarded scalar bodies. `HeapExpressionRules.mergeFact` re-roots `s`, `stop`, and `body` across object merges (`mergeTarget`, `mergeBound`, `mergeBodyClause`).

**Clause elaboration and wire codec** ([bound-annotations.mts](../../tools/bound-annotations.mts), [EffectCodec.lean](../../lean/Verification/Source/EffectCodec.lean)):

```ts
// bound-annotations.mts: Parser.atom + elaborateRequires
// Syntax: `forall i in p: G* B` | `forall i < stop of p: G* B`
// `elemGuard`: `arr[i] === tag ||` (tag ∈ {null, undefined, true, false})
// Body terms: `i`, `p[i]`, `p[i+d]` (d : Nat literal), `p[i].f...`, `q[i].f...`, free terms
// Refuses `elemTag` (`p[i] === null`) as a standalone atom inside a `forall` body.
```

`EffectCodec.lean` encodes and strictly decodes `Bound`, `ElemTarget`, `BodyClause`, and `IndexFact.every` (proved round-trip: `factOf_factJ`, `decode_encode`, `decode_sound`).

### Small concrete example through the existing mechanism

Consider a function with precondition:

```ts
/** @requires safeInteger(k) && 0 <= k && k < advances.length
 *  @requires extras === null || advances.length <= extras.length
 *  @requires extras === null || forall i in advances: advances[i] === null || extras[i] === null || advances[i].length <= extras[i].length */
function readPair(advances: (number[] | null)[], extras: (number[] | null)[] | null, k: number): number {
  const a = advances[k]!;
  if (a === null || extras === null) return 0;
  const e = extras[k]!;
  if (e === null) return 0;
  return a.length > 0 ? e[0]! : 0;
}
```

1. `bound-annotations.mts` elaborates the third clause to `.guarded extras [] .null (.every advances [] (.length advances) [.guarded (.self []) .null (.guarded (.parallel extras [] []) .null (.clause (.atom (.le [(.project .length [], 1), (.parallel extras [] .length [], -1)] 0))))])`.
2. `EffectCodec.factOf` decodes the precondition and `SinglePass` installs it at function entry.
3. Reading `a = advances[k]!` emits `element(a, advances, k)`. The branch `a === null || extras === null` narrows `a !== null` and `extras !== null`, releasing the outer `.guarded extras [] .null` via `releaseGuarded`.
4. Reading `e = extras[k]!` emits `element(e, extras, k)`. `elementInstances` invokes `instantiateEvery`: `0 ≤ k < |advances|` holds, `parallelSlot` matches `element(e, extras, k)` with `k = k`, and `instantiateBodyClause` emits `.guarded a [] .null (.guarded e [] .null (.linear (|a| - |e| ≤ 0)))`.
5. Narrowing `e !== null` (together with `a !== null`) discharges both element guards, yielding `|a| ≤ |e|`. When `a.length > 0`, linear entailment proves `0 < |e|`, certifying `e[0]!`.

---

## Issue #396: Interval quantification

### Proposed general extension

Replace the implicit lower bound `0` of `IndexFact.every` with an explicit affine lower bound, and make both bounds uniform affine expressions over at most one `Term` plus an integer offset:

```lean
/-- An affine index bound `t + offset` (or the constant `offset` when `base = none`). -/
structure IndexBound where
  base : Option Term := none
  offset : Int := 0
  deriving DecidableEq, Repr, Hashable

def IndexBound.eval (ε : EntryState) (ρ : Env) (h : Heap) (b : IndexBound) : Option Int :=
  match b.base with
  | none => some b.offset
  | some t => (termValue ε ρ h t).map (· + b.offset)

inductive IndexFact where
  ...
  | every (slot : Nat) (path : List String) (start stop : IndexBound) (body : List BodyClause)
```

`Term` has no constant-zero constructor because every `Term` reads a slot; `IndexBound` with `base = none, offset = 0` represents `0` without introducing a synthetic slot, and `{ base := some (.value i), offset := 1 }` represents `i + 1` immediately after a write at `i` without requiring a source variable `const next = i + 1`. Prefix quantifiers (`start = ⟨none, 0⟩`), full-array quantifiers (`start = ⟨none, 0⟩, stop = ⟨some |x.p|, 0⟩`), suffix quantifiers (`start = ⟨some i, 0⟩, stop = ⟨some |x.p|, 0⟩`), and arbitrary sub-intervals `[lo, hi)` are all instances of one constructor.

The semantics in `IndexFact.HoldsAt`:

```math
(\forall \mathit{lo} \le i < \mathit{hi}.\ \Phi)(\rho, h) \iff
  \exists w\,\mathit{st}\,\ell\,m\,n.\;
  \mathrm{readPath}\,h\,(\rho\,s)\,p = \mathsf{some}\,w \land
  \mathrm{elementsOf}\,w = \mathsf{some}\,\mathit{st} \land
  h[\mathit{st}]?\mathbin{.\mathrm{bind}}\mathrm{spineEntries} = \mathsf{some}\,\ell \land
  \mathrm{eval}\,\varepsilon\,\rho\,h\,\mathit{lo} = \mathsf{some}\,m \land
  \mathrm{eval}\,\varepsilon\,\rho\,h\,\mathit{hi} = \mathsf{some}\,n \land
  \forall i : \mathbb{N}.\; m \le i \land i < n \to \forall B \in \mathit{body}.\; B.\mathrm{HoldsAt}\,\varepsilon\,\rho\,h\,\ell\,i
```

A second, orthogonal piece of #396 is expressing a pure element-tag assertion such as `extras[j] === null` as a `forall` body. `BodyClause` represents this with no new constructor as `.guarded (.self []) .null (.clause (.atom (.le [] (-1))))` (guarded falsum: `0 ≤ -1` is false, so `BodyClause.HoldsAt` reduces to `∃ w, t.read ρ h ls j = some w ∧ w = .nul`). Only `bound-annotations.mts` needs to admit a standalone `elemTag` atom inside a `forall` body (lifting the refusal at line 934) and `fact-text.mts` to print guarded falsum as `e === null`.

Three general inference rules follow directly from interval bounds:

1. **Interval weakening (`everySubinterval`, generalizing `everyPrefix`):** from $`\forall \mathit{lo} \le i < \mathit{hi}.\ \Phi`$, with $`\mathit{lo}'`$ and $`\mathit{hi}'`$ defined, $`K \vdash \mathit{lo} \le \mathit{lo}'`$, and $`K \vdash \mathit{hi}' \le \mathit{hi}`$, conclude $`\forall \mathit{lo}' \le i < \mathit{hi}'.\ \Phi`$.
2. **Vacuous empty interval (generalizing `every-empty`):** when `elementsKnown` holds (or $`\mathit{hi} = |s.p|`$ and $`K \vdash |s.p| \le 0`$), $`\mathit{lo}`$ and $`\mathit{hi}`$ are defined, and $`K \vdash \mathit{hi} \le \mathit{lo}`$, any body holds on $`[\mathit{lo}, \mathit{hi})`$.
3. **Interval split around an element write at index $`k`$:** given an in-bounds write `store[k] = v` on an array with distinct element cells (#392), an interval quantifier $`\forall \mathit{lo} \le i < \mathit{hi}.\ \Phi`$ yields:
   - $`\forall \mathit{lo} \le i < \mathit{hi}.\ \Phi`$ unchanged if $`K \vdash k < \mathit{lo}`$, $`K \vdash \mathit{hi} \le k`$, or $`v`$ satisfies $`\Phi`$ at $`k`$;
   - the left sub-interval $`\forall \mathit{lo} \le i < k.\ \Phi`$ (when $`K \vdash \mathit{lo} \le k < \mathit{hi}`$) and right sub-interval $`\forall k + 1 \le i < \mathit{hi}.\ \Phi`$ (using `{ base := some (.value k), offset := 1 }`) even when $`v`$ does not satisfy $`\Phi`$.

In the annotation grammar (`tools/bound-annotations.mts`), interval syntax generalizes `forall i < stop of P: B` to `forall lo <= i < hi of P: B` (and `forall lo <= i in P: B` defaulting `hi` to `P.length` / `view(P)`).

### Walkthrough: `quantified-suffix-null-gap.ts`

In [quantified-suffix-null-gap.ts](../../pipeline/examples/quantified-suffix-null-gap.ts), `buildLazyExtras` loops `i` from `0` to `n = srcAdvances.length`, appending `adv = srcAdvances[i] ?? null` to `advances` on every iteration, while lazily allocating `extras ??= new Array(n).fill(null)` and writing `extras[i] = ex` only when `adv !== null && ex !== null`.

- **As the verifier is:** the loop head cannot state that unwritten cells of `extras` hold `null` on $`[i, n)`$ (`IndexFact.every` fixes its lower bound at `0`, and `bound-annotations.mts` refuses `extras[j] === null` as a `forall` body). On an iteration where `extras !== null` and `adv !== null && ex === null`, the dense append `advances[i] = adv` has no fact stating `extras[i] === null`, so the parallel length invariant on `advances` and `extras` cannot extend to `i + 1`. The return `{ advances, extras }` is refused (`source ensures refusal at [1943,1963)`).
- **As it would be (assuming #391–#395):** the loop carries:
  - `advances.length === i && 0 <= i && i <= n`
  - `extras === null || extras.length === n`
  - `extras === null || forall j in advances: advances[j] === null || extras[j] === null || advances[j].length <= extras[j].length`
  - `extras === null || forall i <= j < n of extras: extras[j] === null`
  1. *Loop entry (`i = 0`, `extras = null`):* `extras === null` discharges all three guarded invariants.
  2. *Branch `adv !== null && ex !== null`:*
     - If `extras === null`: `new Array(n).fill(null)` establishes `extras.length === n` and `forall 0 <= j < n of extras: extras[j] === null` (#393). Interval weakening gives `forall 0 <= j < i of extras: extras[j] === null` (discharging the parallel invariant on `[0, i)`) and `forall i <= j < n of extras: extras[j] === null`.
     - After the `??=` merge, `store[i] = ex` overwrites cell `i`: `i` lies outside `[0, i)` (keeping the parallel invariant on `[0, i)`, #392), splits `[i, n)` to the surviving right suffix `forall i + 1 <= j < n of extras: extras[j] === null`, and records `store[i] === ex`.
     - `advances[i] = adv` extends the parallel invariant from `[0, i)` to `[0, i + 1)` using `adv.length <= ex.length` (#395) and preserves the suffix invariant on `extras` by apartness.
  3. *Branch `adv === null || ex === null` with `extras !== null`:*
     - Instantiating `forall i <= j < n of extras: extras[j] === null` at `i` (since `i ≤ i < n`) establishes `extras[i] === null`.
     - `advances[i] = adv` extends the parallel invariant to `[0, i + 1)` vacuously via `adv === null || extras[i] === null` (#395).
     - Interval weakening shrinks `[i, n)` to `[i + 1, n)`.
  4. *Back edge (`i++` binds `i' = i + 1`):* `{ base := some (.value i), offset := 1 }` matches `{ base := some (.value i'), offset := 0 }` via linear equality `i' = i + 1`.
  5. *Loop exit (`i === n`):* `advances.length === n`, so the guarded parallel invariant over `advances` establishes `LazyParallel`'s `@invariant`s.

### Soundness obligations (#396)

- **Survival / framing (`Survival.lean`):** `everySupport` adds `start.support c .keep` (empty when `start.base = none`, else `t.support c .keep`). `IndexFact.every_frame` gains premise `∀ m, start.eval ε ρ h = some m → start.eval ε ρ h' = some m`. No new `Region` constructor is needed.
- **Entailment and instantiation (`HeapKnowledge.lean`):** `everySubinterval_sound` proves `lo ≤ lo' ∧ hi' ≤ hi` implies sub-interval satisfaction; `instantiateEvery_holds` adds the lower-bound premise `K ⊢ lo ≤ k` (which reduces to the existing `K ⊢ 0 ≤ k` when `lo = ⟨none, 0⟩`); `atIndexFollows_sound` checks `lo ≤ idx < hi`.
- **Writes, pushes, and merges (`PromiseCalls.lean`, `IndexWrites.lean`, `HeapExpressionRules.lean`):** `every_written` and the ordinary-array overwrite rule (#392) prove interval survival and `[lo, k)` / `[k + 1, hi)` splitting using cell distinctness (`listT` cells distinct); `every_grown` keeps `start` via `IndexBound.keptBy`; `mergeFact` re-roots both `start` and `stop`.
- **Wire and annotation lowering (`EffectCodec.lean`, `tools/bound-annotations.mts`, `docs/ANNOTATIONS.md`):** `IndexBound` gets a canonical JSON codec (`boundTermJ`/`boundTermOf`) with round-trip proof in `factOf_factJ`; `bound-annotations.mts` parses `lo <= i < hi` and standalone `elemTag` body atoms, rejecting non-integral `lo`/`hi`; `ANNOTATIONS.md` documents the syntax.

### Measured size estimate (#396)

Measured by searching every pattern match on `IndexFact.every` across `lean/` and `tools/`:

- **Lean (14 files):**
  - Core semantics & framing: `IndexFacts.lean` (`IndexBound`, `IndexFact.every`, `slots`, `entrySlots`, `entryTerms`, `defines`, `mapM`, `mapEntry`, `toNow`, `HoldsAt`, `every_frame`, `everyKept`), `Survival.lean` (`everySupport`, `everyCells`, `FactSupport.check_sound`), `HeapKnowledge.lean` (`factFollows`, `every_follows`, `everyPrefix` → `everySubinterval`, `linearFollowsIn`, `instantiateEvery`, `atIndexFollows`, `readEvery`, `liftEvery`), `StepRelations.lean` (`Composer.fact`, `Composer.stops`).
  - Program rules: `PromiseCalls.lean` (`every_grown`, `every_appended`, `everyGrown`, `every_written`, `every_written_prefix`, `everyWritten`, `writtenPrefix`), `IndexWrites.lean` (`writeAtoms`, plus #392 overwrite split), `HeapExpressionRules.lean` (`mergeFact`, `fieldEvery`), `SinglePass.lean` (2 sites), `Parametricity.lean` (1 wildcard), `TolerantFramesStoreOpsNames.lean` (slot-map lemma).
  - Source elaboration & codec: `EffectCodec.lean` (`factJ`, `factOf`, `factOf_factJ`), `SourceClaims.lean` (`EveryClaim`), `Lowering/Flow.lean` (`invariantFact`, `quantified`), `HeadInference.lean` (`Fact.every`, `Fact.everyClaim`, `ofIndexFact`, `Fact.restate`, `Fact.keptAcross`, `Fact.text`), `Wire.lean` (1 site), `MemberSettle.lean` (1 wildcard).
- **TypeScript & tests (5 files):** `tools/declaration-types.mts` (`IndexFact["every"]`), `tools/bound-annotations.mts` (`Parser`, `elaborateRequires`, `indexFactPositions`, `rootsOf`), `tools/diagnostic.mts`, `tools/fact-text.mts`, plus `tests/json-field-names.mts` if field lists change and positive/negative/control cases.
- **Docs (3 files):** `docs/ARITHMETIC.md`, `docs/ANNOTATIONS.md`, `docs/REQUEST-PROTOCOL.md`.
- Note: `TwoStateFormulas.lean`, `AssertionScopes.lean`, and `Parity*.lean` use a separate `Atom.every` and do not need changes unless the paper layer adopts interval bounds.

### Pretext-side alternative (#396)

At [prepare.ts:557-564](../../dev/paper-rules/pretext/src/prepare.ts), `measureAnalysis` allocates `breakableLineStartExtras ??= new Array<number[] | null>(to - from).fill(null)` on the first non-null `startExtras` and writes `breakableLineStartExtrasStore[mi - from] = startExtras`, leaving indices `[mi - from + 1, to - from)` untouched. Notably, `discretionaryHyphenContexts` in the same loop ([prepare.ts:649-660](../../dev/paper-rules/pretext/src/prepare.ts)) avoids suffix reasoning by using lazy prefix growth:

1. **Alternative 396-P1 (lazy prefix growth, matching `discretionaryHyphenContexts`):** allocate `breakableLineStartExtras ??= new Array<number[] | null>(mi - from).fill(null)` on first hit, write at `idx = mi - from` (dense append, #395), and add `else if (breakableLineStartExtras !== null) { breakableLineStartExtras[idx] = null }`.
   - *Effect on Pretext:* zero allocation when no segment has `startExtras` (common case); prefix invariant `breakableLineStartExtras.length === mi - from` holds at every step with prefix-only `every`. Trade-off: when `breakableLineStartExtras !== null`, the array grows dynamically instead of being pre-sized once to `to - from`, and every subsequent iteration pays one null check + write.
2. **Alternative 396-P2 (keep pre-sized allocation, write `null` on else branch):** keep `new Array(to - from).fill(null)` and write `else if (breakableLineStartExtras !== null) breakableLineStartExtras[idx] = null`.
   - *Effect on Pretext:* preserves fixed-capacity allocation (no dynamic resize), discharges the parallel invariant at `idx` without a suffix quantifier, and relies on #393 + `everyPrefix` to cover `[0, mi - from)` on first allocation. Trade-off: adds one redundant write per remaining segment when `breakableLineStartExtras !== null`, leaving a redundant store in Pretext solely for verification.

---

## Issue #397: Shifted parallel indexing

### Proposed general extension

Replace the implicit zero shift in `Bound.parallel` and `ElemTarget.parallel` (and subsume `Bound.offset (delta : Nat)`) with a general affine index shift `IndexShift`:

```lean
/-- An affine shift `Σ c·t + offset` added to the quantified index `i`.
`⟨[], 0⟩` is unshifted `i`; `⟨[], d⟩` is `i + d`; `⟨[(base, 1)], 0⟩` is `i + base`;
`⟨[(base, 1), (from, -1)], 0⟩` is `i + base - from`. -/
structure IndexShift where
  terms : Linear.Form Term := []
  offset : Int := 0
  deriving DecidableEq, Repr, Hashable

def IndexShift.eval (ε : EntryState) (ρ : Env) (h : Heap) (i : Nat) (sh : IndexShift) : Option Nat :=
  if sh.terms.all fun p => (termValue ε ρ h p.1).isSome then
    let idx := (i : Int) + Linear.Form.eval (termValuation ε ρ h) sh.terms + sh.offset
    if 0 ≤ idx then some idx.toNat else none
  else none

inductive Bound where
  | index
  | elem
  | offset (delta : Nat)   -- or unified as `projectAt (shift : IndexShift) ...`
  | project (kind : Term.Kind) (path : List String)
  | parallel (slot : Nat) (path : List String) (shift : IndexShift) (kind : Term.Kind) (elemPath : List String)
  | free (t : Term)

inductive ElemTarget where
  | self (elemPath : List String)
  | parallel (slot : Nat) (path : List String) (shift : IndexShift) (elemPath : List String)
```

Using `Linear.Form Term × Int` rather than a single positive `Term` avoids creating a special case for `+base`: it handles `+base`, `-base`, `base - from` (the exact index expression `at = base + mi - from` in [prepare.ts:464](../../dev/paper-rules/pretext/src/prepare.ts)), constant offsets, and entry terms such as `old(lists.breakableFitAdvances.length)` in `@ensures` postconditions.

Semantics:

- `ElemTarget.read` takes `ε : EntryState` because `sh.terms` may contain `Term.old` entry terms: `.parallel s' p' sh ep` evaluates `j ← sh.eval ε ρ h i` and reads `ls'[j]?`.
- `boundValue` evaluates `.parallel s' p' sh k ep` at `j ← sh.eval ε ρ h i` and reads `ls'[j]?`.
- `parallelSlot` generalizes its index match from `K ⊢ j = k` to:

```math
\forall t \in \mathrm{vars}(\mathit{sh}.\mathrm{terms}).\; \mathrm{termDefined}\,as\,t \quad\land\quad
K \vdash j = k + \mathit{sh}.\mathrm{terms} + \mathit{sh}.\mathrm{offset}
```

### Walkthrough: `quantified-offset-parallel-gap.ts`

In [quantified-offset-parallel-gap.ts](../../pipeline/examples/quantified-offset-parallel-gap.ts), `appendSubRange(prefix, subWidths)` executes four phases:

1. `const advances = prefix.advances.slice(); const base = advances.length;`
2. **Loop 1** (`s = 0 .. subWidths.length - 1`): pushes `[w]` onto `advances` and `[w, 0]` onto `subExtras`.
3. **Loop 2** (`i = 0 .. base - 1`): allocates `extras = new Array(advances.length).fill(null)` and copies `extras[i] = prefix.extras[i] ?? null`.
4. **Loop 3** (`s = 0 .. subExtras.length - 1`): sets `at = base + s` and copies `extras[at] = subExtras[s] ?? null`.

- **As the verifier is:** no `IndexFact.every` can relate `advances[base + s]` to `subExtras[s]`, because `Bound.parallel` and `ElemTarget.parallel` index `ls'[i]?` at the identical `i`. Thus Loop 1 cannot establish any relation between `advances` and `subExtras`, Loop 3 cannot establish that `extras[base + s]` matches `advances[base + s]`, and the return `{ advances, extras }` is refused (`source ensures refusal at [1660,1680)`).
- **As it would be:** tracing every step reveals **four** distinct verifier additions required to close `appendSubRange`, not just `IndexShift`:
  1. *Shallow-copy transfer on `slice()` (line 18):* [array-prototype.mts:345-355](../../tools/array-prototype.mts) states only `result.length === this.length` for 0-arg `slice()`. Relating `advances[i]` to `prefix.extras[i]` for `0 <= i < base` in Loop 2 requires `slice()` to transfer `IndexFact.every` from `prefix.advances` onto the fresh copy `advances`.
  2. *Loop 1 push sequencing (`advances.push([w]); subExtras.push([w, 0])`):*
     - After `advances.push([w])`, the existing shifted invariant `forall k in subExtras: advances[base + k] === null || subExtras[k] === null || advances[base + k].length <= subExtras[k].length` must survive `advances`'s spine extending by `.extend`. `Survival.parallelCells` demands `.keep` on a parallel array's spine; relaxing ordinary-array parallel spines to `.extend` (sound because `Change.Holds.extend_entry` keeps every existing entry `ls[j]` at its index) lets the invariant survive `advances.push([w])`.
     - `advances.push([w])` must also record an element witness at `old(|advances|) = base + s` (`element(v, advances, base + s)` or `atIndex`) so that the immediately following `subExtras.push([w, 0])` has `advances[base + s].length === 1 <= 2 === [w, 0].length` when extending the shifted invariant from `s` to `s + 1`.
  3. *Copy-transfer rule for element writes (Loops 2 and 3):* neither Loop 2 (`extras[i] = prefix.extras[i] ?? null`) nor Loop 3 (`extras[at] = subExtras[s] ?? null`) reads `advances[i]` or `advances[at]` at runtime. Because `instantiateEvery` requires an `element(r', advances, at)` witness for every parallel array, `instantiateEvery` cannot fire in Loop 2 or Loop 3. Closing them requires a **parallel copy-transfer rule** on element writes: writing `dst[at] = v` where `element(v, src, s)` holds (or `v === null`) transfers a body clause relating `advances[at]` to `src[s]` (with `K ⊢ at = s + shift`) into the same body clause relating `advances[at]` to `dst[at]` without a runtime read of `advances[at]`.
  4. *Loop 3 invariant (`forall j < base + s of advances: ...`):* extending the unshifted parallel invariant from `base` (after Loop 2) to `base + subExtras.length = advances.length` (after Loop 3) uses the shifted invariant on `subExtras` plus the copy-transfer rule at each `at = base + s` (and #396's affine `IndexBound` `base + s`, or a loop-bound `at`).

### Soundness obligations (#397)

- **Entry-state threading in `ElemTarget` (`IndexFacts.lean`):** because `IndexShift.terms` holds `Term`s that may have `atEntry = true`, `ElemTarget.read` takes `ε : EntryState`, and `ElemTarget` gains `entrySlots`, `entryTerms`, `mapEntry`, `toNow`. Every `BodyClause` congruence/renaming lemma (`holdsAt_mapM`, `holdsAt_congr`, `holdsAt_congr_entry`, `holdsAt_entry`, `holdsAt_mapEntry`, `holdsAt_congr_entryTerms`, `holdsAt_toNow`) must cover `ElemTarget.parallel`'s shift terms.
- **Survival and `.extend` precision (`Survival.lean`):** `bodyClauseSupport` adds `sh.terms.flatMap (fun p => p.1.support c .keep)` for both `ElemTarget.parallel` and `Bound.parallel`. Relaxing `parallelCells`'s array-spine requirement from `.keep` to `.extend` (when `c.arrayPath s' p'` holds) requires proving `parallelCells_kept` from `Change.Holds.extend_entry` (prefix preservation `ls <+: ls'` keeps `ls'[j]? = some (some l)`).
- **Instantiation (`HeapKnowledge.lean`):** `parallelSlot_read` must prove `i + eval sh.terms + sh.offset = j` from `K.entails` of the two linear inequalities and `termDefined` of every term in `sh.terms`.
- **Push witness, slice transfer, and copy-transfer (`PromiseCalls.lean`, `IndexWrites.lean`, `tools/array-prototype.mts`):**
  - `ReceiverAppends` proves `ls'[ls.length]? = some (some l) ∧ h'[l]? = some (ρ x)`; exposing an `atIndex`/`element` fact at `old(|a|)` follows from `ReceiverAppends`.
  - Shallow-copy transfer for `slice()` adds an audited `OperationPost` (or `ArrayCopy` postcondition) in `tools/array-prototype.mts`, widening the trusted native spec surface.
  - Copy-transfer on `dst[at] = v` (with `element(v, src, s)`) must prove that `dst[at]`'s new cell holds the exact `Val` of `src[s]`, so every `ElemTarget.read` and `boundValue` on `dst[at]` agrees with `src[s]` while `advances[at]` is untouched (requiring `apartFrom` between `dst` and `advances`).
- **Wire and annotation lowering (`EffectCodec.lean`, `tools/bound-annotations.mts`, `docs/ANNOTATIONS.md`):** `bound-annotations.mts`'s `Parser.element` parses only `p[idx]` or `p[idx + d]` with a numeric literal `d`; it must parse general linear index expressions `q[base + s]`, `q[i - base]` inside `forall` bodies and element guards, resolving all shift terms against outer guards and `old(...)`. `EffectCodec` adds `shift` to `Bound.parallel` and `ElemTarget.parallel` with round-trip proofs.

### Measured size estimate (#397)

Measured from every match on `Bound.parallel` / `ElemTarget.parallel` plus the extra write/slice rules above:

- **Lean (15 files):** `IndexFacts.lean` (`IndexShift`, `Bound`, `ElemTarget`, `ElemTarget.read`, `boundValue`, 10+ congruence/renaming/entry theorems), `Survival.lean` (`bodyClauseSupport`, `parallelCells`, `parallelCells_kept`, `FactSupport.check_sound`), `HeapKnowledge.lean` (`boundFollows`, `elemTargetFollows`, `lowerTarget`, `lowerBound`, `parallelSlot`, `parallelSlot_read`, `instantiateBodyClause`), `StepRelations.lean` (`Composer.bodyClause`, `Composer.atom`), `HeapExpressionRules.lean` (`mergeTarget`, `mergeBound`, `mergeBodyClause`), `PromiseCalls.lean` (`every_grown`, `every_appended`, push element witness, slice transfer), `IndexWrites.lean` (copy-transfer write rule), `TolerantFramesStoreOpsNames.lean`, `EffectCodec.lean` (`boundJ`/`boundOf`, `elemTargetJ`/`elemTargetOf`, round-trip proofs), `SourceClaims.lean` (`BodyRef`, `ElemTargetRef`), `Lowering/Flow.lean` (`invariantFact`, `bodyClause`), `HeadInference.lean` (`BodyKey`, `ElemTargetKey`, `Fact.restate`, `Fact.keptAcross`, `ofIndexFact`, `Fact.text`), `Wire.lean`, plus `CallEffects.lean` / `Parity` if `slice()` gains a new `OperationPost`.
- **TypeScript & tests (6 files):** `tools/declaration-types.mts`, `tools/bound-annotations.mts` (`Parser.element`, `splitIndexed`, `elaborateRequires`, `bodyPositions`, `rootsOf`), `tools/array-prototype.mts` (`slice`), `tools/diagnostic.mts`, `tools/fact-text.mts`, plus `tests/json-field-names.mts` and cases/controls.
- **Docs (4 files):** `docs/ARITHMETIC.md`, `docs/ANNOTATIONS.md`, `docs/REQUEST-PROTOCOL.md`, `docs/SOURCE-CONTRACTS.md` (audited `slice` transfer).

### Pretext-side alternative (#397)

At [rich-inline.ts:496-578](../../dev/paper-rules/pretext/src/rich-inline.ts), `prepareRichInline` passes `const lists: ParagraphLists = { widths, segmentFlags: flags, breakableFitAdvances }` to `measureAnalysis` ([prepare.ts:272-275, 370-713](../../dev/paper-rules/pretext/src/prepare.ts)), which writes `widths`, `segmentFlags`, and `breakableFitAdvances` directly at `at = base + (mi - from)`, but allocates `breakableLineStartExtras` locally at index `mi - from` (0-indexed) and returns it on `sub`, forcing `rich-inline.ts:570-578` to copy `sub.breakableLineStartExtras[s]` into `breakableLineStartExtras[itemAt + s]`. `ParagraphLists` has only this one caller in Pretext.

- **Alternative 397-P1 (include `breakableLineStartExtras` on `ParagraphLists`):** pass `breakableLineStartExtras` in `ParagraphLists` (a mutable holder field, or pass the paragraph's array) so `measureAnalysis` writes `breakableLineStartExtras[at] = startExtras` at the exact index `at` where it writes `breakableFitAdvances[at] = fitAdvances` ([prepare.ts:633](../../dev/paper-rules/pretext/src/prepare.ts)).
  - *Effect on Pretext:* deletes the 9-line copy loop at `rich-inline.ts:570-578`, avoids allocating a temporary per-item `sub.breakableLineStartExtras` array for rich-inline items, and aligns `breakableLineStartExtras` with the other three paragraph lists (`widths`, `segmentFlags`, `breakableFitAdvances`). The parallel invariant between `breakableFitAdvances` and `breakableLineStartExtras` stays unshifted (`at` vs `at`) across the call boundary.
  - *Trade-off:* `ParagraphLists` gains one field (`breakableLineStartExtras: (number[] | null)[] | null`) and `measureAnalysis` writes `breakableLineStartExtras` at `at` instead of `mi - from` when `paragraph !== null` (requiring `flags.length` capacity in `ParagraphLists` or lazy prefix growth as in 396-P1). No other Pretext site constructs a shifted parallel `number[][]` invariant (`sub.lineStartExtras` and `sub.lineEndTrims` are 1D `number[] | null` with outer-length invariants only).

---

## Issue #398: Bitmask-guarded body clauses

### Proposed general extension

A bitmask test `(flags[i] & mask) === val` is a periodic congruence on integers ($`\mathrm{ToInt32}(v) \mathbin{\&} m = c`$), not a linear inequality and not a primitive tag (`null`/`undefined`/`true`/`false`). Adding a special `bitMaskEq` case to `GuardTag` would conflate numeric bitwise predicates with primitive tag tests across all 17 files that read `GuardTag` (including `HeapKnowledge.onlyTag` over `ValueSet` and `SurvivalSeparation.tag_reads`).

The clean general formulation separates two orthogonal concerns:

1. **Uniform disjunctive body clauses (`BodyClause`):** unify `BodyClause.guarded` and `LinearClause.either` into a positive disjunction of linear atoms and element-tag atoms:
   ```lean
   inductive BodyClause where
     | linear (f : Linear.Fact Bound)
     | tag (target : ElemTarget) (tag : GuardTag)
     | either (left right : BodyClause)
   ```
   This subsumes both #396's pure element-tag body (`extras[j] === null`) and arbitrary combinations of linear disequalities with element guards (`(flags[i] & 7) !== 2 || extras[i] === null`).
2. **Bitmask term projection and bitwise facts:**
   - Extend `Term` (or `Term.Kind`) and `Bound` with a masked-integer projection `bitMask (mask : Nat)` (for $`0 \le \mathit{mask} < 2^{31}`$), evaluated as `intValue v >>= fun z => some (intAnd (toInt32Bits ...) mask)` (or directly via `IndexNumbers.intAnd (toInt32 b) mask` on `.num b`, reusing `ArithmeticRules.lean`'s semantics).
   - Then `(flags[i] & 7) !== 2 || extras[i] === null` is `.either (.linear (.ne [(.parallel flags [] (.bitMask 7) [], 1)] 2)) (.tag (.parallel extras [] []) .null)` — using existing `.ne` disequalities!
   - Add an exact bitwise step fact in `IndexWrites.stepAtoms` / `ArithmeticRules` so `const m = f & 7` records the linear equality `m = bitMask(7, f)` (connecting runtime slot `m` to the masked term on `f`), together with bitwise algebraic rules:
     - **Constant folding:** when `K ⊢ x = c` (a constant within `int32`), `bitMask(m, x) = intAnd c m`.
     - **Idempotence / absorption:** `bitMask(m, x & m') = bitMask(m & m', x)`.
     - **Disjoint-bit OR invariance:** when `r = x | y` and `y` is a known constant (or masked value) with `intAnd y m = 0`, `bitMask(m, r) = bitMask(m, x)`.

The third algebraic rule (disjoint-bit OR invariance) is not optional for Pretext: `prepare.ts:627, 646` and `rich-inline.ts:451, 541` mutate `flags[at]` with `| SPACED`, `| DROPPED`, `| UNBROKEN` (bits `≥ 8`, disjoint from `KIND_BITS = 0x7`) while preserving the low 3 kind bits.

### Walkthrough: `quantified-bitmask-guard-gap.ts`

In [quantified-bitmask-guard-gap.ts](../../pipeline/examples/quantified-bitmask-guard-gap.ts), `buildAndPatchPreservedSpace(kinds, patchAt)` fills `flags[i] = kinds[i]! & 0x7`, pushes `[10, 20]` / `[1, 2]` when `k === TEXT (1)` and `null` / `null` otherwise, and then if `(flags[patchAt]! & 0x7) === PRESERVED_SPACE (2)` overwrites `advances[patchAt] = [5, 5, 5]`.

- **As the verifier is:**
  1. `bound-annotations.mts` refuses `(flags[i] & 7) !== 2` inside a `forall` clause (`&` is outside the clause lexer at line 230).
  2. Even if encoded, `IndexWrites.stepAtoms` and `ArithmeticRules.maskRange`/`maskBound` record only `0 <= m <= 7` and `m <= f` for `m = f & 7`, discarding the bitwise identity `m = f & 7`.
  3. At `advances[patchAt] = [5, 5, 5]`, the verifier cannot deduce `extras[patchAt] === null` from `(flags[patchAt] & 7) === 2`, so the parallel invariant `advances[i].length <= extras[i].length` fails at the overwrite (`source ensures refusal at [1856,1883)`).
- **As it would be:**
  1. *Loop invariant:* `forall i in advances: (flags[i] & 7) !== 2 || extras[i] === null` (in `BodyClause`: `.either (.linear (.ne [(.parallel flags [] (.bitMask 7) [], 1)] 2)) (.tag (.parallel extras [] []) .null)`).
  2. *Loop body:* `k = kinds[i]! & 7` records `k = bitMask(7, kinds[i])` and `bitMask(7, k) = k` (idempotence of `& 7`); `flags[i] = k` records `flags[i] = k`.
     - Branch `k === 1`: constant folding gives `bitMask(7, flags[i]) = 1 ≠ 2`, satisfying the left disjunct of the bitmask-guarded invariant when `extras.push([1, 2])` runs.
     - Branch `k !== 1`: `extras.push(null)` satisfies the right disjunct `extras[i] === null`.
  3. *Post-loop patch:* `f = flags[patchAt]!` gives `element(f, flags, patchAt)`; `m = f & 7` records `m = bitMask(7, f)`; the `if (m === 2)` branch gives `K ⊢ bitMask(7, f) = 2`.
  4. *Instantiation & overwrite:* instantiating `forall i in advances: (flags[i] & 7) !== 2 || extras[i] === null` at `patchAt` yields `bitMask(7, f) ≠ 2 ∨ extras[patchAt] === null`. Linear entailment refutes `bitMask(7, f) ≠ 2` from `bitMask(7, f) = 2`, leaving `extras[patchAt] === null`, which discharges the parallel invariant across `advances[patchAt] = [5, 5, 5]` (#392).

### Soundness obligations (#398)

- **Bitwise semantics (`IndexFacts.lean`, `IndexNumbers.lean`, `ArithmeticRules.lean`):** define `kindValue` for `.bitMask m` via `toInt32` and `intAnd` (for `0 ≤ m < 2^31`), prove `0 ≤ bitMask m v ≤ m` (`termRange_holds`), and prove the three step rules (exact `bitAnd` equality, idempotence, and disjoint-mask `bitOr` preservation) against `arithBits .bitAnd` / `arithBits .bitOr` in `Semantics.lean` (no `sorry` or axioms).
- **Disjunctive `BodyClause` framing & instantiation (`Survival.lean`, `HeapKnowledge.lean`):** `bitMask m` reads the same element cell as `.value` (requiring no new `Region`, kept by `.init` on numbers or `.keep` when combined with element guards). `instantiateBodyClause` maps `BodyClause.either` to `IndexFact.either`, `BodyClause.tag` to `.guarded r ep g falsum` (or a new `IndexFact.elemTag`), and `BodyClause.linear` to `IndexFact.linear`. `guardEntails` / `caseEntailsAux` must discharge `Linear.Fact.ne` against `K ⊢ t = c` inside disjunctive facts (`IndexFact.either`).
- **Typed-array writes (`PromiseCalls.lean`):** `every_written` on `flags[i] = v` must evaluate `bitMask m` on the written `Uint8Array` value `v` (proving `intAnd (toInt32 (convert .uint8 v)) m = intAnd (toInt32 v) m` when `m ≤ 255`).
- **Wire and annotation lowering (`EffectCodec.lean`, `tools/bound-annotations.mts`, `docs/ANNOTATIONS.md`):** extend `Term.Kind` (or `Bound`), `BodyClause`, lexer (`&`), parser (parenthesized `(p & c)` and `!==` in `forall` bodies), and `EffectCodec` round-trip proofs.

### Measured size estimate (#398)

- **Lean (16+ files):**
  - Core semantics: `IndexFacts.lean` (`Term.Kind.bitMask`, `BodyClause` refactor, `kindValue`, `termValue`, `HoldsAt`, all mapping/congruence/entry lemmas), `IndexNumbers.lean` (bitmask algebra lemmas: idempotence, disjoint-OR, `uint8` conversion), `ArithmeticRules.lean` (exact `bitAnd`/`bitOr` rules), `Survival.lean` (`Term.support`, `bodyClauseSupport`, `BodyClause.needsKeep`, `FactSupport.check_sound`), `HeapKnowledge.lean` (`termRange`, `bodyClauseFollows`, `lowerBodyClause`, `instantiateBodyClause`, `guardEntails` / `ne` elimination in `either`), `StepRelations.lean` (`Composer.bodyClause`).
  - Program rules: `IndexWrites.lean` (`stepAtoms` emitting exact `bitMask` linear equalities for `&` and `|`, `writeAtoms`), `PromiseCalls.lean` (`every_written`, `every_appended`), `HeapExpressionRules.lean` (`mergeBodyClause`, `fieldEveryBody`), `SinglePass.lean`, `TolerantFramesStoreOpsNames.lean`.
  - Source elaboration & codec: `EffectCodec.lean` (`kindJ`/`kindOf`, `bodyClauseJ`/`bodyClauseOf`, round-trip proofs), `SourceClaims.lean` (`BodyClaim`), `Lowering/Flow.lean`, `HeadInference.lean` (`BodyFact`, `Fact.text`, `ofIndexFact`, `Fact.restate`, `Fact.keptAcross`), `Wire.lean`.
- **TypeScript & tests (5 files):** `tools/declaration-types.mts`, `tools/bound-annotations.mts` (lexer `&`, masked terms, general `BodyFact` disjunctions), `tools/diagnostic.mts`, `tools/fact-text.mts`, `tests/json-field-names.mts`, plus positive/negative/control cases.
- **Docs (3 files):** `docs/ARITHMETIC.md`, `docs/ANNOTATIONS.md`, `docs/REQUEST-PROTOCOL.md`.

### Pretext-side alternative (#398)

At [rich-inline.ts:461-468](../../dev/paper-rules/pretext/src/rich-inline.ts), the patch fires only for a rich-inline item with nonzero `extraWidth` opening on a `HARD_BREAK` with `!breaksBefore`, `hardBreakItemRetreat !== 'item'`, preceded by a non-empty `PRESERVED_SPACE` segment:

```ts
const idx = at - 1
if ((idx & 0x7fffffff) !== idx || idx > breakableFitAdvances.length) throw new RangeError('index')
breakableFitAdvances[idx] = advances
if (breakableLineStartExtras !== null) {
  if (idx >= breakableLineStartExtras.length) throw new RangeError('index')
  breakableLineStartExtras[idx] = null
}
```

- **Effect on Pretext:** on every valid execution, `breakableLineStartExtras[idx]` holds `null` for a `PRESERVED_SPACE` segment, so clearing it to `null` (or checking `if (breakableLineStartExtras[idx] !== null) throw ...`) is a semantic no-op on a cold branch. It establishes `breakableLineStartExtras === null || breakableLineStartExtras[idx] === null` directly at the overwrite of `breakableFitAdvances[idx]`, discharging the parallel length invariant with zero verifier changes.
- **Trade-off:** adds one null check and (when `breakableLineStartExtras !== null`) one redundant `null` store on an edge-case branch outside the hot measurement loop. No other Pretext site relies on a bitmask-guarded quantifier over `Uint8Array`.

---

## What this duplicates

| Notion in this design | Existing model in TScert | Relationship / what keeps them apart |
| --- | --- | --- |
| Quantified array fact (`IndexFact.every`) | `TwoStateFormulas.Atom.every` (`lean/Verification/Semantics/TwoStateFormulas.lean:201`, used by `AssertionScopes.lean` and `ParityAssertions.lean`) | `Atom.every` models the note's scalar array quantification (`[0, n)`) for the parity assertion arena; `IndexFact.every` models the single pass's index facts (supporting `ElemTarget`, `BodyClause.guarded`, `Bound.parallel`, typed-array view spines, and `EffectCodec`). Extending `IndexFact.every` does not duplicate `Atom.every`, but widens the gap between the single-pass fact language and the paper assertion arena unless `Atom.every` is updated later. |
| Affine index bounds (`IndexBound`, #396) and affine index shifts (`IndexShift`, #397) | `Linear.Form Term` (`lean/Verification/Semantics/Linear.lean`, `IndexFacts.lean`) | Both reuse `Term` and `Linear.Form Term` directly; `IndexShift` also subsumes `Bound.offset (delta : Nat)` (`IndexFacts.lean:797`), which is a restricted constant-offset special case on `self`. |
| Pure element-tag body (`extras[j] === null`, #396) and uniform `BodyClause` (#398) | `BodyClause.guarded` (`IndexFacts.lean:898`) and `IndexFact.guarded` (`IndexFacts.lean:1374`) | #396 reuses `BodyClause.guarded` with falsum (zero duplication). #398's `BodyClause.either` replaces the asymmetric split between `BodyClause.guarded` (outer) and `LinearClause.either` (inner), avoiding duplication of `GuardTag` across 17 files. |
| Bitwise-AND semantics and bounds (#398) | `IndexNumbers.intAnd` (`IndexNumbers.lean:365`), `ArithmeticRules.maskRange`/`maskBound` (`ArithmeticRules.lean:388-400`), `IndexWrites.stepAtoms` (`IndexWrites.lean:530`) | `ArithmeticRules` models `arithBits .bitAnd` via `intAnd` and `toInt32`, projecting linear inequalities (`0 ≤ r ≤ mask`, `r ≤ x`). #398 adds an exact `bitMask` term kind reading the same `intAnd`/`toInt32` definition, plus new algebraic rules for `&` and `|` that do not exist elsewhere in the verifier. |
| Heap regions and survival (#396, #397, #398) | `Footprints.Region` (`Footprints.lean`) and `Survival.everySupport` (`Survival.lean:516`) | None of #396, #397, or #398 introduces a new `Region` constructor. All three read existing `pathReads`, `everyCells`, `parallelCells`, `elemSpines`, and `Term.support`; #397 additionally uses the existing `Change.extend` relation (`Change.Holds.extend_entry`) for parallel array spines. |
| Element transfer on `slice()` and copy writes (#397) | `tools/array-prototype.mts:345` (`slice` length equality) and `PromiseCalls.every_written` / #392 / #395 | `slice()` models length preservation and freshness; adding element transfer introduces a new audited native postcondition in `array-prototype.mts`. Copy-transfer on element writes is new machinery parallel to `instantiateEvery` for sites that write `dst[at] = src[s]` without reading the third array `advances[at]`. |

---

## Recommendation for owner decision

| Issue | Verifier cost | Pretext-side cost | Recommendation |
| --- | --- | --- | --- |
| **#396 (Interval bounds `IndexBound`)** | **Moderate** (14 Lean files, 5 TS files; zero new `Region`s, zero new theories; also removes `writtenPrefix`'s named-successor restriction) | **Small** (lazy prefix growth matching `prepare.ts:649-660`, or redundant `null` store on else branch) | **Extend `IndexFact.every` with affine interval bounds** (`start`/`stop : IndexBound`) and standalone element-tag bodies. Interval quantification is a fundamental, general upgrade to `IndexFact.every` with a clean soundness story; Pretext can optionally use the `discretionaryHyphenContexts` prefix pattern to unblock immediately while #396 is built. |
| **#397 (Shifted parallel indexing `IndexShift`)** | **High** (15 Lean files, 6 TS files; requires `EntryState` in `ElemTarget.read`, `.extend` spine framing, push element witness, `slice()` audited element-copy postcondition, and a copy-transfer write rule) | **Negative (simplifies Pretext)** (add `breakableLineStartExtras` to `ParagraphLists` at `prepare.ts:272`, deleting a temporary per-item allocation and the 9-line copy loop at `rich-inline.ts:570-578`) | **Handle at the Pretext source boundary.** Putting `breakableLineStartExtras` on `ParagraphLists` makes Pretext both simpler and faster, and avoids expanding trusted `slice()` contracts and adding copy-transfer write machinery for a single call site. Revisit `IndexShift` only if a target genuinely needs offset parallel arrays that cannot share an index frame. |
| **#398 (Bitmask-guarded clauses)** | **Very high** (16+ Lean files, 5 TS files; requires `Term.Kind.bitMask`, uniform disjunctive `BodyClause`, exact `&` tracking, and bitwise `&`/`|` algebraic laws for `flags[at] |= UNBROKEN`) | **Trivial** (3 lines clearing/checking `breakableLineStartExtras[idx] = null` on a cold branch at `rich-inline.ts:461-468`) | **Handle at the Pretext source boundary.** Do not add a bitwise algebra and bitmask-guard theory to `IndexFact.every` for one cold-path patch; keep `IndexFact.every` focused on linear and tag facts. |
