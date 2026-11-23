# Checked local-object confinement across arbitrary-effect calls

## The existing mechanism this extends

Facts over heap locations survive a call through two mechanisms owned by
[FOOTPRINTS.md](../FOOTPRINTS.md) and [DESIGN.md](../DESIGN.md#general-mechanisms):

1. **Framed return preservation in the single pass**
   (`lean/Verification/Programs/SinglePass.lean`,
   `lean/Verification/Programs/TolerantFramesComposeYields.lean`):
   `SinglePass.run` accepts a list `framed : List (Nat × List Footprints.Footprint)`
   mapping graph labels to supports that hold across the step at that label.
   After `checkedStep` runs a node `l`, `SinglePass.keptStep` adds back every
   atom of `st.stepK` whose support is covered by one of `framedAt framed l`:

   ```text
   keptStep (kept : Option (List Footprint)) (entry : State) (st : Stepped):
     keep := (kept.map (fun Ss => framedKept Ss st.stepK)).getD []
     return { st with store := keepStore (st.result :: entry.names) keep st.store }
   ```

   `TolerantFramesComposeYields.framedKept_holds` proves that when every
   support in `Ss` satisfies `Footprints.Supported T ρ s.h s'.h`, every atom
   returned by `framedKept Ss st.stepK` holds in `(push v ρ, s'.h)`.

2. **Heap reachability and frame preservation**
   (`lean/Verification/Semantics/Reach/Values.lean`,
   `lean/Verification/Semantics/Reach/Steps.lean`,
   `lean/Verification/Semantics/Reach/Runs.lean`):
   `TolerantFrames.Reach.step_preserves_unreachable` proves that a single
   small-step transition `Step h t h' t'` leaves unchanged every heap location
   not reachable from the term's root values (`vals allC .empty true false t`)
   and adds no edge from an outside location into an unreachable set.

### Concrete program: `walkVisiting`

```ts
type Cursor = { i: number };

/** @requires safeInteger(c.i) && 0 <= c.i && c.i < xs.length
 *  @ensures safeInteger(c.i) && 0 <= c.i */
function step(xs: number[], c: Cursor): Modifies<{ "c.*": "scalar" }, number> {
  const x = xs[c.i]!;
  c.i = c.i + 1;
  return x;
}

export function walkVisiting(xs: number[], onStep: (x: number) => void): number {
  const c: Cursor = { i: 0 };
  let total = 0;
  while (true) {
    const s = c.i;
    if (s >= xs.length) return total;
    const x = step(xs, c);
    total += x;
    onStep(x);
  }
}
```

#### Without checked confinement

At `onStep(x)`, `onStep` has type `(x: number) => void`, so `PromiseCalls.callerFrame`
is `top` (`cls values/array/view: any`). The loop-head invariants
`0 <= c.i` and `c.i <= 9007199254740991` have produced support
`[(.inCls (.path c [] (.str "i")) .values, .init)]`. Every location in
`c.i` belongs to `.cls .values`, so `Footprints.respects` cannot separate `c.i`
from `top`. `SinglePass.checkedStep` drops all facts over `c.i` after
`onStep(x)`, the back-edge to the loop head lacks both invariants, and
`step(xs, c)` is refused at its precondition.

#### With checked confinement

`LocalConfinement.propose` computes an untrusted per-node table `conf`:

1. At the allocation of `{ i: 0 }` (node `n24`), `c` enters `owned` and `holders`.
2. At `const s = c.i` (`n20`), `Purity.inspectTerm` holds and `c.i` has inert
   type `number` (`LocalConfinement.inertTy`), so `s` is outside `holders` while
   `c` stays in `owned` and `holders`.
3. At `const x = step(xs, c)` (`n12`), `step`'s checked derivation selects
   `Modifies<{ "c.*": "scalar" }, number>`. Its caller frame has `.keep` on
   `cls values/array/view` and `.scalar` on `pathFields c []` (`c ∈ owned`),
   passing `LocalConfinement.frameConfined`. Because `x : number` is inert, `x`
   is outside `holders` and `c` stays in `owned` and `holders`.
4. At `onStep(x)` (`n10`), `node.expression` mentions only `onStep` and `x`,
   neither in `holders` (`LocalConfinement.freeSlotsNotIn = true`). `conf.framed`
   supplies `[(10, [[(.fields c, .keep)]])]` so `SinglePass.keptStep` preserves
   `0 <= c.i` and `c.i <= 9007199254740991` across `onStep(x)`.
5. `SinglePass.run` checks `framed == conf.framed` and
   `SinglePass.checkWalkConfinement` across all 28 visited nodes. Both accept,
   and `walkVisiting` verifies under `Target.RunSound` with `mode8Accepted_sound`
   unchanged.

## Checked local-object confinement

### Semantic invariant (`Verification.Semantics.Confinement`)

At each graph label `l`, environment `ρ`, entry heap length `m₀`, and heap `h`,
`LocalConfinement.ConfinedAt conf width l ρ m₀ h` asserts a predicate
`Priv : Nat → Prop` such that:

- Every location in `Priv` is freshly allocated during the call:
  $`\forall \ell,\; \mathsf{Priv}(\ell) \implies m_0 \le \ell < |h|`$.
- `Priv` is closed from outside (`Confinement.ClosedOut h Priv`): no location
  outside `Priv` stores a value that reaches `Priv`.
- Every slot in `owned` has all non-spine field locations in `Priv`
  (`Confinement.OwnedFields`).
- Every slot in `ownedArr` has its spine location and all listed element cells
  in `Priv` (`Confinement.OwnedArrays`).
- Every slot in `ownedSpines` holds a `.arr` spine whose listed cells lie in
  `Priv` (`Confinement.OwnedSpines`).
- Every slot $`y < \mathsf{width}(l)`$ outside `holders` satisfies
  `Confinement.NoPriv Priv (ρ y)` (`LocalConfinement.HoldersCoverB`).

### Per-node checked transitions (`Verification.Programs.LocalConfinement`)

`LocalConfinement.checkNode` validates each visited node `l` against its
checked step derivation `st.stepDeriv` and knowledge `st.stepK`:

- **Entry**: `conf.at start = {}` (`LocalConfinement.confinedAt_empty`).
- **Framed nodes**: if `l ∈ conf.framedNodes`, every free slot of
  `node.expression` is `< width` and outside `pre.holders`
  (`LocalConfinement.freeSlotsNotIn`). By `Confinement.steps_confined_unreachable`,
  every location in `Priv` keeps its exact contents across the step, yielding
  `Footprints.Supported (confinedFootprint pre.owned pre.ownedArr) ρ s.h s'.h`.
- **Inspectable steps (`Purity.inspectTerm && checkScope`)**: every pre-existing
  heap location keeps its contents, so `Priv` extends by `[s.h.length, s'.h.length)`.
  Fresh object allocations (`makeAt .absent` without spine, `merge`, `makeKey`),
  array-spine allocations (`arrLit`), and array-object wrapper allocations
  (`makeAt .absent [arraySpineKey, proto]` and `letE (arrLit _) (makeAt .absent [arraySpineKey, proto] [.var 0, .var pi])`)
  place slot `0` into `owned` / `ownedArr` / `ownedSpines` and `holders`.
  Reads and operations with inert result type (`inertTy`) leave slot `0` outside
  `holders`; variable copies propagate ownership and holder status; other
  inspectable terms add slot `0` to `holders`.
- **Field writes (`.writeAt f (.var x) (.var y)`)**: when `f ≠ arraySpineKey`,
  `x, y < width`, and either `y ∉ holders` or `x ∈ owned`, `Priv` and
  `ClosedOut` are preserved (`Confinement.steps_writeAt_val_confined`).
- **Confined calls (`confinedCallNormal`)**: when the checked derivation
  `st.stepDeriv` establishes a normal frame where every region outside `owned`
  fields, `ownedArr` cells, and non-`.any` `ownedArr` spines is strictly `.keep`
  (`LocalConfinement.frameConfined`), `ClosedOut` is preserved on `PrivExt`
  (`LocalConfinement.frameConfined_sound`). Strictly `.keep` is required outside
  `Priv` because `Footprints.ScalarStep` and `Footprints.InitStep` permit
  storing an object value (`ConfinementControls.scalar_outside_can_store_object`,
  proved).
- **Exceptional exits**: handler targets reset `owned`, `ownedArr`, and
  `ownedSpines` to empty (`LocalConfinement.checkNode_sound_handler`).
- **Edges**: `LocalConfinement.edgeOk` verifies that every outgoing mapping
  preserves `owned`/`ownedArr`/`ownedSpines` inclusion and `holders` coverage.

### Soundness (proved)

- `Confinement.steps_confined_unreachable` (`lean/Verification/Semantics/Confinement.lean`):
  multi-step preservation of `Priv` and `ClosedOut` from `Reach.step_preserves_unreachable`.
- `LocalConfinement.checkNode_sound_normal` and `checkNode_sound_handler`
  (`lean/Verification/Programs/LocalConfinement.lean`): per-node preservation of
  `ConfinedAt` and discharge of `Supported (confinedFootprint ...)`.
- `TolerantFrames.run_sound_checked_confined`
  (`lean/Verification/Programs/TolerantFramesConfined.lean`): threads
  `ConfinedAt` alongside `passPreU` through `nodesChecked_confined` to prove
  the ordinary `Target.GraphGuarantee` with zero client trust.
- `TolerantFrames.run_sound_pass` dispatches `Target.RunCall.Accepts` between
  unframed and confined walks, leaving `SourceClaimJson.PassUnit.mode8Accepted_sound`
  unchanged (`Verification.Tests.AxiomCheck` verifies zero project axioms).
- `Verification.Tests.ConfinementControls` (`lean/Verification/Tests/ConfinementControls.lean`):
  verifies that forged confinement tables (non-empty `start`, omitted holder,
  framed callback mentioning a holder, escaping write, unverified call) are
  refused.

### The module's execution

The theorems above are of one unit's run, its inputs given at its entry.
The module's execution composes the units
([module composition](../../WORK.md#module-composition)), and `Priv` stays
unreachable there only where no input comes to hold an allocation of the
unit other than by a step of the unit. The module's initialization
(`Front.isInitialization`) allocates the module's cells and constants, and
its inputs, the module's functions, close over them
([module cells](../SOURCE-ELABORATION.md#module-cells)): a call to one may
read and write every one. The initialization therefore proposes no table
(`SourceClaimJson.proposeConfinement`), and its calls keep facts by their
footprints alone. On

```ts
let m: number | string = 1;
function setS(): void { m = "x"; }
setS();
export const out: number = m;
```

a table owning the cell `m` would frame `setS()` and keep `m.value = 1`,
which Node refutes (`out` is `"x"`); with no table the call's footprint
writes the cell and the binding is refused
(`invalid-initialization-call-writes-cell`,
`invalid-initialization-call-writes-constant`).

## What this duplicates

| Modeled concern | Where the rest of the verifier models it | Relationship |
| --- | --- | --- |
| Heap reachability and unreachable-location preservation | `Verification.TolerantFrames.Reach` (`Values.lean`, `Steps.lean`, `Runs.lean`) | Reused directly (`step_preserves_unreachable`, `vals`, `Reaches`, `Inert`). |
| Support coverage and framed fact preservation | `SinglePass.framedKept`, `SinglePass.keptStep`, `Footprints.FactKind.support_sound`, `IndexFact.support?_supports` | Extended in place from `List IndexAtom` to `List Atom` (cells, links, elements, indices) with syntactic region inclusion `Confinement.regionSub`. |
| Call-effect derivations and caller frames | `ExpressionEffects.selected_sound`, `PromiseCalls.requiresTree_sound`, `PromiseCalls.callerFrame` | Reused directly by `LocalConfinement.confinedCallNormal`. |
| Pure/inspectable steps | `Purity.inspectTerm`, `HeapExpressionRules.inspect_instantiate`, `Confinement.inspect_steps_prefix` | Reused directly; no second purity predicate is introduced. |
| Graph soundness and headline theorem | `TolerantFramesComposeYields`, `TolerantFramesGuaranteeWalk`, `PassUnitHeadline` | Reuses `run_traversedC`, `NodesYield`, `footprintKept_of_walk`, `returnsEnsured_of_walk`, and `RegionsHeld`; discharges the existing `Target.RunSound` with no change to `GraphGuarantee` or `mode8Accepted_sound`. |
