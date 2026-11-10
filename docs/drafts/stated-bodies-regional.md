# Draft: the regional check for every claimed footprint, and fresh stable fields

A design for checking a body whose footprint excludes a store region that a
callee states, where the selected store was allocated by the body itself.
For example, `f` states `Modifies<{ values: "any"; stores: "grow" }, number>`
and calls `step(runs, xs)`, whose frame states `"runs.open[*]": "any"`,
where `f` allocated `runs = { open: [] }` itself. Base: branch
`chain1-nullable-fix` at 501e8f69. Claims are labelled **read** (in the
code named), **observed** (with the run) or **conjectured**.

## The existing mechanism this extends

**The regional check and its fresh array storage**
([argument-path store regions](../FOOTPRINTS.md#argument-path-store-regions),
[fresh array storage](../FOOTPRINTS.md#fresh-array-storage),
[stated effects](../SOURCE-ELABORATION.md#stated-effects)). Its parts, all
**read**:

- **Who is checked.** `SourceExtraction` sets `regional := some (s.closed,
  regions)` only where the statement's regions are not empty
  (`Source/SourceExtraction.lean:311`). Every other claimed footprint is
  checked by the plain node-by-node bound check, `compositionalChecked`,
  called from `effectResult` (`Source/SourceRequests.lean:203`).
- **The plain check's calls.** A call is within the bound $`\Phi`$ when
  `eff.footprint.le Φ` holds (`selectedWithinAt`, `Programs/GraphCode.lean:329`).
  A signature that states regions has `Effect.footprint = .top`
  (`Semantics/CallEffects.lean:183`), so the plain check accepts it under
  no bound but `top`. The check's only freshness is `receiverFresh`, for
  the receiver's store of a `push`.
- **The step-frame rule.** The regional check accepts a node when one of
  its step effects (`stepEffects`: within the closed bound, a call at its
  signature's frame, an element write) is rebased to the entry and included
  in the stated frame (`stepWithin`, `rebaseAll`).
- **Fresh facts.** `freshTables` infers, untrusted, two slot tables: fresh
  values (`FreshValue`, in `FreshIfStore` form) and fresh cells
  (`CellFresh`). `checkNodes` checks them at every node and edge. `rebase`
  maps `field s []` and `path s [] []` to no region where `ev.fresh s`
  holds (`RebaseOk.fresh_store`).
- **Stable fields.** A field that every non-null clause of a slot's type
  states `@stable` keeps its location's value across every step
  (`stableFirst`, `stableFirst_frame`, `stableLocations_frame`;
  `stableFieldPresent` admits `null` and `undefined` clauses).
- **Guarded separations.** At a nullable region position the separation
  $`z = g \lor (a.p \mathrel{\#} y)`$ places $`y`$ outside the region,
  because `ArgumentStoreRegion.resolve` selects no store where the position
  holds `null` (965cacb3, 501e8f69;
  [store separation](../ARITHMETIC.md#store-separation)).

The design adds no rule kind. Part 1 runs the regional check, with no
regions, as a second certificate of a claimed footprint. Part 2 adds a third
fresh table beside values and cells.

## What fails today (observed, 2026-11-10, `dev/check-functions.mts`)

| Variant | Outcome |
| --- | --- |
| `f` above | refused at `step(runs, xs)`: "the footprint claimed for 'f' is not established by its body" |
| V1: `const open: number[] = []; const runs: Runs = { open }` | refused, same place |
| V2: `step2(open, xs)` stating `"open[*]": "any"`, `open` a local `[]` | refused, same place |
| V3: `step(maybe, xs)`, `maybe = c ? runs : null`, `runs: Runs \| null` | refused, same place |
| a caller with no statement, through a regional wrapper | verified |

The plain check refuses all four: the callee's region makes its footprint
`top`. Pretext's `measureAnalysis` is refused the same way at
`getUnspacedGraphemes(…, unspacedRuns)`.

## The design

### 1. The regional check as a second certificate of a footprint

`effectResult` stays the one entry point of a claimed footprint
$`\Phi_c`$ (`r.footprint`). It tries its certificates lazily, in order:

1. the existing successes: `top` with no throw or fresh-result promise,
   then purity, then the plain check `compositionalChecked`;
2. where the plain check refuses and the unit promises no fresh result,
   the regional check with no regions, `regionalChecked`, at $`\Phi_c`$
   and `exc = r.onThrow`.

`regionalChecked` is the graph part of `regionalResult` (entry provenance,
no fresh facts at the entry, `checkNodes`), factored out so that both call
one definition. A unit the plain check accepts runs no regional traversal.

What changes, against the code:

- **`SourceExtraction`, `statedWithin`, the slots.** Nothing. A stated body
  without regions keeps `regional := none`, and its slot keeps the
  producer's claim $`\Phi_c`$ (`Extraction.lean:154`). The producer caps
  that claim at the statement (`within_statement`, `source.ml:906`), so it
  can be tighter than the statement. For `f`, the producer joins the call's
  coarse footprint `top` and caps it at `grow`.
- **`regionalResult`.** Unchanged for statements with regions. It calls
  the factored `regionalChecked`.
- **The acceptance path.** `effectResult_preserving` gains the second
  certificate, and `checkRequests_footprint_at` proves `RequestsSafe`'s
  footprint conjunct from it by the lemma below. The lemma covers the
  normal postcondition, and the exceptional one where `r.onThrow` promises
  it.
- **Implementation obligations.** `checkUnitJson_safe` keeps its premise
  and conclusion, and the conversion `mapM FunctionPlan.certify` stays
  exhaustive (`Plans.lean:32`): no plan constructor changes. These are
  obligations of the implementation; the lemma alone does not give them.
- **Diagnostics.** `footprintRefusal` reports the plain check's first
  refused node, then the regional check's.

The lemma: with no regions, the exclusion predicate of
`ArgumentStoreRegionsWithin` (`StoreRegions.lean:19`) holds of every
location, so

```math
\mathrm{ArgumentStoreRegionsWithin}\ \Phi\ [\,]\ \rho\ h_0\ h \;\Longrightarrow\; \Phi.\mathrm{Holds}\ h_0\ h
```

**What a body without regions gains.** A callee's region on a store the
body allocated rebases to no region, through the existing `FreshValue` for
`field s []` and `path s [] []`. V2 verifies with Part 1 alone
(conjectured).

**Completeness.** The lazy order refuses nothing that verifies today. The
two checks differ in what they accept (read):

| Step | Plain | Regional |
| --- | --- | --- |
| no-return region (`inferDead`, `deadNode`) | exempt | checked as a step |
| `unreachableEntry` | exempt | only `emptyType` of the result |
| fresh result (`ret`) | checked | refused |
| `push` on a fresh slot | `receiverFresh` | `ReceiverGrows` rebased (4dd39cc4) |
| a call stating regions | `top` only | rebased |

A generic unit is refused by both: a footprint other than `top` already
requires `qualification.isNone` (`SourceRequests.lean:208`). Making every
stated body regional, with `regional := some (s.closed, [])`, would give
callers the statement in place of the tighter claim
(`Extraction.lean:157`), and would refuse the first three rows.

### 2. A fresh store through one `@stable` field

The definition, with $`b = |h_0|`$:

```math
\mathrm{FieldFresh}_b(h, v, f) \iff \forall u.\ \mathrm{readPath}\ h\ v\ [f] = \mathrm{some}\ u \implies \mathrm{FreshIfStore}\ b\ u
```

A value with no field $`f`$ (`null`, `undefined`, a number) meets it. It
requires `FreshIfStore` and permits absence. `CellFresh` requires a present
field and `FreshValue`, so cells stay a table of their own.

**Kind.** It is a third table of the regional check's own fresh facts
(`FreshTables.fields`, pairs of a slot and a field name). `freshTables`
infers it, untrusted, and `checkNodes` checks it. It is no index atom and
no wire field. Its candidates are bounded to the field names the body's
call steps state in their regions.

**The invariant.** At each label, for each pair $`(s, f)`$ of the table,
$`\mathrm{FieldFresh}_b(h, \rho(s), f)`$ holds in the heap $`h`$ the label
is reached with. The entry's table is empty, so a parameter receives no
fact. A freshly allocated field may have the fact whether or not it is
stable. Carrying the fact across a node needs a proof that the node does
not change that field's location; `@stable` is that proof.

Obligations:

1. **Establishment** (`fieldAlloc_fresh`). At an allocation `makeAt` whose
   keys are distinct, with $`f`$ mapped to an initializer slot
   $`j`$ (`allocationSlots`) holding a fresh value, the allocated field
   holds $`\rho(j)`$, whose store lies at or above $`b`$. The record's own
   freshness says nothing of its contents. The lowering evaluates operands
   into slots before `makeAt` (`Lowering/Atoms.lean:719`). A constant
   meets the fact (`constTerm`).
2. **Transport.** Every retained fact survives the node it crosses, slot
   copies, joins (each incoming edge), loops and handlers. A node keeps
   $`(s, f)`$ where `stableFirst G (entry c) s f` holds: the field's whole
   value is fixed by its world contract, and `storeOf` reads the store's
   location from that value without reading the heap. Call positions map
   to slots through `se.slot`, as `nodeFresh` does.
3. **Throws.** `stableFirst_frame` and `stableLocations_frame` give
   normal-return postconditions only. Their invariant argument is extended
   to `SafePostExc`, so the fact holds at the heap a throw leaves, before
   `handlerFresh_holds` moves it to the handler's slots.
4. **Consumption** (`RebaseOk.fresh_field`). `RebaseEvidence` gains
   `freshField : Nat → String → Bool`, and `rebase` maps `path s [f] k` to
   no region where `k = arrayStoreKey` and `freshField s f` holds; the
   `path` case of `rebase_sound` for a one-field path.

**Completeness.** The field table must not make an existing regional check
fail, for example by exhausting the shared inference fuel. Where inference
with fields finds no fixed point, the check uses the values-and-cells
candidate alone.

### 3. The nullable position

`maybe = c ? runs : null` joins a branch holding `runs`, which meets
$`\mathrm{FieldFresh}`$ for `open`, with the constant `null`, which meets
it because it reads no field. The join keeps the fact where each incoming
branch establishes it, and `stableFieldPresent` admits the `null` clause
of `Runs | null`. Where the position holds `null`,
`ArgumentStoreRegion.resolve` selects no store. The guarded separation is
a caller's fact for keeping a length, and the field fact is the frame's
own, so the two compose without either reading the other.

## Soundness

A claimed freshness cannot be wrong:

- **The record is a parameter.** The entry has no fresh facts
  (`regionalResult` requires `factsAt ft.* r.start` empty).
- **The record holds an old array.** Establishment needs the initializer
  slot's own freshness, which an old array lacks.
- **A join with an old store.** The fact holds after a join only where
  every incoming edge establishes it.
- **The field is mutated.** A non-stable field's fact is dropped at the
  first node that may change its location. A stable location has a stable
  world contract (`StableAt`, `CtrStable`) that every heap a run reaches
  keeps, whatever code runs, a callee the record escapes to included.
- **The literal's store aliases an older one.** An allocation lies at or
  above the heap's length (`alloc_fresh`).
- **The array's contents change.** The fact is of the store's location.

## Trust

None. Every fact is checked in Lean. The tables are inferred, and
acceptance reads only the checks.

## Cases and controls

Positives: `f` above, V1, V2, V3; a record escaping to a callee; a mutation
of the fresh array's contents through an alias; a throwing call caught,
followed by reuse of the record. Negatives, each run under Node with its
result stated: the record is a parameter; a fresh record holding an old
array; a join with an old-store branch; a non-stable field reassigned
before the call. A control of `pipeline/test.mts` forges the claimed
footprint of a unit and requires the independent evidence check to refuse
it. No decoder control: the tables are no wire field.

## Cost

No timing is claimed. A unit the plain check accepts runs no regional
traversal. A unit it refuses adds the fresh-table inference (at most
`2 * P.length + 2` passes) and the regional check, and the diagnostic
recomputes the inference (`Json.lean:56,90`). Search and evidence checking
are measured separately.

## Steps, each mergeable and measured

| # | Step | Measured by |
| --- | --- | --- |
| 1 | Part 1: the lazy regional certificate and its lemma | V2 verifies, the record-parameter negative refused; pipeline cases and pretext's five files unchanged; search and check seconds of `measureAnalysis` and `rich-inline.ts` |
| 2 | Parts 2 and 3: the field table | `f`, V1, V3 and the escape, alias and throw positives verify; the negatives refused; `measureAnalysis` stating `Modifies<{ values: "any"; stores: "grow" }, PreparedText>` verified, then `prepareRichInline` |
| 3 | The forged-footprint control | the control refuses |

## Alternatives considered

**The plain check's call case.** A plain-check rule could accept a call
stating regions when `eff.closed.le Φ` holds and each selected store is
fresh. It would need its own field fact and its own null handling, which
duplicates `rebase` and the fresh tables. It falls short of the single
mechanism that every frame composition goes through.

**Allocation provenance in the heap.** A stamp per object, recording what
each record held at allocation, would decide freshness through any path.
It needs a semantic change and proofs across every rule, with no
motivating program beyond one field. No document in `docs/` describes it
(observed, grep).

**A pretext-side form.** The observed variants that keep
`measureAnalysis`'s statement's shape, V1–V3, are refused. Dropping the statement verifies (the last
row of the table above), but its callers lose the `grow` bound.

## Open questions

1. Whether the lowering of `{ open: [] }` binds the literal to a slot that
   `allocationSlots` reads, or needs a nested-allocation case.
2. Whether `measureAnalysis` meets another refusal after this one (the log
   shows the first).
3. Whether cells become the field table at the cell key, kept by
   `keepsValues`, so one table serves both.
4. The time the regional check adds where the plain check refuses.
