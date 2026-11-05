# Draft: deciding types in search and checking

The remaining steps of the type-decision procedure. Its landed parts are
described where they live: the relation and the engine in
[POSITIVE-TYPES](../POSITIVE-TYPES.md#covered-pairs), instantiation in
[RECURSIVE-EQUATIONS §4](../RECURSIVE-EQUATIONS.md#4-subtyping), the union index
in UNION-SHAPES and narrowing in PROGRAM-TYPING; their measurements are
[WORK](../../WORK.md#status)'s row. This draft keeps the parts of the design
the remaining steps (§5) need.


**Evidence labels.** **Measured** gives the command, the commit and the date.
**Cited** names inspected code or a supplied measurement. **Proved** names a
Lean theorem. **Conjectured** marks a design claim, a proof obligation or an
estimate; every lemma below that no theorem names needs a Lean proof.

## The existing mechanism this extends

Structure-directed comparison: the covered-pairs relation and its engine
([positive types](../POSITIVE-TYPES.md#covered-pairs)), the
[catalogue of selection rules](../UNION-SHAPES.md#3-the-catalogue), and
instantiation of parameterized equations
([recursive equations](../RECURSIVE-EQUATIONS.md#4-subtyping)) (cited).
Every comparison the procedure establishes carries its proof
(`CheckedComparison`), which the checker reads; this draft orders and
shares the work of finding those proofs, for search and checking alike.

## 1. The engine

One procedure for search and checking, untrusted for soundness: every
established result carries its proof (`CheckedComparison`).

1. **Interning.** Trees, label lists and clauses get request-wide identities
   (hash-consing of the syntax met); a type's clause set and label set are
   hash sets of identities.
2. **Memo**.
3. **Identity** by `Mem` and `Clauses`, on the target's identity sets.
4. **Var**, its premises asked recursively.
5. **Inst≤** for a scheme row against an arrow target, its premises
   asked recursively as completed comparisons.
6. **Lists.** Label containment is linear where both lists share an order
   (`memAll`, `subsetIn`), search deduplicates candidate types through a hash
   set (`keepFirst`), and renamed-member pairs are formed once per key and
   schemes.
7. **Structure.** Today's discovery, deletion and validation
   (`growTable`, `gfp`, `checkStructural`), with three changes: with
   selection on, every reading of candidates for a source clause, in demand
   pairs (`demandPairs`), coverage (`coveredIn`) and validation
   (`checkEntries`), reads the index (§2), and with selection off
   (`InstanceImageCheck.general`, the rerun) every clause, as today; a
   row's demand (`demandPairs`, `renamedPairs`, `rowsFor`) is memoized for
   the request, keyed by every input it reads (the row, the selection mode,
   the known rows, the depth, the graph and image check), so selected
   discovery and the rerun keep separate entries; a memo entry is the
   function's value at its key, where today every comparison recomputes it
   for every row of every table it grows; `Same` and `Clauses` answer
   identical clauses and contained types without a row; exact row
   membership reads a hash set. Element-wise coverage of a tag set,
   `SameKind`, the opaque-row conditions and `meetSources` are read as
   today.

**Coverage by assumption, the target form of discovery.** Discovery collects
every candidate's demand pairs before deletion, and deletion rechecks every
row each round. The depth-first form builds the family certificate from the
root, assuming a pair while it is open, keeping a covering's first candidate
that holds, discarding the results established since a failed pair was
pushed. Its completeness for today's search space is open: `TabRen`, arrow
evidence and member instances read rows other coverings insert, which is the
dependency representation WORK's
[selected discovery](../../WORK.md#union-shapes-discovery) states as
missing. The depth-first form replaces discovery and deletion only with that
representation (each covering naming the rows, arrow evidence and instances
it reads, a failure invalidated when they change) and `discovery_complete`
(§4), and only where structural comparison remains a measured cost
after the other steps (§5).

**Resources** keep today's meaning while discovery stays today's:
frontier rounds, `grows` over the rows inserted, exhaustion distinct from
an unestablished question.

## 2. Union members by index

The candidates of a source clause $`a`$ in a target $`B`$ are
`ClauseSelection.candidates G a B`: the clauses of $`B`$ that R1–R5
([UNION-SHAPES](../UNION-SHAPES.md#3-the-catalogue)) leave. R3 excludes $`b`$
when some constraint $`(f, B_k)`$ of $`b`$ (`fixedOf b`), with $`B_k`$ plain,
has the source with entries at $`f`$ each holding a literal $`B_k`$ does not
admit (`litExcl`). With $`V_j`$ the literals of the source's $`j`$-th entry
at $`f`$, a constraint is **retained** when

```math
\mathsf{none}_f\ \lor\ \exists j.\ \forall v\in V_j.\ \mathsf{admits}(B_k,v),
```

$`\mathsf{none}_f`$ saying the source has no entry at $`f`$; an entry with no
literal retains every constraint. R3 at $`f`$ leaves exactly the clauses
whose plain constraints at $`f`$ are all retained.

The **index** of $`B`$, built once per target type of a request, holds per
outer shape its clauses together with the universes `top` and `source`;
per key $`f`$, each plain constraint at $`f`$ with its clause and its
number of plain constraints there; and the constraints by what they admit:
a map from a literal (a singleton, or an element of a tag set) to the
constraints holding it, a set per primitive family (`str`, `num`, `bool`,
`bigint`, `symbol`) of the constraints admitting every literal of that
family, and the set of constraints with `top` or `source`, admitting every
literal. The constraints admitting $`v`$ are its literal's bucket, its
family's set and the universal set. Building the index reads each
constraint's clauses once. A lookup for $`a`$ takes its shape
group (R1); at one key $`f`$ where $`a`$ has entries, it computes the
retained constraints as the union over entries of the intersection over
their literals of the admitting sets, counts them per clause, and keeps the
clauses of the group with no plain constraint at $`f`$ or all retained; it
then filters that set by R2, R4, R5 and R3 at the other keys. The lookup
returns exactly the candidates, in the order and multiplicity of
`ClauseSelection.candidates` (each bucket holds clause positions, merged in
position order): `indexCandidates_eq`, list equality, which discovery
needs because `growTable` inserts rows in candidate order and `grows` reads
the rows inserted; the validator's existential needs only its consequence,
membership equality (`indexCandidates_mem`, §4). A union
discriminated by one key costs, per source clause, the clauses admitting
its literal where the filter reads every target clause.

For a closed entry, the one a comparison validates, the validator reads
candidates only (`checkEntries_eq`, §4); an entry with hypotheses, as
variance validation checks, reads the indexed candidates first and every
clause after, as today. Exact table membership reads a hash set of the
rows; `TabRen`, which accepts a row containing the query after renaming,
scans the rows as today.

## 3. One memo for search and its check

Search's own check of each graph and code it produces runs in the process
that established its comparisons, over the same graph. Search records each
inclusion it establishes with its proof (`Answered.proved`), and its checks
read them as the image check's proved inclusions (`Answered.images`,
`InstanceImageCheck.known`), which `compareUsing` establishes without
comparing. The final check of `--produce-source-claims` reads each request's
own image check, which holds none, and the check stage, in its own process,
holds none.

## 4. Trust and lemmas

**Trusted changes**, each with its lemma (conjectured until proved):

- `Clauses` and `Same`: `clauses_subset_sound`, inclusion of both
  components of `mixedMeaning` (values and argument lists) from split clause
  containment and label containment, a member of a clause row being a
  member through one of its clauses with that clause's built-in invariant;
  `prem_iff` and `prem_complete` restated for the extended `premBase`;
  `family_sound` extended by `Same`; `excludes_self`, a clause is its own
  candidate, so `valid_selected` holds with `Same`.
- `Inst≤`: `inst_covers_sound` — given a checked instance (kinds, call
  scheme, admission over the domain, `InstanceImages` in both components,
  bounds), sound operand premises and a signature covering of each target
  arrow by an available image, a member of the scheme row at the caller's
  assignment is in $`\mathsf{arrs}(L;M)`$: elimination at the instance's
  assignment and transport by the images (`inst_images_sound`'s parts),
  universe-receiver weakening (`top_row_mixed`, `sourceTy_sound`), then the
  signature covering's soundness (`covers_arrows_sound`);
  `compareInstArrsState_sound` and `compareInstState_sound` restated over it.
- Narrowing: `restriction_index_eq` — the indexed lookup returns
  `restriction`'s result, from `restricts_key` (a candidate `restricts`
  accepts has $`a`$'s key) and the index listing each key's candidates in
  list order; `uncoveredField_sound` unchanged.
- The index: `indexCandidates_eq`, the lookup equal as a list to
  `candidates G a B`, used by discovery; the demand memo's entries equal to
  their functions' values at their keys (untrusted, but stated, since
  discovery's decision depends on it).
- The indexed validator: `indexCandidates_mem`,
  `b ∈ indexCandidates G a B ↔ b ∈ candidates G a B`; `checkEntries_eq`,
  for a family of closed entries with `VariablesOk`, lookups to entries of
  the family or sound entries, and sound known rows — the premises
  `checkStructural`'s callers hold as `checkStructural_sound` uses them —
  the decision over candidates, element branch included, equal to the
  decision over `candidates ++ clausesOf`, from `valid_selected` and
  `checkEntries_sound`; `premTable_eq`, hashed exact membership equal to
  the list's, `TabRen` unchanged.
- Memo lookups return an entry whose question is the query's, checked by
  equality as `completedLookup` checks it.

**Untrusted, a preservation lemma:** `families_union_valid` — valid closed
families for $`(S_l,I_l)`$ of one kind, none of whose coverings reads its
source type, with their arrow evidence and member instances kept, form with
the root row $`(\bigcup S_l,\bigcup I_l)`$ a valid closed family. It
is a statement about certificates; that bounded discovery finds the family
is a separate question, measured.

**Untrusted, with completeness lemmas:** `selected_complete` — a valid
closed family whose coverings are by candidates, restricted to the pairs
reachable from its root through those coverings' premises (table rows,
`Var`, `TabRen`, member instances) and their arrow evidence, stays valid;
it needs the dependency closure WORK's
[selected discovery](../../WORK.md#union-shapes-discovery) states. It is a
part of the operational theorem that deleting the rerun needs (§5). `discovery_complete` — with the
dependency representation of §1, a valid closed family in the reach of
today's discovery, its coverings by candidates, is found by the depth-first
form — is the condition for replacing discovery and deletion by it.

**Unchanged:** `SourceClaimJson.checkUnitJson_safe`, its premise and its
conclusion; `FamilyValid` but for `Same`; R1–R5 and their lemmas. Generic
definitions carry `@[nospecialize]`; no `sorry`, no axioms.

**Untrusted:** the engine (interning, search order, assumptions, memo
policy, budgets), the index's construction beyond its lemma, unification
and overload order, every proposal, and search's typing order.

**Removed:** `imagesUpTo`, `structuralImages`, `compareEquivalent`,
`equivalent`, `compareImagesUpTo`, the respelling patches,
`extendInstancePatches`, `instancePatchLimit`; with the rerun's operational
theorem, the reruns and `InstanceImageCheck.general`; with `discovery_complete`,
`growTable`, `gfp` and `coveredIn`.

## 5. Remaining steps

Each step is a green round (`make test`, `make suite`), measured on the
census slices and the width series, with its commit record, and moves the
owning documents in the same commit. No step changes a wire shape; every
change of evidence size is reported.

By measured cost:

1. **Interning** (§1): trees, label lists and clauses given request-wide
   identities, so a label's equality, its hash and its row cost `O(1)` after
   its first visit. Measured, 2026-10-24: of `moduleFunction`'s 2.17
   sampled seconds outside the front end, 0.50 are row lookups, 0.35 label
   and clause equality and 0.26 label hashing; at width 136, 0.15 of 0.28.
   It changes the label type of the equation store.
2. **Checker memo.** `Subtyping.check` state-passing, and the field slices
   shared between a request's graph checks. Measured, 2026-10-24: in
   `moduleFunction`, a graph check computes each of its slices once, 390
   in search's 15 graph checks and 198 in the final check's 9, for 196
   distinct keys; the yield checks take 0.31 of 4.0 sampled seconds.
3. **The final check reads the memo**: `--produce-source-claims`'s check
   of the document answering the inclusions search established (§3).
   Measured, 2026-10-24: the final check takes 0.33 of `moduleFunction`'s
   4.6 sampled seconds, 0.16 of them in comparisons. It reads each request's
   own image check, fixed by the request's store, so this needs the store,
   or the request check, to carry the proved inclusions.
4. **Validator and discovery read the candidate index** (§2), with
   `indexCandidates_eq`, `indexCandidates_mem` and `checkEntries_eq`.
   Measured, 2026-10-24: `ClauseSelection` 1 % of `moduleFunction`'s and
   5 % of width 136's sampled work.
5. **Hashed kernel lookups**: under the graph's label hash, `TabRen`'s rows
   bucketed by their source labels, label containment through a hash set
   where the orders differ, and a meet row's parts read once per premise;
   each with its equality lemma to the list form it replaces. Measured,
   2026-10-24: `premTable`, `subsetIn` and `meetBelow` each at most 1 % of
   `moduleFunction`'s and 2 % of width 136's sampled work.
6. **A request-wide demand memo** (§1): a row's demand kept across a
   request's comparisons. Measured, 2026-10-24: computing demand takes 0.08
   of `moduleFunction`'s and of width 136's sampled seconds.
7. **`Clauses`** in the premise judgment, with `clauses_subset_sound`.
8. **Rerun deleted from the check** only with an operational theorem:
   selected discovery, at today's fuel and growth, finds a valid table
   wherever unrestricted discovery does; `selected_complete` is a part of
   it.
9. **Coverage by assumption**, where structural comparison remains a
   measured cost after the steps above: the dependency representation,
   `discovery_complete`, and discovery and deletion replaced.

This draft is deleted when the last step taken lands.
