# Draft: the subtype decision procedure

A design for review by the owner before any implementation. Base: TScert
main at c71c404.

The subtype relation is
[POSITIVE-TYPES' covered pairs](../POSITIVE-TYPES.md#covered-pairs) and
[RECURSIVE-EQUATIONS §4](../RECURSIVE-EQUATIONS.md#4-subtyping). One
operation decides it for both evidence search and the checker
(`PositiveCertificates.compareUsing`); the two differ only in where instance
choices come from. This draft replaces that operation's algorithm with one
designed whole, states the two rules it adds, and gives the lemmas the
trusted part needs.

**Evidence labels.** **Measured** gives the command, the commit and the date.
**Cited** names inspected code or a supplied measurement. **Proved** names a
Lean theorem. **Conjectured** marks a design claim, a proof obligation or an
estimate; every lemma below that no theorem names needs a Lean proof.

## 1. The algorithm and its cost

### 1.1 The algorithm

**Cited**, at c71c404. A question $`S\le T`$ goes through these steps
(`compareUsingCoreState`, `compareCheckedStep`, `compareStepStateCore`):

1. **Identity.** Every label of $`S`$ is a label of $`T`$ (`subsetUsing`), or
   the premise judgment derives the pair by `Var` (`premAt`).
2. **Instantiation.** When $`S`$ is a scheme row and $`T`$ an arrow contract,
   each proposed instance is tried in order (`compareInstancesState`). For
   every target arrow some signature's image must have the target's
   operands up to the order of union members, the receiver compared unless
   the signature's receiver is the universe, and an effect covering the
   target's (`instSig`, `sigMatch`, `sigBodyMatch`). Each operand's image is
   the substitution or a respelling proved equal to it by subtyping in both
   directions (`imagesUpTo`, `compareImagesUpTo`, `compareEquivalent`), or a
   checked finite table (`finiteInstanceImages`, `TableOk`).
3. **Structural coverage.** The pairs reachable from $`(S,T)`$ are collected
   frontier by frontier, every candidate target clause of every source clause
   contributing its demand pairs (`growTable`, `demandPairs`); rows not
   covered are deleted until every row is covered, each round rechecking
   every row (`gfp`, `coveredIn`); the result is validated
   (`checkStructural`, `checkEntries`).
4. **Rerun.** A comparison not established while reading only candidate
   clauses is redone reading every target clause (`compareStructural`,
   `compareStepState`), because completeness of the selected search is not
   proved ([WORK](../../WORK.md#union-shapes-discovery)).

Completed comparisons are cached within one operation, in a list searched
linearly (`completedLookup`); each operation starts empty. Search
additionally answers a repeated top-level request from its first answer
(`CertificateProducer.Answered`). For a scheme instance the producer
proposes the unified instance with its substitution images, respelling
patches built from each signature whose arity and effect admit a target
arrow (each operand's image respelled as the target's operand, as the target
less the other operands' images, or as the whole target, combined across
target arrows up to `instancePatchLimit`), and the row-matched instance
(`matchedInstance`) (`instanceCandidates`).

### 1.2 What it costs

**Cited — mechanism**, the investigation of 2026-10-23 at 2628711, on the
slice of `fragment-statements.mts#patternDefaults` inside larger slices,
where the compiler API's `Node` union has 116–136 members. One request takes
72 s at width 116: whether `node.elements.flatMap`'s member is below the
claimed instantiated signature. The array overlay's `flatMap` is a scheme
with six signatures, one per callback footprint; only the sixth, the
claimed callback's footprint, holds. Each candidate's images are checked by
`compareEquivalent`: 24 equivalence checks, 8 distinct, 86.5 of the
search's 96 s. The receiver's image is rechecked for every candidate
(3.9 s each); the callback images of candidates 1–5 fail (8.9 s each).

**Measured**, 2026-10-23, c71c404, a copy of the verifier tracing each image
check that is not the substitution, on the synthetic width-5 input of that
investigation: those images are respellings of three kinds.

- A binder is read met with the source universe, `T ⊓ J`. Substitution
  distributes the meet over the instance's union, giving
  `{∧(15,J), …, ∧(19,J)}`, while the claim spells the type `967`.
- `967` is one label whose row holds the five members' clauses; the
  instance names the five member labels.
- A lifted literal of the overlay applied to its arguments
  (`778(∧(24,J), …)`) stands where the claim states a closed literal of its
  own (`1025`) whose row is the same arrow.

The rows of `∧(c,J)` and `c` are the same clauses (meeting a record with the
source universe gives the record, `meet`). Each kind differs in spelling
only, yet the identity step never applies (no label in common), and every
comparison unfolds both sides.

**Cited — cost per check.** `growTable` pairs every source member with every
target member ($`2n^2`$ pairs a round, computed twice per row: for the
candidates and for `step`'s test of an empty demand), `gfp` rechecks every
row each round (26,915 clause pairs), and a failing direction is redone
without selection. A check costs about $`n^2`$ (exponent 1.8–2.0); the
number of checks does not depend on the width.

**Measured — the width series**, 2026-10-23, the synthetic inputs through
`verifier --produce-source-claims` serially, elapsed seconds; the 2628711
split is the investigation's trace:

| Width of `Node` | 5 | 20 | 30 | 50 | 87 | 136 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Search and check, c71c404 | 0.88 | | 7.55 | 18.6 | 54.6 | 137.6 |
| Same, 2628711 | 0.85 | 4.18 | 7.49 | 20.3 | 53.0 | 134.1 |
| Of which image equivalence, 2628711 | 0.2 | 3.1 | 6.1 | 17.2 | 47.1 | 120.7 |
| The rest, 2628711 | 0.65 | 1.08 | 1.39 | 3.1 | 5.9 | 13.4 |

The rest grows with the width too: the other questions compare `Node`
unions through the same all-pairs coverage.

**Measured — census slices**, 2026-10-23, c71c404, `make census` of the
named functions with `TSCERT_STAGE_STORE=off`, median of 3 serial runs
[range], CPU seconds:

| Slice | Search CPU | Check CPU | Evidence MB | Outcome |
| --- | ---: | ---: | ---: | --- |
| `patternDefaults` | 0.8 [0.8–0.8] | 0.4 [0.4–0.5] | 0.3 | verified |
| `forOfPattern` | 115.0 [113.8–115.7] | — | — | refused at search |
| `pattern` | 15.1 [15.0–15.1] | — | — | refused at search |
| `moduleFunction` | 29.1 [29.0–29.4] | 5.0 [5.0–5.1] | 5.2 | verified |
| `inertRead` | 21.1 [20.9–21.1] | 3.6 [3.6–3.6] | 5.3 | verified |
| `resolve` | 20.4 [20.2–20.4] | 3.4 [3.3–3.4] | 2.7 | verified |
| `collect` | 1.7 [1.7–1.7] | 1.0 [1.0–1.0] | 4.3 | verified |
| `closeStatements` | 1.2 [1.2–1.2] | 0.7 [0.7–0.7] | 3.9 | verified |

The two refusals are at a source expression obligation.

**Measured — attribution**, 2026-10-23, c71c404, one traced run of the copy
on each slice's artifacts, elapsed seconds of the outermost image checks
that are not the substitution, and of the outermost `checkUsing` calls:

| Run | Total | Image checks | Failing image checks | `checkUsing` calls |
| --- | ---: | ---: | ---: | ---: |
| `forOfPattern` | 116.9 | 89.7 (158) | 50.6 (55) | 0.07 (918, all by label identity) |
| `pattern` | 14.8 | 8.3 (115) | 4.1 (34) | 0.05 (870, all by label identity) |
| `moduleFunction` | 28.6 | 4.2 (1,686) | 0.8 (10) | 0.19 (2,372, all by label identity) |
| `inertRead` | 20.1 | 0.3 (651) | 0 (0) | 0.17 (2,064, all by label identity) |
| `resolve` | 19.8 | 0.3 (651) | 0 (0) | 0.16 (2,024, all by label identity) |
| `collect` | 1.6 | 0.1 (6) | 0 (0) | 0.00 (8, all by label identity) |
| `closeStatements` | 1.2 | 0 (0) | 0 (0) | 0 (0) |
| Width 136 | 138.7 | 125.1 (24) | 66.9 (5) | 0.00 (42, all by label identity) |

### 1.3 The causes

1. **Equality where the rule needs inclusion.** The instance rule asks for
   the instance's operands to be the target's, so a respelled operand costs
   two subtype checks, and a wrong overload is refuted by a failing
   equivalence.
2. **Several spellings of one type** (§1.2), with identity tested on labels
   only.
3. **Union members compared each against each** in table growth, coverage
   and the validator's candidate filter (`ClauseSelection.candidates` filters
   every target clause for every source clause).
4. **The greatest fixed point re-closed over the whole table** each round,
   after every candidate's demand pairs were collected eagerly.
5. **Results discarded**: per-operation caches, a rerun without selection,
   several respelling candidates per signature.

## 2. What TypeScript does, and what fits

TypeScript's checker ([TypeScript](../REFERENCES.md#typescript)) relates
types fast by five means. Each is placed here by the trust boundary: the
checker stays sound and decides a stated relation; search is untrusted.

| Means | Fits | Where |
| --- | --- | --- |
| One spelling per type: equal syntax is one object | yes, per request | engine: interned trees and clauses |
| Equal types are one object | in part: equal clauses | the `Clauses` rule, trusted lemma |
| Union members matched by identity or index | yes | engine and validator; validator lemma |
| Relation results cached for the whole run | yes, scoped | engine; proofs ride with entries |
| Recursive questions assumed while open | yes | engine; the validator is unchanged |
| Overloads and type arguments decided locally | yes | producer; the rule becomes inclusion |

**Syntax and types.** Interning gives every tree and every clause a request
encounters one identity, so syntactic equality and hashing cost $`O(1)`$
after a tree's first visit. That is identity of syntax. Equality of types is
equality of their unfoldings, and a non-regular family unfolds to infinitely
many distinct types
([RECURSIVE-EQUATIONS §1](../RECURSIVE-EQUATIONS.md#1-the-problem)), so no
finite canonicalization decides it. The level at which the spellings of
§1.2 coincide is a type's **clauses**: a type means the union of its clause
rows' clause meanings and its other labels' meanings, so two types with the
same clauses and the same other labels are one type, whatever labels carry
the clauses. The `Clauses` rule (§3.1) makes that an identity; all three
kinds of §1.2 are then identities.


**Overloads.** With the instance rule stated as inclusion (§3.1), an
instance's images are the substitution, so the producer proposes instances,
not respellings: the binders found by unifying the target arrows with the
signatures, each target arrow's overload the first signature whose clause
structure, effects included, unifies. Structure orders the signatures and
excludes only what the rule excludes (arity, an effect that does not cover);
an overload of the same structure is still refuted by its operands.

## 3. The target procedure

### 3.1 The relation

The rules are those of POSITIVE-TYPES and RECURSIVE-EQUATIONS §4 with two
rules added. A **derivation** of $`S\le T`$ is finite and inductive; its
leaves are guarded family certificates, coinductive inside:

- **identity**: `Mem`, or `Clauses` below;
- **Var**: two applications of one head with validated variance, its
  argument premises derivations;
- **instantiation**: `Inst≤` below, its bound, arrow and part premises
  derivations;
- **structure**: a family certificate (table, arrow evidence, member
  instances) the validator accepts that contains $`(S,T)`$, each member
  instance with its premises derivations. Inside the certificate, premises
  are read by the premise judgment (table rows, `Mem`, `Clauses`, `Var`,
  `Inst` of validated entries, `TabRen`), never by a derivation outside it.

**Soundness** is semantic: an accepted question's inclusion holds at every
parameter assignment, for both components (`compareUsing_sound`, unchanged
in statement). Acceptance constructs a derivation, and every derivation is
sound by the lemmas of §5.

**Clause identity.** Besides `Mem` (a label of $`A`$ that is a label of
$`B`$), the premise judgment $`\Delta(A,B)`$ holds when every split clause of
$`A`$'s clause rows is a split clause of $`B`$'s clause rows and every other
label of $`A`$ is a label of $`B`$; and in coverage a split source clause
that is a split clause of the target is covered:

```math
\frac{\mathsf{split}(\mathsf{cl}_G(A^{\mathsf{c}}))\subseteq\mathsf{split}(\mathsf{cl}_G(B))\qquad A\setminus A^{\mathsf{c}}\subseteq B}
     {\Delta(A,B)}\ \textsf{Clauses}
\qquad
\frac{a\in\mathsf{split}(\mathsf{cl}_G(B))}{\Delta;\kappa;A\vdash a\sqsubseteq_B}\ \textsf{Same}
```

where $`A^{\mathsf c}`$ is the clause rows of $`A`$.

**Instantiation by inclusion.** A scheme row $`i`$ is below a target with
arrow contract $`\mathsf{arrs}(L;M)`$ and opaque parts $`\vec P`$
(`instanceTarget`) when an instance $`c`$ is checked as today (kinds and
arity, `instKinds`; a call scheme; the image check; admission,
`compareAllowed`; every bound), each target arrow is covered by one
signature's image, and $`i`$ is below each part:

```math
\frac{c\ \text{checked}\qquad
      \forall q\in L.\ \exists p\in\Sigma.\ p[c]_q\sqsubseteq_{\mathsf{sig}}q\qquad
      \forall q\in M.\ \exists p\in\Sigma_\ldots.\ p[c]_q\sqsubseteq_{\mathsf{sig}}q\qquad
      \forall P\in\vec P.\ \{i\}\le P}
     {\{i\}\ \le\ T}\ \textsf{Inst}_\le
```

$`p[c]_q`$ is the signature's image through the instance's table
(`sigImg`, `restImg`), defined when every operand it reads has an image;
where $`p`$'s receiver admits every value (`receiverUniverse`: `top`, or
`source` with the target's receiver a source type) its receiver is $`q`$'s
and its body alone is imaged, as `sigBodyMatch` reads it.
$`\sqsubseteq_{\mathsf{sig}}`$ is one signature covering one signature of the
same arity: receiver and arguments contravariant, result covariant, the
effect covering $`q`$'s; for variadic signatures the fixed arguments and
the result likewise, and the complete rest pack contravariantly, as an
inclusion of argument-list components (tuple length, positions and
optionality included). Its operand premises are
derivations. Today's rule (`instSig`, `instRest`) is its case of operands
equal up to member order. It is F<:'s instantiation followed by
subsumption ([Pierce 2002](../REFERENCES.md#pierce-2002), chapter 26).

The image check keeps its two forms (`eitherImages`): the substitution, now
exact (`substitutionTableOk`), and the checked finite table (`TableOk`).
Image equivalence (`imagesUpTo`, `structuralImages`, `compareEquivalent`)
has no remaining use. Instance premises are read as bound premises are
today: completed derivations, never assumed, a repeat on the instance path
requiring a guarded structural derivation
([§4.4](../RECURSIVE-EQUATIONS.md#44-instantiation)).

### 3.2 The engine

One procedure for search and checking, untrusted for soundness: every
established result carries its proof (`CheckedComparison`).

1. **Interning.** Trees, label lists and clauses get request-wide identities
   (hash-consing of the syntax met); a type's clause set and label set are
   sorted identity arrays.
2. **Memo** of completed successes (§3.5).
3. **Identity** by `Mem` and `Clauses`, on the target's identity sets.
4. **Var**, its premises asked recursively.
5. **Inst≤** for a scheme row against an arrow target (§3.4), its premises
   asked recursively as completed comparisons.
6. **Structure, by assumption.** The family certificate is built depth
   first. A pair open on the current path is assumed; a pair established in
   this question holds. Each premise of a covering is decided by what the
   premise judgment reads: a table row (the pair is visited), `Mem`,
   `Clauses`, `Var` and `Inst` of validated entries, `TabRen`; and
   prototype-member coverage reads member instances, each validated before
   use as a completed comparison. For each split source clause: `Same`,
   else the target clauses the index returns (§3.3), each checked first by
   its premise-free conditions, then by its premises in turn; the first
   covering clause is kept. When a pair fails, every result established
   since it was pushed is discarded; a pair established while assumptions
   are open stays provisional until the outermost open pair closes.
7. **Validation.** The established pairs, with the arrow evidence and
   member instances their coverings used, are the table `checkEntries`
   validates; the structural result is that validation.

**What it decides.** The engine's generating function is today's search
space: coverings by candidates; arrow evidence as `arrowSearch` produces it
(domain union and combinations of two source signatures, not the nested
combinations `ArrowCert` admits); `TabRen` over the rows inserted; member
instances as `rowInstances` proposes them. Within one question, a pair that
fails while every open pair is assumed is outside the greatest fixed point
of that function over the pairs the question reaches: assumptions only add
premises. Depth-first search with every candidate tried decides membership
in that fixed point
([Pierce 2002](../REFERENCES.md#pierce-2002), chapter 21, for
finite-state generating functions; it transfers where the reachable set is
finite). A pair is evaluated again only after a failure discards its
provisional result, so a question evaluates a pair at most once more per
failed pair.

**Resources.** A question's budget counts pairs evaluated and instance
descent; growth refuses as `grows` does, over the pairs inserted in the
question; exhaustion stays an outcome distinct from an unestablished
question. These differ from today's frontier rounds, and `grows` depends on
insertion order, so a question near either limit can be decided
differently: the design does not claim preservation of today's acceptances
under resource limits (§3.6).

### 3.3 Union members by index

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
returns exactly the candidates (`indexCandidates_mem`, §5). A union
discriminated by one key costs, per source clause, the clauses admitting
its literal where the filter reads every target clause.

For a closed entry, the one a comparison validates, the validator reads
candidates only (`checkEntries_eq`, §5); an entry with hypotheses, as
variance validation checks, reads the indexed candidates first and every
clause after, as today. Table membership reads a hash set of the rows, and
`TabRen` the rows of the queried head pair, where both scan the table.

### 3.4 Instances

**Search.** The proposal routes stay, with exact images: unification of the
target arrows with the signatures (`unifyScheme`, including relaxed matching
of fixed operands); unification of the arguments without the results (the
`exact` route's inference); prototype members with either host as receiver
and the receiver-free inference (`rowInstances`); and the row-matched
instance (`matchedInstance`), for equation labels too, its finite table
checked by `TableOk`. Each route gives one instance; within it each target
arrow chooses the first signature whose structure unifies. The respelling
patches, `extendInstancePatches` and `instancePatchLimit` are removed: they
vary images only, which exact images fix.

**Checking.** The evidence names the instance; the checker checks it and
`Inst≤`, trying for each target arrow first the signatures whose arity and
effect admit it and whose operands' clause shapes agree with its operands',
then the others with that arity and effect. The order changes cost, not the
existential.

### 3.5 The memo

A request-wide map from a question to its completed success, with its
`CheckedComparison`, in one graph and one image check
(`Checked.graph_eq`, `Checked.images_eq`): a success holds in every context,
its proof being of the inclusion at every assignment. Failures and
exhaustions are not kept across questions: whether a question fails
depends on its instance path, its proposals and its resources. Search
threads the memo through every question of a request (`Answered`,
extended); the checker threads it through a request's checking by the
subtyping interface (`Subtyping.check`, made state-passing). Memo entries
answer top-level questions and instance premises; inside a family
certificate premises are read by the premise judgment only.

### 3.6 What is preserved

- **Soundness:** unchanged statement.
- **Instances:** a witness accepted today is accepted with the same
  binders where the new engine establishes its operand premises. Today's
  check established each respelled image $`I`$ and its substitution $`S`$
  included both ways; the new premise relates the target operand $`Q`$, the
  union of the entry images, to the exact image, the union of the
  substitutions. That premise is composed of inclusions today's engine
  established in parts; that the new engine establishes the composed
  question is conjectured, not proved: composing completed comparisons
  over a union is not a rule of the structural engine.
- **Structure:** a certificate outside the generating function of §3.2 (a
  nested combination, a row only another search would insert) is not
  searched, as today. Today's search draws its tables from the same
  function; that the depth-first search finds a table wherever today's
  growth and deletion find one (`selected_complete` and `discovery_complete`,
  §5) is conjectured. Resources differ (§3.2), so preservation is claimed
  only for questions within both budgets.

What is not proved is measured: every pipeline case keeps its expected
outcome, and the eight census slices keep theirs; any other change is a
coverage result, reported with its cause.

## 4. Invariants

1. Every established comparison, cached or fresh, carries a proof of the
   inclusion at every parameter assignment (`CheckedComparison`).
2. The validator's decision on a family is today's under the extended
   premise judgment; candidate reading and hash lookups change its cost.
3. Instance images are the exact substitution (equations) or a checked
   finite table.
4. Selection excludes no covering of any valid closed entry (R1–R5,
   `valid_selected`, extended to `Same`).
5. A family certificate's premises are read by the premise judgment only;
   completed comparisons enter it as validated member instances.
6. Assumptions discharge operand premises only, which a constructor guards;
   instance premises are completed derivations.
7. Only successes are reused across questions.

## 5. Trust and lemmas

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
- The indexed validator: `indexCandidates_mem`,
  `b ∈ indexCandidates G a B ↔ b ∈ candidates G a B`; `checkEntries_eq`,
  for a family of closed entries with `VariablesOk`, lookups to entries of
  the family or sound entries, and sound known rows — the premises
  `checkStructural`'s callers hold as `checkStructural_sound` uses them —
  the decision over candidates, element branch included, equal to the
  decision over `candidates ++ clausesOf`, from `valid_selected` and
  `checkEntries_sound`; `premTable_eq`, hashed membership and head-pair
  `TabRen` equal to the list scans.
- Memo lookups return an entry whose question is the query's, checked by
  equality as `completedLookup` checks it.

**Untrusted, with completeness lemmas:** `selected_complete` — a valid
closed family whose coverings are by candidates, restricted to the pairs
reachable from its root through those coverings' premises (table rows,
`Var`, `TabRen`, member instances) and their arrow evidence, stays valid;
it needs the dependency closure WORK's
[selected discovery](../../WORK.md#union-shapes-discovery) states. With
`discovery_complete` — a table in the reach of §3.2's generating function,
its coverings by candidates, is found by the depth-first search — it is the
condition for deleting the rerun.

**Unchanged:** `SourceClaimJson.checkJson_safe`, its premise and its
conclusion; `FamilyValid` but for `Same`; R1–R5 and their lemmas. Generic
definitions carry `@[nospecialize]`; no `sorry`, no axioms.

**Untrusted:** the engine (interning, search order, assumptions, memo
policy, budgets), the index's construction beyond its lemma, unification
and overload order, every proposal.

**Removed:** `imagesUpTo`, `structuralImages`, `compareEquivalent`,
`equivalent`, `compareImagesUpTo`, `growTable`, `gfp`, `coveredIn`, the
respelling patches, `extendInstancePatches`, `instancePatchLimit`; with the
completeness lemmas, the reruns and `InstanceImageCheck.general`.

## 6. Certificates and the checker's search

**Conjectured — a linear check needs explicit witnesses.** A certificate of
a question would be its table with, per row, per split source clause, the
covering target clause's position or `Same`; per premise its rule with its
row, entry or instance; for `TabRen` the renaming and the renamed row it
generates; and arrow evidence with each domain split, each combination's
chosen signatures and the compatibility of each pair of their result labels
written out. Its size is charged with every term it names or generates.
With interned terms, rows in a hash set and validation memoized by evidence
entry, each obligation is checked in time proportional to the terms it
names, preprocessing and instance validation included, so the check is
linear in that size. A combination's compatibility obligations are a product
of result labels; the certificate pays their size where the checker today
pays their search.

**The checker keeps deciding.** The checker runs the engine with the
evidence's instance choices in place of the proposal routes. Its work on a
question is not bounded by search's in general: search's memo holds
results of questions checking does not ask, and supplied member choices
change the traversal. The measured check stages take 0.4–5.0 s CPU
(§1.2), and in every check traced each checker comparison is decided by
label identity; reading and decoding are the dominant part of checking
([certificate sharing](certificate-sharing.md#measurements-and-their-limits)),
and a certificate adds to that part. So the checker's structural search is
kept, with the memo of §3.5. The census reports check CPU per slice; a slice
whose check spends its time in structural search is where certificates
replace it, with the same validator.

## 7. Expected costs

**Conjectured.** Without image equivalence (§3.1) and with the respelled
operands identities by `Clauses`, the image-check time of §1.2's
attribution is removed: 89.7 s of `forOfPattern`'s 116.9 s, 8.3 of
`pattern`'s 14.8, 4.2 of `moduleFunction`'s 28.6, 125.1 of the width-136
run's 138.7; the image checks of `inertRead`, `resolve`, `collect` and
`closeStatements` take at most 0.3 s. The rest compares `Node` unions by
index, $`O(n)`$ each, so the width-independent part of the width-5 run
(0.65 s at 2628711) dominates the width series:

| Width of `Node` | 5 | 30 | 50 | 87 | 136 |
| --- | ---: | ---: | ---: | ---: | ---: |
| Today, c71c404 | 0.88 | 7.55 | 18.6 | 54.6 | 137.6 |
| Expected | ≤ 0.9 | ≤ 1 | ≤ 1 | ≤ 1.5 | ≤ 2 |

The criterion is the shape: the time at width 136 within twice the time at
width 5. For `inertRead`, `resolve`, `collect` and `closeStatements`, whose
search spends its time outside image checks, the expected change is what
the index and the engine save in their structural comparisons, measured at
each step. Outcomes are unchanged: six verified, `forOfPattern` and
`pattern` refused at their source expression obligation.

## 8. Migration

Each step is a green round (`make test`, `make suite`), measured on the
eight census slices and the width series, with its commit record, and moves
the owning documents in the same commit: POSITIVE-TYPES for the relation and
the engine, RECURSIVE-EQUATIONS §4.4 and §6 for instantiation, UNION-SHAPES
§7 for the index and the rerun, WORK's row for the measurements. No step
changes a wire shape: the evidence keeps instance choices with their
tables, which become exact substitutions; evidence bytes change only where
a proposal's images change, and that change is reported.

1. **Validator.** Index, candidates-only existential for closed entries,
   hashed table lookups, with `indexCandidates_mem`, `checkEntries_eq` and
   `premTable_eq`. The decision is unchanged.
2. **Clause identity.** `Clauses` and `Same` in the premise judgment, the
   coverage rule and the identity step, with `clauses_subset_sound` and
   `excludes_self`, which keeps step 1's equality.
3. **Instantiation by inclusion.** `Inst≤` in `compareInstArrsState`, exact
   images, the proposal routes without patches; image equivalence and the
   patches deleted in the same commit.
4. **Engine.** Interning, the memo of successes in search, structure by
   assumption; `growTable`, `gfp` and `coveredIn` deleted in the same
   commit; the rerun kept.
5. **Checker memo.** `Subtyping.check` state-passing, the memo threaded
   through a request's checking.
6. **Rerun.** `selected_complete` and `discovery_complete` proved and the
   reruns deleted.

Step 2 follows step 1 (it extends the selection lemma step 1 uses); step 3
is independent of both; step 4 uses step 1's index and step 2's identity;
step 5 uses step 4's memo; step 6 follows step 4, whose search the lemma is
about. This draft is deleted when step 6 lands.
