# Draft: deciding types in search and checking

A design for review by the owner before any implementation. Base: TScert
main at c71c404.

The subtype relation is
[POSITIVE-TYPES' covered pairs](../POSITIVE-TYPES.md#covered-pairs) and
[RECURSIVE-EQUATIONS §4](../RECURSIVE-EQUATIONS.md#4-subtyping). One
operation decides it for both evidence search and the checker
(`PositiveCertificates.compareUsing`); the two differ only in where instance
choices come from. What asks it, search's typing of expressions and the
narrowing of a union by a member test, sets how often it is asked. This
draft designs the three together: the comparison's algorithm and the two
rules it adds, narrowing by an index, and typing by synthesis, with the
lemmas the trusted part needs.

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

**Measured — image checks**, 2026-10-23, c71c404, one traced run of the
copy on each slice's artifacts, elapsed seconds of the outermost image checks
that are not the substitution (count):

| Run | Total | Image checks | Failing image checks |
| --- | ---: | ---: | ---: |
| `forOfPattern` | 116.9 | 89.7 (158) | 50.6 (55) |
| `pattern` | 14.8 | 8.3 (115) | 4.1 (34) |
| `moduleFunction` | 28.6 | 4.2 (1,686) | 0.8 (10) |
| `inertRead` | 20.1 | 0.3 (651) | 0 |
| `resolve` | 19.8 | 0.3 (651) | 0 |
| `collect` | 1.6 | 0.1 (6) | 0 |
| `closeStatements` | 1.2 | 0 | 0 |
| Width 136 | 138.7 | 125.1 (24) | 66.9 (5) |

**Measured — the whole verifier**, 2026-10-23, c71c404, macOS `sample` at
1 ms over one run of the uninstrumented verifier on each slice's artifacts,
`--produce-source-claims` (search, then its own check of the evidence) and
`--check-source-claims` on the evidence it wrote; seconds of working
samples, each sample assigned to the first mechanism of the list on its
stack:

| Mechanism | `moduleFunction` | `inertRead` | `resolve` | `forOfPattern` | `pattern` | `collect` | `closeStatements` |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Narrowing by a member test (`uncoveredField`) | 6.40 | 5.88 | 5.74 | 4.52 | 0.79 | 0 | 0 |
| Other narrowing slices | 3.32 | 2.84 | 2.72 | 4.32 | 1.29 | 0 | 0 |
| Image equivalence | 3.73 | 0.23 | 0.23 | 78.44 | 7.48 | 0.08 | 0 |
| Search's subtype requests (the rest) | 6.01 | 5.04 | 5.07 | 9.03 | 1.13 | 0.02 | 0.01 |
| Search re-checking its candidate evidence | 1.19 | 0.10 | 0.08 | 2.45 | 0.57 | 0.08 | 0.01 |
| Label membership (`subsetUsing`) | 0.71 | 0.59 | 0.56 | 0.21 | 0.02 | 0.01 | 0.02 |
| Structural tables, outside the above | 0.26 | 0.27 | 0.25 | 0.30 | 0.04 | 0 | 0 |
| Reading and writing documents | 2.56 | 2.23 | 1.91 | 2.38 | 1.33 | 0.80 | 0.42 |
| Everything else | 0.50 | 0.42 | 0.39 | 0.23 | 0.17 | 0.01 | 0.15 |
| **Search run** | 24.7 | 17.6 | 16.9 | 101.9 | 12.8 | 1.0 | 0.6 |
| Check: reading documents | 1.40 | 1.23 | 1.09 | — | — | 0.39 | 0.12 |
| Check: narrowing | 0.88 | 0.78 | 0.74 | — | — | 0 | 0 |
| Check: image equivalence | 0.71 | 0.08 | 0.08 | — | — | 0.03 | 0 |
| Check: other comparisons | 0.95 | 0.50 | 0.45 | — | — | 0.06 | 0.02 |
| Check: everything else | 0.14 | 0.14 | 0.15 | — | — | 0 | 0.07 |
| **Check run** | 4.1 | 2.7 | 2.5 | — | — | 0.5 | 0.2 |

The census's stage CPU is larger than the sampled work (29.1 against 24.7 s
for `moduleFunction`'s search): it counts every thread and the process's
start.

**Measured — what multiplies**, the traced copy, same runs:

- **Narrowing.** `uncoveredField` runs 1,280 times in `moduleFunction`
  (1,126 and 1,110 in `inertRead` and `resolve`), mostly over `Node` and its
  restrictions (108 × 108 labels in 266 calls, 108 × 492 in 74). For each
  label of the narrowed type it scans the candidate labels, unfolding each
  and comparing its record clause component by component (`restriction`,
  `restricts`): $`n\cdot m`$ unfoldings and clause comparisons a call.
- **Generate and test.** Search types an expression by trying types: a read
  `x.f` tries every type of the unit's pool that has a field `f` as the
  receiver's type, then asks whether `x`'s type is below it. Of
  `moduleFunction`'s 7,715 distinct subtype requests, 6,045 are such
  coercions of a variable, 6,031 of them failing (3.2 s traced); 42,402
  requests are answered again from the producer's table. `inertRead` and
  `resolve` have 6,022 and 6,020 failing requests of 7,585 and 7,461.
- **Recomputation across passes.** Search checks each candidate evidence
  tree as the checker would (`checkTreeS`), and its comparisons go through
  the checker's operation, which starts empty: every comparison search made
  is made again, then again in the check stage's process.
- **Lists.** Label membership tests a list against a list
  ($`O(|S|\cdot|T|)`$, 108 × 108 for `Node`).

### 1.3 The causes

Of the comparison itself:

1. **Equality where the rule needs inclusion.** The instance rule asks for
   the instance's operands to be the target's, so a respelled operand costs
   two subtype checks, and a wrong overload is refuted by a failing
   equivalence.
2. **Several spellings of one type** (§1.2), with identity tested on labels
   only, and labels compared as lists.
3. **Union members compared each against each** in table growth, coverage
   and the validator's candidate filter (`ClauseSelection.candidates` filters
   every target clause for every source clause).
4. **The greatest fixed point re-closed over the whole table** each round,
   after every candidate's demand pairs were collected eagerly.
5. **Results discarded**: per-operation caches, a rerun without selection,
   several respelling candidates per signature.

Of what asks it:

6. **Narrowing pairs every member with every candidate**: a member test's
   slice scans the candidates for each member of the narrowed union.
7. **Types guessed, then tested**: search proposes the types of an
   expression's parts from the unit's pool and refutes the wrong ones by
   failing subtype questions, where the parts' types determine them.
8. **Answers not shared across passes**: search's own check, and the check
   stage, decide again every comparison search established.

Reading and writing documents (2.6 of `moduleFunction`'s 24.7 s, 0.8 of
`collect`'s 1.0 s) is the subject of
[certificate sharing](certificate-sharing.md), not of this design.

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
| Expression types synthesized from their parts | yes | producer's typing (§3.7) |

**Syntax and types.** Interning gives every tree and every clause a request
encounters one identity, so syntactic equality and hashing cost $`O(1)`$
after a tree's first visit. That is identity of syntax; this design
canonicalizes nothing beyond it, and two spellings whose unfoldings agree
only deeper are related by comparison. The level at which the spellings of
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

$`p[c]_q`$ is the signature's image through the instance's table, defined
when every operand it reads has an image; where $`p`$'s receiver admits
every value (`receiverUniverse`: `top`, or `source` with the target's
receiver a source type) its receiver is $`q`$'s and its body alone is
imaged (`sigPremises`, `restPremises`).
$`\sqsubseteq_{\mathsf{sig}}`$ is one signature covering one signature of the
same arity: receiver and arguments contravariant, result covariant, the
effect covering $`q`$'s; for variadic signatures the fixed arguments and
the result likewise, and the complete rest pack contravariantly, as an
inclusion of argument-list components (tuple length, positions and
optionality included). Its operand premises are derivations. Its case of
operands equal up to member order is the rule it replaces. It is F<:'s
instantiation followed by subsumption
([Pierce 2002](../REFERENCES.md#pierce-2002), chapter 26).

The image check keeps its two forms (`eitherImages`): the substitution,
exact (`exactImages`, `substitutionTableOk`), and the checked finite table
(`TableOk`). Instance premises are read as bound premises are
today: completed derivations, never assumed, a repeat on the instance path
requiring a guarded structural derivation
([§4.4](../RECURSIVE-EQUATIONS.md#44-instantiation)).

### 3.2 The engine

One procedure for search and checking, untrusted for soundness: every
established result carries its proof (`CheckedComparison`).

1. **Interning.** Trees, label lists and clauses get request-wide identities
   (hash-consing of the syntax met); a type's clause set and label set are
   hash sets of identities.
2. **Memo** (§3.5).
3. **Identity** by `Mem` and `Clauses`, on the target's identity sets.
4. **Var**, its premises asked recursively.
5. **Inst≤** for a scheme row against an arrow target (§3.4), its premises
   asked recursively as completed comparisons.
6. **Lists.** Label containment is linear where both lists share an order
   (`memAll`, `subsetIn`), search deduplicates candidate types through a hash
   set (`keepFirst`), and renamed-member pairs are formed once per key and
   schemes.
7. **Structure.** Today's discovery, deletion and validation
   (`growTable`, `gfp`, `checkStructural`), with three changes: with
   selection on, every reading of candidates for a source clause, in demand
   pairs (`demandPairs`), coverage (`coveredIn`) and validation
   (`checkEntries`), reads the index (§3.3), and with selection off
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
(§5), and only where structural comparison remains a measured cost
after the other steps (§8).

**Resources** keep today's meaning while discovery stays today's:
frontier rounds, `grows` over the rows inserted, exhaustion distinct from
an unestablished question.

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
returns exactly the candidates, in the order and multiplicity of
`ClauseSelection.candidates` (each bucket holds clause positions, merged in
position order): `indexCandidates_eq`, list equality, which discovery
needs because `growTable` inserts rows in candidate order and `grows` reads
the rows inserted; the validator's existential needs only its consequence,
membership equality (`indexCandidates_mem`, §5). A union
discriminated by one key costs, per source clause, the clauses admitting
its literal where the filter reads every target clause.

For a closed entry, the one a comparison validates, the validator reads
candidates only (`checkEntries_eq`, §5); an entry with hypotheses, as
variance validation checks, reads the indexed candidates first and every
clause after, as today. Exact table membership reads a hash set of the
rows; `TabRen`, which accepts a row containing the query after renaming,
scans the rows as today.

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
its proof being of the inclusion at every assignment. Inside the
comparison operation failures and exhaustions are not kept across
questions: an inner question's failure depends on its instance path, its
proposals and its resources. Search's top-level table (`Answered`) keeps
every outcome, as today; a question it records as unestablished is answered
by the success map first, so a success found later wins, and an
unestablished answer is reused as today otherwise, with today's coverage. The success
map is threaded through the inner questions of search and, by the
subtyping interface (`Subtyping.check`, made state-passing), through a
request's checking. Memo entries answer top-level questions and instance
premises; inside a family certificate premises are read by the premise
judgment only.

### 3.6 Narrowing by index

A member test's slice reads, for each label $`a`$ of the narrowed union, the
first candidate label $`b\ne a`$ whose one record clause is $`a`$'s clause
with its views of the tested key $`f`$ at another type (`restriction`,
`restricts`). The candidates are unfolded once per slice (`candidateRows`,
`restrictionIn_eq`). `restricts` requires the two clauses' first operands
equal and their views equal but at $`f`$, so $`b`$ is found among the
candidates with $`a`$'s **key**: a hash of the first operand and of the
views with the views at $`f`$ at no type, under the graph's label hash
(`restrictKey`, `NormalGraph.labelHash`, which the equations' graph takes
from a label's tree). The index of a candidate list maps a key to the
candidates holding it in list order, built once per list (`rowIndex`,
`rowIndex_getD`); a lookup reads $`a`$'s key's candidates and keeps the
first that `restricts` accepts, which is the first of the whole list that
does (`restrictionAt_eq`): a candidate `restricts` accepts has $`a`$'s key
(`restricts_key`). A slice then costs $`m`$ key computations for the index,
$`n`$ lookups, and `restricts` on each label's bucket, where it costs
$`n\cdot m`$ unfoldings and comparisons. A bucket holds the candidates
sharing a member's record clause but for the tested key; `restricts` and its
nested reads of field types run on the bucket only.

**Measured**, 2026-10-23, the traced copy with `uncoveredField` reading each
candidate's row once per call (a prototype of the index's first half):
`moduleFunction`'s 1,280 calls take 2.1 s where they take 7.3 s, `inertRead`'s
1,126 take 1.9 s where 6.8; the buckets total 40 candidates a call
(35 in `inertRead`), at most 30 for one label, against the 11,664 pairs of a
108 × 108 call. The index removes the remaining pairwise `restricts` calls.

Search asks the same yield checks repeatedly (1,280 `uncoveredField` calls
in `moduleFunction`, over few distinct sizes). Search's answers table
(`Answered`) keeps each yield check's outcome by its inputs (the slot's
type, the key, the tags, the answer, the yield's type), so a repeated check
is answered from its first. This memo is search's: the checker's slices are
its own.

Narrowing is trusted: the checker computes the same slices
(`uncoveredField_sound`). The index reads the graph's label hash, which no
meaning reads; `restriction` keeps its statement and its proof, and the
indexed lookup is proved equal to it.

### 3.7 Typing by synthesis

Search types an expression bidirectionally. Each term's type is
**synthesized** from its parts: a variable's from the context, a read's
from its receiver's synthesized type (its field, its view, or the read
summary of a union, `summaryUsing`), a call's from its callee's member
signature, an operator's from its operands'. The claimed type is
**checked** once, where the term meets it, by one subtype question
(`coerce`). Synthesis is a partial function: it returns one candidate type
for a variable (its slot's type), a read of a field from a receiver whose
synthesized type is one record clause (that field's, view's or optional
field's type, by the read rules), and a call whose callee synthesizes one
member signature (its result); it returns none for any other form,
including a read from a union receiver other than a variable, which goes to
the pool at once. The candidate is one more alternative, first, at the same
fuel as the pool's: an alternative costs no fuel today, fuel being spent by
recursion. Per form:

- a read `a.f` against a claimed type $`A`$: the receiver type `a`
  synthesizes (a variable's slot type; a read's field type); a union
  receiver through the read summary of that type, key and $`A`$
  (`summaryUsing` takes the claimed type, which checking supplies);
- a call or construct: the callee's synthesized type, its signatures in
  declaration order filtered by arity and effect, the first whose argument
  checks hold; a rest call's spread operands at their synthesized types;
- an operator: its operands' synthesized types, then the pool's operand
  types.

Within a rule, search establishes the parts (callee, receiver, arguments,
the receiver of a read) before it compares the rule's result with the
claimed type: a wrong candidate then fails at its parts, which the parts'
types decide, rather than at a comparison of its result with the claim.

Fuel and budgets are today's; evidence is the same rules' nodes. The pool keeps the types no part determines: a literal's
singleton or family label, a fresh object's code type, `undefined`.

As search, this orders alternatives: each `findSearch?` over the pool tries
the synthesized type first and the pool after, so a term search typed
before keeps every alternative it had, and a wrong guess is no longer tried
before the type its parts determine. Where the synthesized attempt fails,
the pool is still tried, at today's cost.

**Measured**, 2026-10-23, the traced copy: of `moduleFunction`'s 6,031
failing variable coercions, 5,893 (1.19 s traced) lie in an alternative
search that then succeeds, 138 (1.98 s) in one that fails; `inertRead`'s
are 5,885 (1.19 s) and 129 (1.90 s). Synthesis-first leaves the first kind
where the synthesized candidate is the one that succeeds; the second kind
stays. Search is untrusted, so this changes no
trusted code and no wire.

### 3.8 One memo for search and its check

Search's own check of each graph and code it produces runs in the process
that established its comparisons, over the same graph. Search records each
inclusion it establishes with its proof (`Answered.proved`), and its checks
read them as the image check's proved inclusions (`Answered.images`,
`InstanceImageCheck.known`), which `compareUsing` establishes without
comparing. The final check of `--produce-source-claims` reads each request's
own image check, which holds none, and the check stage, in its own process,
holds none.

### 3.9 What is preserved

- **Soundness:** unchanged statement.
- **Instances:** a witness accepted today is accepted with the same
  binders when the engine establishes its operand premises. Today's check
  established, for each respelled entry, the respelled image $`I_l`$ and the
  substitution $`S_l`$ included both ways; the new premise relates the
  target operand $`Q=\bigcup_l I_l`$ to the exact image
  $`S=\bigcup_l S_l`$ (or the reverse). It composes the parts
  constructively where each part was established by identity, `Var` or a
  structural family: a label of $`S_l`$ that is a label of $`I_l`$ is one of
  $`Q`$; a `Var` premise against a member of $`I_l`$ is one against a member
  of $`Q`$; and the union of the parts' valid families with the root row
  $`(S,Q)`$ is a valid family (`families_union_valid`, §5) when no part's
  covering reads its source type (`self`, the receiver premise of method
  coverage, `CoversArrows`): each source clause of $`S`$ is then covered in
  $`I_l\subseteq Q`$ with premises in its part's family. A part whose
  covering reads its source type, or established by instantiation, is not
  composed: its premise read at the union may fail. Whether discovery from
  $`(S,Q)`$ finds the composed family within today's fuel and growth is not
  proved. So instance preservation is claimed for the composable parts and
  measured for the rest: step 1 deletes image equivalence, and a case or
  census slice it loses is a coverage result that revises the design (§8).
- **Structure:** discovery and deletion stay today's; selected discovery
  reads candidates as today, now through the index, and the rerun without
  selection stays (§8, the rerun). The depth-first form, where it is taken,
  carries `discovery_complete`.

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
7. Inside the comparison operation only successes are reused across
   questions; search's top-level answers (`Answered`) keep every outcome,
   each for its fixed graph, image check, proposals and budget.

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
the root row $`(\bigcup S_l,\bigcup I_l)`$ a valid closed family (§3.9). It
is a statement about certificates; that bounded discovery finds the family
is a separate question, measured.

**Untrusted, with completeness lemmas:** `selected_complete` — a valid
closed family whose coverings are by candidates, restricted to the pairs
reachable from its root through those coverings' premises (table rows,
`Var`, `TabRen`, member instances) and their arrow evidence, stays valid;
it needs the dependency closure WORK's
[selected discovery](../../WORK.md#union-shapes-discovery) states. It is a
part of the operational theorem that deleting the rerun needs (§8). `discovery_complete` — with the
dependency representation of §3.2, a valid closed family in the reach of
today's discovery, its coverings by candidates, is found by the depth-first
form — is the condition for replacing discovery and deletion by it.

**Unchanged:** `SourceClaimJson.checkJson_safe`, its premise and its
conclusion; `FamilyValid` but for `Same`; R1–R5 and their lemmas. Generic
definitions carry `@[nospecialize]`; no `sorry`, no axioms.

**Untrusted:** the engine (interning, search order, assumptions, memo
policy, budgets), the index's construction beyond its lemma, unification
and overload order, every proposal, and search's typing order (§3.7).

**Removed:** `imagesUpTo`, `structuralImages`, `compareEquivalent`,
`equivalent`, `compareImagesUpTo`, the respelling patches,
`extendInstancePatches`, `instancePatchLimit`; with the rerun's operational
theorem, the reruns and `InstanceImageCheck.general`; with `discovery_complete`,
`growTable`, `gfp` and `coveredIn`.

## 6. Certificates and the checker's search

**Conjectured — a linear check needs explicit witnesses.** A certificate of
a question would be its table with, per row, per split source clause, the
covering target clause's position or `Same`, or for a tag set covered
element by element a covering position per element; per premise its rule with its
row, entry or instance; for `TabRen` the renaming and the renamed row it
generates; and arrow evidence with each domain split, each combination's
chosen signatures and the compatibility of each pair of their result labels
written out. Its size is charged with every term it names or generates.
With interned terms, rows in a hash set and validation memoized by evidence
entry, each obligation is checked in time proportional to the terms it
names, preprocessing and instance validation included, so the check is
linear in that size.

**The checker keeps deciding.** The checker runs the engine with the
evidence's instance choices in place of the proposal routes. The measured
check runs (§1.2) spend, of 4.1, 2.7 and 2.5 s, 1.66, 0.58 and 0.53 s in
comparisons (image equivalence 0.71, 0.08 and 0.08 of it), 0.88, 0.78 and
0.74 s in narrowing, and 1.40, 1.23 and 1.09 s reading the documents. Image
equivalence leaves with §3.1 and narrowing's pairs with §3.6; what the
remaining comparisons cost is projected, not measured, and is measured when
each step lands. Reading is the largest part measured to remain, and a
certificate adds to it; the checker's structural search is kept, with the
memo of §3.5. A slice whose check spends its time in structural search
after these steps is where certificates replace it, with the same
validator.

## 7. Expected costs

**Conjectured**, from §1.2's samples: what each part of the design removes,
and what it leaves.

| Part | Removes | Leaves |
| --- | --- | --- |
| Instantiation by inclusion (§3.1) | image equivalence | the one-direction operand comparisons |
| Clause identity, interning, the index (§3.1–§3.3) | label membership; most structural comparison of respelled or discriminated unions | comparisons of genuinely different structure |
| Narrowing by index and search's yield memo (§3.6) | `uncoveredField`'s pairs; repeated yield checks | one bucket scan per label; distinct checks |
| Typing by synthesis (§3.7) | coercions of guessed types tried before the synthesized one | exhaustive failures |
| One memo for search and its check (§3.8) | search re-checking its own comparisons | — |

The structural engine's parts in `moduleFunction`'s search, inclusive
samples, which overlap each other and include their share inside image
equivalence: discovery (`growTable`) 5.86 s, of which demand pairs
(`demandPairs`) 1.73 and renamed members (`renamedPairs`) 2.82; deletion
(`gfp`, with `coveredIn`) 2.14; validation (`checkEntries`) 1.68; the
`TabRen` scan (`premTable`) 1.77; member instances (`rowInstances`) 1.25.
Non-overlapping, after image equivalence and narrowing, the subtype
requests take 6.0 s and search's re-check 1.19. The index and clause
identity act on demand pairs, coverage and validation; the demand memo on
demand pairs and renamed members; image equivalence's removal on its share
of each. The `TabRen` scan, `rowArrows`' arrow products and
`rowInstances`' traversal are kept, and the high end below keeps them.

Per slice, CPU seconds: today the census medians of §1.2; expected from the
sampled work less what the parts remove, scaled by the census-to-sample
ratio of each slice (1.13–1.21 for these five; `collect` 1.7 and
`closeStatements` 2.0, whose search is mostly the process outside the
sampled work). With §1.2's rows, the low end keeps reading and writing,
lowering, graph checks and the rest, and a tenth of the subtype requests,
the other narrowing slices and the structural tables, and 3% of
`uncoveredField`'s time (a conjectured fraction: the measured bucket counts
are 0.3% of the pairs, but surviving `restricts` calls read nested types); the high end removes only image
equivalence and `uncoveredField`'s repeated row reads (the measured
prototype, 2.1 of 7.3 s) and keeps everything else, the subtype requests,
the other slices, the re-check and label membership included. For
`moduleFunction` that is 2.56 + 0.48 + 0.1·(6.01 + 3.32 + 0.26) + 0.03·6.40
= 4.2 s sampled (4.9 s census) and 24.7 − 3.73 − (1 − 2.1/7.3)·6.40 = 16.4 s
sampled (19.3 s census). The check intervals keep reading the documents
and the rest, remove image equivalence, and keep from a quarter (low) to a
half (high) of narrowing and of the other comparisons, scaled by each
slice's check ratio (1.22–1.36). Where a slice lands between the ends is
what the steps measure.

| Slice | Search today | Search expected | Check today | Check expected |
| --- | ---: | ---: | ---: | ---: |
| `moduleFunction` | 29.1 | 4.9–19.3 | 5.0 | 2–3 |
| `inertRead` | 21.1 | 4.4–15.8 | 3.6 | 2–2.5 |
| `resolve` | 20.4 | 4.0–15.3 | 3.4 | 2–2.5 |
| `forOfPattern` | 115.0 | 4.6–22.8 | — | — |
| `pattern` | 15.1 | 2.1–5.6 | — | — |
| `patternDefaults` | 0.8 | ≤ 0.8 | 0.4 | ≤ 0.4 |
| `collect` | 1.7 | 1.6–1.7 | 1.0 | 0.9–1.0 |
| `closeStatements` | 1.2 | 1.2 | 0.7 | 0.7 |

`collect` and `closeStatements` spend 0.8 of 1.0 s and 0.4 of 0.6 s of their
search's sampled work reading and writing documents and at most 0.2 s
comparing types: their cost is
[certificate sharing](certificate-sharing.md)'s, not this design's. The
width series is expected flat: the time at width 136 within twice the time
measured at width 5.

Outcomes are unchanged: six verified, `forOfPattern` and `pattern` refused
at their source expression obligation.

**Measured against the expectation**, 2026-10-24, after the steps
[WORK](../../WORK.md#status) lists, census medians, search CPU today →
measured: `moduleFunction` 29.1 → 6.5 s, `inertRead` 21.1 → 5.4,
`resolve` 20.4 → 4.9, `forOfPattern` 115.0 → 5.4, `pattern` 15.1 → 2.8,
`patternDefaults` 0.8 → 0.5, `collect` 1.7 → 1.6, `closeStatements` 1.2 → 1.2;
check CPU `moduleFunction` 5.0 → 2.9, `inertRead` 3.6 → 2.5, `resolve`
3.4 → 2.3. Each lies within its expected interval. The width series is
0.88 / 7.55 / 18.6 / 54.6 / 137.6 → 0.53 / 0.93 / 1.25 / 1.99 / 3.20 s. The
width criterion is on the part the design acts on: the sampled time outside
the front end (reading the fragment and the claims, lowering and freezing
them) and the evidence write, at width 136 within 12 times its time at
width 5 (the widths' ratio, 136/5, is 27), and within 1.5 times its time at
width 87 scaled by 136/87. Measured at widths 5 / 30 / 87 / 136 it is
0.10 / 0.18 / 0.54 / 0.89 s, within both bounds (1.20 and 1.27); the front
end takes 0.21 / 0.46 / 0.96 / 1.60 s, which the input's own growth sets.

## 8. Migration

Each step is a green round (`make test`, `make suite`), measured on the
eight census slices (search and check CPU, evidence bytes, outcome) and the
width series, with its commit record, and moves the owning documents in the
same commit: POSITIVE-TYPES for the relation and the engine,
RECURSIVE-EQUATIONS §4.4 and §6 for instantiation, UNION-SHAPES §7 for the
index and the rerun, PROGRAM-TYPING for narrowing, WORK's row for the
measurements. No step changes a wire shape; every change of evidence size
is reported. A step whose measurement falls short of §7's expectation is
explained before the next lands, and the design revised where the
explanation requires it.

Landed, in order: instantiation by inclusion; narrowing's candidates
unfolded once and search's slice memo; typing by synthesis; `Same` with
linear containment and renamed-member pairs once; hashed deduplication of
search's candidates; parts before the claim with bucketed `Same` lookups in
search; the keyed narrowing index; no table grown from a pair no valid
family covers; clause membership by an index under the label hash, in
search and in the validator, which reads a pair's target clauses once, as
its opaque rows do; the row-matched instance computed when the engine reaches
it, and reading no row where a target signature has no scheme signature of
its effect and arity; search's checks of its graphs and codes answering the
inclusions it established from their proofs. Each step's measurement is
WORK's row.

Remaining:

1. **Hashed kernel lookups.** Under the graph's label hash, `TabRen`'s rows
   bucketed by their source labels, label containment through a hash set
   where the orders differ, and a meet row's parts read once per premise;
   each with its equality lemma to the list form it replaces.
2. **The final check reads the memo**: `--produce-source-claims`'s check
   of the document answering the inclusions search established (§3.8).
3. **Validator and discovery read the candidate index** (§3.3), with
   `indexCandidates_eq`, `indexCandidates_mem` and `checkEntries_eq`.
4. **`Clauses`** in the premise judgment, with `clauses_subset_sound`.
5. **Checker memo.** `Subtyping.check` state-passing.
6. **Rerun.** Deleted only with an operational theorem: selected discovery,
   at today's fuel and growth, finds a valid table wherever unrestricted
   discovery does; `selected_complete` is a part of it.
7. **Coverage by assumption**, where structural comparison remains a
   measured cost after steps 1–6: the dependency representation,
   `discovery_complete`, and discovery and deletion replaced.

This draft is deleted when the last step taken lands.
