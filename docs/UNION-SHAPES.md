# Structure-directed comparison

This document specifies a framework for comparing and refining types whose
cost follows the structure the types expose rather than the product of their
arm counts. Its organizing idea is **shape**: values of different shapes have
different runtime representations, so the arms of a union can be indexed by
the cells their members can occupy, and a comparison reads only the arms of
matching cells. Each rule of the framework is syntax-directed: the compared
clauses' own syntax excludes the target arms that cannot cover them.

The framework is a [catalogue](#3-the-catalogue) of rules, each with the
structure it needs, its soundness lemma, its fallback and its measured
coverage, and a [measurement](#5-measurement) that ranks the fallbacks by cost.
That ranking is how the next rule is found: discriminated unions by a literal
field are the first entry, and the data names the next ones
([candidates](#6-candidates-the-data-names)).

R1–R5 are implemented in the structural engine
([implementation](#9-the-implementation)); R6 and R7 are not. Each claim
carries its status: **proved** (with the theorem and where it lives),
**sketched** (an argument in this document), **cited** (with the source's
scope), **measured** (with date and commit), or **open**. The lemmas of R1–R5
are in `lean/Verification/Types/ClauseSelection.lean`; the others are proved
in a file outside the repository against the library at commit 84b326a.

The types, their meaning and the subtyping rules the framework restricts are
those of [POSITIVE-TYPES](POSITIVE-TYPES.md): a type $`A`$ is a finite union
of labels, a label's body a union of clauses, $`⟦A⟧_n(W)`$ its members at
level $`n`$ in world $`W`$, and a pair $`(A,B)`$ of a table $`\Delta`$ is
[covered](POSITIVE-TYPES.md#covered-pairs) when every split part of every
clause of $`A`$ is covered by some clause of $`B`$.

## 1. Shapes and cells

### 1.1 Outer shapes

Every closed value $`v`$ has one **outer shape** $`\sigma(v)`$: null,
boolean, plain object, function, undefined, number, string, internal element
store, bigint, symbol or class (`valueShape`). Every clause $`c`$ other than
`top` and `source` has one shape $`\sigma(c)`$ (`shape`): `refs` and `dict`
are plain objects, `arrs` and `callable` are functions, a literal shares its
family's shape. A JavaScript array is a plain object owning the store key
([the array shape](POSITIVE-TYPES.md#records)); the clause `list` describes
the internal store, and `arrs` describes call signatures. The outer shapes
partition the values: $`\sigma`$ is a function on values.

### 1.2 Cells

A **cell** refines an outer shape by a value the shape fixes:

- a primitive's cell is the value itself: a bit pattern for a number, a
  string, an integer for a bigint, an identity for a symbol, `true` or
  `false`; null and undefined are one cell each;
- a plain object's cell at a **discriminant key** $`f`$ is the cell of the
  value its field $`f`$ holds.

Primitive cells partition the primitive values. Object cells do not
partition values: the value at $`f`$ is the content of a heap location, and
the object's type constrains that location's lifetime contract, which
[Lemma 7](#41-discriminant-separation) relates to cells only one level down
and under a heap that meets the world.

### 1.3 Types as sets of possible cells

A **cell set** is $`\top`$, every cell, or a finite map from outer shapes to
either the whole shape or a finite set of that shape's cells. The cell set
of a clause is

```math
C(\mathsf{top})=C(\mathsf{source})=\top,\qquad
C(\mathsf{str})=\{\mathrm{string}\mapsto\mathrm{all}\},\qquad
C(\mathsf{strLit}\,s)=\{\mathrm{string}\mapsto\{s\}\},\qquad
C(\mathsf{numLit}\,x)=\{\mathrm{number}\mapsto\{x\}\},
```

and likewise for the other families and literals, with
$`C(\mathsf{bool})=\{\mathrm{boolean}\mapsto\{\mathsf{true},\mathsf{false}\}\}`$
and $`C(c)=\{\sigma(c)\mapsto\mathrm{all}\}`$ for a structured clause. A
type's cell set is the union over its clauses when every label is a clause
row, and $`\top`$ otherwise: a parameter, scheme or meet row has no clauses to
read ([`expand`](POSITIVE-TYPES.md#covered-pairs)), which is the **unknown
case**. Writing $`\gamma`$ for the values a cell set names,

```math
v\in⟦A⟧_n(W)\ \Longrightarrow\ v\in\gamma(C(A)),
```

and on primitive shapes the converse holds for a plain type (every label a
clause row) with no `top` or `source` clause: a literal clause holds its value at every level and world, a
family every value of its shape. The string case of both directions is proved
(`str_excluded`, `str_included`); the other primitive shapes follow by the
same case analysis on the clause (sketched).

A record clause **fixes** a key $`f`$ through an invariant field or a
readonly view at $`f`$, `length` excepted (a `length` view is also met
through the array store). An optional field does not fix $`f`$, and records
are open: a clause naming no entry at $`f`$ may own $`f`$ at any value. The
**literals** $`L(A)`$ of a type are its literal clauses' values; each is a
member of $`⟦A⟧`$ at every level and world.

## 2. The framework

### 2.1 A rule is an exclusion

A **selection rule** is a decidable test $`\mathsf{excl}(a,b)`$ on a source
clause and a target clause, read from their syntax, with a **selection
lemma**: no sound table derives $`a\sqsubseteq b`$ when $`\mathsf{excl}(a,b)`$.
A table is **sound** when each of its pairs is an inclusion,
$`\Delta(A,B)\Rightarrow⟦A⟧_n(W)\subseteq⟦B⟧_n(W)`$ for every $`n,W`$. A table
the checker accepts is sound under its entry's hypotheses: `family_sound`
discharges the entry's variable, lookup and known-arrow obligations, and
coverage reads its premises through the premise relation `Prem` (table rows,
`Var`, `Inst`, `TabRen`), not through table membership alone. The selection
lemmas below take a sound relation as a premise, so they apply to whatever
relation coverage reads once that relation is shown sound.
The rules of a catalogue combine by disjunction, and the **candidates** of a
source clause are the target clauses no rule excludes:

```math
\mathsf{cand}_B(a)=\{\,b\in\mathsf{cl}_G(B)\mid\lnot\,\mathsf{excl}_1(a,b)\land\cdots\land\lnot\,\mathsf{excl}_k(a,b)\,\}.
```

Shape-directed coverage is the covered-pair rule with candidates in place of
all target clauses, the table grown only by the demand pairs of candidate
pairs:

```math
\frac{\mathsf{SameKind}(A,B)\qquad\mathsf{Opaque}(A,B)\qquad
      \forall a\in\mathsf{split}(\mathsf{cl}_G(A)\mathbin{+\!\!+}\mathsf{mcl}_G(A,B)).\;\exists b\in\mathsf{cand}_B(a).\;
      \Delta;\kappa;A\vdash a\sqsubseteq b}
     {\Delta;\kappa\vdash(A,B)\ \mathsf{covered}_{\mathsf{shape}}}
```

### 2.2 What every rule inherits

- **Soundness: proved.** The rule's premises imply the general rule's, since
  $`\mathsf{cand}_B(a)\subseteq\mathsf{cl}_G(B)`$ (`valid_of_valid'`, in an
  abstract model of the table check; for the Lean checker it is the
  monotonicity of `List.any` over a sublist). A wrong exclusion costs
  coverage, never soundness.
- **Completeness relative to the general rule: proved conditionally in an
  abstract model, open for the checker.** In the model a table is a set of
  pairs, a pair is covered when each source clause has a covering target
  clause whose premises are read in the table, and a covering reads only its
  own demand pairs. Under two hypotheses, that every table the full check
  accepts is sound and that each rule has its selection lemma, the two checks
  accept the same tables (`valid'_of_valid`); under two more, locality of a
  covering in its demand pairs and closure of the reachable set, a valid table
  restricted to the pairs reachable through candidates stays valid
  (`valid'_within`). For the checker, the first obligation is proved:
  selection holds for the hypothesis-dependent premise relation `Prem` of a
  valid closed entry, so every covering a completed certificate chooses is
  by a candidate and the same table, read with candidates only, is a valid
  certificate (`SelectionPreservation.valid_selected`, from
  `prem_sound_closed`). Closing the gap further needs:
  - preservation of the dependencies through `TabRen`, `Inst` and `Var`, the
    opaque-row conditions and the arrow evidence;
  - proofs of the locality and reachability closure `valid'_within` assumes;
  - for budgeted search, a simulation of growth detection, insertion order
    and fuel, or a narrower guarantee: the restricted search falls back to the
    general one wherever it refuses.
- **Fallback:** a clause no rule applies to keeps every target clause as a
  candidate, which is the general rule.

So a new rule needs exactly its selection lemma, and its value is measured by
how many candidates it removes where the time is.

### 2.3 Other kinds of rule

Two further kinds of structure-directed rule are not exclusions:

- a **decomposition** splits a source clause spanning several cells into
  parts covered separately ([R6](#r6-decomposition-of-a-source-spanning-cells));
- a **representation** gives a set of cells one atom, so that inclusion,
  selection and tests cost one operation on the set
  ([R7](#r7-compact-cell-sets)).

## 3. The catalogue

Each entry states its eligibility, its exclusion, its selection lemma and
its status. The coverage columns are [measured](#5-measurement).

### R1. Outer shape

- **Eligible:** every clause pair.
- **Excludes** $`b`$ when $`b\notin\{\mathsf{top},\mathsf{source}\}`$ and
  $`\sigma(b)\ne\sigma(a)`$.
- **Lemma 1 (proved, `ClauseSelection.covers_shape`):**
  $`\Delta;S\vdash a\sqsubseteq b\Rightarrow b=\mathsf{top}\lor b=\mathsf{source}\lor\sigma(a)=\sigma(b)`$,
  for every table, by cases on the coverage rule. The meanings are disjoint
  too: for $`c\notin\{\mathsf{top},\mathsf{source}\}`$,
  $`v\in⟦c⟧_n(W)\Rightarrow\sigma(v)=\sigma(c)`$ (`semWithArgs_shape`).

### R2. Primitive cells

- **Eligible:** a primitive source clause.
- **Excludes** a primitive target that does not admit the source's cell: a
  literal not equal to the source's literal, or a literal when the source is
  the whole family.
- **Lemma 2 (proved, `ClauseSelection.covers_prim`):** the coverage rule's
  primitive cases are exactly identity, a literal under its family, and `top`
  or `source`.

### R3. Literal discriminants

- **Eligible:** a record or dictionary source with an entry at a key the
  record or dictionary target fixes at a plain type.
- **Excludes** $`b`$ when $`b`$ fixes $`f`$ at a plain $`B_f`$, the source has
  an entry at $`f`$, and every source entry $`(f{:}A)`$ has its own literal
  $`\ell_A\in L(A)`$ with $`\ell_A\notin\gamma(C(B_f))`$.
- **Lemma 3 (proved, `refs_exclude`, `fields_exclude`, `views_exclude`):** let
  $`\Delta`$ be sound and the target fix $`f`$ at $`B`$ (in $`\varphi'`$, or
  in $`\psi'`$ with $`f\ne\mathtt{length}`$); if some $`n,W,v`$ has
  $`v\in⟦A⟧_n(W)`$ for every source entry $`(f{:}A)\in\Phi\,\psi`$ and
  $`v\notin⟦B⟧_n(W)`$, then

  ```math
  \Delta;S\nvdash\mathsf{Ref}(\Phi;\psi;\ldots)\sqsubseteq\mathsf{Ref}(\varphi';\psi';\ldots).
  ```

  The literal form the exclusion uses is `ClauseSelection.covers_litExcl`
  (proved, for record and dictionary clauses on both sides and every
  singleton: string, number, boolean, bigint, symbol, null, undefined): each
  source entry at $`f`$ holds some literal that no clause of the plain type
  $`B`$ admits; whichever entry coverage selects supplies its own
  counterexample. The lemma is about the field types, so it carries no level
  or heap premise, unlike separation (Lemma 7). It is a coverage exclusion,
  not a disjointness of meanings. Callable targets reach the same field
  condition and are not selected by R3. Entries at `"x"` and `"y"` exclude a
  target fixing `"z"`, and exclude no target admitting `"x"` or `"y"`.

### R4. Required keys

- **Eligible:** a record or dictionary source and target.
- **Excludes** $`b`$ when $`b`$ fixes a key at which the source has no field
  and no view.
- **Lemma 4 (proved, `ClauseSelection.covers_keyExcl`):** a record or
  dictionary target fixing $`f`$ is covered by a record or dictionary source
  only if the source holds a field or a view at $`f`$, whatever the table.
  Callable clauses are not selected by R4. This is where a Term arm meets an array arm: an array holds no
  `kind`, and a Term arm holds no store.

### R5. The dictionary bound

- **Eligible:** a record source and a dictionary target.
- **Excludes** $`b`$ when the source has no own-key bound listing its keys
  ($`\mathsf{among}`$) without the prototype key.
- **Lemma 5 (proved, `ClauseSelection.covers_boundExcl`):** coverage of a dictionary by a
  record needs such a bound (`CoversKeys`), a necessary condition of the rule,
  not a disjointness of meanings. An array clause's bound excludes keys, so a
  dictionary covers no array clause without a further qualifying
  $`\mathsf{among}`$ bound, and `Json`'s object arm is then no candidate.

Together (proved, `ClauseSelection.covers_candidate`): under a sound
relation, every target clause covering a source clause is a candidate.

### R6. Decomposition of a source spanning cells

A source clause spanning several cells of one shape is split along them before
coverage. `split` replaces `bool` by `true` and `false`
([splitting](POSITIVE-TYPES.md#covered-pairs)); with compact cell sets it also
splits a set along the target's cells,

```math
\mathsf{split}_B(\mathsf{numIn}(S))=\{\,\mathsf{numIn}(S\cap\gamma(C(b)))\mid b\in\mathsf{cl}_G(B)\,\}\cup\{\mathsf{numIn}(S\setminus\textstyle\bigcup_b\gamma(C(b)))\},
```

empty parts dropped and a one-element part read as its literal.

- **Soundness: sketched.** The parts' meanings union to the whole, exactly,
  which is the argument that justifies splitting `bool`.
- **Completeness:** the rule adds derivations; $`\mathsf{numIn}(\{1,2\})\le 1\lor 2`$
  has none without it.
- **Scope.** The split acts on a clause's own cells, never through a record
  field: the decomposition of `{ done: boolean }` into its two Boolean arms is
  unsound in this model ([absorption](#43-absorption-laws)).

### R7. Compact cell sets

A [kind set](COMPILER-API.md#compact-kind-sets) $`\mathsf{numIn}(S)`$ is a
cell set within the number shape as one atom, and serves three purposes:

- **types:** a union of number literals is one atom, and inclusion is set
  inclusion, $`S\subseteq T\Rightarrow\mathsf{numIn}(S)\le\mathsf{numIn}(T)`$;
- **selection:** $`\gamma(C(\mathsf{numIn}(S)))=S`$, so an arm at a kind set is
  a candidate for a source literal $`k`$ exactly when $`k\in S`$;
- **tests:** a test slices the set element by element.

The string analogue $`\mathsf{strIn}(S)`$, for a finite set $`S`$ of at least
two strings, means $`v=\mathsf{str}(s)`$ with $`s\in S`$, with the same rules
and slices by string equality, which is exact: $`T_{\mathsf{strEq}(t)}(S)=S\cap\{t\}`$,
$`T_{\mathsf{truthy}}(S)=S\setminus\{\texttt{""}\}`$.

**Cells and tests use different equalities on numbers.** A number cell is a
bit pattern, so $`\mathsf{numLit}(+0)`$ and $`\mathsf{numLit}(-0)`$ are two
cells. A test is JavaScript's $`\mathrm{numberEqual}`$: a test against $`+0`$
keeps both cells on its true edge, and a NaN cell is on every false edge. The
slice is defined by the step's own test and is exact for it (proved,
`numSlice_sound`, `numSlice_exact`):

```math
x\in T_{\mathsf{numEq}(b),q}(S)\iff x\in S\land\mathrm{numberEqual}(x,b)=q .
```

Selection uses membership, refinement the test; each is exact for its
purpose.

**The node invariant's residual arms.** A unit's residual $`R_u`$ holds
`kind` at $`\mathsf{numIn}(\mathrm{members}(A)\setminus K_u)`$. Its inclusion
of a replaced shape $`S_k`$ needs $`k`$ in the set; two residuals compare by
set inclusion; a test $`e.\mathtt{kind}\equiv k`$ slices the residual's set
and drops the arm when the slice is empty. Each is one operation on one
atom, where the literal union costs one per literal.

The Lean library has a predicate named `numIn` (`PositiveRules.numIn`, "a
type holding every number") unrelated to the kind-set atom; the atom needs
another Lean name.

### Refinement

Refinement by a test keeps the arms not contradicting the observation
([`tagSlice`, `fieldSlice`](PROGRAM-TYPING.md)), one pass over the arms; an
index by cell makes a test against one literal a lookup. Soundness is proved
for both slices (`tagSlice_sound`, `fieldSlice_sound`), the field slice under
the heap premise of Lemma 7.

## 4. Lemmas outside the selection rules

### 4.1 Discriminant separation

**Lemma 7 (qualified separation; proved, `separation`).** Let $`a`$ and $`a'`$
be record clauses with entries $`f{:}K`$ and $`f{:}K'`$, each an invariant
field or a view other than `length`, such that every clause of $`K`$ answers a
test $`t`$ with $`q`$ and every clause of $`K'`$ answers it with $`\lnot q`$
([`Answers`](PROGRAM-TYPING.md)). For a heap $`h`$ satisfying $`W`$ at level
$`n+1`$,

```math
v\in⟦a⟧_{n+1}(W)\ \land\ v\in⟦a'⟧_{n+1}(W)\ \land\ h\vDash_{n+1}W\ \Longrightarrow\ \bot .
```

The value the heap holds at the field's location is in $`⟦K⟧_n`$ and in
$`⟦K'⟧_n`$ in the truncated world (`field_value`), and the test answers it
both ways. Both premises are needed (sketched from the definitions): at level
0 a view and an invariant field constrain the contract nowhere, so an object
owning $`f`$ is in both clauses; and in a world whose contract at the
location admits no value both constraints hold at every level, a world no
heap satisfies. The lemma justifies refinement, which observes a value in a
real heap; it does not make $`a\land a'`$ empty, and normalization keeps such
a meet ([incompatible contracts are kept](POSITIVE-TYPES.md#conjunction-and-normalization)).

### 4.2 Host kinds

A compiler node type is the union of the shapes $`S_k`$ of its member kinds
([the node invariant](COMPILER-API.md#the-node-invariant)), each a record whose
`kind` is a readonly view at the number literal $`k`$.

- R1–R5 apply to these arms as written: they read the declared types and
  need no host assumption.
- Lemma 7 applies to a host node only through T4, which makes a host object
  behave as the record of its stated members, and the union is the node
  type's meaning only in host-admissible worlds, which T1 defines
  ([trust](COMPILER-API.md#trust)). Refinement of a node union by its `kind`
  is sound relative to T1 and T4; neither is proved.

### 4.3 Absorption laws

Laws that hold:

- **Different shapes meet at bottom:** $`\sigma(c)\ne\sigma(d)\Rightarrow c\land d=\bot`$
  for $`c,d\notin\{\mathsf{top},\mathsf{source}\}`$. Proved (`meet_sound`).
- **The universes are units:** $`\mathsf{top}\land c=c`$, and
  $`\mathsf{source}\land c=c`$ for $`c`$ neither a store nor a pack clause.
  Proved (`meet_sound`).
- **A cell inside a wider arm is absorbed:** $`⟦c⟧\subseteq⟦d⟧\Rightarrow c\lor d\equiv d`$,
  so $`\mathsf{strLit}\,s\lor\mathsf{str}\equiv\mathsf{str}`$ and
  $`\mathsf{numLit}\,b\lor\mathsf{numIn}(S)\equiv\mathsf{numIn}(S\cup\{b\})`$.
  Immediate from the meanings (sketched).
- **A source-valued type absorbs `source` under a meet:** $`⟦\mathsf{source}\land X⟧=⟦X⟧`$
  for $`X`$ of source-valued clauses (`sourceClause_sound`). Replacing one by
  the other inside an equation store also needs a congruence proof: open.

Laws that fail:

- **Two discriminants do not meet at bottom:** $`\mathsf{Ref}\{f{:}x\}\land\mathsf{Ref}\{f{:}y\}`$
  with $`x\ne y`$ has members at level 0 (§4.1).
- **A discriminant field does not decompose.** For views,

  ```math
  ⟦\mathsf{Ref}(;\,\mathit{done}{:}\mathsf{bool})⟧\not\subseteq⟦\mathsf{Ref}(;\,\mathit{done}{:}\mathsf{true})⟧\cup⟦\mathsf{Ref}(;\,\mathit{done}{:}\mathsf{false})⟧ :
  ```

  an object whose `done` location has the contract `bool` is, at level 1, in
  the left side and in neither arm, whose views need the contract within
  `true`, respectively `false` (sketched). A field type is a lifetime
  contract of its location, and another alias may write the other Boolean.

## 5. Measurement

### 5.1 The instrumentation

A profiling mode of the verifier's structural engine, enabled by the
environment variable `TSCERT_PROFILE` (a file path), writes one JSON line per
table growth (`growTable` at the root of a comparison) and per validation
(`comparePrepared`: the greatest fixed point and the table check), in search
and in checking alike. Each line records:

- the time, and its start, so nested comparisons are subtracted from the time
  of the comparison containing them (exclusive time);
- the outer shapes and arm counts of the root source and target, with a mark
  for parameter, scheme or meet rows;
- for the table: its rows, the source clauses, and the **clause pairs**: for
  each row, its enumerated source clauses (`sourceClauses` and `meetSources`)
  times its target clauses, the pairs the general coverage test may examine;
  and the candidates among them under R1–R3, R1–R4 and R1–R5, by the class of
  each row's target (one clause, record union, union of one
  primitive shape, mixed, universe, rows);
- for each source clause keeping more than one candidate, its **fallback
  reason**: a universe target, several arms of one non-object shape, a record
  source with no literal field (by array, dictionary or record, and the
  candidates' kinds), a target arm not fixing the source's literal keys, or
  candidates sharing the source's literal.

The clause pairs are hypothetical: the coverage test stops at the first
covering clause, `demandPairs` enumerates sources differently, and validation
can regrow a table after discovering known members, so the counts are neither
predicate executions nor generated dependencies. The candidates are computed
beside the general rule, which still decides. Tested on 2026-10-18: all 1,518
pipeline cases keep their expected outcome with the mode on and off, and the
decoders' evidence is byte-identical with and without it. That is result and
evidence preservation on these inputs, not operational neutrality: the mode
adds time, which can change an outcome at the 30 s limit, and a failed write
of a line reruns the computation it timed. The timed regions omit other
comparison paths (the preliminary label-inclusion check, instance search,
the premise judgment), and a nested line's logging cost stays inside its
parent's time. The mode is a scratch patch
of `Types/PositiveCertificates.lean` with a new `Types/ComparisonProfile.lean`,
outside the repository: its writer is an `implemented_by` replacement of a
pure function inside the checker, which makes the compiled checker run code
the proofs do not describe. That is a review obligation for a trusted
component, which a measurement tool should not add; a version for the
repository would wrap the engine from outside the checker's proof scope.

Kind tests and refinement are not comparisons of the structural engine; the
evidence they produce is measured from the evidence document.

### 5.2 The dataset

Measured on 2026-10-18 at commit 84b326a with the scratch patch, wall-clock
times on a machine shared with other work, one run each. The datasets:
`termsOf` (the slice of `calculus.mts` holding `decodeTerm` and
`decodeCode`, verified by running the verifier directly, outside the
pipeline's 30 s limit), `statementsOnPath` against the 347-literal reading
([a measured slice](COMPILER-API.md#a-measured-slice)), all pipeline cases,
and every top-level function of `tools/` and `dev/` sliced into its own file
(313 and 24 slices).

| Dataset | Run | Comparisons | Grow and validate | Clause pairs | R1–R3 | R1–R4 | R1–R5 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `termsOf` search | 32.9 s | 23,790 | 25.7 s | 473,597 | 85,828 | 58,830 | 40,151 |
| `termsOf` check | 5.4 s | 1,998 | 3.5 s | 31,021 | 3,468 | 3,249 | 3,073 |
| `statementsOnPath` search | 23.6 s | 1,120 | 1.05 s | 64,982 | 689 | 684 | 684 |
| `statementsOnPath` check | 13.6 s | 96 | 0.11 s | 263 | 110 | 110 | 110 |
| pipeline cases | 1,811 runs | 156,212 | 16.0 s | 224,374 | 146,325 | 141,265 | 139,563 |
| `tools/` slices | 168 runs | 233,077 | 118.4 s | 1,696,484 | 181,523 | 142,450 | 118,521 |
| `dev/` slices | 44 runs | 224,546 | 9.2 s | 271,842 | 135,780 | 134,412 | 134,364 |

"Run" is the command's wall time in a separate run of the instrumented
verifier, and for the census the number of verifier processes. "Grow and validate" is exclusive time summed over both kinds of line;
clause pairs and candidates are counted on growth lines only, summed over
their tables' rows; every count below uses that basis.

### 5.3 What the data shows

- **The decoders' time is mostly in this engine, and the catalogue removes
  most of its clause pairs.** In `termsOf`'s search, growth and validation
  take 25.7 s of a 32.9 s run. R1–R5 leave 40,151 of 473,597 clause pairs (a
  factor 11.8), and every enumerated source clause of the recorded tables
  keeps at most one candidate; opaque premises and the work outside these
  tables are not counted. Rows whose target is a record union hold 409,883
  of the pairs and keep 27,180.
- **Each rule contributes there.** R1–R3 take the pairs to 85,828 and R4 to
  58,830. In a run with R1–R4 only, every source clause keeping more than one
  candidate was an array source against `Json`'s array and object arms (4,922
  over growth and validation lines), which R5 removes.
- **`statementsOnPath`'s timed comparisons are a small part of its run.** They
  take 1.05 s of 23.6 s of search and 0.11 s of 13.6 s of checking. Its largest
  tables compare a union of 348 number literals with one of 33 (62,946 clause
  pairs in unions of one primitive shape, 124 candidates under R2), which R7
  would make one set inclusion. Its evidence is 108 MB, of which 19.8 MB are
  482,498 `numLit` atoms; the serialized `context` fields sum to 82.5 MB (a
  field nested inside another counted in both). Contexts contain literals, so
  the two sizes overlap and savings in them do not add. The size of the
  representation is measured; that it causes the remaining run time is not.
- **The census slices follow the decoders.** Over the `tools/` slices the
  catalogue leaves 118,521 of 1,696,484 pairs (a factor 14); unions of one
  primitive shape, mostly string literals, hold 525,929 pairs and keep 4,822.
  98 source clauses keep more than one candidate: 88 whose candidates share
  their literal and 10 with a target arm not fixing their literal keys.
- **The pipeline cases are small.** They spend 16.0 s over 1,811 runs and
  their tables have little union structure (a factor 1.6). Of their 2,395
  source clauses keeping more than one candidate, 2,019 meet a target arm not
  fixing their literal keys.
- **Comparisons repeat.** Lines with the same shape signature (kind,
  result, root shapes, row and pair counts) recur within a run: `termsOf`'s
  search has 23,790 lines and 377 signatures, the repeats taking 24.8 s of its
  25.7 s; the `tools/` slices have 233,077 lines and 5,904 signatures per run.
  A signature is a proxy: different types with equal counts share one, so
  these numbers bound the repetition from above.

What the data does not show: the time the rules would save. A factor 11.8 in
candidates is no prediction of a factor 11.8 in time: the time per pair
varies, the coverage test stops at its first success, building the index
costs time, and the restricted tables would have other rows than those
measured here. The profile ranks fallback reasons by count; the time of the
comparisons containing a reason bounds what removing it could save, and is
not time spent on those pairs.

## 6. Candidates the data names

1. **Reuse of established comparisons within a run** (open, a new kind of
   rule). The signature counts suggest that much of the decoders' comparison
   time repeats comparisons, but a signature is no identity. The engine's
   cache lives within one comparison request. Reusing an established
   inclusion across requests of one run is sound wherever the result means
   the same inclusion: a structural result holds at every parameter
   assignment (`compareUsing_sound`). First the identity of a comparison must
   be measured, which needs the labels together with the graph, the
   assignment and the checker context the result was read in; transport of a
   result across a growing equation store needs its own lemma.
2. **Compact cell sets, R7** (specified). The `statementsOnPath` evidence and
   its number-literal tables are what R7 represents as one atom.
3. **Open target arms** (open). In the pipeline cases, a record source whose
   literal keys a target arm leaves open is the top fallback. A rule here
   needs a fact that the target arm cannot hold the source's literal: an
   own-key bound excluding the key, or a key the source lacks (R4 reversed
   does not hold: records are open).
4. **Shared literals** (open). Arms sharing a literal, such as overlapping
   record arms, keep several candidates; a second discriminant key, read by
   R3 as it stands, may separate them.

## 7. Evidence

What the checker **recomputes**: the structural table (subtype evidence
carries instance choices only, `SubtypeChoices`; the checker reruns table
growth, the greatest fixed point and its validation, `checkUsing`), the
candidates (a function of the compared types), and a test's slices. What the
evidence **stores**: the instance choices, and the program-typing derivation
node by node.

The measured bulk is in the second part. In `statementsOnPath`'s 108 MB,
the 7,016 `flsLit` and 7,004 `ifFalse` certificates are one per literal of a
`kind` tested against a constant ([a measured slice](COMPILER-API.md#a-measured-slice)),
and the `numLit` atoms are 19.8 MB (§5.3). The selection rules do not change
these. R7, making a test one node with two slices and a kind set one atom,
and sharing a kind set or context repeated across nodes, as a field of the
one declared evidence type under the [wire conventions](../CLAUDE.md#conventions),
are experiments: their effect on time is to be measured by phase (derivation
construction, refinement, serialization, parsing, checking, allocation),
with unique and repeated contexts and sets counted.

## 8. Prior work

- **Algorithmic subtyping and its completeness.**
  [Pierce 2002](REFERENCES.md#pierce-2002) presents algorithmic subtyping as
  syntax-directed rules proved sound and complete for a declarative system
  (chapter 16, records with width and depth subtyping), and subtyping of
  recursive types as membership in a greatest fixed point decided by a
  terminating algorithm (chapter 21). Its results concern those calculi.
  What transfers is the form of the argument: each selection lemma is an
  inversion lemma, and the agreement of §2.2 is a greatest-fixed-point
  argument of chapter 21's kind.
- **Semantic subtyping.** [Frisch, Castagna and Benzaken 2008](REFERENCES.md#frisch-castagna-and-benzaken-2008)
  and [Castagna and Frisch 2005](REFERENCES.md#castagna-and-frisch-2005)
  decide inclusion as emptiness of a difference after splitting every type
  by its constructor kind (basic, product, arrow), which partitions their
  value domain; the decision is complete for their set-theoretic model. The
  outer shapes of §1.1 play that role here. The completeness result does not
  transfer: this language has no negation, record fields are lifetime
  contracts of heap locations, and laws of their model fail in this one (the
  arrow law [already cited](REFERENCES.md#frisch-castagna-and-benzaken-2008),
  and the field decomposition of §4.3).
- **TypeScript's discriminated unions.** [TypeScript 30779](REFERENCES.md#typescript-30779),
  released in TypeScript 3.5, relates a source object type to a target union
  with discriminant properties by decomposing the source along its
  discriminants' literal types (`{ done: boolean; value: number }` against its
  `true` and `false` variants), up to 25 combinations. It is precedent for selecting target arms by
  discriminant; its decomposition through properties is the law §4.3 refutes
  in this model, where a property's type constrains every later write.
- **Tagged sums.** In [Milner et al. 1997](REFERENCES.md#milner-et-al-1997)
  a datatype's constructors are generative, so the values of different
  constructors are disjoint by construction, and case analysis selects a
  branch by the constructor. [Maranget 2008](REFERENCES.md#maranget-2008)
  compiles such matches to decision trees that test a value's constructor
  once per node. [Garrigue 1998](REFERENCES.md#garrigue-1998) gives polymorphic
  variants a structural subtyping that is tag-directed: a source tag is
  compared with the one target tag of its name, and tags are disjoint by
  construction. R3 is that rule's selection with the tag replaced by a
  record discriminant. What R3 proves is a coverage exclusion, from the field
  types; disjointness of the arms' meanings holds only as Lemma 7 states it,
  at a successor level under a heap satisfying the world.

## 9. The implementation

`ClauseSelection.candidates G a B` is the target clauses of $`B`$ that R1–R5
leave for the source clause $`a`$. With `SearchBudget.select` on, the
default:

- table growth adds only the demand pairs of candidate clause pairs
  (`demandPairs`), and the greatest fixed point's coverage test reads only
  candidates (`coveredIn`);
- the table check reads the candidates first and then every target clause
  (`checkEntries`, its existential over `candidates ++ clausesOf`);
- a structural comparison or a comparison step not established with
  selection is redone with selection off (`compareStructural`,
  `compareStepState`), so the restricted search establishes nothing less than
  the general one.

**Soundness (proved).** A candidate is a target clause
(`ClauseSelection.mem_candidates`), so each covering found is one of the
general rule's, and `checkEntries_sound`, `compareStructural_sound` and
`compareStepState_sound` hold with their statements unchanged, as does
`checkJson_safe`. Completeness of the restricted table search alone stays
the open bridge of §2.2; the rerun stands in for it.

### 9.1 Measured

On 2026-10-18 at the merge of main 71fe5e6, before (the merge alone) and
after (with the selection), user time, median of 3 runs of the verifier on
the same artifacts, on a machine other work was loading (load averages 4 to
30 during the runs; wall time exceeded user time by up to 2.3 times in the
earlier runs of the day). `termsOf`, `decodeTerm` and `decodeCode` are
three slices of `calculus.mts` holding the same functions, and measure the
same.

| Unit | Search before | Search after | Check before | Check after |
| --- | --- | --- | --- | --- |
| `termsOf` | 30.2 s | 23.5 s | 5.0 s | 3.2 s |
| `printGraph` | 48.6 s | 38.0 s | 9.7 s | 6.8 s |
| `pageBody` | 12.7 s | 13.8 s | 4.9 s | 4.8 s |
| `card` | 10.2 s | 11.1 s | 4.0 s | 4.1 s |
| `statementsOnPath` | 16.0 s | 16.9 s | 11.7 s | 11.8 s |

The engine's own counts, from one profiled run of each (the scratch profile
of §5.1, growth lines only; "restricted" counts the comparisons with
selection on, "reruns" those redone with it off):

| Unit, search | Demand pairs before | restricted | reruns | Clause pairs before | restricted | Engine time before | restricted | reruns |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `termsOf` | 470,306 | 41,560 | 215,809 | 473,597 | 13,204 | 26.1 s | 9.3 s | 9.8 s |
| `printGraph` | 872,480 | 92,331 | 461,345 | 854,027 | 24,573 | 37.6 s | 16.5 s | 13.6 s |
| `pageBody` | 62,218 | 61,874 | 16,860 | 49,650 | 29,340 | 1.6 s | 1.8 s | 0.5 s |
| `card` | 36,879 | 36,707 | 13,613 | 36,897 | 19,687 | 1.1 s | 1.1 s | 0.4 s |
| `statementsOnPath` | 82,999 | 20,361 | 62,951 | 64,982 | 684 | 1.06 s | 1.23 s | 0.80 s |

- **Where selection works,** the restricted engine generates an eleventh of
  the demand pairs and reads a thirty-sixth of the clause pairs on
  `termsOf`, and its time falls from 26.1 s to 9.3 s.
- **The reruns cost as much as they save elsewhere, and rescue nothing
  measured.** On `termsOf`, 9,143 of the 11,895 comparisons are not
  established, as many as the general engine leaves unestablished,
  and each is redone in full: 9.8 s, none established. Over the seven units,
  no rerun establishes its comparison.
- **The index's cost.** Computing every source clause's candidates once over
  each grown table takes 0.57 s on `termsOf`'s search and 0.55 s on
  `statementsOnPath`'s, where it exceeds what selection saves; the engine
  recomputes candidates in each round of the greatest fixed point, so its
  cost is a multiple of that pass.
- **Evidence** is byte-identical before and after on all five units: the
  restricted engine chooses the same derivations there.
- **The suite and the census.** `make suite` passes before and after (63 s
  and 73 s of wall time, the second under a load average of 82). The `tools/`
  census at the 60 s limit verifies 79 slices before and 83 after, its 4
  search timeouts gone (176 s and 153 s of wall time); the `dev/` census
  verifies 23 of 24 both times (65 s and 52 s).

### 9.2 Measured since

At 496dd97 (main with candidate selection), user time, median of 3, load
averages 3 to 5:

- **Candidates prepared once per table** for every round of the greatest
  fixed point (a scratch patch, not committed): `termsOf` search 26.3 s →
  26.0 s, `printGraph` 41.7 s → 41.6 s, `pageBody` 13.9 s → 15.4 s, `card`
  12.4 s → 12.2 s, `statementsOnPath` 18.9 s → 17.3 s; `printGraph`'s check
  7.6 s → 6.8 s, the other checks within 0.15 s. No consistent gain.
- **Where `statementsOnPath`'s search goes** (macOS `sample`, 1 ms interval,
  one run): of about 17,400 samples on the working thread, 5,866 are in
  `EquationGraphs.arityOk` under `Label.ofTree?`, the scope check of a label
  built from a tree, which looks a header up in the signature, a list, by
  index. The structural engine's growth and validation were 1.23 s of the
  run (§9.1). The cost is outside union comparison; R6 and R7 address
  neither.
- **The scope check over the signature as an array** (`Tree.scopedIn`,
  `Equations.headers`), against the build without it, the same session, load
  averages 2 to 6: `statementsOnPath` search 16.8 s → 10.9 s and check
  12.3 s → 5.8 s; `printGraph` 38.0 s → 37.2 s and 6.8 s → 6.3 s; `pageBody`
  13.8 s → 13.4 s and 4.8 s → 4.5 s; `card` 11.1 s → 10.8 s and 4.1 s → 3.8 s;
  `termsOf` 23.5 s → 24.0 s and 3.3 s → 3.2 s. Evidence byte-identical on
  all of them.

### 9.3 Where the search time goes

Measured on 2026-10-18 at a071881, user time; step times are medians of 3
runs, profiles one run each with the scratch profile (§5.1), whose request
lines record each subtype request's identity: the graph it is asked in (its
address in the process), and the hashes of its source and target.

**Time by step.** The parser, the lowering and the producer take under a
second of each unit; the time is search and check:

| Unit | Search | Check | Lowering + producer |
| --- | --- | --- | --- |
| `termsOf` | 23.9 s | 3.2 s | 0.1 s |
| `printGraph` | 38.8 s | 6.6 s | 0.02 s |
| `pageBody` | 13.5 s | 4.5 s | 0.3 s |
| `card` | 11.1 s | 4.1 s | 0.3 s |
| `statementsOnPath` | 11.2 s | 6.3 s | 0.1 s |
| ten verified slices of `regexp.mts` and `regexp-shape.mts` | 29.8 s together | 20.3 s together | 0.1 s |

**Reruns.** Every rerun follows a restricted attempt that completed without
establishing its comparison, none stopped by growth or the budget, and no
rerun establishes its comparison: `termsOf` 9,143 reruns (12.1 s), `printGraph`
41,383 (18.4 s), `pageBody` 9,970 (1.6 s), `card` 6,518 (1.3 s),
`statementsOnPath` 430 (0.9 s). From 89% (`card`) to 99% of them read
tables with ordinary premises only (no meet source, no renamed scheme pair, no instance member);
the rest have rows whose target holds call signatures. Instance members and
renamed pairs occur in none.

**Repeated requests.** Within one search, most subtype requests are asked
again with the same graph, source and target, and every repeated identity
gave the same answer each time it was asked:

| Unit, search | Outermost requests | Distinct | Time | Time in repeats | Repeats refused | Their time |
| --- | --- | --- | --- | --- | --- | --- |
| `termsOf` | 107,721 | 3,926 | 24.9 s | 14.7 s | 6,015 | 11.9 s |
| `printGraph` | 230,522 | 12,129 | 41.7 s | 22.8 s | 31,973 | 19.8 s |
| `pageBody` | 336,373 | 8,325 | 6.7 s | 3.4 s | 6,407 | 2.4 s |
| `card` | 283,936 | 4,885 | 4.7 s | 2.8 s | 4,889 | 2.1 s |
| `statementsOnPath` | 15,113 | 366 | 2.9 s | 1.6 s | 262 | 1.3 s |

The reruns sit mostly inside repeated requests: on `termsOf`, 6,017 reruns
(10.8 s) are inside repeats and 2,700 (1.3 s) inside first requests. In the
checker the requests do not repeat (`termsOf`: 220 requests, 219 distinct).

**What this says.** Removing the reruns (the dependency representation of
§9.6, step 2) would remove at most their 12.1 s on `termsOf` and 18.4 s on
`printGraph`. Answering a request already answered in the same graph would
remove the repeats, 14.7 s and 22.8 s, which include most of the reruns'
time: the same refused comparisons are asked again, and each time they run
restricted and then in full. Reuse within one graph needs no transport
across store growth; across the graph's growth (316 graph addresses in
`termsOf`'s search) it does. That a refused answer stays refused is a
fact about the search, not about the types, so reusing refusals concerns
coverage only: an accepted result is still checked.

**The `FieldTerm` experiment.** Naming the record of an object type term's
field as an interface (`interface FieldTerm { name: PropertyKey; optional:
boolean; readonly: boolean; type: TypeTerm; span: Span }`, in a copy of
`tools/`) makes `execResult`'s pipeline run take 311 s of wall time (201 s of
user time) and end in the source step, a tool failure of the compiler's API
(`RemoteNode.forEachChild` from `declaration-graph.mts`), where it otherwise
verifies in 2.7 s. A CPU profile of that run puts 305 of its 308 s under
`computed-types.mts` (`computedType`, `indexedAccess`, `aliasApplication`,
`distributed`), 165 s of it waiting on the compiler API's channel (`read`).
The time is in the front end's evaluation of computed types, before any
search: none of recursive structural comparison, union expansion, repeated
requests or reruns.

### 9.4 Reuse of answered requests

**Why requests repeat.** The producer's candidate search asks them: for an
expression, `expressionWithUsing` tries the claimed type and then every type
of the unit's pool (`List.findCheck?` over `A :: pool`), coercing each
candidate to the target, so each expression asks the same pairs again. A
sample of `termsOf`'s search puts 12,959 of its samples under those
candidate searches and 4,210 under the producer's checks of the trees it
builds (`checkTreeResult` from `HeapExpressionRules.checkedOutput`). The
order already tries the claimed type first; the repetition is the pool's, so
the answer is reused rather than the order changed.

**Across graph states.** The graph changes rarely within a search (296 times
in `termsOf`'s 107,721 outermost requests, 693 in `printGraph`'s 230,522), and
a request almost always comes in the graph of the request before it. Besides
the repeats within a state (`termsOf` 103,795, 13.5 s of profiled time;
`printGraph` 218,393, 21.0 s), 1,416 requests of `termsOf` (6.4 s) and 4,882 of
`printGraph` (11.5 s) are first in their state but were asked in an earlier
one: what reuse across states, with a transport of answers, would add.

**The reuse.** The compiled producer answers a request asked again in the
same search context from its first answer (`CertificateProducer.subtypeReused`,
the implementation of `subtypeUsing`, whose meaning is `subtypeSearch`). The
context is the graph, the image check and the label type's three class
dictionaries, `Instantiates` (which proposes instance candidates), `Hashable`
and `DecidableEq`, compared by address and kept alive by the store; the
source and target are compared by equality. `subtypeSearch` is a function of
exactly these, so a stored answer is the one recomputation gives. The store
is process-global and type-erased, read back only in the context it was
written in. It is unsafe code because a pure store would have to be threaded
through every caller of `subtypeUsing`, the producer's whole expression
search; the producer is untrusted, its results are checked, and the CLI's
check mode never reaches it: `checkJson` runs the reference search, and the
check mode sets a flag (`CertificateProducer.checkingRef`) on which reaching
the reuse ends the process with a fault, which no pipeline case triggers
(`make suite`, 2026-10-19). Check mode constructs lowering recipes; only
evidence production renders them (`DirectProof.renderWith`), which reaches
the reuse. Of
`termsOf`'s requests through it, 101,503 are answered from the store and
3,497 searched (32 changes of state); `pageBody` 323,824 and 6,176;
`statementsOnPath` 14,689 and 311.

Measured at 09ddb9b (the context then without its dictionaries) against
8780e6e on 2026-10-19, user time, median of 3, on
a machine other work loaded (load averages 3 to 25); evidence byte-identical
on all seven units:

| Unit | Search before | Search after | Check before | Check after |
| --- | --- | --- | --- | --- |
| `termsOf` | 25.2 s | 13.7 s | 3.5 s | 3.3 s |
| `decodeTerm` | 23.0 s | 13.9 s | 3.1 s | 3.6 s |
| `decodeCode` | 23.7 s | 14.1 s | 3.2 s | 3.7 s |
| `printGraph` | 36.9 s | 31.6 s | 6.2 s | 6.5 s |
| `pageBody` | 14.4 s | 14.4 s | 4.9 s | 5.0 s |
| `card` | 11.5 s | 11.8 s | 4.4 s | 4.3 s |
| `statementsOnPath` | 11.7 s | 12.9 s | 6.4 s | 6.2 s |

With the dictionaries in the context, at the following commit, the seven
units measure within the noise of the after column (`termsOf` 14.8 s,
`printGraph` 30.4 s, `statementsOnPath` 12.3 s of search), evidence again
byte-identical.

Where the repeats were cheap (`pageBody`, `card`, `statementsOnPath`) the
reuse saves nothing measurable; the profile's per-request lines had inflated
their share. The seven searches run at once take 47.8 s and 38.8 s of wall
time before, 35.2 s and 43.2 s after (two rounds each, load 9 to 16):
`printGraph` sets that time, and the rounds do not separate.

**The step limit.** At a 30 s step limit, under the census's parallel load
(load averages 28 to 33, other work running), 12 of the slices that verify at
60 s time out in search: `termsOf`, `decodeTerm`, `decodeCode`, `showTerm`, `showCode`,
`decodeTarget`, `untypedAmbientField`, four of `regexp.mts` (`members`,
`nativeRegExp`, `structuralRegExp`, `libraryRegExpTerm`), and `printGraph`.
The limit stays 60 s. That run is a stress measurement; a decision on the
limit needs per-step wall and CPU time at the suite's own concurrency on an
otherwise idle machine.

### 9.5 Reuse across graph objects: a design

**What a "graph state" is.** Evidence search runs after the equations are
frozen: `freezePlans` turns the lowering's growing store into one `Frozen`
value, and every request it yields has the frozen store as its types
(`SourceRequest.over`: `types := F.store`). That store's graph reads only
the equations, `graph _ := E.graph`, the row map of their signature, bodies,
built-ins and domain; its image check reads the equations, the store's
variances and its budget (`images c := eitherImages (finiteInstanceImages
E.graph) (imagesUpTo E c.variances c.heads.subtypeBudget)`). Each call of
`RequestJson.graph` and `StoreView.images` builds these objects afresh.
Logging the equations behind each graph built (a scratch patch, 2026-10-19,
at b484bee): `termsOf`'s search builds 358 graphs, 333 distinct objects, from
one equation set; `pageBody`'s 852 (573 objects) from one; `printGraph`'s 664
(564 objects) from three, its own and those its certified imports bring. The
"graph states" of §9.4 are rebuilt objects of one frozen equation set, not a
graph that grows: no head, row or hypothesis is added between them.

**The transport lemma.** For stores `c` and `c'` of one frozen equation set
`E`,

```math
\mathrm{graph}(c)=\mathrm{graph}(c')=E.\mathrm{graph},\qquad
c.\mathrm{variances}=c'.\mathrm{variances}\land c.\mathrm{budget}=c'.\mathrm{budget}
\Rightarrow \mathrm{images}(c)=\mathrm{images}(c'),
```

both by the definitions (proved: `Checked.graph_eq`, by `rfl`, and
`Checked.images_eq`, a congruence). `subtypeSearch` is a function of the graph, the image
check, the three dictionaries, the source and the target, so its answer in
one object is its answer in the other: its whole result transports, an
exhaustion included, and no monotonicity question arises, since nothing
grows. The
document's requests share one store (`types := F.store`), so the condition
holds between all of them.

**The key.** An answer depends on the equation set (its signature, bodies,
built-ins and domain), the store's variances and budget, the dictionaries, the
source and the target; never on the store's head table, which the frozen
graph does not read. Answers do not transport between different equation
sets: `printGraph`'s three are separate, a domain change (`withDomain`, which
builds `{ E with domain := D }`) makes another, and so would a store whose
variances or budget differ.

**How the producer carries answers.** The graph and the image check are
computed once for the document, from the frozen equations and store, and
passed to every producer step of every request (`ExpressionClaims.produceUsing`,
`renderKnownUsing`, `produceResponse` and what they call), in place of the
per-call `RequestJson.graph r.toRequest` and `StoreView.images r.types`. The
objects are then the same throughout the document, and the reuse keyed by
their addresses (§9.4) answers across what are now separate objects. The
change is in the producer's plumbing, pure, with no new unsafe code; the
checker keeps calling `RequestJson.graph` as it does, and acceptance is
unchanged. A request with a qualified body keeps its own graph and image
check, over which its body checker is stated.

Implemented (`produceDocument`, `produceResponseUsing`, `produceGraphUsing`):
the graph and image-check objects are one per document. The reuse's hits
barely move (`termsOf`: 102,468 answered from the store, 3,532 searched,
34 changes of context, against 101,503, 3,497 and 32 before): every change
of context is now a change of a class dictionary's address: the label type's
`DecidableEq` in all 34, `Instantiates` in 25, `Hashable` in 13 (2026-10-19). The dictionaries are rebuilt where they are resolved, so the
address-keyed store still forgets at each rebuild; the safe memo, whose
dictionaries are fixed by the function that holds it, does not.

**Expected gain.** Of the requests first asked in their graph object, those
asked before in another object of the document: `termsOf` 1,416 (6.4 s of
profiled search time), `printGraph` 4,882 (11.5 s), §9.4. These are upper
bounds: in `printGraph` some come from its other equation sets, and the
profile's per-request cost inflates cheap requests (these average 4.5 ms and
2.4 ms, so the inflation is small).

**The safe memo: first, together or after.** The producer already threads a
pure store of answered requests through one request's rendered plans
(`DirectProof.SubtypeCache` in `ExpressionClaims.produceUsing`). The unsafe
reuse of §9.4 could be replaced by that store threaded through
`expressionWithUsing` and every caller of `subtypeUsing`, the producer's whole
expression search, made state-passing. Hoisting the graph and the image check
comes first: it is small, independent of how answers are stored, and
measurable on its own with the reuse as it is. The safe memo comes after, in
its own commit: once one document shares one graph, its scope is the document
and its key needs no addresses, so it can replace the unsafe store with the
gains measured equal.

### 9.6 Next steps

The steps are for the owner to choose. In order:

1. **One graph and image check per document**, then the safe memo (§9.5):
   up to 6.4 s of `termsOf`'s and 11.5 s of `printGraph`'s profiled search
   time.
2. **Discovery of the selected certificate.** `valid_selected` keeps a
   completed certificate valid under selection. That the selected search
   finds it needs, beyond it: the certificate restricted to the root and the
   dependencies of its coverings, with every premise and every piece of
   evidence kept; and a selected discovery whose universe contains that
   restriction, with pruning monotone on it. The engine does not represent
   those dependencies: `demandPairs` enumerates `clausesOf` where coverage
   reads `sourceClauses ++ meetSources`; `TabRen` discharges a premise
   through another row; `rowArrows` derives arrow evidence from every row,
   and `compareStepStateCore` reads instance members from every row of the
   table; growth detection (`grows`) depends on the rows already inserted.
   The design change this needs is one dependency representation that
   discovery produces and coverage, arrow evidence and member discovery
   read: each covering naming the pairs and the evidence it uses. That
   changes the engine's interface, and waits for the owner.
3. **The rerun.** Removed exactly where the preservation theorem applies,
   once it covers discovery; kept elsewhere.
4. **R7, R6 and evidence sharing for `statementsOnPath`**, ranked by what
   remains of its run after the scope check.

## Lean

In the library (`Types/ClauseSelection.lean`): `excludes`, `candidates`,
`mem_candidates`, `any_candidates`, `covers_shape` (Lemma 1), `covers_prim`
(Lemma 2), `covers_litExcl` (Lemma 3), `covers_keyExcl` (Lemma 4),
`covers_boundExcl` (Lemma 5), `covers_candidate`; in
`Types/SelectionPreservation.lean`: `prem_sound_closed`, `valid_selected`; in
`Types/PositiveCertificates.lean`: `SearchBudget.select`,
`InstanceImageCheck.general`, `compareStructural`, `compareStepState`.

Proved outside the repository against the library at commit 84b326a, each
depending on no axiom beyond `propext`, `Classical.choice` and `Quot.sound`:
`covers_shape` (Lemma 1), `str_excluded` and `str_included` (§1.3),
`views_exclude`, `fields_exclude`, `refs_exclude`, `refs_exclude_lit`,
`refs_exclude_lits` (Lemma 3), `refs_exclude_absent` (Lemma 4), `dict_needs_among` (Lemma 5),
`separation` (Lemma 7), `numSlice_sound` and `numSlice_exact` (R7), and
`valid_of_valid'`, `valid'_of_valid` and `valid'_within` (§2.2, conditional
lemmas about an abstract model). The library's own: `semWithArgs_shape`, `meet_sound`,
`sourceClause_sound`, `field_value`, `fieldSlice_sound`, `tagSlice_sound`,
`checkStructural_sound`, `family_sound`, `compareUsing_sound`.
