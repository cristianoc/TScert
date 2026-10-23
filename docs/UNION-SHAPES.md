# Structure-directed comparison

This document specifies a framework for comparing and refining types whose
cost follows the structure the types expose rather than the product of their
arm counts. Its organizing idea is **shape**: values of different shapes have
different runtime representations, so the arms of a union can be indexed by
the cells their members can occupy, and a comparison reads only the arms of
matching cells. Each rule of the framework is syntax-directed: the compared
clauses' own syntax excludes the target arms that cannot cover them.

The framework is a [catalogue](#3-the-catalogue) of rules, each with the
structure it needs, its soundness lemma and its fallback. A new rule is
chosen by the fallbacks that cost the most search time.

R1–R5 are the structural engine's candidate selection
([implementation](#7-the-implementation)); R6 and R7 are specified here
([WORK](../WORK.md#status) tracks them). Each claim carries its label:
**proved** (with the theorem; the lemmas of R1–R5 are in
`lean/Verification/Types/ClauseSelection.lean`), **stated** (a lemma whose
proof is not in the repository), **sketched** (an argument in this
document), **cited** (with the source's scope), or **open**.

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
family every value of its shape. The string case of both directions is
stated (`str_excluded`, `str_included`; proof not in the repository); the
other primitive shapes follow by the same case analysis on the clause
(sketched).

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
  $`\mathsf{cand}_B(a)\subseteq\mathsf{cl}_G(B)`$
  (`ClauseSelection.mem_candidates`). A wrong exclusion costs coverage, never
  soundness.
- **Completeness relative to the general rule: stated in an abstract model,
  open for the checker.** In the model a table is a set of pairs, a pair is
  covered when each source clause has a covering target clause whose
  premises are read in the table, and a covering reads only its own demand
  pairs. Under two hypotheses, that every table the full check accepts is
  sound and that each rule has its selection lemma, the two checks accept
  the same tables (`valid'_of_valid`); under two more, locality of a covering
  in its demand pairs and closure of the reachable set, a valid table
  restricted to the pairs reachable through candidates stays valid
  (`valid'_within`). Both are stated, their proofs not in the repository.
  For the checker, the first obligation is proved:
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

So a new rule needs exactly its selection lemma, and its value is how many
candidates it removes where the search spends its time.

### 2.3 Other kinds of rule

Two further kinds of structure-directed rule are not exclusions:

- a **decomposition** splits a source clause spanning several cells into
  parts covered separately ([R6](#r6-decomposition-of-a-source-spanning-cells));
- a **representation** gives a set of cells one atom, so that inclusion,
  selection and tests cost one operation on the set
  ([R7](#r7-compact-cell-sets)).

## 3. The catalogue

Each entry states its eligibility, its exclusion and its selection lemma.

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
- **Lemma 3 (stated, `refs_exclude`, `fields_exclude`, `views_exclude`;
  proof not in the repository):** let
  $`\Delta`$ be sound and the target fix $`f`$ at $`B`$ (in $`\varphi'`$, or
  in $`\psi'`$ with $`f\ne\mathtt{length}`$); if some $`n,W,v`$ has
  $`v\in⟦A⟧_n(W)`$ for every source entry $`(f{:}A)\in\Phi\,\psi`$ and
  $`v\notin⟦B⟧_n(W)`$, then

  ```math
  \Delta;S\nvdash\mathsf{Ref}(\Phi;\psi;\ldots)\sqsubseteq\mathsf{Ref}(\varphi';\psi';\ldots).
  ```

  The literal form the exclusion uses is proved (`ClauseSelection.covers_litExcl`,
  for record and dictionary clauses on both sides and every
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

A [kind set](HOST-FAMILIES.md#tag-sets) $`\mathsf{numIn}(S)`$ is a
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
slice is defined by the step's own test and is exact for it (stated,
`numSlice_sound`, `numSlice_exact`; proof not in the repository):

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

**Lemma 7 (qualified separation; stated, `separation`, proof not in the
repository).** Let $`a`$ and $`a'`$
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
  type's meaning only for the values T1 and T1′ describe
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

## 5. Evidence

What the checker **recomputes**: the structural table (subtype evidence
carries instance choices only, `SubtypeChoices`; the checker reruns table
growth, the greatest fixed point and its validation, `checkUsing`), the
candidates (a function of the compared types), and a test's slices. What the
evidence **stores**: the instance choices, and the program-typing derivation
node by node. The selection rules change only the first part; R7, making a
test one node with two slices and a kind set one atom, would change the
second.

## 6. Prior work

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

## 7. The implementation

`ClauseSelection.candidates G a B` is the target clauses of $`B`$ that R1–R5
leave for the source clause $`a`$. With `SearchBudget.select` on, the
default:

- table growth adds only the demand pairs of candidate clause pairs
  (`demandPairs`), and the greatest fixed point's coverage test reads only
  candidates (`coveredIn`);
- the table check reads the candidates first and then every target clause
  (`checkEntries`, its existential over `candidates ++ clausesOf`);
- a structural comparison or a comparison step not established with
  selection is redone with selection off (`InstanceImageCheck.general`, in
  `compareStructural` and `compareStepState`), so the restricted search
  establishes nothing less than the general one.

**Soundness (proved).** A candidate is a target clause
(`ClauseSelection.mem_candidates`), so each covering found is one of the
general rule's, and `checkEntries_sound`, `compareStructural_sound` and
`compareStepState_sound` hold with their statements unchanged, as does
`checkJson_safe`. Completeness of the restricted table search alone is the
open bridge of [§2.2](#22-what-every-rule-inherits); the rerun stands in for
it.

**Answered requests.** The producer's candidate search asks the same subtype
requests many times: for an expression it tries the claimed type and then
every type of the unit's pool, coercing each to the target; for a receiver,
an array or an index it tries first the type the part synthesizes (a
variable's slot type, a field's type read from a record), then the pool
(`synthesizedFirst`). The producer
answers a request asked again from its first answer: a table from source and
target to `subtypeSearch`'s whole result, an exhaustion included
(`CertificateProducer.Answered`), threaded through every search of a
document. The table is keyed by source and target alone because every
request of a document reads one graph and one image check, built once from
the frozen store: a checked store's graph is its equations' and its image
check reads only the equations, the variances and the budget (proved,
`Checked.graph_eq`, `Checked.images_eq`). The checker recomputes every
comparison, so the table concerns search only.

**Where the search time sits.** In `statementsOnPath`'s search (macOS
`sample`, one run, 2026-10-18), about a third of the working thread's
samples were in the scope check of labels built from trees
(`EquationGraphs.arityOk` under `Label.ofTree?`), and the structural
engine's growth and validation took 1.2 s of a 17 s search. That time is
outside union comparison, and R6 and R7 do not address it.

## Lean

In `Types/ClauseSelection.lean`: `excludes`, `candidates`, `mem_candidates`,
`any_candidates`, `covers_shape` (Lemma 1), `covers_prim` (Lemma 2),
`covers_litExcl` (Lemma 3, literal form), `covers_keyExcl` (Lemma 4),
`covers_boundExcl` (Lemma 5), `covers_candidate`. In
`Types/SelectionPreservation.lean`: `prem_sound_closed`, `valid_selected`.
In `Types/PositiveCertificates.lean`: `SearchBudget.select`,
`InstanceImageCheck.general`, `demandPairs`, `coveredIn`, `checkEntries`,
`compareStructural`, `compareStepState` and their soundness theorems,
`checkStructural_sound`, `compareUsing_sound`. Elsewhere in the library:
`semWithArgs_shape`, `meet_sound`, `sourceClause_sound`
(`Types/PositiveNormalization.lean`); `field_value`, `fieldSlice_sound`,
`tagSlice_sound` (`Programs/BranchRefinement.lean`); `family_sound`
(`Types/PairFamilies.lean`); `CertificateProducer.Answered`
(`Programs/CertificateProducer.lean`); `Checked.graph_eq`,
`Checked.images_eq` (`Source/Equations/Store.lean`).

Stated, with proofs not in the repository: `str_excluded` and
`str_included` (§1.3); `views_exclude`, `fields_exclude`, `refs_exclude`,
`refs_exclude_lit`, `refs_exclude_lits` (Lemma 3, general form);
`refs_exclude_absent` (Lemma 4, semantic form); `dict_needs_among` (Lemma 5,
semantic form); `separation` (Lemma 7); `numSlice_sound` and
`numSlice_exact` (R7); `valid_of_valid'`, `valid'_of_valid` and
`valid'_within` (§2.2, about an abstract model).
