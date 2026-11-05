# Draft: canonical heap knowledge

A design written against TScert main at b59096f; its progress is
[WORK.md's](../../WORK.md#status). It designs the representation of places V, K, L and S of
[canonical representations](canonicity.md#31-lean-heap-knowledge), which
states their requirements, the contract their normalizers prove
([§5.1](canonicity.md#51-proved-lean-v-k-l-s-t-e-b-o-i-x)) and the bounds
they state ([§4](canonicity.md#4-resource-bounds)).

**Evidence labels.** **Measured** gives the command, the commit and the date.
**Cited** names inspected code. **Proved** names a Lean theorem.
**Conjectured** marks a design claim, a proof obligation or an estimate.

## 1. Scope and structure

Heap knowledge is built by the search (`CertificateProducer.lean`), written
into the evidence (`EvidenceWire.lean`), read back and checked edge by edge
(`HeapKnowledge.check`, `ControlFlow.lean`). All of it is Lean: the design
changes Lean's types and operations and the evidence's knowledge entries
(**cited**).

The design has three parts, in the terms of
[§1.1](canonicity.md#11-what-a-place-fixes):

- **Raw knowledge** $`R`$ is today's `Knowledge`: lists of facts, links and
  separation facts, with one change, a fact's contents is a value set
  (§2) where it is a list of atoms. Every operation of today keeps its
  definition and its soundness theorem on raw knowledge: observation,
  copy, shift, projection, dropping the result, writes, allocation, stable
  preservation, the conjunction with requirements and the merge.
- **Stored knowledge** $`S_\Gamma`$ is the normal form at the point's
  context $`\Gamma`$ (§6): one value fact per alias class, one cell fact
  per class and field without a read link, one link per class and field,
  separation by classes.
- **Two functions** connect them: $`\mathsf{norm}_\Gamma : R \to R`$, whose
  results are stored knowledge, and
  $`\mathsf{expand}_\Gamma : S_\Gamma \to R`$, which restates every fact the
  normal form omits (§6.2). An operation on stored knowledge is
  $`\mathsf{norm}_{\Gamma'} \circ \mathit{op} \circ \mathsf{expand}_\Gamma`$,
  and every reader of facts reads $`\mathsf{expand}_\Gamma`$: one query
  interface and one transport between contexts, whatever the operation.

## 2. V: value sets

### 2.1 The representation

A value set has one component per kind of value the calculus has (`isVal`:
null, undefined, Booleans, numbers, strings, bigints, symbols, objects,
element stores):

```math
V \;=\; \langle\, \mathit{nul}, \mathit{undef}, \mathit{sym}, \mathit{arr} : \mathsf{Bool};\ \
\mathit{bool} \subseteq \{\mathsf{true}, \mathsf{false}\};\ \
\mathit{num} : \mathsf{Lit}(\mathsf{Bits});\ \ \mathit{str} : \mathsf{Lit}(\mathsf{String});\ \
\mathit{big} : \mathsf{Lit}(\mathbb{Z});\ \ \mathit{obj} : \mathsf{Obj} \,\rangle
```

- $`\mathsf{Lit}(X)`$ is *these* $`F`$ or *all but* $`F`$, with $`F`$ a
  finite subset of $`X`$, stored sorted and without duplicates.
- $`\mathsf{Bits}`$ are the 64-bit patterns of numbers: a number is a
  member when its pattern is. $`+0`$ and $`-0`$ are two members, as are
  two NaN patterns, so a literal atom translates exactly.
- $`\mathsf{Obj}`$ is *none*, or a conjunction of clauses, each a
  disjunction of tag literals $`(t, q)`$ over the tags whose answer on an
  object depends on the object: `isRef`, `isFun`, `isArray`,
  `typeofObject` and `hasKey k`. *All* is the empty conjunction.

**Meaning.** $`v \in ⟦V⟧`$ when $`v`$ is a value and the component of its
kind admits it. A literal component admits the literals of $`F`$ (*these*)
or those outside it (*all but*). A clause admits an object when one of its
literals does, and a literal $`(t, q)`$ admits $`v`$ when
$`\mathsf{tagHolds}\ t\ v = q`$ or $`\mathsf{protoFree}\ t\ v =
\mathsf{false}`$, the meaning of today's tag atom (`Atom.holds`): both
answers of `hasKey k` admit an object that lacks its own `k` and reads a
prototype.

**Tags on primitives.** On a primitive, a tag's answer is a value set
(`ValueSets.ofTag`): a kind test is constant on the kind; `strEq`,
`boolEq` and `bigintEq` select one literal, and `truthy` answers `false` on
`""` among strings and `0` among bigints, exactly. Among numbers, `numEq b`
answering `true` with $`b`$ neither a zero nor NaN selects $`b`$; the other
number answers (an equality with a zero or NaN, a failed equality, and
`truthy`, which reads every NaN pattern) keep every number, as
`observeAtom` does today. Making them exact needs lemmas on bit patterns
that core Lean proves only through `bv_decide`, whose axiom the axiom check
refuses. Tag literals remain only on objects.

### 2.2 Translation of today's atoms

`ValueSet.ofAtoms : List Atom → V` is the union of each atom's set: `nul`,
`undef`, `tru`, `fls` their flag or Boolean; `num` every number; `numLit b`
*these* $`\{b\}`$ in the part of $`b`$; `str` and `strLit s` likewise;
`defined`, `nonNull`, `nonNullish` every kind but the excluded ones; `tag t
q` its answer's set on each primitive kind and, on objects, the unit clause
$`(t, q)`$, or *all* or *none* where the answer on objects is constant.

Theorems `ofAtoms_holds` and `holds_ofAtoms`:
$`(\exists a \in A,\ a.\mathsf{holds}\ v) \implies v \in ⟦\mathsf{ofAtoms}\ A⟧`$,
and the converse where no atom of $`A`$ is a tag answer, the atoms `atoms`
reads from types, so `atoms_sem` and the reads that use its
reverse direction (`includes_sound`) carry over. The search keeps producing
atoms where that is simplest (`observeAtom`, `atoms`); their lists enter
knowledge only through `ofAtoms`.

### 2.3 Operations

- **Meet**, component by component: flags by `and`, Booleans by
  intersection, literal components by the four cases, objects by
  concatenating clauses. Exact.
- **Join**: flags by `or`, literal components dually, objects by the clauses
  $`c \cup c'`$ for every clause $`c`$ of one and $`c'`$ of the other. Exact,
  and the clause count multiplies.
- **Widening** $`\nabla_8`$, used only where the search merges states
  (§8): the join, then, where the object component has more than 8 clauses,
  the 8 smallest by size and then order. It weakens the join, which a merge
  may do: each edge into the merge is still checked.
- **Inclusion** $`V \le V'`$: componentwise; literal components exactly;
  objects when every clause of $`V'`$ contains a clause of $`V`$. Sound;
  complete on primitives; incomplete on objects (a clause implied only by
  resolution is not seen).
- **Restriction** to a context $`C`$ (§2.4): the meet with $`C`$.

### 2.4 Contexts

A value set is read at a **context**: a value set $`C`$ its slot's type
denotes, $`\mathsf{ofAtoms}\ (\mathsf{atoms}\ G\ A)`$ where `atoms` is
defined (a type of finitely many primitive predicates), and every value
otherwise. Its **contextual meaning** is $`⟦V⟧ \cap ⟦C⟧`$; the premise that
makes $`C`$ hold of the slot is `EnvOk G Γ ρ n W`, as for `withTypedLinks`
today (§6.1).

### 2.5 Laws, normal form and the four obligations

Laws, each a rewrite preserving the contextual meaning:

1. sort and deduplicate each literal set, clause and conjunction;
2. remove a clause containing $`(t, \mathsf{true})`$ and
   $`(t, \mathsf{false})`$, for every tag ($`\mathsf{tagHolds}`$ answers one
   of the two, whatever the prototype);
3. remove a clause containing another clause (absorption);
4. an empty clause makes the object component *none*;
5. unit clauses $`(t, \mathsf{true})`$ and $`(t, \mathsf{false})`$ make it
   *none* for a tag reading no prototype (every object tag but `hasKey`);
6. two encodings of one literal component under one context are related
   when they denote the same contextual set: the Boolean component's
   *these* $`\{\mathsf{true}\}`$ and *all but* $`\{\mathsf{false}\}`$;
   *these* $`P`$ and *all but* $`F_C \setminus P`$ under a context
   component *these* $`F_C`$;
7. a component and its restriction to the context's component are related.

**The normalizer** computes, per component, the **contextual set**: the
component restricted to the context (law 7), an intermediate value never
stored. It then **encodes** that set as a function of the set alone:

- *none* where it is empty, *all* where it equals the context's component;
- under a context component *these* $`F_C`$: *these* $`P`$ or *all but*
  $`F_C \setminus P`$, the one with fewer literals, *these* on a tie;
- otherwise the set is finite or cofinite, and its encoding is that one:
  the literals, or the excluded literals the context does not exclude.

On objects it applies laws 1–5: sorted, the tautological and absorbed
clauses removed, and *none* where a clause is empty or two unit clauses of
a tag reading no prototype disagree.

**Stored** is the normalizer's fixed point: $`\mathsf{norm}_C\ V = V`$.

**The invariant** $`\mathsf{inv}_C(V)`$ is read from the contextual set
$`V \sqcap C`$, component by component: on each primitive component, that
set; on objects, *none* where the restricted object component is *none*
(the context admits no object), has an empty clause, or has among its
⊆-minimal non-tautological clauses two disagreeing unit clauses of a tag
reading no prototype, and otherwise that set of minimal non-tautological
clauses.

The four obligations of
[§5.1](canonicity.md#51-proved-lean-v-k-l-s-t-e-b-o-i-x):

- **laws:** each law preserves the contextual meaning;
- **normalize:** $`\mathsf{norm}_C\ V`$ and $`V`$ are related by the laws
  (the normalizer's steps are laws 1–7);
- **stored:** $`\mathsf{norm}_C`$ is idempotent: the encoding of a
  contextual set restricts to itself;
- **unique:** each law preserves $`\mathsf{inv}_C`$ (laws 2 and 3 keep the
  minimal non-tautological clauses; law 5 maps to *none* exactly where the
  invariant is *none*; laws 6 and 7 keep the contextual set), and a stored
  value set is the encoding of its invariant, so two stored value sets
  related by the laws are equal.

On strings and bigints, infinite universes, the equivalence is equality of
contextual meaning. On numbers, a finite universe, it is that equality
under a finite context; otherwise *these* $`F`$ and *all but*
$`\mathsf{Bits} \setminus F`$ stay distinct, which no operation forms
($`2^{63}`$ literals). On objects, two conjunctions equivalent
only by resolution stay distinct, which
[the property](canonicity.md#11-what-a-place-fixes) allows.

## 3. L: links

**Representation.** A partition of the slots that hold one value, each
class named by its least slot; the read links, at most one per receiver
class and field, each naming its destination class and whether the read
may find no field.

**Laws.**

1. alias links generate the partition: orientation, order, duplicates, an
   alias implied by others, and the `field` and `optional` of an alias
   link, which its meaning ignores;
2. a read link stated on several slots of one class is one link;
3. **two reads of one field from one object give one value**: read links
   $`(c, f, p, u)`$ and $`(c', f, p', v)`$ with $`[c] = [c']`$ hold at one
   heap, so $`\rho(u) = \rho(v)`$ and $`u`$, $`v`$ join one class. One
   receiver has one field lookup and one heap lookup; an absent key of an
   object without a prototype reads `undefined` both times (`ReadGave`).
   The merged link may find no field only where both may: $`p \land p'`$.

**Normalizer.** A union–find over the slots closes the partition under
laws 1 and 3 until no two links of one receiver class and field have
different destination classes; it terminates because classes only merge.
Then one link remains per receiver class and field. The obligations: each
law preserves `HeapLinks.Holds`; the stored predicate is a partition named
by least slots with one link per receiver class and field; the invariant is
the partition and the set of (receiver class, field, destination class,
may-find-none), which determines a stored value.

**Check.** `HeapLinks.check` (f23d943) compares by class. It gains the
merged destinations, and accepts a source read that finds the field as
justification of a target read that may not: `lookup = some l` and
`h[l]? = some v` give `ReadGave`.

## 4. K: facts

### 4.1 Representation

Two finite maps, sorted by key:

- **value facts**, from a class representative to a value set;
- **cell facts**, from a receiver class representative and a field to a
  value set; a cell fact also states that the receiver is an object whose
  read of the field gives a value (`HeapFacts.Holds`, `ReadGave`).

A value fact carries no field.

### 4.2 Laws

1. facts on the slots of one class are one fact, their meet (value facts:
   the slots hold one value; cell facts: the receivers are one object);
2. facts on one key are one fact, their meet (today's chains of shrinking
   lists are this case: **measured**, knowledge-growth deck);
3. **a cell fact behind a read link is the destination's value fact**: with
   a read link $`(c, f, p, v)`$, the cell fact on $`([c], f)`$ and the value
   fact on $`[v]`$ meet into the value fact on $`[v]`$, and no cell fact is
   stored on $`([c], f)`$. Both state the value `ReadGave` gives, the link
   states that read, and `linkFacts_holds` recovers the cell fact;
4. **a value fact is read at its class's context**: the meet of its
   members' contexts (each member's type, under `EnvOk`); V's encoding
   applies at that context, and a value fact that is *all* there is not
   stored;
5. a cell fact without a read link stays, even when its value set is
   *all*: it states that the read exists.

The stored predicate: maps keyed by representatives, no cell fact behind a
read link, every value set stored at its key's context, no value fact equal
to its context. The invariant: the partition's invariant; for each class,
the contextual invariant of its **value constraint**, the meet of its value
facts and of the cell facts on every receiver class and field whose read
link has this class as destination (law 3); and for each class–field pair
without a read link, whether a cell fact is present and, where present, the
contextual invariant of the meet of its cell facts. It determines a stored value: a present
cell without a read link is a stored cell fact, *all* included.

## 5. S: separation

The atomic statement of a separation fact is
$`\mathsf{Apart}(i, F, j, g)`$: the locations of scope $`F`$ of slot
$`i`$'s object (one field, or every own location) differ from field $`g`$
of slot $`j`$'s (`HeapSeparation.Apart`: **cited**).

**Representation.** Grouped facts between class representatives: a
subject, its scope (a list of fields, or *whole*) and its partners, each a
representative with the fields of it. The depth is the point's slot count,
part of the context, and levels are computed from it.

**Laws.** Grouped and split statements are one set of atomic pairs (a fact
with several fields and partners is the pairs it states); a whole pair
$`(c, \mathit{whole}) \to (d, g)`$ absorbs every field pair
$`\{(c, f), (d, g)\}`$, since every location a lookup of $`f`$ finds is in
the object's field list (`At`); endpoints on the slots of one class are the
class's; order and duplicates.

**Whole and per-field forms stay distinct.** A whole pair is not implied by
the field pairs over a key bound: a field list may hold one key twice
(`[(f, 0), (f, 1)]` satisfies `among {f}`), a lookup finds the first
location only, and no premise of the meaning (`EnvOk`, `ownKeysT`) states
that field keys are distinct (**cited**: `HeapSeparation.At`, `ownKeysT`,
`EnvOk`). The property draft's requirement for S is amended to read so.

**Stored** is the compacted form (`SeparationNormal.compact`): every level
read through its slot's representative, one fact per subject and scope, its
partners merged by level, levels and fields in order and each once, facts
without partners dropped. It holds exactly where the separation holds
(`compact_holds`: **proved**), is its own compacted form (`compact_idem`:
**proved**) and has at most the separation's facts, with at most one
partner per level and each field once (`compact_size`: **proved**). It is
not unique: two groupings of the same atomic pairs stay two forms, and
structural equality of S is equality of representation. Its readers ask by
class rather than by spelling: an edge compares each target pair with the
source's pairs through the source's representatives
(`HeapSeparation.checkBy`: **proved** sound), and a write asks whether some
slots of the two classes are apart (`HeapSeparation.apartBy`: **proved**
sound), so no pair is restated on the aliases of its slots.

## 6. Knowledge

### 6.1 Meaning

$`\mathsf{HoldsIn}\ G\ \Gamma\ k\ \rho\ n\ W\ h`$ holds when
`EnvOk G Γ ρ n W` and $`\mathsf{expand}_\Gamma\ k`$ holds
(`HeapKnowledge.Holds`). Every theorem of the normalizer, of `expand` and of
the check takes `EnvOk` as a premise, with the graph $`G`$ interpreting the
types and the slots below $`|\Gamma|`$, as `withTypedLinks_holds` does
today.

### 6.2 Expansion

$`\mathsf{expand}_\Gamma\ k`$ restates what the laws omitted:

- the alias links of each class, and each read link on every slot of its
  receiver class with every slot of its destination class;
- each value fact on every slot of its class, at the class's context
  (restricted, §2.4), and the class's context as a value fact where none is
  stored;
- each cell fact on every slot of its receiver class, and behind each read
  link the destination's value fact as a cell fact (`linkFacts`);
- each atomic separation pair on every slot of its classes, a reference
  reading the edge check and the write rule answer by class without it
  (§5).

Theorem: $`\mathsf{HoldsIn}\ \Gamma\ k \iff \mathsf{HoldsIn}\ \Gamma\
(\mathsf{norm}_\Gamma\ k)`$ and $`\mathsf{Holds}\ (\mathsf{expand}_\Gamma\
(\mathsf{norm}_\Gamma\ k)) \iff \mathsf{Holds}\ k`$ under `EnvOk`.

Expansion is the reference; an implementation may expand only what an
operation reads or changes, with a theorem that its result equals
$`\mathsf{norm} \circ \mathit{op} \circ \mathsf{expand}`$. In particular
an operation that removes a slot (projection, dropping the result, a
merge's mapping) keeps what that slot's facts and links stated of the
others: the class's context passes to the remaining members as an explicit
fact, and a cell fact behind a link to a removed destination is restated
on its receiver.

### 6.3 The check

`HeapKnowledge.check Γ a b m` checks each stored fact, link and
separation pair of the target $`b`$ against $`\mathsf{expand}_\Gamma\ a`$
at the mapped slots, by value-set inclusion after restricting the source's
meet at the mapped slot to the target class's context:
$`V_a \sqcap C_b \le V_b`$
([`knowledge-edge`](../PROGRAM-TYPING.md#stored-knowledge-and-how-it-is-read)). The target's omitted facts need no
check: its context facts follow from the target typing, which `ControlFlow`
checks before the knowledge (`MappedCovers`), and its cell facts behind
links follow from its checked links and value facts. Theorem
`check_sound`: `EnvOk` of the source, the mapped typing and
$`\mathsf{HoldsIn}\ a`$ give $`\mathsf{HoldsIn}\ b`$ at the mapped
environment.

### 6.4 Where normal forms are required

Every knowledge the search stores in its table or writes is
$`\mathsf{norm}_\Gamma`$ of the raw result at the point's context; the type
of stored knowledge is the subtype of normal forms. The evidence decoder
checks that each entry is stored at the context it is used at
([§5.3](canonicity.md#53-checked-at-the-boundary-wire-into-lean-w-x)).

### 6.5 Readers are entailment queries

Readers that today find a fact by its spelling ask instead whether the
knowledge entails what they need, through two queries on
$`\mathsf{expand}_\Gamma`$:

- the **value** of a slot: the meet of its value facts, at its context, a
  value set;
- the **cell** of a slot and field: absent where no cell fact and no read
  link states the read, and otherwise the meet of the cell facts with the
  read link's destination value, an `Option ValueSet`. Present, it comes
  with a theorem that the slot holds an object whose read of the field
  gives a value in the set (`ReadGave`), as membership of a cell fact gives
  today.

A reader checks presence where it needs the read, and compares by
inclusion (§2.3):

- `observedRead i R` (`HeapExpressionRules.lean`, `observedRead`: **cited**)
  asks today that the fact $`(i, R, f)`$ be a member of the cells; it asks
  instead that $`\mathsf{cell}(i, f)`$ be present and $`\le
  \mathsf{ofAtoms}\ R`$;
- `slicedRead` asks today that every atom of a cell fact answer the tag
  syntactically (`Atom.answers`); it asks instead that
  $`\mathsf{cell}(i, f)`$ be present and $`\le \mathsf{ofTag}\ t\ q`$;
- `valuesAt` and `knownValue` return and compare the value query;
  `includes` becomes $`\mathsf{value} \le \mathsf{ofAtoms}\ (\mathsf{atoms}\ G\ A)`$;
- the branch check, promise yields and cuts read the queries;
- the check (§6.3) requires, for each target cell fact, a present source
  cell at the mapped slot and field, included in it.

The evidence's requested sets (`observedRead`'s $`R`$, `knownValue`'s)
are value sets. Each reader's soundness theorem is restated with the query
in place of membership; the query accepts every request membership accepts
today, since a member fact makes the cell present and is among those it
meets.

## 7. The evidence

A knowledge entry carries its links, value facts, cell facts and
separation facts, each link and separation fact a position in its table. A
fact's contents are a position in the document's table of value sets, each
distinct value set written once
([evidence document](../REQUEST-PROTOCOL.md#evidence-document)); a value set
is written component by component, and a literal set lists its literals
and whether it is *these* or *all but*.

## 8. Bounds

**Stored knowledge, per point**, with $`s`$ slots, $`r`$ read links,
$`k`$ keys (classes times fields tested or read), $`e`$ separation pairs and
$`o`$ observations of a key along the path:

- links: $`s`$ partition entries and at most $`r`$ read links;
- facts: at most $`s + k`$;
- separation: at most $`e`$ atomic pairs;
- literals of one primitive component: under a finite context component of
  $`N`$ literals, at most $`N/2`$ (the encoding); under any other context,
  at most the literals the $`o`$ answers selected or excluded, plus, where
  an alias member was removed (§6.2), that member's context: up to $`N`$
  for a narrow member of $`N`$ literals joined to a wider one;
- object clauses: at most $`o + 8`$: one per observation, plus the 8 a
  merge's widening leaves (§2.3).

**Work, per operation**, on the classes and keys it touches, of $`m`$ items
in all:

- normalization: sorting $`O(m \log m)`$; absorption $`O(c^2 l)`$ for
  $`c`$ clauses of $`l`$ literals; the union–find near-linear in slots and
  links; the encoding linear in the context's literals, enumerated without
  being stored;
- a join of object components of $`c_1`$ and $`c_2`$ clauses builds
  $`c_1 c_2`$ clauses of at most $`l_1 + l_2`$ literals before absorption
  and widening, so $`O((o + 8)^2)`$ clauses;
- the operations work on classes: projection and dropping the result
  map each class to the classes of its remaining members; a write keeps
  the cell facts `apart` allows and drops the read links; a merge joins
  key by key over the classes the predecessors' partitions share;
  observation meets one class's value constraint and its cell keys. None
  restates a read link per pair of slots. Each costs $`O(m \log m)`$ in the
  stored knowledge it reads and writes, $`m`$ counting its output, plus the
  literals of the contexts whose classes change, plus the join
  intermediates above;
- a merge whose predecessors' partitions differ splits classes: a class of
  one predecessor becomes one class per class of the shared partition it
  meets, and its facts and links are replicated on each. Its output is
  at most the product of the predecessors' stored sizes (a grid of
  receivers aliased by rows in one and by columns in the other gives
  $`q^3`$ links from inputs of $`q^2`$), and its cost is
  $`O(m \log m)`$ in that output. The workloads of this section merge
  predecessors whose partitions agree on the receiver, which bounds their
  output by their inputs;
- expansion, which restates every read link on every pair of receiver and
  destination slots ($`pq`$ links for classes of $`p`$ and $`q`$ slots),
  is the reference the operations' theorems are stated against: each
  class-level operation is proved equal to
  $`\mathsf{norm} \circ \mathit{op} \circ \mathsf{expand}`$ and is
  never computed.

**Workloads.** Each a generated program at $`n = 4, 8, 16, 32`$:

1. **Disjunction:** `type Kind = 0 | 1 | … | 99; type Node = { readonly
   kind: Kind }`, and a function returning whether `node.kind === 0 ||
   … || node.kind === n - 1` (the deck's function).
2. **Repeated test:** the same, testing `node.kind === 0` $`n`$ times.
3. **Guards:** an object of a type with $`n`$ optional keys and a
   condition of $`n`$ tests `"k_i" in o`, each a different key.
4. **Fields:** a record of $`n`$ fields of type `Kind` and $`n`$
   consecutive `if (o.f_i === 0) return i;`.

In each, a test reads a field into a new slot, so a point after $`i`$ tests
retains $`O(i)`$ slots (the deck **measured** $`n + 2`$ slots holding the
object in workload 1), its context lists their types, and its partition has
$`O(i)`$ entries. The per-point element count is therefore $`O(i)`$ in every
workload, from the partition alone, plus $`O(i)`$ literals in workload 1 and
$`O(i)`$ clauses in workload 3. Over $`n`$ points the knowledge elements
grow with exponent 2 in every workload, against about 3 times the type's
size today (workload 1, **measured**, deck). **Bytes.** Serialized, a point adds to its elements identifiers in decimal
(slots and table indices up to the document's size: $`O(\log n)`$ digits),
field names of the workloads (`kind`, `k_i`, `f_i`: $`O(\log n)`$
characters), literals of at most three characters, and the proofs of its
edges. The proofs per point are not derived here: they are measured. The
prediction for $`n \le 32`$ is an evidence size growing with exponent at
most 2 up to the logarithmic widths, so at most 2.3 between 16 and 32
repetitions (**conjectured**).

## 9. Measurements and done

Before and after, at each workload's four sizes and on the census slices of
`moduleFunction` and `confined`: facts, literals, clauses and links per
point, evidence bytes, and search and check CPU. Done when, between 16 and 32 repetitions of every workload, the knowledge
elements grow with an exponent of at most 2 and the evidence bytes with an
exponent of at most 2.3,
`moduleFunction` writes no more than the 4.9 MB of evidence it wrote before
`call-keep` (**measured**, deck), and `make suite` and `make test` pass with
every case at its expected outcome.

## 10. Order of work

1. V: the representation, `ofAtoms` as an equivalence, the operations,
   `norm` and the four obligations; raw facts carry value sets.
2. L: the partition, law 3, and the check's optional reads.
3. K and S on representatives; `expand`, `Knowledge.norm` and their
   theorems; `check` with contexts.
4. The search stores normal forms; the evidence format and its decoder's
   validator.
5. The workloads as pipeline cases, and the measurements of §9.

Each step builds with no `sorry` and passes the suites; the search's output
changes from step 4.

## 11. Decisions for the owner

1. **Contextual literal sets** (§2.5, the encoding): the smaller of *these* and
   *all but*, enumerating the context's literals while normalizing.
2. **Cell facts behind a read link are not stored** (§4.2, law 3);
   `expand` restores them for every reader.
3. **Widening at merges to 8 clauses per object component** (§2.3), with
   observations and meets exact and unrestricted.
4. **S keeps whole and per-field forms distinct, and is stored compacted
   rather than as atomic pairs** (§5): a field list may hold a key twice,
   so a key bound does not make the two forms equivalent; the compacted
   form is bounded and idempotent but not unique, and its readers ask by
   class. The property draft's requirement for S is amended accordingly.
