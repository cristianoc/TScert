# Quantified facts in Pretext's array builders

## The existing mechanism this extends

[Quantified clauses](../ARITHMETIC.md#quantified-clauses) state a fact for
each index below an upper bound. Their [footprints](../FOOTPRINTS.md#supports-of-index-facts)
include what the array paths, element cells, bounds, guards, and projections
read. The ordinary pass checks the facts at the write, the incoming edges,
and the return.

The current checks, in the order a builder uses them, are:

```text
ArrayFilled(n, v) supplies a fresh dense array and length = n.
IndexFact.every reads the array, its element spine, and stop.
For each natural i < stop, BodyClause interprets the facts at i.
Bound.parallel and ElemTarget.parallel read the same i in another array.
instantiateEvery reads a checked element at k and requires 0 <= k < stop.
A write keeps a fact if its support survives, or a write rule re-establishes it.
```

These are the intrinsic in `tools/intrinsics.mts`, `IndexFact.HoldsAt`,
`boundValue`, `ElemTarget.read`, `instantiateEvery`, and the checks in
`IndexWrites` and `PromiseCalls`. World and heap typing supply readable
array contracts. An element read supplies the checked identity of its
result. The arithmetic solver decides integer comparisons over the
resulting paths and lengths.

For example, process `advances = [[3], [4, 5], [6]]` with
`incomingExtras = [null, [10, 20], null]`. The builder leaves extras absent
for the first row, allocates three null entries for the second, and writes
`[10, 20]` at index 1. The next step leaves index 2 unchanged. The required
fact at index 2 follows from its stored null, so the lengths of its two rows
never need comparing. The fill contract supplies the length of extras. It
supplies no fact about the value stored at index 2. The prefix fact over
already processed indices covers 0 and 1 at that point.

The proposed extension keeps the same steps. The fill contract supplies the
value stored at every allocated index. Each write keeps the same fact over
the indices it leaves unchanged. The read at index 2 gives the null value;
the guarded body holds by that value. A suffix bound, a shifted index, and
a value test in the body affect which locations a quantified clause reads.
They retain the same heap fact and footprint mechanism.

## Filled arrays

The [audited fill](../SOURCE-CONTRACTS.md#new-array-filled-at-once) writes
its actual value into every element of the fresh array. State that property
for the actual value, for every type of value the intrinsic accepts. In
the model, the pointwise clause equates the stored value with the entry
argument. This is identity of stored values, including a shared object
reference or a number's exact bits. The source operator `===` follows
the JavaScript equality rule.

For `attachEmptyExtras([[3], null])`, the postcondition states that the
fresh spine has two present cells carrying null. Both parallel index reads
in the consumer are below that spine's length. A quantified bound can
discharge its guard from the fill fact when its index domain is included in
the filled domain and every earlier guard in its body is defined at that
index. In a contract that tests `extras[i] === null` first, no read of an
advances element is needed to establish the guarded body. The implication is
a proof obligation even when the parallel length relation is vacuous.

The write rules preserve equality on cells they keep and establish it on
a replaced cell only where the written value is the same. Aliasing an
inner object preserves the identity fact across mutation of its fields,
while a separately stated length bound still depends on its spine. An
empty array with the correct length fails the fill fact if it has holes.
Filling with `[]` satisfies the length contract and violates the
pointwise bound for `[[3]]`.

An isolated verifier probe takes the null-filled extras as an input. A
guarded clause with a contradictory body states that each of its elements
is null. With the length inequality also supplied as a precondition, the
return still refuses the parallel clause whose first guard tests the
extras. The diagnostic lists both preconditions. This locates a second
obligation in quantified entailment, independently of the intrinsic.

## What writes establish about a quantified domain

The existing rules for a typed-array exact write and an ordinary array
append use the same two obligations. The old indices keep their body
facts, and the index being written satisfies the body in the new heap.
The ordinary-array version needs the checked distinction between the
locations of different indices and the value stored at a location.
Distinct cells can carry the same inner array.

For `chunks = [[3]]`, overwriting index 0 with `[42]` leaves the domain
unchanged and checks that the new row has length at least one. Appending
null at index 1 extends the domain by one and discharges its body by the
guard on the new cell. Both `push(null)` and an indexed write at
`chunks.length` can use this argument once their checked transition states
the new cell and value. Isolated versions of both expressions reach the
return on the current verifier and lose the guard-based invariant. The
indexed write's diagnostic retains the new length and the bound of the
written index.

For a parallel append, after `advances[i] = row`, the completed prefix
ends before `i` until `extras[i] = ex` establishes the other read.
The two read identities and the body's check then extend the prefix by one.
A partial update can preserve the old prefix without implying a fact of
the unfinished pair. Appending a row of length two and an extra of
length one fails the body at the new index.

When a function grows an inner `number[]` and promises to preserve a
quantified fact over an outer array of nullable rows, the check has two
separate premises. Its write must be disjoint from the outer spine, and
any aliased inner row's length must change in a direction the body's
comparison permits. Distinct element types alone do not establish that
two empty spines differ from their contents. A separation proof must use
the mutable spine contracts where they entail it, or another witness of
separation. A probe that grows only the inner array and returns the bag
already loses the outer invariant, with no outer append to explain the
refusal.

## Suffixes in lazy allocation

With the current allocation pattern in `measureAnalysis`, the useful
second fact at an iteration boundary is that each cell between the current
cursor and the end still stores null. A quantified range with both bounds
states it directly. Its array and both bounds denote at the point of
checking. For natural indices the body holds when the lower bound is at
most the index and the index is below the upper bound. Inclusion of ranges
gives weakening. Equal or reversed bounds give an empty domain, with the
array and terms still required to denote.

For the example above, allocation at index 1 establishes null on the whole
range. The write at 1 establishes the parallel fact on that element and
keeps the null fact on the suffix starting at 2. At the next iteration, the
existing element-read rule checks both ends of the suffix. It can read the
null at 2, and the next loop edge carries the empty suffix. The conservative
support can retain the whole spine and its element cells. Using a narrower
support requires a separate proof that the change outside that support
keeps the domain and the body reads.

There is also a source form that needs only prefixes. On the first non-null
extra at index 1, fill the one earlier position with null and append
`[10, 20]`. On each later iteration append the new extra or null. The
first and third rows of the example still have null extras, and a build
with no non-null extras returns null without allocating. This form replaces
preallocation to the final length with incremental growth. It requires
checked fill and append cases and an audit of the loop's observations of
length and allocation. Its runtime cost on Pretext has not been measured.

## Subrange indexing

In the rich-inline builder, `measureAnalysis` writes advances into the
paragraph at `base + s`. Its returned extras start at index zero. When a
paragraph has one previous row, the first returned extra must be paired
with paragraph row 1. The same-index parallel read at index 0 reaches
the previous paragraph row, so the existing quantifier cannot state that
pairing.

An indexed body read can instead use an affine expression in the binder
and the existing integer terms. Both the parallel guard and the projection
use that expression. For a local extra at index 0, a fact over the item's
range reads the advances at `base + 0`. Instantiation checks the index
of each concrete read against its expression and the domain of the
quantifier. In the example, after copying the extra to paragraph index 1,
the identity of the copied element gives the bound at paragraph index 1.
Negative or out-of-range computed indices do not denote a data read.

The source option is to supply a shared destination for extras through
`ParagraphLists` in the paragraph lane. Both writes then use `itemAt + s`
and the caller consumes the already aligned data; standalone measurements
still build item-relative extras. The audit is of who owns the destination,
when a null destination is allocated, and what the resulting effect
declares. This changes a measurement interface and the order of writes;
a source change needs an equivalence check of those effects and the
returned nullable representation.

## Masked segment kinds

The hard-break branch in the rich-inline builder replaces an earlier
preserved space's advances. For flags `[1, 2]`, advances
`[[10, 20], null]`, and extras `[[1, 2], null]`, the branch replaces advances
at index 1 with `[5, 5, 5]`. The old length comparison does not establish
the new one. A fact about the masked kind entails that extras at 1 is null,
which makes the new comparison vacuous.

For a reusable language rule, the body guard reads the flag's numeric
value and applies the calculus's bitwise operation
(`arithBits .bitAnd` in `Calculus.lean`). It compares the result as a
number, retaining JavaScript's signed 32-bit conversion. Narrowing from the
program's masked test then reads that checked fact at the same index.
The fact's support includes the view's element cells, so a write through
an alias of that view can invalidate the premise. The proof does not treat
a matching flag in a different cell as evidence.

The source option for this particular construction is to write null into
the corresponding extras cell where the destination exists, before
overwriting advances. In the example, the write leaves that cell's value
unchanged. The proof of source equivalence must show that every earlier
write of extras on that code path leaves the preserved space's entry null
and that no observer can see the extra write through an alias. A fixture
with an earlier non-null extra would change its result under the rewrite
and serves as a distinguishing case for that audit. The existing
single-array overwrite and parallel construction rules are prerequisites
to using this form in the verifier.

## What this duplicates

- Filled element identity is the pointwise form of the existing checked
  element-read relation. The effect's normal postcondition carries it;
  no second map of filled arrays is used.
- Range membership and a shifted read use the existing linear terms and
  entailment checks. They do not give the binder a second integer
  semantics.
- The bitmask uses the existing calculus operation and numeric equality.
  Its guard reads the same view cells that the normal region footprints
  describe.
- All new forms use `IndexFact.support?` and the normal write and call
  proofs. The return link rule changes the paths under checked links. It
  supplies no element facts lost by a preceding write.

The change surface includes the annotation parser and fact wire, the
quantifier semantics and entailment, and the support and write checks. A
text search for the existing constructors finds `.every` in 19 Lean files
under `lean/Verification` and `.parallel` in 11; those counts are an
inventory of readers, not estimates of edited files. The source
alternatives have not been measured.

The construction fixtures for suffixes and shifted indexing still refuse
with their parallel clause removed. The masked-kind fixture still refuses
when it omits the overwrite. Those comparisons locate earlier missing
construction facts. The direct tests of the three designs need a checked
input contract supplying the table facts, followed by the relevant read
or write. The construction cases then check that the facts are also built
by the actual loops.
