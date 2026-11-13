# Draft: separation facts for heap knowledge

The design of separation facts. The rules are stated formally in
[separation facts](../PROGRAM-TYPING.md#separation-facts), their JSON
spelling in [heap facts](../REQUEST-PROTOCOL.md#heap-facts). Claims are
labelled **proved** (with the Lean name) or **cited** (with the document
and its scope).

## The existing mechanism this extends

The [heap state assertions](../PROGRAM-TYPING.md#heap-state-and-assertions)
checked on every incoming edge, whose knowledge holds cell facts, value
facts and read and alias links
([stored knowledge](../PROGRAM-TYPING.md#stored-knowledge-and-how-it-is-read);
cited). A separation fact is one more kind of entry of that knowledge,
spelled as the other entries are ([heap facts](../REQUEST-PROTOCOL.md#heap-facts)), and read by a write as the other facts
are.

## 1. The representation

Heap knowledge is cell facts, value facts, read and alias links, and a
separation $`S=(d,A)`$. Level $`\ell<d`$ names slot $`d-1-\ell`$: pushing a
result renames every slot and no level, so a fact is one value from the
allocation that states it until a drop, a copy, a projection or a join
changes it, and one entry of the evidence document's `separations` table
wherever knowledge names it. A slot at or past the depth has no level, and
no fact names it.

A fact $`(x,F,O)`$ separates the fields $`F`$ of the object at level $`x`$
($`F=\star`$: every own location of it) from the listed fields of the object
at each partner level. It is a product: the subject's freshness is stated
once, whatever the number of partners' fields, and field-location
inequality is derived on demand by the query $`\mathrm{apart}`$, which a
write consults to keep the cell facts it separates from the written field.

The identity of a value is its level, local to the execution state the
knowledge describes: a level names the value one slot holds there, never an
allocation site, so a loop's repeated allocation is the object its
iteration's slot holds, and an edge into the loop head maps its facts like
every other fact. A separation without facts has one spelling, $`(0,[\,])`$,
which the start node's empty knowledge and the cut equality compare.

## 2. Where facts come from

- **Allocation** states $`(D,\star,O_\Gamma)`$: every own location of the
  fresh object lies past the old heap, every contract field of a slot of
  $`\Gamma`$ in it. Imported and argument objects in $`\Gamma`$ are partners
  by their contract fields; a slot obtained later is not.
- **The lowering's statement entries** state, for each private cell, one
  explicit fact of its field `value`, partners the slots allocated before it
  and the cells and fresh constants allocated after it: the residual form.
  Every incoming edge proves it, the second orientation of the edge rule
  justifying the pairs with objects allocated after the cell.
- **Copies** take the copied slot's facts in both roles; no rule relates a
  value and its copy.
- **Writes, calls, observations, reads** keep the separation, pushed. A
  handler's edge carries the throwing node's entry knowledge, so no fact of
  the interrupted expression's own allocation reaches it.
- **The producer's projection and join** (untrusted) map facts to every
  target slot a mapping takes from their slots, and keep the pairs every
  joined state justifies: a whole-object fact's pairs another state
  justifies only for some fields stay as residual facts of those fields.

## 3. Proofs

**Proved** ([HeapSeparation.lean](../../lean/Verification/Semantics/HeapSeparation.lean),
namespace `HeapSeparation`, unless named otherwise).

1. `norm_holds`, `shift_holds`, `drop_holds`, `rebase_holds`, `copy_holds`:
   each operation preserves the meaning for the environment it produces; a
   slot without a level contributes nothing (`copy` of it is the push,
   `apart` of it false).
2. `allocate_holds`, with `HeapExpressionRules.fresh_apart`: the
   allocation's fact holds after an allocation of a fresh object at the
   heap's end; `alloc_sound`, `fresh_holds`, `merge_alloc_sound` and
   `makeKey_alloc_sound` use it.
3. `apart_sound`: the query gives the inequality of the two field
   locations; `write_sound` uses it.
4. `check_sound`: an accepted edge transports the meaning to
   $`\mathrm{mapEnv}\;m\;\rho`$; `HeapKnowledge.check_sound` has the
   component, and with it `checkGraphAssertions` and every edge check.
5. Heap independence: the meaning takes no heap, so `ordinaryOutput_holds`,
   `handlerFacts_holds`, `withStable_sound` and the call and promise rules
   carry it across writes, calls, normal and exceptional edges.
6. Representation: any set of pairwise location inequalities has a
   separation of the same meaning, one explicit fact each (`ofPairs_iff`);
   after an allocation the query answers for every field of the fresh
   object and every pair of $`\mathrm{contractFields}(\Gamma)`$
   (`allocate_apart`).
7. Reassignment: the operations mention the graph only through
   `contractFields`; the existing reassignment proofs hold unchanged.

`SourceClaimJson.checkUnitJson_safe` keeps its premise and conclusion:
knowledge holds at every node by `checkStep_sound` and the edge lemmas, with
the separation a fourth conjunct of `HeapKnowledge.Holds`. The producer's
projection and join carry no proof; that the edges they build are accepted
is measured by the pipeline cases and the census slices, preservation on
those inputs.

## 4. Trust

Trusted and proved: the knowledge semantics (`HeapSeparation.Holds`) and the
checker's separation operations. Trusted and audited: the evidence
decoder's lookup of the `separations` table, as the other tables'.
Unchanged in role: the lowering and request machinery that selects cuts and
compares node knowledge with their assertions. Untrusted: the producer's
propagation, projection and join, the encoder's interning, and the content
of each proposed assertion, which every incoming edge proves. No assumption
is added.

## 5. Tests

Pipeline cases: `fresh-separation` (positive): a captured `let`, a heap
cell, allocated by each loop iteration, at a join, before a call and before
a throwing call, written while a parameter's tested field is read after
the write, in the loop body, after the call and in the handler; every
write keeps the field's fact through a separation fact.
`invalid-fresh-copy-write` and `invalid-fresh-loop-alias` (negative): a
write through a copy of a fresh object, and through an older variable the
fresh object was stored in, forgets the tested field (each returns null
under Node where TypeScript reads a number).

Forged-document controls (`pipeline/test.mts`, the separation control): an
argument stated fresh (a fact no allocation states), a fact naming a level
at its depth, and a separation at a depth one off (a stale slot map) are
each refused by heap knowledge at the edge entering the node and accepted
with the separation check bypassed; the cell's explicit fact removed from
every node of the body, the knowledge consistent from edge to edge, is
refused at a node whose stated output it established; a knowledge entry
naming a position past the separations table is refused by the decoder.
The producer's join, which no source case reaches with a whole-object and
an explicit fact for one pair, is exercised by
`lean/Verification/Tests/SeparationControls.lean`.
