# Draft: separation facts for heap knowledge

The design of [certificate sharing's](certificate-sharing.md#stage-4-allocation-freshness-and-slot-relative-heap-knowledge)
stage 4; its status is the Certificate size row of [WORK](../../WORK.md#status).
Base: TScert main at ec59551. Claims are labelled **proved** (with the Lean
name), **cited** (with the document or measurement and its scope) or
**conjectured**.

## 1. Current state

**Cited (code at ec59551).** Heap knowledge `K = (Σ, Π, Λ)` holds cell facts,
value facts and links (`HeapKnowledge.Knowledge`). A distinct link
$`x.f\neq y.g`$ states that field `f` of the object in slot `x` and field
`g` of the object in slot `y` are different locations
(`HeapLinks.Holds`). It is heap-independent, so it survives writes and
calls (`HeapLinks.stable`). Its one consumer is the write rule: a write to
$`x.f`$ keeps the cell facts at locations a distinct link separates from it
(`HeapLinks.distinctFrom`, `writeOutput`, `write_sound`). Its producers are:

- allocation (`allocOutput`, `alloc_sound`, `fresh_holds`): for the fresh
  object in the result slot, one link per pair of its field and a field
  $`(s,g)\in\mathrm{contractFields}(\Gamma)`$, the fields every record of
  slot `s`'s type names;
- the lowering's statement-entry assertions (`distinctLinks`,
  [Source model](../SOURCE-MODEL.md#current-content-assertions)): for each
  private cell `i`, links $`i.\mathsf{value}\neq j.g`$ to the fields of the
  slots older than the cell and of the cells and fresh constants newer than
  it, restated at each cut and proved by every incoming edge.

Links are slot-indexed: pushing a result renames every slot, so every node's
links are new links, and allocation multiplies fields by contract fields.

**Cited (measurement, 2026-10-23, evidence of the census slices at ec59551).**

| Slice | Evidence MB | Distinct links | Their bytes MB | Link references in knowledge MB |
| --- | ---: | ---: | ---: | ---: |
| `collect` | 77.5 | 524,166 of 525,806 | 55.0 | 18.9 |
| `closeStatements` | 51.5 | 345,945 total links | 35.9 | 12.2 |

In `collect`'s 1,329 knowledge entries, the 2,798,774 distinct-link
references group into 3,940 (entry, cell) pairs; each cell is separated
from 255 (slot, field) pairs on average; cell and value facts occupy 1.42 MB.
Every distinct link is product-shaped: per entry and cell, its links are
exactly the cell's fields times its partners' fields.

## 2. The representation

**Conjectured.** Knowledge gains a fourth component, its separation
$`S=(d,A)`$, and loses distinct links: a link is a read or an alias link.

- $`d`$, the depth, fixes the slot-relative map: **level** $`\ell<d`$ names
  slot $`d-1-\ell`$, and slot $`i<d`$ has level $`\ell_i=d-1-i`$. A slot
  $`i\geq d`$ has no level: no fact can name it. A push renames every slot
  and no level.
- $`A`$ is a finite list of **separation facts** $`a=(x,F,O)`$: a subject
  level $`x`$, its fields $`F`$, either $`\star`$ (every own location of the
  object) or a finite set of keys, and its partners $`O`$, a nonempty finite
  list of pairs $`(y,G)`$ of a level and a finite set of keys.

Its meaning, for an environment $`\rho`$, where $`\mathrm{loc}_\star(v)`$ is
the set of $`v`$'s own locations (the locations its field map lists),
$`\mathrm{loc}_F(v)`$ the locations of $`v`$'s fields named in $`F`$, and
$`v.g\mapsto l`$ that $`v`$'s field `g` is at $`l`$; a value that is no
object has none:

```math
⟦(d,A)⟧\rho \iff \forall (x,F,O)\in A.\;
  x<d \;\wedge\; \forall (y,G)\in O.\; y<d \;\wedge\;
  \forall g\in G.\;\mathrm{Apart}_\rho(d-1-x,\,F,\;d-1-y,\,g)
```

```math
\mathrm{Apart}_\rho(i,F,j,g)\iff\forall l\in\mathrm{loc}_F(\rho(i)).\;\forall l'.\;
  \rho(j).g\mapsto l'\Rightarrow l\neq l'
```

It mentions no heap: it holds across every heap change, as distinct links
do. A fact is a product: it states the separation of the subject's fields
$`F`$ from every partner key, once. Where $`F`$ is a finite set the fact is
the conjunction of its pairs, $`\mathrm{Apart}_\rho(i,\{f\},j,g)`$, which is
symmetric:

```math
\mathrm{Apart}_\rho(i,\{f\},j,g)\iff\mathrm{Apart}_\rho(j,\{g\},i,f)
\qquad
\mathrm{Apart}_\rho(i,\star,j,g)\Rightarrow\mathrm{Apart}_\rho(i,\{f\},j,g)
```

**Canonical form.** Every operation returns its result through
$`\mathrm{norm}(d,A)`$, which removes the facts without partners and is
$`(0,[\,])`$ where none is left: knowledge that states no separation has one
spelling, which the start node's check (empty knowledge) and the cut checks
(equality with the lowering's assertion) compare.

**Identities.** The identity of a value is its level, local to the
execution state the knowledge describes: a level names the value one slot
holds in that state, never an allocation site. An allocation repeated by a
loop puts each object in the slot its iteration binds; a fact about that
slot is about the object it holds now, and an edge into the loop head maps
it like every other fact. **Provenance** is a checked relation: an
allocation establishes its fact from the heap's state at that moment, and
every later fact is the image of an established one under the rules below.

## 3. The rules

Each rule's output is a function of its input knowledge (and, where named,
the sequent's context $`\Gamma`$); the checker computes it, the node states
it, and the two are compared, as for the other components. Write
$`\mathrm{lv}(i)`$ for slot $`i`$'s level, defined only for $`i<d`$.

**Push** (every rule pushing a result, `shift`):
$`(d,A)\mapsto\mathrm{norm}(d+1,A)`$.

**Drop the result** (`dropResult`): slot 0 is level $`d-1`$; the result is
$`\mathrm{norm}(d-1,A')`$, where $`A'`$ removes the facts whose subject is
$`d-1`$ and the partners at $`d-1`$.

**Rebase** to a depth $`D\geq d`$: every level $`\ell\mapsto\ell+D-d`$; the
slots named are unchanged.

**Copy** of slot $`i`$ (`copy`; the pure read of a variable and the linked
read): where $`i<d`$, the copy, level $`d`$ of the pushed knowledge, holds
slot $`i`$'s value, so it receives slot $`i`$'s facts in both roles:

```math
A\mapsto A^{+}\cup\{(d,F,O)\mid(\mathrm{lv}(i),F,O)\in A^{+}\}
\qquad
A^{+}=\{(x,F,\;O\cup\{(d,G)\mid(\mathrm{lv}(i),G)\in O\})\mid(x,F,O)\in A\}
```

and the result is $`\mathrm{norm}(d+1,\cdot)`$. Where $`i\geq d`$ it is the
push. A copy relates the copy and the original only where a fact already
related slot $`i`$ to itself (a residual separating two fields of one
object); no rule introduces separation between a value and its copy.

**Allocation** (`allocOutput`; the literal, the merge and the computed-key
allocation): with $`D=\max(d,|\Gamma|)`$ and $`A`$ rebased to $`D`$,

```math
\frac{\Gamma\vdash_G r\leftarrow\mathrm{alloc}(\dots):B
      \qquad O_\Gamma=\{(D-1-s,\;G_s)\mid G_s=\{g\mid(s,g)\in\mathrm{contractFields}(\Gamma)\}\neq\emptyset\}}
     {(d,A)\vdash r\leftarrow\mathrm{alloc}(\dots)\dashv\mathrm{norm}(D+1,\;A\cup\{(D,\star,O_\Gamma)\})}
```

Every slot of $`\Gamma`$ has a level at depth $`D`$, so every contract
field `allocOutput` separates now is a partner, those of argument and
imported objects in $`\Gamma`$ included. Its premise is the existing one:
every own location of the fresh object is at least the old heap's length
(`slots_ge`), and every contract field of a slot of $`\Gamma`$ is a location
of the old heap (`fieldOperand_sound`, `HeapOk`).

**Separation query** (`apart`), for field `f` of slot `i` and field `g` of
slot `s`, both below $`d`$ (else false), with $`\star`$ containing every key
and $`O(y)`$ the union of the key sets $`O`$ pairs with $`y`$:

```math
\mathrm{apart}_S(i.f,\;s.g)\iff\exists(x,F,O)\in A.\;
  (x=\mathrm{lv}(i)\wedge f\in F\wedge g\in O(\mathrm{lv}(s)))\;\vee\;(x=\mathrm{lv}(s)\wedge g\in F\wedge f\in O(\mathrm{lv}(i)))
```

**Write** $`x.f\leftarrow v`$ (`writeOutput`): it keeps the cell facts
$`z.g\mapsto R`$ with $`\mathrm{apart}_S(x.f,\;z.g)`$, as it keeps those a
distinct link separates now, and keeps $`S`$, pushed.

**Calls, observations, reads**: $`S`$ is kept and pushed where the result is
pushed (`ordinaryOutput`, `observe`, `readFrame`). **Handlers**: a handler's
edge carries the node's *entry* knowledge (`handlerFacts`), so the facts an
interrupted allocation would have established never reach it; the entry's
separation is pushed past the thrown value.

**Edge** with mapping $`m`$ (target slot $`j`$ receives source slot
$`m(j)`$) from a source $`(d_s,A_s)`$ to a target $`(d_t,A_t)`$
(`HeapKnowledge.check`, and `checkGraphAssertions` with $`m`$ the identity):
let $`\tau(\ell)=d_s-1-m(d_t-1-\ell)`$, defined where $`\ell<d_t`$ and
$`m(d_t-1-\ell)<d_s`$. The source is read as its set of pairs

```math
P_s=\{(x,\star,y,g)\mid(x,\star,O)\in A_s,\,g\in O(y)\}\cup\{(x,f,y,g)\mid(x,F,O)\in A_s,\,f\in F\neq\star,\,g\in O(y)\}
```

and every target fact $`(x,F,O)`$ has its levels defined, and each of its
pairs is justified, one pair at a time, in either orientation: for every
$`(y,G)\in O`$ and $`g\in G`$,

```math
F=\star:\;(\tau x,\star,\tau y,g)\in P_s
\qquad
f\in F\neq\star:\;\{(\tau x,\star,\tau y,g),(\tau x,f,\tau y,g),(\tau y,\star,\tau x,f),(\tau y,g,\tau x,f)\}\cap P_s\neq\emptyset
```

This accepts every pair the distinct-link check accepts now, under either
orientation, and a grouped target justified by several source facts.

**Projection** (`project`, the producer's): a source fact's subject and
partners are mapped to every target slot the mapping takes from their slot
(each preimage, as `HeapLinks.pull` maps links), at depth
$`|\Gamma_{\mathrm{target}}|`$. **Join** (`meet`, the producer's), of
projections at one depth: each fact of the first state keeps the partner
keys whose pairs every other state justifies, by the edge rule's pair test
at the identity mapping; where the first state's fact has fields
$`\star`$ and another state's has explicit fields $`F'`$ for the same
subject, the join states the fact with $`F'`$, a residual. A fact left without partners is removed. Both are
untrusted: every edge is checked by the edge rule.

**Cut**: the lowering's assertion states, for each private cell `i`, the
one fact $`(\mathrm{lv}(i),\{\mathsf{value}\},O_i)`$, where $`O_i`$ groups by
slot the links `distinctLinks` states now, at $`d=|\Gamma|`$; the second
orientation of the edge rule justifies its pairs with the cells and fresh
constants allocated after the cell.

## 4. What stays explicit

**Conjectured.** A fact with explicit fields $`F`$ is the residual form. Any
set of distinct links has a representation with the same meaning, one
explicit fact per link: $`x.f\neq y.g`$ is the fact
$`(\ell_x,\{f\},[(\ell_y,\{g\})])`$ (`Separation.ofPairs_iff`). The
lowering's cut assertions keep this form, grouped by cell. Allocation states
the compact form. Separation is never inferred: a slot obtained after an
allocation (a read, a call's result, an imported object read later) is no
partner of its fact; a later alias inherits exactly the facts of the slot it
copies; distinct slots are separated only where a fact says so.

## 5. Lemmas

**Conjectured; each is a Lean proof of this stage.**

1. `Separation.norm_holds`, `shift_holds`, `drop_holds`, `rebase_holds`,
   `copy_holds`: each operation preserves the meaning for the environment it
   produces; out-of-range slots contribute nothing.
2. `Separation.alloc_holds`: after an allocation of a fresh object at the
   heap's end, the output separation holds.
3. `Separation.apart_sound`: $`\mathrm{apart}_S(i.f,s.g)`$ and
   $`⟦S⟧\rho`$ give $`l\neq l'`$ for the locations of $`\rho(i).f`$ and
   $`\rho(s).g`$, the inequality `HeapLinks.distinct_sound` gives now;
   `write_sound` uses it in place.
4. `Separation.check_sound`: an accepted edge transports the meaning to
   $`\mathrm{mapEnv}\;m\;\rho`$; `HeapKnowledge.check_sound` gains the
   component, and with it `checkGraphAssertions` and every edge check.
5. Heap independence: the meaning takes no heap, so the separation is
   carried unchanged by `stable_holds`, `alloc_frames`, `handlerFacts_holds`,
   `ordinaryOutput_holds` and the call and promise rules, across writes,
   calls, normal and exceptional edges.
6. Representation: `Separation.ofPairs_iff` (§4), and
   `Separation.alloc_apart`, the allocation's completeness against the
   current rule: after an allocation, $`\mathrm{apart}`$ answers true for
   every pair of a field of the fresh object and a pair of
   $`\mathrm{contractFields}(\Gamma)`$, which is every distinct link
   `allocOutput` states now.
7. Reassignment: the separation operations mention the graph only through
   `contractFields`, which the existing reassignment lemmas cover;
   `checkStep`'s, the graph checks' and the qualified bodies' reassignment
   proofs extend to the new output, which is the same function of the
   context in both graphs.

`SourceClaimJson.checkJson_safe` keeps its premise and conclusion: knowledge
holds at every node by `checkStep_sound` and the edge lemmas, extended by the
fourth conjunct of `HeapKnowledge.Holds`. The producer's projection and join
are untrusted and carry no proof; their completeness (that the edges they
build are accepted) is what the pipeline cases and the five census slices
measure: no verified outcome may change. That is preservation measured on
those inputs, not a universal completeness theorem.

## 6. The wire

**Conjectured.** The evidence document gains a `separations` table of
facts, interned like the other tables; a knowledge entry carries its depth
and the positions of its facts. Since levels survive pushes, a fact is one
entry from its allocation until a drop, a copy, a projection or a join
changes it. Links lose `distinct` and `other`. The decoder reads the table
strictly, as the others, and resolves fact positions as it resolves link
positions, refusing a position past the table. The diagnostic's knowledge
reader (`diagnostic.mts`) follows the new shape.

## 7. Trust

Changed trusted code: the knowledge semantics (`Separation.Holds`), the
checker functions of §3 (proved by §5), the evidence decoder's lookup of the
new table (audited, as the other tables' lookups), and the lowering and
request machinery that selects cuts and compares node knowledge with their
assertions (unchanged in role; its assertions change form). Untrusted: the
producer's propagation, projection and join, the encoder's interning, and the
content of each proposed assertion, which every incoming edge proves. No
assumption is added.

## 8. Expected size

**Cited (computed from `collect`'s and `closeStatements`' evidence at ec59551,
regrouping their distinct links by knowledge entry and subject and
addressing them by level; scripts and inputs in the measurement's scratch
directory).** `collect`'s 2.8 million distinct-link references become 3,940
fact references over 402 distinct facts, 1.23 MB in a compact array spelling;
`closeStatements`' 1.8 million become 4,836 references over 477 facts,
0.78 MB. This regrouping models the representation, not the propagation of
§3; the implementation's evidence is measured on the five slices before and
after. **Conjectured:** with JSON field names, the evidence of `collect` and
`closeStatements` falls from 77.5 and 51.5 MB to about 5 MB each. An edge
check builds the source's pair set once, by hashing, and looks each target
pair up: `collect`'s pairs number 1,004,979 in all, where its edge checks
hash 2,798,774 link references now. A write's query scans the facts once per
cell fact it keeps.

## 9. Tests

Pipeline cases, positive and negative, each run against today's outcome:

- repeated allocations: an object allocated in a loop body, written, keeps a
  fact about an outer cell and about the object the previous iteration
  allocated (positive); the same object reached through a loop-carried
  alias is no partner (negative: a write through the alias forgets);
- an alias by assignment, a join of two allocations, a call and a write
  between the allocation and the use (positive where today's links
  sufficed);
- a throw inside `try` after an allocation: the handler keeps the separation
  established before the throwing node (positive), and none of the
  interrupted expression's.

Forged-document controls (`pipeline/test.mts`): a separation fact or a
partner no allocation justifies; normal-output freshness carried on an
exceptional edge; a fact naming a level at or past its depth (an
out-of-range slot) and a target separation with its depth shifted by one (a
stale slot map); a grouped target pair whose source orientation is reversed
(accepted) and one with no source pair (refused); a cut whose assertion
drops a private cell's explicit fact, with a write that needs it; a
knowledge entry naming a position past the separations table.
