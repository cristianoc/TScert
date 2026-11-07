# Field paths and record invariants

Part of [checked bound annotations](checked-bound-annotations.md) (#115). Drafted by Astra from the census of the original pretext on `907a40f0`.

## The existing mechanism this extends

**Existing at `907a40f0`.** [Linear facts](../PROGRAM-TYPING.md#linear-facts)
range over `value`, `length` and `view` terms rooted at slots.
[Written preconditions](../PROGRAM-TYPING.md#written-preconditions) supply
`Effect.pre`; callers prove them and bodies assume them.
[Result facts](../PROGRAM-TYPING.md#reads-below-the-length) use `Effect.ensures`,
currently available only on trusted signatures.
`HeapLinks.Holds` relates a field-read slot to its current heap cell.
[Footprints](../FOOTPRINTS.md) own the preservation obligations for heap facts.

**Proposed.** Extend those terms with field paths and reuse their entailment,
call contracts and read links. Record invariants are named heap predicates,
elaborated into these facts at checked boundaries.
The broader [bound-annotation draft](checked-bound-annotations.md) proposes
invariants, guarded clauses and checked postconditions; those are design,
whereas the ten branch records establish the mechanisms listed above.
[View lengths and ensures](view-lengths-and-ensures.md) supplies their design context.

**Owner-supplied measurement.** On `bound-annotations-opus` at `907a40f0`,
109/209 functions of original pretext `0d102a5` verify.
Of the 100 refused functions, 49 first fail at an index read.
This counts functions by first refusal, not reads closed by this proposal.
The goal is to retain the original `x[k]!` expressions, with bounds proved
from annotations and code under JavaScript arithmetic and heap semantics.

## 1. Field-path terms

**Proposed.** A path is a root value followed by finitely many fixed field keys.
The initial source syntax admits named data fields; computed keys, getters
and proxy-mediated access require separate checked semantics.
A clause is a specification and executes no property access.

```math
\begin{aligned}
\mathrm{read}(\rho,h,x)&=\rho(x),\\
\mathrm{read}(\rho,h,p.f)&=h(\ell)
 \quad\text{if }\mathrm{read}(\rho,h,p)=o\text{ and }o(f)=\ell,\\
⟦\mathrm{value}(p)⟧_{\rho,h}&=\mathrm{intValue}(\mathrm{read}(\rho,h,p)),\\
⟦\mathrm{length}(p)⟧_{\rho,h}&=\mathrm{lengthOf}(h,\mathrm{read}(\rho,h,p)),\\
⟦\mathrm{view}(p)⟧_{\rho,h}&=\mathrm{viewLengthOf}(h,\mathrm{read}(\rho,h,p)).
\end{aligned}
```

**Proposed.** These are partial evaluations: every intermediate must be an object
with the required data field and an allocated cell.
The endpoint must meet the existing term's definedness condition:
a safe-integer number, an admissible array store, or an admitted host view.
A linear fact requires every term defined, even when normalization cancels it.
Nullable paths need a checked guard; absent fields cannot denote zero.

**Proposed preservation.** A path's support contains every traversed field cell.
A length additionally depends on the terminal array store; a view count
depends on its model length cell. Root slots must retain their values.
Heap extension preserves evaluation; a mutation preserves it when the
support is unchanged, or a dedicated theorem establishes the same value.
Store `grow` alone preserves neither exact length nor equal parallel lengths.
The first implementation retains heap-dependent facts across heap-preserving
calls and forgets them across other calls and writes.
Finer preservation uses proved support separation, including aliases.
Normal-return footprints supply no preservation on exceptional edges.

**Proposed read bridge.** If current read links establish `s = read(p)`,
then `value(s)`, `length(s)` and `view(s)` equal the corresponding path terms
where defined. Compose this lemma along nested reads and destructuring.
An old slot remains a snapshot after a field replacement; its link to the
current path expires. Slot equality alone cannot renew that link.

**Proposed representation.** Generalize a term to `{kind, root, path}`,
with an empty path representing the existing slot term.
Entry claims name `{name, path, term, coefficient}` using resolved binding
identities and canonical keys; lowering resolves roots to actual slots.
The producer proposes facts; Lean checks every incoming edge.
**Implemented differently.** Lean applies the read bridge itself, from the
read links its own rules state, at three places (entailment, the read, a
dropped slot: [the read bridge](../PROGRAM-TYPING.md#linear-facts)), so no
bridge is proposed: a link is already checked knowledge, and a proposed one
would add a claim with nothing to decide.
Neither a property spelling nor a producer assertion supplies entry assumptions.
Audit renaming, projection, elimination, alias classes and all three wire readers.

**Proposed annotations.** `safeInteger(cursor.itemIndex)` names a path value;
`p.widths.length` names an array length and `p.segmentFlags.length` a view count.
For example, `@requires safeInteger(i) && 0 <= i && i < p.widths.length`
and `@requires p.segmentFlags.length === p.widths.length` bound a flags read.
Every arithmetic intermediate retains the existing safe-integer obligations.
`@ensures result.widths.length === n` names the returned heap and the entry
value of argument `n`; checked code needs preserved entry-value bindings.
Written ensures remain refused until every normal return proves them;
`old` heap observations require a separate snapshot design.

## 2. Record invariants

**Proposed.** `@invariant` on an alias/interface names a predicate `I(this,h)`.
For `PreparedLineBreakData`, candidate clauses equate `widths.length`,
`breakableFitAdvances.length` and the actual typed view's element count.
Nullable arrays need guarded equalities, such as
`this.lineEndTrims === null || this.lineEndTrims.length === this.widths.length`.
Guarded clauses are an additional checker obligation, not existing syntax.
An index stored beside its array may state safe integrality and strict bounds.
A cursor with an end sentinel instead permits equality at rest; a read needs
a strict branch bound. A cursor's relation to a separate record belongs
in a callable precondition unless both values share an invariant root.

**Proposed establishment.** Construction establishes the predicate before
publishing the value at the invariant-bearing boundary.
Every write affecting its support must prove the predicate in the resulting
heap while the record is closed. This includes writes through aliases,
nested-array mutation, field replacement and native calls.
A field's ordinary storage contract remains unchanged.

**Proposed assumption rule.** Reading a value at the annotated type exposes
the predicate only with a current closed-invariant witness.
A signature may supply that witness through its checked precondition;
a construction, validation or postcondition may establish it.
A TypeScript type name alone supplies no persistent heap fact.
Inheritance, intersections, structural conversions, imports and function-value
flows must preserve these obligations or refuse the conversion.

**Proposed mutation discipline.** Pushing to one parallel array breaks equality
until the other append completes. Such builders use raw construction state,
then prove the invariant before publication.
For published records, temporarily opening an invariant requires an exclusive
capability covering its support and all observer aliases.
Callbacks, escaping references and exception handlers must be unable to
observe an open record as closed; restoration is required before such exposure.
That capability discipline is further design work; the first step refuses
temporary opening and checks each supported mutation while closed.

**Proposed alias rule.** `readonly` restricts writes through a reference;
it proves neither immutable array contents nor absence of writable aliases.
Persistent invariant-bearing references require checked control of all writers.
Without that control, retain the predicate as expiring point knowledge and
re-establish it at each observation boundary.
External inputs require validation or an explicit trusted contract; external
calls must account for callbacks, mutation and exceptional exits.

**Observed in source.** `segmentFlags` documents JSON copies with indexed
properties but no length. Such copies do not satisfy the typed-view predicate.
Supporting them requires a distinct indexed-record contract or validation;
a view-length equality covers only actual admitted typed arrays.

**Trust proposal.** Lean checks establishment, transport and consumption.
The front end remains responsible for annotation attachment, path resolution,
faithful declaration translation and signature/request agreement.
Native result facts and external invariants require separate contract audits.
The owner reviews these trust changes and any alias-exclusion assumption;
the existing fixed-buffer view assumption does not imply record immutability.

## 3. Minimal first step and acceptance evidence

**Proposed first delivery.** Implement field paths, checked read bridges and
path-valued `@requires`, using conservative heap invalidation.
This targets both parameter indices into record arrays and record-held indices
without requiring invariant capabilities or checked user-code ensures.
The hypothesis is that this reaches the largest shared class among the 49;
the aggregate measurement does not establish that ranking or a closure count.
Classify those functions by missing bounds, path transport, mutations,
postconditions and captures before reporting expected gains.
Exported requires are currently refused: original exported helpers additionally
need checked export/import contracts or validated entry boundaries.

**Proposed cases.** Preserve census-linked sources for `segmentFlags[segmentIndex]!`,
destructured parallel arrays, nested paths, and `itemSegments[cursor.itemIndex]!`.
Check callers establish the annotations; include loop merges and pure helper calls.
For `out.widthTrims[i - from]!`, prove safe integral `from <= i < to`,
the allocation's length `to - from`, non-nullness and capture stability.
That example additionally needs checked `zeros` ensures and a closure contract;
field paths alone do not close it.

**Proposed controls.** Forge an entry path fact, substitute another root/key,
retain a link after alias replacement, and carry a length across truncation.
Bypass the producer and annotation parser where their interpretations matter.
Run concrete unsafe sources under Node: fractional or end indices, unequal
parallel arrays, callback mutation, and observing an interrupted two-array append.
Keep safe unsupported cases as gaps, including guarded clauses and captures.

**Proposed proof obligations.** In `Semantics/IndexFacts.lean`, extend `Term`,
`termValue`, `IndexFact.HoldsAt`, renaming and extension lemmas.
In `Semantics/HeapLinks.lean`, prove path-to-slot agreement from `Holds`;
in `Semantics/HeapKnowledge.lean`, extend `termDefined_sound`,
`pickTerm_eq`, `linearFollows_sound` and elimination soundness.
All paths are relative to `lean/Verification/`.
`Programs/IndexWrites.lean` must justify read equalities and arithmetic;
`Programs/PromiseCalls.lean` must preserve `preconditionHolds_sound`
and `ensuresCall_sound` for path substitutions.
`Semantics/CallEffects.lean` must retain the exact pre/post heap interpretation.
Audit `Source/SourceClaims.lean`, extraction and `Source/Claims/Plans.lean`;
any new certified constructor needs its checker and safety theorem.
`SourceClaimJson.checkUnitJson_safe` must cover every accepted function,
with precisely its declared entry assumptions. Require `make test`,
the axiom check and documentation checks; report targeted before/after
function outcomes without treating a later first refusal as verification.