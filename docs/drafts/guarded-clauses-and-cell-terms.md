# Guarded clauses and cell terms

Part of [checked bound annotations](checked-bound-annotations.md) (#115). Drafted by Astra on `cdda1137`.

## The existing mechanism this extends

**Existing at `cdda1137`, `bound-annotations-opus`.** [Linear facts](../PROGRAM-TYPING.md#linear-facts)
use partial `value`, `length` and `view` terms rooted at slots with field paths.
[Written preconditions](../PROGRAM-TYPING.md#written-preconditions) supply checked call obligations.
[Record invariants](../PROGRAM-TYPING.md#record-invariants) supply parameter preconditions
and result facts proved at normal returns, including facts over tracked entry arguments.
[Footprints](../FOOTPRINTS.md#index-facts) govern preservation between those boundaries.
The [field-path design](field-paths-and-record-invariants.md#41-revision-after-review-invariants-as-boundary-contracts)
states this boundary interpretation.

**Existing.** `IndexAtom.cond` conditions a fact on a slot's truthiness.
Read links relate current field contents to read slots; field tests refine those contents.
`SourceFacts.heldInCell` selects cells for locals updated inside expressions.
A cell already is an object owning `valueField`, the string key `"value"`.
The producer and entry-claim lowering currently exclude such bindings from linear terms.

**Proposed.** Extend index facts with guarded clauses and admit cell contents through existing paths.
The goal is the original pretext `x[k]!` reads, with bounds proved under modeled JavaScript semantics.
These extensions supply obligations and proof rules; they establish no coverage claim by themselves.

## Guarded clauses

**Proposed syntax.** Extend conjunctions with ordered clauses `G || C`, recursively,
where `G` is `P === null` or `P === undefined`, and `C` is an existing clause.
Resolve `undefined` as the primitive value; refuse a shadowed binding.
Resolve later paths under the preceding guards' false alternatives.
Thus `this.items === undefined || this.items.hyphenWidths === null || C`
admits `C` where `items` is present and `hyphenWidths` is non-null.
Keep every arithmetic definedness and safe-range obligation under the same guards.

**Proposed representation.** Add `IndexFact.guarded(path, tag, body)`,
where `tag` is exactly `null` or `undefined`, and `body` is another index fact.
A conjunction elaborates to several facts; chains become nested guarded facts.
This places the predicate in the existing `pre`, `ensures` and knowledge fact lists.
The truthiness condition on `IndexAtom` remains the outer condition for expression results.

**Proposed meaning.** Let `readGuard` read a path using the existing `HeapFacts.ReadGave`
relation at each field; its empty path reads the root slot.
A guarded fact holds exactly when that read succeeds and either its value equals
the stated tag or its body holds in the same environment and heap.
A matching guard requires neither the body's paths nor its arithmetic terms to be defined.
A failed path evaluation establishes no disjunction.

**Optional fields.** `ReadGave` admits absence as `undefined` only with no prototype to consult.
Use precisely that admitted optional-field semantics; inherited reads need their own checked rule.
Missing intermediate objects cannot be traversed: an earlier matching guard must short-circuit them.
Keep numeric `readPath` unchanged: a missing field never supplies a numeric term.
This distinction admits absent `items` without interpreting a missing length as zero.

**Proposed elimination.** A current read link transports a guard path to its read slot.
A checked `!== null` or `!== undefined` observation eliminates the corresponding alternative.
Repeat through the chain, then feed the exposed linear facts to existing entailment.
An optional read observed unequal to `undefined` proves presence before a numeric path bridge.
Destructuring uses the same links; the name `f` in `const { f } = p` carries no special authority.
A comparison result stored in a Boolean may use the existing condition-slot mechanism.

**Proposed introduction.** To prove `G || F`, establish the guard read and either
its matching tag, or `F`; alternatively check both cases of an exhaustive tag split.
On the unequal case, recursively prove the body; on the equal case, discharge the clause.
Existing matching guarded premises may also entail a target through checked path substitution.
Every reachable return proves its own result clause through `GraphCode.returnEntails`.
A null-valued builder return therefore proves the guard, while an array-valued return proves its bound.
The same rule checks call preconditions; a result type alone supplies no clause.

**Proposed joins.** Retain a guarded candidate only when every incoming edge entails it.
For `const h = items === undefined ? null : items.hyphenWidths`, prove
`h === null || h.length === widths.length` separately on the two arms.
This preserves the correlation needed by pretext's later `if (h !== null)` read.
A solver budget exhaustion refuses the obligation or forgets a candidate; it never assumes the body.

**Proposed preservation.** Extend footprint checks to guard reads as well as body terms.
Initially retain a whole clause only when every potentially evaluated dependency is preserved.
Guard paths depend on intermediate object fields and the tested endpoint, of any value kind.
Optional absence additionally depends on the object's field/prototype view remaining valid.
Preserving a length alone cannot preserve a clause whose nullable field may be replaced.
An independently proved matching guard may re-establish the clause after a write.
A destructured value remains a snapshot; its expired link cannot justify facts about the current field.
Normal-return footprints provide no preservation on a throwing edge without `onThrow`.

## Terms for bindings held in cells

**Proposed term.** For a cell-reference slot `c`, use the existing term
`{kind: "value", slot: c, path: ["value"]}`.
For a source path rooted at a cell-held binding, prepend `"value"` to that path;
the same composition supports array lengths and view counts stored in cells.
Definedness requires an allocated field containing a safe-integer number for a value term.
An uninitialized cell supplies no such fact; its fixed storage contract remains unchanged.

**Proposed read rule.** Reuse `readAtoms` and `readBridge` for `c.value ↦ old`.
The read slot gets the cell's current bounds and integrality facts.
Its ordinary value facts remain true after a write, while its link to `c.value` expires.

**Proposed write rule.** Before writing, restate relevant cell facts onto that old read slot.
Evaluate the update and prove its arithmetic on old/new value slots.
Apply the write footprint, discard affected current-heap facts and links,
then use the existing write link `c.value ↦ new` to establish facts of the stored value.
Eliminate temporary slots only after deriving the facts needed at the continuation.
This is read/write transport through paths, with no timeless equation between old and current contents.

**JavaScript order.** Prefix `++i` returns `new`; postfix `i++` returns `old`.
For `if (++i >= n)`, the continuing false edge bounds the stored `new` value.
For `xs[at++]!`, the read uses `old` although the cell already contains `new`.
Prove increment exactness with the existing safe-integer arithmetic rule;
fractions, coercible values and overflow cannot acquire integer facts from update syntax.
Respect evaluation order for the receiver, index and any intervening effects.

**Proposed preservation.** Cell terms are heap-dependent numeric-field paths.
Writes to their location invalidate them; proved separation may preserve other cells' facts.
Calls and closures may change captured cells according to their certified footprints.
A same-named binding, shared storage contract or ordinary slot fact proves no location separation.
Cell initialization transports initializer facts through allocation; cell-held parameters
transport their input facts through the parameter-cell allocation.

## Wire, implementation and proof obligations

**Proposed guarded wire.** Encode the new fact constructor with `{path, tag, body}`;
a path carries `{slot, path}` and the tag has the two stated alternatives.
Give source entry linear claims a required ordered `guards` list, empty for unconditional facts,
whose paths use binding names; wrap the linear fact and its definedness obligations together.
Update the single accepted shape and its fixtures, with exact decoding and no version tag.
Cell terms need no new term kind: source names denote binding contents, and lowering
resolves storage itself, prepending `"value"` for cells rather than trusting a producer-selected slot.

**Proposed implementation locations.** Relative to `lean/Verification/`,
`Semantics/IndexFacts.lean` owns guarded meaning, renaming, extension and preservation.
`Semantics/HeapLinks.lean` and `Semantics/HeapKnowledge.lean` own guard bridges,
introduction/elimination, definedness, projection, entailment and joins.
`Programs/HeapExpressionRules.lean` and `Programs/IndexWrites.lean` own read/write transport
and arithmetic facts; `Programs/PromiseCalls.lean` transports guarded pre/postconditions.
Audit `Programs/GraphCode.lean` return checks and entry-value tracking.
`Source/Lowering/Flow.lean` resolves entry terms through storage;
`Lowering/Bindings.lean`, `Lowering/Execution.lean` and parameter extraction cover allocation and updates.
Update `Source/EffectJson.lean`, claims readers, `tools/type-graph.mts`,
`tools/source-claims.mts`, `tools/bound-annotations.mts` and their producer counterparts.

**Proposed producer.** Extend `linear_facts.ml` with guarded candidates and cell-content paths.
Mirror expression evaluation order, snapshot/write transfer and checked branch specialization.
Propose loop facts using the existing bounded convergence policy; Lean checks every incoming edge.
Prove each extension through `SourceClaimJson.checkUnitJson_safe`, preserving its exact CLI premise,
all accepted functions and normal-return guarantees; run the axiom check with no new trust assumption.

## Cases and smallest first steps

**Proposed guarded first step.** One required nullable field, one guard, one length equality:
an analyzed builder and caller, a destructured null test, and the original bounded read.
Then add absent optional fields, ordered chains, conditional aliases and invariant-returning helpers.
Associate cases with `returnsFromUnfitHyphen` and `walkPreparedComplexLines`.

**Proposed cell first step.** Admit existing path terms for cell-held entry claims and prove
snapshot/write transport sufficient for `cursor-nested-update-refused` and its loop back edge.
Then cover postfix reads, assignments, two distinct cells and captured-cell mutation.
These are separate deliverables; neither alone establishes the whole walker's verification.

**Proposed negatives and controls.** Execute unsafe fixtures under Node showing an undefined read:
unequal parallel arrays, alias truncation, replacement after destructuring, an inclusive bound,
a wrong null/undefined guard, prefix/postfix confusion, fractional indices and callback cell mutation.
Add forged claims bypassing the producer for guard removal, wrong roots/keys,
stale links, undefined body terms, old/new substitution and facts across captured-cell writes.
Keep safe unsupported examples as gaps; report targeted function outcomes without a branch census.
Validation comprises the relevant cases, wire/type checks, `make test`, axiom and documentation checks.