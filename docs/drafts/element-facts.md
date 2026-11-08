# Element facts

Part of [checked bound annotations](checked-bound-annotations.md) (#115). Drafted by Astra on `5701f1e9`.

## The existing mechanism this extends

**Existing at `5701f1e9`.** [The elements fact](../FOOTPRINTS.md#the-elements-fact)
states `ElemsAt R`: every present element has a kind admitted by `ElemPred`.
The locations it reads include the array store and element locations; holes remain separate.
[Linear facts](../PROGRAM-TYPING.md#linear-facts) supply checked integer arithmetic,
heap-dependent terms, read bridges, and preservation through known changes.
[Type invariants](../PROGRAM-TYPING.md#type-invariants) carry boundary obligations;
[guarded clauses](../PROGRAM-TYPING.md#guarded-clauses) handle nullable fields.
**Proposed:** extend this elements mechanism with predicates relating numeric
elements to existing terms, carried through the same knowledge and contracts.
`ElemPred`'s kind sets cannot express these relations: their predicates read no heap.
The extension therefore needs explicit dependencies on the terms its bounds read.

## Objective and scope

The owner’s target is pretext `2b11a4c` without bound rewrites, with arithmetic
annotations, at `/private/tmp/claude-501/astra-115/target/final/pretext/src`.
Complete verification includes builders, consumers, imports, and initialization.
The approximately 25 element-dependent refusals are the supplied work estimate.
The `5701f1e9` record reports 148/211 shallow, 129 deep, and three marked unsafe sites;
those measurements do not establish that element facts alone close the target.
Any real unsafe execution requires a repair or an independently justified precondition.

## Proposed fact and read rule

Write `E(xs, q, P)` for a fact about the prefix ending at `q`.
The array and external terms must denote, with safe-integer `0 ≤ q ≤ length(xs)`.
For every present index `i < q`, its value is a safe integer `v` satisfying `P(i,v)`.
Initially `P` is a conjunction of linear inequalities, such as `0 ≤ v ≤ length(ys)`.
A full-array fact uses `q = length(xs)`; a prefix uses an existing numeric term.
Presence remains a separate obligation: a fact about present elements permits holes.
The requested universal fact combines `E` with presence throughout its domain.

At `v = xs[k]`, prove a safe-integer index, `0 ≤ k < q`, and presence at `k`.
Instantiate `P(k,v)` and `safeInteger(v)` in the ordinary linear knowledge.
The rule must cover `%ElementAt%` and every other admitted element-read lowering.
Its bridge states that the returned value is the current element at that index.
A saved numeric result remains a snapshot; later mutation expires its read link.
Inclusive endpoint bounds support iteration endpoints; indexing requires strict bounds.
Thus `itemSegments[index + 1] ≤ widths.length` bounds the inner loop of `narrowsLine`,
while `segmentItems[i]` needs a strict bound for indexing `hyphenWidths`.
`starts[next] ≤ normalized.length` alone does not justify `spaceSources[starts[next]]`.

## Proposed preservation and establishment

The locations the fact reads are its receiver paths, the store, the relevant element
locations, and every location the endpoint and the predicate’s external terms read.
An operation preserves the fact when it preserves those locations, or proves a transfer.
A checked write inside the prefix preserves `E` when its stored value satisfies `P`;
a write outside the prefix preserves it when its frame condition leaves those locations unchanged.
The proof uses actual locations and alias information, including aliases of bounds.
Changing a bound requires proving the resulting predicate of all retained elements.
For example, growth of an upper-bound length weakens the obligation; shrinkage does not.

`push(v)` extends a full fact when `v` satisfies the post-state predicate and
old elements still satisfy it; multiple arguments require each corresponding check.
Existing `receiverGrows` alone proves neither appended contents nor exact growth.
Extend the audited push contract with its append relation, including normal-return scope.
Array literals establish the fact from each evaluated element and its presence.
An empty array establishes it vacuously; spread needs the source’s corresponding fact.
The existing [immediate fill lowering](../SOURCE-CONTRACTS.md#new-array-filled-at-once)
establishes a dense full fact when the fill value meets the predicate.
Bounds are evaluated in the final heap: evaluation of the fill value can change them.

## Proposed loop certificates

The loop invariant is `E(xs, j, P)` plus presence on `[0,j)` and scalar bounds.
Initialization proves the empty prefix, or a prefix already supplied by the caller.
Writing at exactly `j` establishes that element; incrementing to `j + 1`
extends the prefix after proving safe arithmetic and preserving its earlier elements.
Lean checks initialization, every back edge, and each exit through existing cut checks.
`continue`, exceptions, and early returns receive their actual established prefix.
A return claiming the full array proves `j = length(xs)`; a partial builder exports `j`.
`findGraphemeEnds` needs an output-prefix contract indexed by its returned `count`,
conditional on `ends !== null`, with sufficient capacity and bounds on stored endpoints.
Its callers consume `[0,count)`, independently of the unused capacity of `ends`.

Monotonicity is a proposed second predicate: adjacent present values satisfy
`xs[i] ≤ xs[i+1]`, with presence proved wherever an application needs it.
Appending checks the last pair; replacing an interior value checks both neighbors.
An arbitrary ordered pair requires a proved finite-chain rule over a present interval.
Bounds alone should handle consumers whose loops already establish their needed order.

## Proposed JavaScript and host obligations

Existing length terms cover ordinary arrays and typed-array lengths.
A string-length term requires its own UTF-16 length interpretation, admissibility bound,
read bridge, and safe-integer theorem before clauses can name `text.length`.
Ordinary numeric bounds require safe integers; comparison truth alone excludes neither
fractions nor all problematic numeric values needed by integer reasoning.

Typed arrays require a content model: `%ByteSet%` currently changes no modeled location.
Introduce modeled backing bytes and view offset/kind; shared views read the same bytes.
Every content-changing native must expose those writes, including `fill`, `set`,
`copyWithin`, and overlapping `subarray` views; recompute affected values or drop facts.
Existing fixed-size, non-detached-buffer assumptions remain explicit host assumptions.
A typed write proves the bound of its converted stored value: `Int32Array` can wrap,
`Uint8Array` reduces modulo 256, and floating arrays can contain NaN or fractions.
Exact integer preservation is available when the value lies in the destination range.
Native contracts and conversion behavior belong in [SOURCE-CONTRACTS](../SOURCE-CONTRACTS.md);
normal-return guarantees give no preservation on a caught exceptional path.

## Proposed annotations, wire, and implementation

Use specification-only `forall(xs, 0, q, (i, v) => safeInteger(v) && 0 <= v && v <= hi)`.
Admit it inside `@requires`, `@invariant`, and their existing nullable guards.
The quantifier ranges over present elements; density supplies universal presence.
Prefer this explicit syntax initially: JavaScript `every` skips holes and permits effects.
A runtime `every` rule needs a certified predicate and preservation through all callbacks.
Builder result-prefix clauses need a checked result binder in the contract language.
Type invariants remain boundary obligations, with each construction and return checked.

Extend `IndexFact` with an element clause containing receiver path, prefix term,
and linear predicates with scoped index/value binders; reuse existing guarded facts.
Carry it through Fragment, `tools/source-claims.mts`, declarations, and evidence.
Decode one exact shape, reject unknown fields, and audit every substitution and mapping.
The producer proposes templates from annotations, literals, fills, writes, and pushes;
joins retain provable common predicates, and widening never enlarges a certified prefix.
Lean owners are `Semantics/IndexFacts.lean`, `HeapKnowledge.lean`, `CallEffects.lean`,
`FootprintStability.lean`, and `Programs/IndexWrites.lean`, `HeapExpressionRules.lean`,
`PromiseCalls.lean`, under `lean/Verification/`; `Linear.lean` checks instantiated arithmetic.
Wire and certification extend `Source/EffectJson.lean`, `Lowering/Atoms.lean`,
`Lowering/Flow.lean`, and `Claims/Json.lean`, preserving `checkUnitJson_safe`.

## Proposed first step and evidence

First implement ordinary-array interval facts, read instantiation, boundary contracts,
literal/fill introduction, and checked prefix-write/push transfer as one complete slice.
Target `narrowsLine` and its builder first; this exercises dependent bounds end to end.
This is the smallest reusable slice; the greatest numerical gain among the 25 is unmeasured.
Follow with typed backing-store semantics and `findGraphemeEnds`’ counted-prefix contract,
targeting `getUnspacedGraphemes`, `countEmojiGlyphs`, and `setupClusterBoundaries`.
Generated tables additionally need checked decoding, row/stride predicates, and bit arithmetic:
`unpackClassRuns`, `unpackTable`, and `markRuleBoundaries` cannot inherit generator comments as proofs.

Keep target-associated positive cases for dependent reads, prefix loops, fill, push, and aliases.
Run Node negatives for holes, inclusive indexing, skipped prefix writes, alias mutation,
shrinking bound arrays, typed conversion wraparound, and overlapping-view invalidation.
Forge element facts, prefixes, receiver paths, and postconditions at verifier boundaries.
Validate targeted builders and consumers, then `make test`; report exact target refusals.
Complete verification requires every remaining obligation and unsafe site to be resolved.