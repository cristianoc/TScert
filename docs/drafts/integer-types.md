# Integer types in the program's annotations

A type the verifier declares, `SafeInt`, that a program writes wherever it
writes `number` for a value that is a safe integer. TypeScript reads it as
`number`; TScert reads it as a type of its own: the JavaScript numbers in
the safe-integer range, both zeros included, which the clause predicate
`safeInteger(x)` states of a value and Lean's `SafeIntegers.SafeInt`
defines. The papers' sort $`\mathit{SafeInt}`$ is the arithmetic-rules work's
(pull request #259), not yet on this line.

## The existing mechanisms this extends

- **Types the verifier declares** ([ANNOTATIONS.md](../ANNOTATIONS.md#types-the-verifier-declares)):
  `Modifies<P, T>`, `Fresh<T>`, `Resolvable` and `Awaitable` in
  [`tools/resolvable.d.ts`](../../tools/resolvable.d.ts), recognised by the
  declaration their name binds to, the canonical file or a file of the same
  text (`tools/declaration-graph.mts`). Each is a bound or a statement:
  `Modifies` and `Fresh` are refused wherever a type is read, and
  `statedResult` reads a statement. `SafeInt` is the first read as a type,
  which is new work in `tools/type-term.mts`.
- **Types** (`Types/PositiveGraphs.lean`, `Types/PositiveNormalization.lean`):
  a type is a node of the normal graph, whose rows are clauses; numbers are
  the clauses `num`, `numLit` and `numIn`. Their meaning, meet, inclusion
  (`Types/PositiveRules.lean`, through which `subtypeUsing` decides),
  selection (`Types/ClauseSelection.lean`), renaming and decoding
  (`Source/RequestJson.lean`) are defined over clauses. A union is a list of
  clauses.
- **Integer facts** ([DESIGN.md](../DESIGN.md#general-mechanisms)): the
  index fact $`\mathrm{int}(x)`$ of a slot holds where its value decodes by
  `SafeIntegers.safeIntOfBits` (`IndexFacts.intValue`); a linear fact
  requires every term it names defined, so it implies the integrality of
  each (`HeapKnowledge.intSlot`). For a path, integrality is $`P\le
  2^{53}-1`$; for an element under `every`, an element bound.
- **Type to fact**: `IndexWrites.litSlot` reads a slot whose one clause is a
  decodable `numLit` as an arithmetic constant, in `linearAtoms`.
- **Fact to type**: a node's exit refines its context by facts
  (`SinglePass.refinedContext`, through `PromiseCalls.refineBy`, sound by
  `envOk_refineBy`), with `(slot, type)` facts; that context is checked
  against the target's claimed context. A step is checked at its node's
  claimed context (`SinglePass.checkedStep`, the sequent
  $`\langle\Gamma, e, A\rangle`$ of the claim), which the front lowers
  from TypeScript's types, so a slot TypeScript types `number` is read at
  `number` by every value check.
- **The clause reader** (`tools/bound-annotations.mts`): a comparison
  requires each operand stated integral, by `safeInteger(...)`, to keep the
  clause's JavaScript reading ([ARITHMETIC.md](../ARITHMETIC.md#the-clause-language)).

## The problem

TypeScript has one numeric type, so every precondition bounding an index
repeats `safeInteger(i)`:

```ts
/** @requires safeInteger(i) && 0 <= i && i < xs.length */
export function at(xs: number[], i: number): number { return xs[i]!; }
```

ACSL (`integer`), JML (`\bigint`), Dafny (`int`, subset types) and
refinement-type systems (Liquid Haskell, Flux, Refined TypeScript) put
integrality in the signature's types; relations between values stay in the
contract.

## Routes

- **A. Sugar at named positions** (a parameter, a result, a field): each
  position its own case, the meaning holding only where a case exists.
- **C. Type-invariant elaboration, extended**: boundary obligations exist
  only at function declarations, and optional types, unions with a
  non-naming arm and generic references name none (ARITHMETIC.md, "Type
  invariants"). It would give path facts at boundaries, and nothing where
  a type is read elsewhere.
- **B. A type clause (proposed)**: one clause, read by every reader of a
  type.

## The clause `int`

`Clause` gains `int`, meaning $`\exists b.\ v = \mathtt{num}\ b \wedge
\mathrm{safeIntOfBits}\ b \ne \mathrm{none}`$:

- **Meet**: `num ⊓ int = int`; `numLit b ⊓ int` is `numLit b` where `b`
  decodes and empty otherwise; `numIn S ⊓ int` keeps the members of `S`
  that decode.
- **Inclusion**: `int ≤ num`; `numLit b ≤ int` and `numIn S ≤ int` where
  every literal decodes; `num ≤ int` never.
- **Decoding, renaming, rank and selection** read it as any clause.
- `SafeInt` lowers to the clause `int` (`tools/type-term.mts`).

Every reader of a type reads the clause: parameters, results, fields,
elements, union arms, written generic arguments, `Map` values, readonly
views, spread, destructuring and rest read the type they read today.
`ValueSet` and knowledge are unchanged: knowledge carries integrality as
$`\mathrm{int}`$, and `HeapKnowledge.primitive` maps the clause `int` to no
primitive atom of its own.

## The bridge

- **Type to fact**: in `linearAtoms`, a slot whose clauses are all at most
  `int` gives $`\mathrm{int}(x)`$. `litSlot` is its instance at a single
  decodable literal and is removed. For a path whose type is `SafeInt`,
  the fact is $`P\le 2^{53}-1`$; for an element of a `SafeInt[]` under
  `every`, the element bound.
- **Fact to type**: a step is checked at its claimed context $`\Gamma`$
  refined by the facts of its knowledge $`k`$ (`kE`, the facts the step
  reads): each slot $`x_i`$ that $`k`$ states a safe integer
  (`HeapKnowledge.intSlot`: an unconditional $`\mathrm{int}(x_i)`$, a length
  or a linear fact naming it) is read at $`\Gamma_i\sqcap\mathtt{int}`$.
  The pass represents that meet where it is `int`, where a clause of
  $`\Gamma_i`$ includes `int` (`number`, `int`, `unknown`), at the graph's
  `int` label, a lookup as `NormalGraph.literal` is for literals, read after
  its row is checked to be the one clause `int`; every other slot keeps
  $`\Gamma_i`$, which is sound and loses the meet of a literal union with
  `int` (`1 | string` at `1`). The refined context $`\Gamma^{k}`$ is the
  sequent of the step's own checks: the search of its derivation and
  `directCall` (an operand at its parameter), and the selection and normal
  effect of the step (`jOf`, `StepAccepted`), so a write's value at its
  location's contract, an argument at its parameter, a binding's or storage
  contract's coercion and a return of a slot at the result read
  $`\Gamma^{k}_i`$. A writing step is selected again over every fact at
  the same refined sequent.
- **Re-checks of a step's derivation**: wherever a step's derivation or
  context is read again against its node's claim, a derivation at a context
  refined by the step's facts `stepK` is accepted as one at $`\Gamma`$, each
  of its slots $`\Gamma_i`$ or the `int` label at a slot `stepK` states a
  safe integer, its length $`|\Gamma|`$: `derivChecked` (read by
  `footprintCheck`, `stepGrades`, `stepCertificate` and `outFreshOf`, and
  its proof's copy `passDerivChecked`), `promiseDerivChecked`,
  `regionalDerivChecked`, `regionalHeaderChecked`, the header of the
  regional node evidence, and the yields (`checkYsAt`, `stepYields`,
  reading `checkedYields` and `nodeYields` at the derivation's context).
  The regional checks of stable fields and nullish slots read $`\Gamma`$,
  which is sound.
  - **Soundness**: $`\mathrm{EnvOk}(\Gamma,\rho)`$ and
    $`\mathrm{Holds}(k,\rho,h)`$ give $`\mathrm{EnvOk}(\Gamma^{k},\rho)`$:
    an atom `intSlot` reads states $`\rho(x_i)=\mathtt{num}\,b`$ with
    $`\mathrm{safeIntOfBits}\ b\ne\mathrm{none}`$ (`intSlot_sound`),
    the meaning of the clause `int`, through `PromiseCalls.envOk_set`. Each
    consumer of a re-checked derivation holds `stepK` at the node's
    environment, an ordinary tree's as a `requiresTree`'s does, so it has
    the refined context's typing too.
  - **The exit**: an edge needs the refinement only into a slot its target
    already claims within `int`. Such a slot is a binding or field declared
    `SafeInt`, every write of which is a step checked at the contract
    (a storage-contract coercion or a write), so the edge into it carries a
    value already at `int`; the exit (`refinedContext`) adds no refinement.
  - **Mutable storage** is unchanged: the refinement types a read, and a
    location's contract is established at its allocation and every write.

Both directions are proved against `safeIntOfBits` with `intValue_safe` and
`intValue_num`. Subtyping stays a relation between types, for every value;
`number <: SafeInt` never holds.

## Clauses

The clause reader's integrality checks become one query on the operand
path's resolved type: integral where the type is `SafeInt` (every arm of a
union), or where `safeInteger(...)` is written. The elaborated facts are
unchanged, and Lean establishes them as today. Then

```ts
/** @requires 0 <= i && i < xs.length */
export function at(xs: number[], i: SafeInt): number { return xs[i]!; }
```

means what the clause with `safeInteger(i)` means.

## Values that reach `SafeInt`

- **Inferred generic instantiations** are TypeScript's, at `number`, since
  the alias is erased: `identity(i)`, `[i]`, `xs.map(x => x)` reach
  `SafeInt` only through the bridge on the value; written arguments
  (`Map<string, SafeInt>`) keep it.
- **Optional positions**: `f?: SafeInt` is `SafeInt | undefined`, as a
  `Map` lookup's result is, until presence is established.
- **Mutable storage**: a location typed `SafeInt` is a storage contract,
  established at its allocation and every write; a read's refinement never
  strengthens it. `@invariant safeInteger(this.f)` states the same of a
  field as a type invariant, a fact frames preserve; the type is the
  contract every heap meets.
- **Typed arrays**: an element of a `uint8`, `uint16` or `int32` view is a
  safe integer by its format (`Semantics/ViewFormats.lean`); its read
  gives $`\mathrm{int}`$, or its element type is `int`, so `const k: SafeInt
  = bytes[i]` holds. A `float64` view's element is a `number`.
- **Native results**: their reviewed contracts keep their declared result
  types (`number`); results their postconditions state integral
  (`indexOf`, string lengths) reach `SafeInt` through the bridge.
- **`JSON.parse`**: a `JsonValue`'s numbers are `number`; a value reaches
  `SafeInt` through a test that gives $`\mathrm{int}`$
  (`Number.isSafeInteger`), whose fact is part of this work where it is
  missing.
- **Signatures**: a checked definition or import establishes its results;
  an exported parameter's `SafeInt` is assumed of external callers, as
  every exported type is (DESIGN.md's trust surface); a `SafeInt` in an
  external declaration with no body is assumed as its `number` would be.

## Ranges

A non-negative safe integer (`SafeNat`) would be a second clause with its
own bridge; it is left for later. Relations between values stay in
clauses.

## Compatibility and controls

- A program that writes no `SafeInt` keeps its verdicts, except where the
  bridge adds a fact (a slot of a single decodable literal already gives
  one); the case set is compared before and after.
- Recognition follows the binding: a re-export or alias reaching the
  declaration of `resolvable.d.ts` is `SafeInt`; another binding named
  `SafeInt` is what it declares.
- Controls: a forged `int` clause, a forged result at `SafeInt`, a forged
  $`\mathrm{int}`$ fact; a comparison whose operand is typed `number` with
  no $`\mathrm{int}`$ fact (refused); a refinement in one context followed
  by an unrefined check of the same pair of types.
- Values at the edges: fractions, NaN, the infinities, both zeros,
  $`\pm(2^{53}-1)`$ and $`2^{53}`$; negative cases run under Node (a return
  of `x / 2` at `SafeInt` with `x` odd read as an index; `NaN` written into
  a `SafeInt` field).

## Steps

1. The clause `int`: meaning, meet, inclusion, decoding; `SafeInt` read by
   `tools/type-term.mts`; the case set compared. `SafeInt` then holds safe
   literals and values already typed `SafeInt`; anything else is refused.
2. Type to fact in `linearAtoms`, replacing `litSlot`; the clause reader's
   query. `SafeInt` operands then serve as indices without
   `safeInteger(i)`.
3. Fact to type: each step checked at its context refined by its
   knowledge's integer facts, and the re-checks of its derivation reading
   that refinement; the exit refinement into slots claimed within `int`;
   typed-array elements of an integer format and `Number.isSafeInteger`'s
   true branch stating $`\mathrm{int}`$. Arithmetic results known to be
   safe integers are then stored at, passed as and returned at `SafeInt`.

## Documentation

ANNOTATIONS.md (`SafeInt` beside the other declared types),
CLAIM-LANGUAGE.md and the types' documentation (the clause), ARITHMETIC.md
(the bridge and the clause reader), and the papers, where the type
`SafeInt` denotes $`\mathit{SafeInt}`$.
