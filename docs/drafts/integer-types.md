# Integer types in the program's annotations

A type the verifier declares, `SafeInt`, that a program writes wherever it
writes `number` for a value that is a safe integer. TypeScript reads it as
`number`; TScert reads it as the sort $`\mathit{SafeInt}`$ of
[Tolerant frames](tolerant-frames-note/note.tex): the JavaScript numbers in
the safe-integer range, both zeros included, the values of which the clause
predicate `safeInteger(x)` holds.

## The existing mechanisms this extends

- **Types the verifier declares** ([ANNOTATIONS.md](../ANNOTATIONS.md#types-the-verifier-declares)):
  `Modifies<P, T>`, `Fresh<T>`, `Resolvable` and `Awaitable` in
  [`tools/resolvable.d.ts`](../../tools/resolvable.d.ts). The declaration
  graph recognises each by the declaration its name binds to, the canonical
  file or an exact-byte copy of it, and refuses external and ambient uses
  (`tools/declaration-graph.mts`); `statedResult` (`tools/type-term.mts`)
  reads the recognised ones at a signature's result. TypeScript reads each
  as its argument or as `unknown`.
- **Types as claims** ([CLAIM-LANGUAGE.md](../CLAIM-LANGUAGE.md)): source
  `number` lowers to number contents, a `ValueSet` whose `num` component
  is a finite set of literals or its complement (`Lit UInt64`,
  `Semantics/ValueSets.lean`); inclusion, joins, meets and normalisation
  are defined on that representation.
- **Integer facts** ([DESIGN.md](../DESIGN.md#general-mechanisms)): the
  index fact $`\mathrm{int}(x)`$ holds where the slot's value decodes by
  `SafeIntegers.safeIntOfBits` (`IndexFacts.intValue`); the clause
  `safeInteger(x)` elaborates to it ([the clause language](../ARITHMETIC.md#the-clause-language)),
  and clause comparisons require each compared operand to be stated
  integral (`tools/bound-annotations.mts`).
- **Bridges from contents to arithmetic**: `IndexWrites.litSlot` reads a
  singleton numeric literal type as an arithmetic constant;
  `HeapKnowledge.typeAtoms` and `typeSets`, `KnowledgeExpand`'s context
  extraction and `BranchRefinement`'s `factSlice` read facts off a slot's
  contents.
- **Type invariants** ([ARITHMETIC.md](../ARITHMETIC.md#type-invariants)):
  a type's `@invariant` elaborates to boundary clauses at the parameters
  and results of functions naming the type (`tools/fragment-statements.mts`).

## The problem

TypeScript has one numeric type. A bound on an index needs the index to be
an integer, so every precondition that bounds an index repeats
`safeInteger(i)`, and every quantified fact repeats it on its elements:

```ts
/** @requires safeInteger(i) && 0 <= i && i < xs.length */
export function at(xs: number[], i: number): number { return xs[i]!; }
```

ACSL (`integer`), JML (`\bigint`), Dafny (`int`, subset types) and
refinement-type systems (Liquid Haskell, Flux, Refined TypeScript) give
integers a sort in the signature; the relation between values
(`i < xs.length`) stays in the contract.

## Three routes

- **A. Sugar at named positions**: `i: SafeInt` elaborates to a clause at a
  parameter, a result, a field. Each position is a case of its own, and the
  meaning holds only where a case exists.
- **C. Type-invariant elaboration, extended compositionally**: a type
  carrying `SafeInt` elaborates to boundary clauses as `@invariant` does,
  over the type grammar. It supplies contracts at boundaries only: the
  mechanism excludes generic references and gives no fact from a field
  read, a cast or a native result (ARITHMETIC.md, "Type invariants").
  Making it hold everywhere a type is read would rebuild route B inside it.
- **B. A sort in the claim language (proposed)**: `SafeInt` is a refinement
  of number contents, so every place that reads a type reads it: a
  parameter, a result, a field, an element, a union's arm, a generic
  argument, a `Map`'s value.

## Route B

**Number contents.** `num` becomes a small predicate algebra: a finite set
of literals, its complement, the safe integers, and their meets and joins,
with inclusion, normalisation, substitution, serialisation and printing
defined on it and proved sound. Membership in the safe integers is
`safeIntOfBits` decoding, the same definition `int(x)` reads. An
observation may widen to `number`; a required annotation keeps its whole
meaning. `SafeInt` lowers to these contents in the source graph, the Lean
decoder and the native claim constructors.

**The bridge, one checked step shared by every value check**:

- from a slot's certified contents admitting only safe integers, the index
  fact $`\mathrm{int}(x)`$;
- from an established $`\mathrm{int}(x)`$, the slot's current contents met
  with the safe integers.

Both directions are proved against `safeIntOfBits`. Subtyping stays a
relation between types, for every value, cached per pair: `number <:
SafeInt` never holds; a value produced at `SafeInt` (an argument, a return,
a field write, an element write) is checked by refining that slot's
contents through the bridge, then checking the refined type against the
required one.

**Clauses.** A clause comparison accepts an operand whose resolved type
admits only safe integers, through one query over the type; a union with a
non-integer arm answers no. The Lean checker establishes the integrality
from the bridge, not from the clause reader's answer. Then

```ts
/** @requires 0 <= i && i < xs.length */
export function at(xs: number[], i: SafeInt): number { return xs[i]!; }
```

means what the clause with `safeInteger(i)` means.

**Obligations at each kind of position**, stated over the type grammar:

- **Unions**: integrality holds where every arm admits only safe integers.
- **Generics**: the refinement is preserved by substitution, bounds and
  checked instantiation.
- **Mutable storage**: a location typed `SafeInt` is established at its
  allocation and at every write; refining one read never strengthens the
  location's contract.
- **Arrays**: `SafeInt[]` states its elements' contents; presence stays
  separate, so an indexed read still needs its element present. A
  quantified clause over the elements requires presence and is not what
  `SafeInt[]` elaborates to.
- **Map values**: the value parameter is preserved through the reviewed
  host contracts; a possibly absent result is `SafeInt | undefined` until
  presence is established.
- **Signatures**: a checked definition or import establishes its results;
  an exported parameter's type is assumed of external callers, as every
  exported type is (DESIGN.md's trust surface), since TypeScript does not
  enforce the refinement.

These obligations are on the acceptance path that `mode8Accepted_sound`
covers.

## Ranges

A non-negative safe integer is a unary predicate the contents algebra could
carry beside the safe integers, with a bridge for $`0\le x`$ too; it is left
for later, under the name `SafeNat`. Relations between values (`i <
xs.length`) stay in clauses.

## Compatibility and controls

- A program that writes no `SafeInt` keeps its verdicts: the case set is
  compared before and after, since normalisation and refinement are
  shared.
- Recognition follows the binding: a re-export or alias reaching the
  declaration of `resolvable.d.ts` is `SafeInt`; another binding named
  `SafeInt` is what it declares. Controls for shadowing, re-exports and
  aliases.
- Controls forging a `SafeInt` claim, a result at `SafeInt` and an
  $`\mathrm{int}`$ fact; a refinement in one context followed by an
  unrefined check of the same pair of types (no cache leak); unsafe writes
  through aliases, absent elements and optional results.
- Values at the edges: fractions, NaN, the infinities, both zeros,
  $`\pm(2^{53}-1)`$ and $`2^{53}`$.
- Negative cases run under Node: a return of `x / 2` at `SafeInt` with `x`
  odd, read as an index (`xs[0.5]` is `undefined`); `NaN` written into a
  `SafeInt` field.

## Documentation

ANNOTATIONS.md (`SafeInt` beside the other declared types),
CLAIM-LANGUAGE.md (the number contents), ARITHMETIC.md (the bridge and the
clause reader), and the papers' $`\mathit{SafeInt}`$ (named on the branch
of the arithmetic-rules work, `note.tex` §2), with the sentence that the
type `SafeInt` denotes it.
