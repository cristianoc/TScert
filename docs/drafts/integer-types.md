# Integer types in the program's annotations

A type the verifier declares, `SafeInt`, that a program writes wherever it
writes `number` for a value that is a safe integer: TypeScript reads it as
`number`; TScert reads it as the sort $`\mathit{SafeInt}`$ of
[Tolerant frames](tolerant-frames-note/note.tex), the values of which the
clause predicate `safeInteger(x)` holds.

## The existing mechanisms this extends

- **Types the verifier declares** ([ANNOTATIONS.md](../ANNOTATIONS.md#types-the-verifier-declares)):
  `Modifies<P, T>` and `Fresh<T>` in [`tools/resolvable.d.ts`](../../tools/resolvable.d.ts),
  recognised by the declaration TypeScript binds the name to, never by its
  spelling (`statedResult` in [`tools/type-term.mts`](../../tools/type-term.mts)).
  TypeScript reads each as `T`; TScert reads a fact from it. `Fresh<T>` is
  the nearest: a fact about the value, written as its type, at a result.
- **Integer facts** ([DESIGN.md](../DESIGN.md#general-mechanisms)): the
  clause `safeInteger(x)` elaborates to the index fact $`\mathrm{int}(x)`$,
  and `safeInteger(P)` of a path to $`P\le 2^{53}-1`$
  ([the clause language](../ARITHMETIC.md#the-clause-language)).
- **Types as claims** ([the claim language](../CLAIM-LANGUAGE.md)): a
  program's types are read into claims, which every position of a value
  reads the same way (parameters, results, fields, elements, unions,
  generic arguments), with subtyping between them and an obligation where a
  value is produced at a type.

## The problem

TypeScript has one numeric type. A bound on an index needs the index to be
an integer, so every precondition that bounds an index repeats
`safeInteger(i)`, and every quantified fact repeats it on its elements:

```ts
/** @requires safeInteger(i) && 0 <= i && i < xs.length */
export function at(xs: number[], i: number): number { return xs[i]!; }
/** @requires forall k in ends: safeInteger(ends[k]) && 0 <= ends[k] && ends[k] < widths.length */
```

Other specification languages give integers a sort of their own in the
signature: ACSL's `integer`, JML's `\bigint`, Dafny's `int`, `nat` and
subset types, refinement types in Liquid Haskell, Flux and Refined
TypeScript. The relation between values (`i < xs.length`) stays in the
contract; the sort is in the type.

## Two routes

**A. Sugar for the clause, at listed positions.** `i: SafeInt` at a
parameter elaborates to `@requires safeInteger(i)`, at a result to an
`@ensures`, at a field to a type invariant, in `SafeInt[]` to a quantified
clause. Each position needs its own elaboration; any other position is
refused. This is a list of supported cases standing for a property
([general statements](../../AGENTS.md#general-statements-no-lists-of-special-cases)):
the property is "a value of this type is a safe integer", wherever the
type is.

**B. A sort in the claim language (proposed).** `SafeInt` reads as a claim
whose numeric contents are the safe integers: a refinement of `number`'s
contents. Every position reads it as it reads any type, so it holds at a
parameter, a result, a field, an array's elements, a union's arm, a generic
argument, and in a `Map`'s values, with no position named:

- **Reading**: where a value at type `SafeInt` is read into a slot, the
  slot gets the index fact $`\mathrm{int}(x)`$, as a guard's answer gives a
  fact today. The two meet in one place: the claim states the sort, the
  index facts state integers, and reading converts the first to the second.
- **Producing**: where a value is produced at type `SafeInt` (an argument,
  a return, a field write, an element write), the obligation is the
  claim's: subtyping from `number` holds where $`\mathrm{int}(x)`$ is
  entailed at that point, from the index facts. A literal is its own proof.
- **Subtyping**: `SafeInt <: number`; `number <: SafeInt` only through the
  index fact.
- **Trust**: as for every type of an exported signature: a caller outside
  the analysed sources passes a value of the type
  ([trust surface](../DESIGN.md)).

## Ranges

`Nat` (`SafeInt` with $`0\le x`$) and index types bounded by a length
(`i < xs.length`) are refinements with a range. Ranges are linear facts,
which the claim language does not carry; they stay in clauses. Whether
`Nat` alone (a lower bound of 0, no other term) enters the claim language
is a question below.

## Cases

- Positive: `at(xs: number[], i: SafeInt)` with `@requires 0 <= i && i < xs.length`
  verifies; a function returning `SafeInt` read by a caller as an index;
  a record field `SafeInt` read as an index; `SafeInt[]` elements read as
  indices; a `Map<string, SafeInt>`'s value read as an index.
- Negative, unsafe under Node: returning `x / 2` at `SafeInt` with `x` odd,
  read as an index (`xs[0.5]` is `undefined`); writing `NaN` into a
  `SafeInt` field.
- A control: a `SafeInt` written by any other spelling than the
  declaration of `resolvable.d.ts` reads as `number`.

## Documentation

- ANNOTATIONS.md, "Types the verifier declares": `SafeInt`, its meaning and
  an example; `tests/docs.mts` checks the entry matches the readers.
- The papers name the sort $`\mathit{SafeInt}`$ as `SafeInt` names it.

## Questions for the reviews

1. Route B: does the claim language admit a contents refinement for
   numbers, and where does reading convert it to $`\mathrm{int}(x)`$ so that
   no second representation of the same fact arises?
2. Is `Nat` worth a sort (a lower bound alone), or do ranges stay in
   clauses only?
3. Does `SafeInt` change any existing program's verdict (a program that
   writes no `SafeInt` must be unaffected)?
4. Is the name right (`SafeInt` against `Int`, `Integer` or `int`), given
   `safeInteger(x)` in clauses and the paper's $`\mathit{SafeInt}`$?
