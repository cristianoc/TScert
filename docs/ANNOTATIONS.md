# Annotations

Every annotation TScert reads from a program, with one example each. Each
entry links to the document that owns its rules. An annotation runs no code:
the JavaScript is the same with and without it.

## Facts about values

JSDoc tags whose text is a clause of
[the clause language](ARITHMETIC.md#the-clause-language): `safeInteger(p)`,
linear comparisons over integers, paths `x.f` and lengths `p.length`, `&&`,
`||` and `!`, guards such as `p === null || …`, and a closing quantified atom
`forall i in xs: …`. [Where clauses are written](ARITHMETIC.md#the-clause-language)
lists what each tag may name.

### `@requires C`

On a function declaration, an arrow, a function expression, or the
statement binding one. A precondition: the body assumes it, and every call
establishes it. [Preconditions](ARITHMETIC.md#preconditions).

```ts
/** @requires safeInteger(i) && 0 <= i && i < xs.length */
function at(xs: number[], i: number): number {
  return xs[i]!;
}
```

A quantified atom states its body of every element:

```ts
/** @requires safeInteger(k) && 0 <= k && k < ends.length
 *  @requires forall i in ends: safeInteger(ends[i]) && 0 <= ends[i] && ends[i] < widths.length */
function widthAt(widths: number[], ends: number[], k: number): number {
  return widths[ends[k]!]!;
}
```

### `@ensures C`

On a synchronous module function declaration. A postcondition: the body
establishes it at each return, and each caller assumes it after the call;
`result` names the returned value.
[Postconditions](ARITHMETIC.md#postconditions).

```ts
/** @ensures result.length === 2 */
function pair(a: number, b: number): number[] {
  return [a, b];
}
```

### `@invariant C` on a type

On a type alias or an interface. A type invariant over `this`: it holds of
the parameters and results of module functions whose types name the type.
[Type invariants](ARITHMETIC.md#type-invariants).

```ts
/** @invariant this.starts.length === this.flags.length */
type Analysis = { starts: number[]; flags: boolean[] };
```

### `@representation T`

Beside an `@invariant`, on an opaque type: `T` is the record type the
invariant's paths read, which makes the type a sealed handle.
[Sealed handles](ARITHMETIC.md#type-invariants).

```ts
/** @invariant safeInteger(this.count) && this.widths.length === this.count
 *  @representation PreparedRep */
type Prepared = { readonly [brand]: true };
type PreparedRep = { widths: number[]; count: number };
```

### `@invariant C` before a loop

In the comment immediately before a `while`, `do` or `for` loop. A loop
invariant over the bindings in scope: every entry to the loop's head
establishes it, and the body assumes it.
[Loop invariants](ARITHMETIC.md#loop-invariants).

```ts
let j = 0;
/** @invariant safeInteger(i) && safeInteger(j) && 0 <= j && j <= 2 * i */
for (let i = 0; i < xs.length; i++) { s += xs[i]! * ys[j]!; j += 2; }
```

## Facts about fields

### `@stable`

On a required `readonly` field of a record type. The field holds the value
its object literal put there for the object's life, so a fact known through
it survives any call. [Records](POSITIVE-TYPES.md#records).

```ts
type Runs = {
  /** @stable */
  readonly openBrackets: number[];
};
```

## Types the verifier declares

Aliases of [`tools/resolvable.d.ts`](../tools/resolvable.d.ts), recognized
by the declaration TypeScript binds the name to.

### `Within<F, T>`

As a written signature's result type, or a type guard's promised type. The
call returns a `T` and changes previously allocated locations at most as `F`
allows; TypeScript reads it as `T`. The verifier certifies it from the
function's code. [Stated effects](SOURCE-ELABORATION.md#stated-effects).

```ts
function count(xs: readonly number[]): Within<{ value: "keep"; store: "keep" }, number> {
  return xs.length;
}
```

### `Footprint`

The bound of `Within`'s `F`, written in place as a type literal:
`value` (`"keep"`, `"init"`, `"scalar"` or `"any"`) bounds changes to
locations holding a value, `store` (`"keep"`, `"grow"` or `"any"`) changes
to array stores, and `onThrow: true` makes the bound hold on a throw too.
[Stated effects](SOURCE-ELABORATION.md#stated-effects).

```ts
function evens(n: number): Within<{ value: "any"; store: "grow" }, number[]> {
  const out: number[] = [];
  for (let i = 0; i < n; i += 2) out.push(i);
  return out;
}
```

### `Resolvable`

As a type parameter's bound, `T extends Resolvable`, on the program's own
generic functions: `T` owns an observation and a result, as `Awaited<T>`
implies. [Implied bounds](SOURCE-CONTRACTS.md#implied-bounds).

```ts
async function settle<T extends Resolvable>(value: T): Promise<Awaited<T>> {
  return await value;
}
```

### `Awaitable`

As a type parameter's bound, `T extends Awaitable`, on the program's own
function declarations: `T` owns an observation, what `await` on it yields.
[Implied bounds](SOURCE-CONTRACTS.md#implied-bounds).

```ts
async function log<T extends Awaitable>(value: T): Promise<void> {
  await value;
}
```

## What is inferred, and where an annotation is required

TScert infers the types of locals and of functions written as arguments,
the effect of every function whose body it checks, and the integer facts a
body's own tests and writes establish. An annotation it reads on such a
body states a contract, and the body's check proves it.

An annotation is required at a unit's boundary: each function declaration,
class member and function a module binding holds states its parameters' and
result's types ([modules and code units](SOURCE-CONTRACTS.md#modules-and-code-units),
[refusals](SOURCE-FRAGMENT.md)). A fact crosses a function boundary only
as a clause: `@requires` and `@invariant` for what a body assumes, `@ensures`
and `@invariant` for what a caller learns, `Within` for what a callback or
function value may change.
