# Annotations

Every annotation TScert reads from a program, with one example each. Each
entry links to the document that owns its rules. An annotation runs no code:
the JavaScript is the same with and without it.

## Facts about values

JSDoc tags whose text is a clause of
[the clause language](ARITHMETIC.md#the-clause-language): `safeInteger(p)`,
linear comparisons over integers, paths `x.f` and lengths `p.length`, `&&`,
`||` and `!`, guards such as `p === null || …`, a closing quantified atom
`forall i in xs: …`, and `p !== q` of two arrays, whose stores differ. [Where clauses are written](ARITHMETIC.md#the-clause-language)
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

`p !== q` of two arrays states that their stores differ, so the body keeps
`flags`'s facts across a call whose frame changes the other's store
([store separation](ARITHMETIC.md#store-separation)):

```ts
/** @requires flags !== runs.openBrackets */
function measure(flags: number[], runs: Runs): number { … }
```

### `@ensures C`

On a synchronous module function declaration. A postcondition: the body
establishes it at each return, and each caller assumes it after the call;
`result` names the returned value, and `old(P)` or `old(P.length)` the term
in the state the call started in.
[Postconditions](ARITHMETIC.md#postconditions),
[two-state postconditions](ARITHMETIC.md#two-state-postconditions).

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

### `Modifies<P, T>`

As a written signature's result type, or a type guard's promised type. The
call returns a `T`; on a normal return every previously allocated location
keeps its contents but those `P` names, each changed at most as `P` says.
`P` is a type literal: `values` (`"keep"`, `"init"`, `"scalar"`, `"grow"`
or `"any"`) bounds changes to locations holding a value, `stores` the same
for array stores, and `onThrow: true` makes the bound hold on a throw too;
`{}` states that nothing previously allocated changes. On a function
declaration, `"x[*]": "any"` excepts the store parameter `x` holds at the
call, and `"x.f[*]": "any"` the store its `@stable` field `f` holds, which
may change arbitrarily. TypeScript reads it as `T`; the
verifier certifies it from the function's code.
[Stated effects](SOURCE-ELABORATION.md#stated-effects).

```ts
function count(xs: readonly number[]): Modifies<{}, number> {
  return xs.length;
}

function evens(n: number): Modifies<{ values: "any"; stores: "grow" }, number[]> {
  const out: number[] = [];
  for (let i = 0; i < n; i += 2) out.push(i);
  return out;
}

function shrink(xs: number[]): Modifies<{ values: "any"; "xs[*]": "any" }, void> {
  xs.pop();
}
```

### `Fresh<T>`

As a written signature's result type, alone or as the `T` of `Modifies`: a
normal return's value holds an array store the call allocated, so the
caller's facts about every other store survive changes to it. TypeScript
reads it as `T`; the verifier certifies it from the function's code.
[Stated effects](SOURCE-ELABORATION.md#stated-effects).

```ts
function copy(xs: readonly number[]): Fresh<number[]> {
  return xs.slice();
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
and `@invariant` for what a caller learns, `Modifies` for what a callback or
function value may change, `Fresh` for a result the call allocated.

## What is inferred and has no written form

Each of these is a claim TScert infers inside a body that no annotation
states. The spelling beside each is a proposal, read by no reader.

- **A narrowed binding's type at a statement**: after
  `if (node.kind === K.Element)`, `node`'s type there
  (`/** @assert node: Element */`).
- **A field's current contents at a statement**: after
  `if (o.next !== null)`, `o.next`'s type there
  (`/** @assert o.next: Node */`).
- **An integer fact at a statement other than function entry or a loop
  head**: `i < xs.length` after an `if` or `switch` join
  (`/** @assert i < xs.length */`).
- **Region separation at a loop head or statement**: two locally
  allocated arrays sharing no element cell (`/** @invariant apart(out, src) */`).
- **The frame of an overloaded declaration**, one `Modifies` per overload.
- **The frame of a generic closure or method**:
  `<T,>(x: T): Modifies<{ values: "keep"; stores: "keep" }, T> => x`.
- **Dense presence of an array that is no tuple**: a result with no hole
  (`Dense<number[]>`).
- **A record's exact own keys**: a spread or an absent key's read
  continuing at the prototype (`Exact<{ a: number }>`).
- **Facts over a binding a closure captures before its initialization**:
  `0 <= count` for a `count` declared after the closure.
- **A frame depending on a callback**: a wrapper that changes what its
  callback `f` changes, and nothing else.
