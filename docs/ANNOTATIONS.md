# Annotations

Every annotation TScert reads from a program, with one example each. Each
entry links to the document that owns its rules. An annotation runs no code:
the JavaScript is the same with and without it.

## Facts about values

JSDoc tags whose text is a clause of
[the clause language](ARITHMETIC.md#the-clause-language): `safeInteger(p)`,
linear comparisons over integers, paths `x.f`, lengths `p.length`, indexed
elements `p[q]` and their lengths `p[q].length`, `&&`,
`||` and `!`, guards such as `p === null || …`, `p !== null || …`, and
`p[q] === null || …` (testing `null`, `undefined`, `true`, or `false`), a closing quantified atom
`forall i in xs: …`, and `p !== q` of two arrays, whose spines differ. [Where clauses are written](ARITHMETIC.md#the-clause-language)
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

`p !== q` of two arrays states that their spines differ, so the body keeps
`flags`'s facts across a call whose frame changes the other's spine
([spine separation](ARITHMETIC.md#spine-separation)):

```ts
/** @requires flags !== runs.openBrackets */
function measure(flags: number[], runs: Runs): number { … }
```

An indexed-element clause bounds a term by a property or length of an array
element at another path's index
([indexed-element clauses](ARITHMETIC.md#indexed-element-clauses)):

```ts
/** @requires safeInteger(c.segmentIndex) && 0 <= c.segmentIndex && c.segmentIndex < h.advances.length
 *  @requires safeInteger(c.graphemeIndex) && 0 <= c.graphemeIndex
 *  @requires h.advances[c.segmentIndex] === null || c.graphemeIndex < h.advances[c.segmentIndex].length */
function startAdvance(h: Handle, c: Cursor): number {
  const advances = h.advances[c.segmentIndex];
  if (advances === undefined || advances === null) return 0;
  return advances[c.graphemeIndex]!;
}
```

### `@ensures C`

On a synchronous module function declaration. A postcondition: the body
establishes it at each return, and each caller assumes it after the call;
`result` names the returned value, and `old(P)` or `old(P.length)` the term
in the state the call started in, a term of a linear clause or a prefix
clause's bound.
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
`P` is a type literal: `values` (`"keep"`, `"init"`, `"scalar"`,
`"extend"`, `"grow"` or `"any"`) bounds changes to locations holding a
value, `spines` the same for array spines, `"extend"` appending fresh
cells at a spine's end, as `push` does, and `onThrow: true` makes the bound hold on a throw too;
`{}` states that nothing previously allocated changes. `P` may instead be
a type parameter in scope, `Modifies<E, T>`, which the verifier reads as
letting every location change, at every instance of `E`; an application
of an alias stating its parameter's frame admits there a type parameter
only ([arguments without type meaning](SOURCE-CONTRACTS.md#arguments-without-type-meaning)). On a function
declaration, `"x[*]": "any"` excepts the spine parameter `x` holds at the
call, and `"x.f[*]": "any"` the spine its `@stable` field `f` holds, which
may change arbitrarily; the declared type at the region's path is an
array type, each member an array, `null` or `undefined`. A field region
`"x.g": c` (or `"x.f.g": c`) lets the field `g` of the object `x` (or its
`@stable` field `f`) holds at the call change within the change `c`, and
`"x.*": c` (or `"x.f.*": c`) every field of it. TypeScript reads it as `T`; the
verifier certifies it from the function's code.
[Stated effects](SOURCE-ELABORATION.md#stated-effects).

```ts
function count(xs: readonly number[]): Modifies<{}, number> {
  return xs.length;
}

function evens(n: number): Modifies<{ values: "any"; spines: "grow" }, number[]> {
  const out: number[] = [];
  for (let i = 0; i < n; i += 2) out.push(i);
  return out;
}

function shrink(xs: number[]): Modifies<{ values: "any"; "xs[*]": "any" }, void> {
  xs.pop();
}

type Footprint = { [location: string]: "keep" | "init" | "scalar" | "extend" | "grow" | "any" };
type Visitor<E extends Footprint> = (i: number) => Modifies<E, void>;
function each<E extends Footprint>(n: number, visit: Visitor<E>): void {
  for (let i = 0; i < n; i++) visit(i);
}
const seen: number[] = [];
each<{ "seen[*]": "extend" }>(3, i => { seen.push(i); });
```

### `Fresh<T>`

As a written signature's result type, alone or as the `T` of `Modifies`: a
normal return's value holds an array spine the call allocated, so the
caller's facts about every other spine survive changes to it. TypeScript
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

### `SafeInt`

As a type, wherever a type is read: the safe integers, the numbers whose
value is an integer of magnitude at most $`2^{53}-1`$, both zeros included.
TypeScript reads it as `number`; the verifier reads it as the clause `int`
([the safe integers](POSITIVE-TYPES.md#the-safe-integers)), so a value
reaches it where its type is within the safe integers (a safe literal, a
value already typed `SafeInt`) or where the facts state it a safe integer
([a type from integrality](ARITHMETIC.md#linear-facts)): a sum under a
bound, an element of a `Uint8Array`, `Uint16Array` or `Int32Array`, a value
`Number.isSafeInteger` answered `true` of. A `SafeInt` is a `number`, and a
`number` is not a `SafeInt`. A computed type, a key type or a mapped type
reading it is refused ([the source fragment](SOURCE-FRAGMENT.md#model-limits)),
since TypeScript evaluates it reading `SafeInt` as `number`.

```ts
function keep(i: SafeInt): SafeInt {
  return i;
}

function answer(): SafeInt {
  return keep(42);
}

/** @requires 0 <= n && n < 100 */
function next(n: SafeInt): SafeInt {
  return keep(n + 1);
}
```

A `SafeInt` value is a safe integer in every fact the verifier reads of it
([integrality from a type](ARITHMETIC.md#linear-facts)), and a clause
compares a parameter, a binding a loop invariant names, a path or an
element whose type is `SafeInt` with no `safeInteger(...)`
([integrality](ARITHMETIC.md#the-clause-language)):

```ts
/** @requires 0 <= i && i < xs.length */
function at(xs: number[], i: SafeInt): number {
  return xs[i]!;
}
```

## Experimental effect-language annotations

Annotations read only by the experimental paper-rules prototype
([the mode's draft](drafts/paper-rules-mode.md),
[An effect language for TScert](drafts/effect-languages.md)) and declared in
a project's `paper.d.ts`. To the ordinary verifier their effect parameters
carry no type meaning ([arguments without type meaning](SOURCE-CONTRACTS.md#arguments-without-type-meaning)),
so they leave every ordinary verdict unchanged.

- **`AtMost<P>`**: as an effect type parameter's constraint,
  `<E extends AtMost<P>>`, bounds the effect variable `E` by the effect
  literal `P` (with explicit `else` and declared-reach keys `"x.**"`).
- **`Effects<P, T>`**: as a function declaration's return type (or as the `T`
  of `Modifies<OrdP, Effects<P, T>>`), states the function's paper-language
  effect `P` (including confined module-private state `"@state": c`), checked
  against the function's body and its module's confinement obligations
  (`OwnerConfined`).
- **`Join<E, P>`**: as a call's effect type argument, `f<Join<E, P>>(…)`,
  forwards an enclosing effect variable `E` joined pointwise with a closed
  anchored effect `P` (such as `Join<E, { "@state": "any" }>`), checked by
  showing both `E`'s bound and `P` lie within the callee's bound and the
  callback's extra steps lie within `P`.
- **`"@state"`**: as a region key in `Effects<P, T>`, `Join<E, P>`, or a
  call's effect instance (`{ "@state": "any" }`), denotes the confined
  module-private state of the defining module and its confined callees
  (unexported `let` cells never mutated through, and unexported freshly
  initialized containers that never escape and whose mutated nested interiors
  are freshly acquired and never escape). By boundary closure
  (`Confinement.ClosedOut`), `"@state"` is disjoint from every external root
  region and declared reach `"x.**"`.

```ts
let cached: Config | null = null;
export function getConfig(): Modifies<{ values: "init" }, Effects<{ "@state": "any" }, Config>> {
  return cached ??= buildConfig();
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
  `<T,>(x: T): Modifies<{ values: "keep"; spines: "keep" }, T> => x`.
- **Dense presence of an array that is no tuple**: a result with no hole
  (`Dense<number[]>`).
- **A record's exact own keys**: a spread or an absent key's read
  continuing at the prototype (`Exact<{ a: number }>`).
- **Facts over a binding a closure captures before its initialization**:
  `0 <= count` for a `count` declared after the closure.
- **A frame depending on a callback**: a wrapper that changes what its
  callback `f` changes, and nothing else.
