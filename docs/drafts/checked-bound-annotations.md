# Draft: checked bound annotations

The design of the written contracts for integer facts that
[the clause language](../ARITHMETIC.md#the-clause-language) does not admit:
entry values of paths, named predicates, an invariant a builder opens, and
contracts on signatures, captures and parameters the built forms leave
out. It answers [TScert #104](../REFERENCES.md#tscert-104)'s decision P,
the interprocedural preconditions. Claims are labelled **proved** (with the
Lean name), **cited** (with the document and its scope), **observed** (a
run under Node, with its version and date) or **conjectured**; every Lean
name this draft gives without a location is a proposal.

## The existing mechanism this extends

**Cited.** [Arithmetic](../ARITHMETIC.md): a clause written as a JSDoc tag
elaborates to index facts, linear facts over value, length and path terms;
a [precondition](../ARITHMETIC.md#preconditions) is a signature's `pre`,
assumed by its code and established at each call (`call-requires`); a
[postcondition](../ARITHMETIC.md#postconditions) is its `ensures`, proved
at each return (`return-ensures`) and gained by callers (`call-ensures`); a
[type invariant](../ARITHMETIC.md#type-invariants) is a pair of them
attached by type; an ordinary arrow erases only a signature without a
precondition (`Effect.plain`). The forms below extend that language and
those obligations.

## 1. Forms of the language

### 1.1 Where clauses are written

**Conjectured.** Beyond the built tags:

| Tag | Written on | Binds |
| --- | --- | --- |
| `@requires C` | a function type, or a method signature of an interface or a type literal | its parameters and `this` |
| `@ensures C` | a method, an arrow or a function expression bound to a `const` | its parameters, `this`, `result` and `old(…)` |
| `@opens x` | a signature with a body | removes the invariant requirement of parameter `x` (§1.4) |
| `@invariant C` | a class declaring a record type | `this`, the record |
| `@predicate name(x: T, …) C` | any declaration of the module | a named clause of the module, expanded where it is used |

An ensures is written only where Lean certifies the code that meets it; a
signature without a body (a function type, an interface method, a
`declare function`, an overload signature, an abstract method) states a
requires at most, which every value at that type must accept.

**Hook keys.** A requires on a member an implicit call can reach is
refused, since its implicit callers establish nothing. The closed list of
**hook keys** is the union of the admitted mechanisms that call one:
conversion hooks (`toString`, `valueOf`, `join`, `Symbol.toPrimitive`,
[prototype contracts](../SOURCE-CONTRACTS.md#prototype-contracts)); the
members of [the iterator protocol](../SOURCE-ELABORATION.md#the-iterator-protocol)
(`Symbol.iterator`, `Symbol.asyncIterator`, `next`, `return`, `throw`);
`then` ([objects owning `then`](../SOURCE-CONTRACTS.md#objects-owning-then));
`toJSON` ([`JSON` and `Error`](../SOURCE-CONTRACTS.md#json-and-error));
`Symbol.hasInstance` ([imported classes and `instanceof`](../SOURCE-CONTRACTS.md#imported-classes-and-instanceof));
and `constructor` and `Symbol.species` as the properties a species lookup
reads (a class's own constructor is no hook: `new` sites establish its
requires). Lean refuses, from the Fragment, a requires on every function
type at a hook key in the Fragment's types: a member with a body, an
interface method signature, and a record field holding a contracted
function value (`{ toString: f }`), so this refusal rests on no front-end
code. A mechanism admitting a new implicit call adds its key to the list.
**Observed.** With a requires on `toString` bounding `this.at`,
`` `${new Cursor([4.5], 1)}` `` is `"width undefined"`: the template
literal calls `toString` with nothing established.

### 1.2 Named predicates

**Conjectured.** A `@predicate` is a macro of its module, substituted
hygienically before anything else reads the clause: its own names are
renamed apart, so a parameter called `n` at the use site does not capture
its `n`. Another module sees only the expanded atoms; a cycle of
predicates is refused. Pretext's trims record needs four guarded atoms on
every signature that returns one:

```ts
/** @predicate trimLengths(r: HanKerningTrims, n: number)
 *    (r.widthTrims === null || r.widthTrims.length === n) &&
 *    (r.lineStartExtras === null || r.lineStartExtras.length === n) &&
 *    (r.lineEndTrims === null || r.lineEndTrims.length === n) &&
 *    (r.overflowLineEndTrims === null || r.overflowLineEndTrims.length === n)
 */
```

### 1.3 Entry values: `old`

**Conjectured.** `old(P)`, with `P` number-valued, is $`⟦P⟧(\rho_0,h_0)`$,
the path read in the call's entry heap. A number is immutable, so `old(P)`
names one number for the whole call and needs no snapshot of the heap: it
elaborates to a ghost slot bound by entry read links, which no node reads
and every edge keeps. `old` of an object, whose meaning needs the entry
heap's contents, is refused. An `old(P)` is admitted only where the whole
requires entails that every prefix of `P` is present at entry; a guarded
requires such as `x === null || safeInteger(x.n)` admits `x` null, so it
admits no `old(x.n)`. Two occurrences of one path name one ghost. A call
gains an ensures atom naming `old(P_i)` only where a caller slot is linked
to $`P_i`$ at the actuals after their evaluation. An append contract:

```ts
/** @requires safeInteger(from) && safeInteger(to) && 0 <= from && from <= to && to <= texts.length
 *  @requires widths.length + (to - from) <= 4294967295
 *  @ensures widths.length === old(widths.length) + to - from
 */
export function measureInto(widths: number[], texts: string[], from: number, to: number): void {
  const base = widths.length
  for (let mi = from, at = base; mi < to; mi++, at++) widths[at] = texts[mi]!.length
}
```

**Observed.** Written without `old`, `widths.length === to - from` is false
on `widths = [9]`, `from = 0`, `to = 2`: the length after the call is `3`.

### 1.4 Opening an invariant, and what names a record

**Conjectured.** A declared type **names** `T` also when it is
`Readonly<T>`, an interface extending `T` or a class implementing `T`, each
resolved by declaration identity through re-exports.

- `this` of a member at a hook key (§1.1) carries neither the requirement
  nor the ensures of $`\mathrm{inv}_T(\mathtt{this})`$, so a class with an
  invariant may have conversion hooks; an explicit call of such a member
  keeps the invariant's atom by the member's certified footprint, and a
  call by a native (a conversion, an iteration) by that native's callback
  effects; a constructor is under `@opens this`, ensuring the invariant
  without requiring it;
- `this` of any other method of a class or interface naming `T` is a
  parameter naming it;
- `@opens x` removes the requirement for `x` and keeps its ensures: an
  appending builder receives a record whose invariant may not hold, and
  establishes it before every normal return.

## 2. Obligations

### 2.1 Captures of a local closure

**Conjectured.** A captured binding reaches a closure's body as graph code
binds captures ([closures are graph code](../DESIGN.md#closures-are-graph-code)):
a `const` capture as a value, a mutable one as a cell. A local closure's
contract may name its captures only when the closure does not escape and
the captures it names are `const` bindings or parameters nothing assigns
([a `let` nothing assigns](../SOURCE-ELABORATION.md#a-let-nothing-assigns)).
A closure does not escape when it is bound by `const` and every use of its
binding is a direct call inside the unit; Lean checks this inventory from
the unit's graph. Its contract is then indexed by its capture environment:
the producer proposes a precondition and a postcondition over its
parameters and captures, Lean certifies its body from the first at the
return goal of the second, and each call establishes the precondition in
the caller's current knowledge, where the captured bindings are the
caller's own slots. A requirement over a capture is checked in the state
of each invocation. A closure that escapes has a contract over its
parameters only (`bounds-captured-precondition-gap`, pretext's local Han
kerning helpers).

**Observed.** The same body in a closure that escapes, `trimAdder(r, 0, 2)`,
after the caller sets `r.widthTrims = [0]`, reads `undefined` at index 1
and stores `NaN` there.

### 2.2 A defaulted parameter

**Conjectured.** A clause naming a defaulted parameter is checked after
parameter initialization in the body, and at each call that supplies the
parameter (`bounds-default-precondition-gap`, pretext's defaulted start
cursor).

### 2.3 Values not shown integral

**Conjectured.** A comparison with no arithmetic compares two numbers in
IEEE order, false where either is NaN: an order atom, for values the
clause does not state safe integers. On two safe integers an order atom
and a linear fact state the same thing, and a step converts one to the
other.

## 3. Cases and controls

**Conjectured.** Positive pipeline cases: an append contract with `old`; a
record invariant kept by a walker and established by a builder with
`@opens`; a module predicate expanded at two signatures; a non-escaping
closure with a capture contract; a defaulted cursor. Negative cases, each
run under Node with a concrete wrong value: an escaping closure called
after its captured record shrank; a requires at a hook key reached by a
template literal. Controls (`pipeline/test.mts`), bypassing the producer: a
ghost slot bound to another path, or to the path after a mutation; a
requires attached to a member at a hook key in a forged Fragment; a
non-escaping closure's capture contract with its binding passed as a
value; an ensures on a signature without a body.
