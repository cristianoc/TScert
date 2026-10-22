# Source rewrites

Changes made to TScert's own TypeScript so that it verifies, each with the
property of the original code that TScert cannot establish and the general
rewrite that removes it. Each entry is a small instance of an operation
TScert is meant to support in general: given code it refuses, propose the
rewrite that makes it sound, or show the behaviour the refusal guards
against.

A rewrite here never weakens a check or hides a behaviour: it either states
a type the code already relies on, adds the check a type promised, or makes
an implicit correlation explicit. A change made for a reason other than
soundness (a tool's defect) is listed apart. A rewrite that a fix of the
verifier would make unnecessary is not one: that fix goes to the verifier.

## Rewrites

### A guard that promises more than its body checks

`isRecordList(v): v is Record<string, unknown>[]` returned
`Array.isArray(v)`, and `isList(v): v is unknown[]` promised a writable
array of any elements. TypeScript does not check a guard's promise; TScert
does, and refuses it.

- **Rewrite:** the guard promises what its body establishes:
  `isList(v): v is readonly unknown[]`, and a reader checks each element
  where it reads it. A first rewrite, `Array.isArray(v) && v.every(isObject)`,
  was still unsound: `every` skips holes, so `new Array(1)` passed with an
  `undefined` element.
- **Pattern:** a type predicate's promise is narrowed to the body's tests,
  or the body gains the tests the promise needs, element by element where
  the promise is about elements.
- **Commits:** 4db5021, 54aa29f (`tools/claim-text.mts`, `tools/diagnostic-view.mts`).

### A dictionary guard over `unknown`

The readers of claims, type graphs and diagnostics took `unknown` and used
`typeof v === "object" && v !== null` as a guard for a dictionary. For an
arbitrary value that test admits class instances and host objects, so the
dictionary promise cannot be established, and every helper built on it was
refused.

- **Rewrite:** the readers take `JsonValue` (`null | boolean | number |
  string | readonly JsonValue[] | { readonly [key: string]: JsonValue }`),
  the type of what they actually read, over which the same tests decide
  the arms.
- **Pattern:** a value read as data is typed by the data's grammar at the
  boundary where it enters (`JSON.parse`, a decoder), not as `unknown`
  inspected by structural tests.
- **Commit:** 795f331 (`tools/calculus.mts`, `claim-text.mts`, `claim.mts`,
  `type-graph.mts`, `diagnostic-view.mts`).

### An annotation weaker than the value the code relies on

`bigintValue` took `unknown` and read a field after an `in` test on an open
object, which no rule admits; `readExplanations` read `JSON.parse`'s result
as `unknown` the same way.

- **Rewrite:** state the type the producer of the value guarantees: the
  synchronous API's bigint literal value (kept `unknown` where the API may
  leave it absent, and spelled only when it is a bigint), and `JSON.parse`'s
  result at a declared JSON type.
- **Pattern:** replace a test-and-read on an open object by the declared type
  of the value's source, where that source's contract states it.
- **Commits:** 2288e06, c76d588 (`tools/computed-types.mts`,
  `pipeline/verify-source.mts`).

### A gate method that reads nothing of the gate

`statements` found the first statement that always jumps with
`list.findIndex((s) => gate.abrupt(s))`, `Gate.abrupt` a field annotated
`typeof statements.abrupt`, and `abrupt` recursed through `gate.abrupt`.
The field's contract is its annotation, an ordinary arrow, which states no
effect ([calls through a location](SOURCE-MODEL.md#inferred-call-effects-elaboration-and-certification)):
a `Gate` whose `abrupt` shrinks the list through another reference is a
value of the type, so the callback is `findIndex`'s unrestricted one and
its element `Statement | undefined`. The code relied on the field holding
the module function, which no annotation states.

- **Rewrite:** `abrupt(s: Statement): boolean` is a module function
  recursing through its own binding, called as `abrupt(s)`; `Gate` holds no
  `abrupt` field. Its effect is certified from its body.
- **Pattern:** a function that needs nothing of the object it is reached
  through is called by its binding, whose certified signature a call reads;
  a call through a field reads the field's contract.
- **Commit:** the one adding this entry (`tools/fragment-statements.mts`,
  `tools/fragment-parse.mts`).

## Rewrites required, not made

### A key tested with `in` on an open record

`if (inferred && "refused" in inferred) gate.fail(node, inferred.refused)`
(`tools/fragment-expressions.mts`, `tools/fragment-classes.mts`), where
`inferred` is a result or `{ refused: string }` (in `fragment-expressions.mts`
`{ functionType; bagType } | { refused: string }`, in `fragment-classes.mts` a
type term or `{ refused: string }`). After the test, the result arm stays
possible: an open record may own `refused` at any
type, so reading `inferred.refused` as a string is refused on principle
(`invalid-in-open`, `invalid-in-open-closure`). It blocks the
`fragment-expressions.mts` slices (`expr`, `binary` and the functions
calling `expr`), measured 2026-10-22.

- **Rewrite to make:** a discriminant field on each arm (`kind: "refused"`
  and `kind: "inferred"`), tested instead of the key, so the test decides the
  arm whatever other fields a value carries.
- **Pattern:** an `in` test that stands for a tag becomes a tag.

## Changes for a tool's defect

### The compiler API's empty-tuple panic

TypeScript 7.0.2's API panics writing a union that holds an empty array
literal's tuple type (fixed upstream in 7.1). `forInEntryReads` destructured
`ts.isVariableStatement(s) ? s.declarationList.declarations : []`, so every
slice including it ended in that tool failure.

- **Change:** read the first declaration by index, forming no empty tuple.
- **Commit:** f704fdb (`tools/fragment-support.mts`).
