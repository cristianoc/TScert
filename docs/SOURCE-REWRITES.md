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

### A key tested with `in` on an open record

The gate's answers for a node (`staticType`, `contextualParam`,
`assignTypes`, `computedType`, `blockType`, `completion`, `symbolName` of
`tools/declaration-graph.mts`) were each a result or `{ refused: string }`,
read with `if (inferred && "refused" in inferred) gate.fail(node,
inferred.refused)`. After the test the result arm stays possible: an open
record may own `refused` at any type, so reading `inferred.refused` as a
string is refused on principle (`invalid-in-open`,
`invalid-in-open-closure`).

- **Rewrite:** every answer is one shape, `Answered<T>`, `{ ok: true; value:
  T } | { ok: false; refused: string }`, produced and read by its `ok` tag.
- **Pattern:** an `in` test that stands for a tag becomes a tag.
- **Commit:** this entry's commit (`tools/declaration-graph.mts`,
  `fragment-parse.mts`, `fragment-expressions.mts`, `fragment-classes.mts`).

## Rewrites required, not made

### An index read whose range a check elsewhere establishes

`Object.assign`'s callable form reads `const initial = node.arguments[1]`
and tests `ts.isObjectLiteralExpression(initial)`
(`tools/fragment-expressions.mts`); `callableAssign` (`fragment-support.mts`)
reads `node.arguments[0]` and `[1]` after `node.arguments.length === 2`.
TypeScript types an index read at the element type; at run time a read past
the end gives `undefined`, so TScert reads it at `Expression | undefined`.
A compiler-API guard's promise holds on its domain, the family's nodes
([the domain obligation](HOST-FAMILIES.md#calls)), so the guard narrows
nothing for an argument that may be `undefined`, and the read
`initial.properties` after it is refused ("missing field properties"). The
length test that makes the read in range is in another function, an
implicit correlation. It blocks `fragment-expressions.mts#expr` and
`#binary` ([measurement](../WORK.md#census-answered-tag)).

- **Rewrite to make:** the check returns what it establishes:
  `callableAssign` returns the arrow and the object literal it tested, or
  null, and its callers read those.
- **Pattern:** a value whose presence another function checks becomes that
  function's result.

## Changes for a tool's defect

### The compiler API's empty-tuple panic

TypeScript 7.0.2's API panics writing a union that holds an empty array
literal's tuple type (fixed upstream in 7.1). `forInEntryReads` destructured
`ts.isVariableStatement(s) ? s.declarationList.declarations : []`, so every
slice including it ended in that tool failure.

- **Change:** read the first declaration by index, forming no empty tuple.
- **Commit:** f704fdb (`tools/fragment-support.mts`).
