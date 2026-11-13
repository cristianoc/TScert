# Claim language and boundaries

Diagnostics display the types the verifier computed and the obligations that
failed, never trusted assertions. Source identity, claim identity, and proof checking remain separate.
There are two explicitly typed representations: the structural claim text a
diagnostic prints, which can state TypeScript shapes outside the calculus, and
the native graph the declaration document and the verifier use. Lifting a graph into
the text fails rather than erasing a requirement.

## Structural claim text

`tools/claim.mts` declares `ClaimType`, `Atom`, `Field`, `RecordAtom`, and
`FunctionAtom`; the source parser imports its `Atom`.
`decodeClaimType` checks fields recursively. `tools/claim-text.mts` supplies
`printType`, and `lift`, which reads a normalized claim into this encoding.
The printed text determines its type without a previous claim.

| Form | Meaning |
| --- | --- |
| `unknown`, `never` | Top and empty union |
| `boolean`, `null`, `undefined`, `string`, `number` | Primitive types |
| `true`, `false`, `"text"`, `3` | Literal types |
| `A \| B` | Union |
| `{ name: A, optional?: B }` | Required and optional fields |
| `{ "a,b": A }` | Quoted field name |
| `{ value: A = (B) }` | Storage invariant A and current-content assertion B |
| `(A, B) => C` | Ordered parameters and result; zero parameters and nested functions are allowed |
| `((A) => B) & { value: C }` | Combined invocation and field contract |
| `T` | A type parameter of the enclosing function or closure, by its source name |
| `<T>(arg0: T) => T` | A quantified callable; binders carry `extends A` when bounded, and its parameters are shown positionally |
| `() => T` | A callable over an enclosing type parameter, with no binders of its own |
| `T @{...}` | Explicit nondefault object metadata |

Arrow alternatives in a union are parenthesized. Nondefault metadata on an
arrow follows parentheses around the whole arrow, so it cannot attach to the
result by accident. Bare records have absent indexes and unknown call,
constructor and array modes; bare functions have unknown constructor and array
modes. For example:

```text
((boolean) => null) @{"construct":"absent"}
{ value: boolean } @{"call":"absent","indexes":{"string":"synthetic","number":"absent","symbol":"synthetic"}}
```

Metadata holds only the mode fields `call`, `construct`, `array` and
`indexes`, and `and` (a list of structural atoms for simultaneous
requirements). The printer writes every nondefault mode, including `and`.
An unknown shape is shown as its exact JSON. `(unavailable)` marks an atom
its writer could not express; it is not a type.

The text grammar is a claim language, not all TypeScript syntax. Syntactic
expressibility is distinct from verification support: optional or multiple
fields can be printed, and the source adapter supports its documented fragment.

A bare graph-label list such as `[5]` is not the claim language: its meaning
depends on the accompanying graph. `lift` reads a label list through its
table into structural text, to a depth bound (3 for a diagnostic); below the
top a union shows its first arms and `…`, a row the table's `names` lists is
shown by its name, and a label the table has no row for is shown as
`type n`.

## Native graph and term language

`tools/type-graph.mts` declares the complete native `Clause`, `Arrow`, `Row`, and
`TypeGraph` types, shared by the declaration document's readers and the
diagnostics. It mirrors
`PositiveNormalization.Clause` as serialized by `RequestJson.lean`. Both rows and
label lists denote unions; clauses retain all simultaneous field contracts and
all ordered arrow domains/results. Labels have no implicit meaning in a general
request graph.

`decodeGraph` validates every constructor, field, and reference of the exact
JSON syntax.

`tools/calculus.mts` similarly declares `Term`, `CallCode`, and `Tag`
against `Calculus.lean`. The wire writes a constructor as an object whose one
key names it; `decodeTerm` and `decodeTag` check that JSON exactly and build
values naming their constructor in `kind` beside its fields, which `showTerm`
and `showTag` print by cases. Terms retain native slot numbers so the printed
obligation matches the calculus; source names are shown alongside in its
context table.

`tools/control-flow.mts` declares the program graph over those terms —
`Target`, `Continuation`, and `ProgramNode` — against `ControlFlow.lean`. A node
names its successors and their slot maps explicitly, so the node in a failure
record is validated as program data rather than inferred from its expression;
`decodeNode` builds continuations the same way, named by `kind`.

## Obligations and consistency

`tools/diagnostic.mts` decodes the native failure record and
`tools/diagnostic-view.mts` presents it, printing its types in the structural
claim text; [OBLIGATION-DIAGNOSTICS](OBLIGATION-DIAGNOSTICS.md) owns the
record and [its presentation](OBLIGATION-DIAGNOSTICS.md#presentation).
TypeScript compilation (the `Front-end types` suite) checks these shared
declarations against source extraction and the diagnostic presentation.
