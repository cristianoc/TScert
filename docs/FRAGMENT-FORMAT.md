# Fragment source format

Fragment is the source syntax exchanged between the TypeScript parser, the
OCaml claim producer and Lean. It carries expressions, statements, annotations
and source identities. Execution plans specify their evaluation order;
SourceClaims supplies proposed types at points in those plans.

This document owns the source wire format's conventions and its document
fields. The constructor union, with every constructor's fields and its
evaluation order, is declared and commented in
[fragment.mts](../tools/fragment.mts), which this document does not repeat.
[Source elaboration](SOURCE-ELABORATION.md) states how source operations are
justified by calculus rules; [source contracts](SOURCE-CONTRACTS.md)
interprets declarations and annotations. [SOURCE-CLAIMS](SOURCE-CLAIMS.md)
owns the execution-plan and claim formats, and
[REQUEST-PROTOCOL](REQUEST-PROTOCOL.md) owns extracted calculus requests and
their certificates. [The fragment boundary](SOURCE-FRAGMENT.md) lists source
restrictions.

## Source mode

The document (`Ast` in `fragment.mts`) has these fields:

| Field          | Meaning                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       |
| -------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `file`         | Source file identity used by the claims and verification request.                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| `sourceSha256` | Digest of the source text parsed to obtain this document.                                                                                                                                                                                                                                                                                                                                                                                                                                                     |
| `declarations` | Resolved source type declarations and their dependencies, in the declaration-document format.                                                                                                                                                                                                                                                                                                                                                                                                                 |
| `init`         | Module-initialization statements, in source order, run once after the function declarations exist.                                                                                                                                                                                                                                                                                                                                                                                                           |
| `functions`    | Function definitions to check.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| `modules`      | The program modules [certified imports](SOURCE-CONTRACTS.md#certified-imports) may read, each once: `location`, the module identity its declarations carry, and `sourceSha256`, the digest of the bytes lowered (its artifact), with its `declarations`, `init` and `functions` as a file's, and `absent`, each function it could not lower as `name`, `namePos` and the parser's `reason`. A module is listed only where no code of it, lowered or absent, writes the binding of one of its function declarations. The verifier reads each apart from the document: a document decoded as a file's has an empty `modules`. |

A function (`FunctionAst`) has these fields:

| Field        | Meaning                                                                                                                                                                                                                                                                                                                                   |
| ------------ | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `name`       | The declared name.                                                                                                                                                                                                                                                                                                                        |
| `namePos`    | The name's span.                                                                                                                                                                                                                                                                                                                          |
| `typeParams` | Type parameters, each `name`, `bound` (`null` when absent) and `resolution`: `null`, or `{"observation": o, "result": r}` for a qualified parameter ([implied bounds](SOURCE-CONTRACTS.md#implied-bounds)), distinct nonempty names the parameter owns, `r` `null` for an observation-qualified one. No two owned names in one signature coincide. [ResolutionWire.lean](../lean/Verification/Source/ResolutionWire.lean) decodes it (`Slots`) and checks the ownership (`validateOwnership`). |
| `params`     | Parameters, each `name`, `pos` and `type`, with `rest: true` for a rest parameter.                                                                                                                                                                                                                                                        |
| `retType`    | The result annotation; for a guard, its plain result, `boolean` or `void`.                                                                                                                                                                                                                                                               |
| `guard`      | `null`, or the promise of a result annotation `x is T` or `asserts x is T`: `param`, the parameter's position among the actuals, `asserts`, `type` (`T`) and `span`.                                                                                                                                                                     |
| `stated`     | `null`, or the effect the result annotation states, `Within<F, T>` ([stated effects](SOURCE-ELABORATION.md#stated-effects)), of which `retType` is `T`: `footprint`, a closed footprint other than `{value: any, store: any}`, and `onThrow`. The unit's claim lies within it.                                                                 |
| `completion` | `sync`, or `async` for a definition with its own `async` modifier, whose footprint is then [`top`](FOOTPRINTS.md#the-checked-callback-contract).                                                                                                                                                                                            |
| `body`       | The statements.                                                                                                                                                                                                                                                                                                                           |
| `strict`     | Whether the function's code is strict; a sloppy call converts a receiver that is not an object.                                                                                                                                                                                                                                          |

Annotations are source type terms; their declaration references name the
declaration resolved by TypeScript.

## Conventions

A span is the half-open pair `[start,end]` of offsets in UTF-16 code units.
Expression and statement objects use `k` to identify their constructor and
`pos` for their span. Binding identifiers also have their own source spans.
These identities locate obligations and associate claims with source syntax;
the execution point distinguishes repeated uses of one source span in a plan.

[declaration-types.mts](../tools/declaration-types.mts) declares source type
terms, declaration documents and property keys. A property key is a string or
`{"symbol":i}`, where `i` identifies a unique-symbol declaration in the
declaration document. A symbol key is distinct from every string key.

Names no source identifier spells carry the lowering's own bindings: an
optional chain's saved receiver (`CHAIN`, `?.`), a parameter pattern's hidden
parameter name, and the intrinsics (`intrinsics.mts`) that stand for `await`,
an async body's returns, iteration steps and `slice` rests.

The parser [fragment-parse.mts](../tools/fragment-parse.mts) writes these
forms; Lean's [Fragment decoder](../lean/Verification/Source/Fragment.lean)
checks their shapes. The [field-name check](../tests/json-field-names.mts)
compares wire readers and writers. It checks spelling agreement, not
preservation of source semantics.

## Statements and bindings

`const` and `let` statements carry a `bindings` array (`BindingAst`): `name`,
`namePos`, `annot` (a source type term or `null`), `init`, and `early`, which
marks a binding a mention may reach before its initialization
([lexical bindings before initialization](SOURCE-ELABORATION.md#lexical-bindings-before-initialization)),
a cell allocated where its block is entered. Initializers run in binding
order, so an initializer sees earlier bindings of the same declaration. A
`destructure` statement binds a pattern (`PatternAst`) from its initializer.

Source functions and block-bodied closures contain statement lists.
Parameter patterns and defaults are entry statements over hidden parameter
names. A `blockBody` expression is the wrapper used for a closure's statement
body. The
[binding rules](SOURCE-ELABORATION.md#parameter-initialization-order) specify
the required initialization order and available names.

## Objects, cells and annotations

A mutable binding's storage contract is fixed for its allocated lifetime.
For an annotated binding, the annotation supplies that contract. For an
unannotated binding, the producer supplies a declaration contract keyed by its
initializer span and name, which Lean checks against initialization and
writes. Point-entry claims describe current contents within that contract.
The [source elaboration rules](SOURCE-ELABORATION.md#mutable-bindings-and-module-constants)
own the translation of `assign` and the field writes, and their obligations.
A source span alone is insufficient to identify a point-specific contents
claim.

Expression annotations and proposed claim types have different encodings.
Fragment annotations are source type terms. Bounded record atoms in claims
state read and write permissions; their encoding and invariant-arm absorption
law belong to [SOURCE-CLAIMS](SOURCE-CLAIMS.md#record-alternative-absorption).
An unsupported operand or union arm is refused, never discarded. The decoder
checks the complete contract before elaboration can use it.

## Expression closures and calls

A `lambda`'s `result` is a source annotation or `null`; an absent annotation
leaves the result type to a checked producer proposal, and `guard` carries a
guard's promise as a function's does, `stated` its result annotation's
statement, which a signature its code is checked at covers over the
annotation's whole domain, and `completion` its completion kind as a
function's does. Its `receiver` is `null` for an arrow or
`{type,strict}` for an ordinary function.

The call constructors (`apply`, `invoke`, `new`, `callWithReceiver`,
`bindWithReceiver`, `applyWithReceiver`) keep their operands distinct in the
tree. Lean's execution plans save their values in source evaluation order
before performing the invocation. Closure bodies have their own checked graphs
and capture interfaces. A class value is `ctor`: its constructor lambda as
construct-only code and its static fields.

### Receivers

A method call saves its object and the method read before evaluating its
arguments. The saved object supplies the invocation receiver. A copied method
is a callable value, whose plain call supplies the plain-call receiver.

An ordinary function binds `this` from its receiver; an arrow captures the
enclosing `this`. Strictness and source restrictions on the standard `call`,
`apply` and `bind` operations are part of the parser boundary. The
[source closure rules](SOURCE-ELABORATION.md#source-closures-and-their-annotations)
state how receiver contracts enter checking.

### Tests

Comparison and guard expressions retain their operands and source spans:
equality (`bin`), `typeofTest`, `arrayTest`, `inTest`, `instanceTest`, and
`tagMember`, a family guard's call
([a guard on any argument](HOST-FAMILIES.md#a-guard-on-any-argument)). The
execution plan evaluates their operands and selects the control-flow edge.
The exported expression claim and each destination's entry claim are
independently checked. An observation justifies only the refinements
supported by the corresponding rule; a producer claim cannot establish a test
result.

## Verification boundary

The [source commands](REQUEST-PROTOCOL.md#run-the-verifier) consume Fragment,
SourceClaims and evidence. Lean reconstructs execution plans and extracted
requests from the supplied syntax and claims. Source identity, declaration
dependencies, claim sites, inputs, outputs and required obligations are checked
before acceptance.

The acceptance theorem proves safety of the extracted calculus programs under
their input contracts. Faithful parsing, source evaluation order and the
interpretation of external declarations remain the review obligations named
in [the trust surface](DESIGN.md#trust-surface). A well-formed Fragment document
alone establishes neither source correspondence nor program safety.
