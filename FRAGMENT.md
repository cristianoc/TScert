# Fragment source format

Fragment is the source syntax exchanged between the TypeScript parser, the
OCaml claim producer and Lean. It carries expressions, statements, annotations
and source identities. Execution plans specify their evaluation order;
SourceClaims supplies proposed types at points in those plans.

This document owns the source wire format. [Source elaboration](SOURCE-ELABORATION.md)
states how source operations are justified by calculus rules;
[source contracts](SOURCE-CONTRACTS.md) interprets declarations and annotations.
[SOURCE-CLAIMS](SOURCE-CLAIMS.md) owns the execution-plan and claim formats,
and [REQUEST-PROTOCOL](REQUEST-PROTOCOL.md) owns extracted calculus requests
and their certificates. [The fragment boundary](SOURCE-FRAGMENT.md) lists
source restrictions.

## Source mode

The file object has these fields:

| Field | Meaning |
| --- | --- |
| `file` | Source file identity used by the claims and verification request. |
| `sourceSha256` | Digest of the source text parsed to obtain this document. |
| `declarations` | Resolved source type declarations and their dependencies, in the declaration-document format. |
| `init` | Module-initialization statements, in source order. |
| `functions` | Function definitions to check. |

Each function contains `name`, `namePos`, `typeParams`, `params`, `retType`
and `body`. A type parameter has `name`, `bound` and `resolution`, with `null`
for an absent bound. `resolution` is `null`, or
`{"observation": o, "result": r}` for a qualified parameter
([implied bounds](SOURCE-CONTRACTS.md#implied-bounds)): distinct names the
parameter owns, naming its observed payload and, for a resolution-qualified
parameter, its resolved result; `r` is `null` for an observation-qualified
one. No two owned names in one signature coincide. Each parameter has `name`, `pos` and `type`, with `rest: true` for a
rest parameter. Annotations are source type terms; their declaration references
name the declaration resolved by TypeScript.

A span is the half-open pair `[start,end]` of offsets in UTF-16 code units.
Expression and statement objects use `k` to identify their constructor and
`pos` for their span. Binding identifiers also have their own source spans.
These identities locate obligations and associate claims with source syntax;
the execution point distinguishes repeated uses of one source span in a plan.

The exact constructor union is declared in [fragment.mts](tools/fragment.mts).
[declaration-types.mts](tools/declaration-types.mts) declares source type terms,
declaration documents and property keys. A property key is a string or
`{"symbol":i}`, where `i` identifies a unique-symbol declaration in the
declaration document. A symbol key is distinct from every string key.

The parser [fragment-parse.mts](tools/fragment-parse.mts) writes these forms;
Lean's [Fragment decoder](lean/Verification/Source/Fragment.lean) checks their
shapes. The [field-name check](tests/json-field-names.mts) compares wire readers
and writers. It checks spelling agreement, not preservation of source semantics.

## Statements and bindings

`const` and `let` statements carry a `bindings` array. Each binding has
`name`, `namePos`, `annot` and `init`. The annotation is a source type term or
`null`. Initializers run in binding order, so an initializer sees earlier
bindings of the same declaration. A `destructure` statement carries `target`,
`default_` and `init`; its pattern names bindings, ordered object properties
or array positions, defaults and optional rest bindings.

The other statement constructors represent expression statements, return,
throw, conditional branches, loops, labeled blocks, break, continue, handlers
and finalizers. A `while` contains both `body` and `update`; a loop's continue
path executes that update before returning to the condition. A `try` contains
`body`, an optional `handler`, and an optional `finalizer`. A `closing`
statement represents iterator closing on exits requiring it.

Source functions and block-bodied closures contain statement lists. Parameter
patterns and defaults may be represented by entry statements over hidden
parameter names. A `blockBody` expression is the wrapper used for a closure's
statement body. The [binding rules](SOURCE-ELABORATION.md#parameter-initialization-order)
specify the required initialization order and available names.

## Record-contract export boundary

Object allocation uses `alloc` with an ordered `fields` array of `{name,e}`
entries. Object construction with spreads uses `build` with ordered field or
spread parts. A `read` carries `field` and `e`; an `index` carries `e` and `key`.
Their write counterparts retain the receiver, key where needed, and right-hand
side as separate operands. An `arrayLit` carries its ordered `elems`.

Expression annotations and proposed claim types have different encodings.
Fragment annotations are source type terms. Bounded record atoms in claims
state read and write permissions; their encoding and invariant-arm absorption
law belong to [SOURCE-CLAIMS](SOURCE-CLAIMS.md#record-alternative-absorption).
An unsupported operand or union arm must be refused, rather than discarded.
The decoder checks the complete contract before elaboration can use it.

## Cell source lowering

A mutable binding's storage contract is fixed for its allocated lifetime.
For an annotated binding, the annotation supplies that contract. For an
unannotated binding, the producer supplies a declaration contract keyed by its
initializer span and name, which Lean checks against initialization and writes.
Point-entry claims describe current contents within that contract.

A local assignment uses `{"k":"assign","pos":span,"name":name,
"namePos":span,"rhs":expression}`. The lowering evaluates the right-hand
side once, writes it into the binding's cell, and returns the saved value.
Field assignment similarly saves the receiver before evaluating the
right-hand side. The [source elaboration rules](SOURCE-ELABORATION.md#mutable-bindings-and-module-constants)
own the translation and its obligations. A source span alone is insufficient
to identify a point-specific contents claim.

## Expression closures and calls

A `lambda` carries `typeParams`, `params`, `receiver`, `result` and `body`.
Its `result` is a source annotation or `null`; an absent annotation leaves the
result type to a checked producer proposal. Each parameter has `name` and
`type`, with optional `default` and `rest` fields. A receiver is `null` for an
arrow or `{type,strict}` for an ordinary function. The `body` is an expression
or a `blockBody`.

| Constructor | Operands and additional fields |
| --- | --- |
| `apply` | `callee`, ordered `args`, optional spread indices `spreads`, optional `typeArgs`. |
| `invoke` | The same fields; `callee` is a property reference whose saved object supplies the receiver. |
| `new` | `callee`, ordered `args`, optional `typeArgs`. |
| `ctor` | Constructor `lambda`, with optional class `typeParams`. |
| `callWithReceiver` | `callee`, `receiver`, ordered `args`. |
| `bindWithReceiver` | `callee`, `receiver`, ordered saved-prefix `args`. |
| `applyWithReceiver` | `callee`, `receiver`, and `list`, or `null` for an omitted argument list. |

These operands remain distinct in the tree. Lean's execution plans save their
values in source evaluation order before performing the invocation. Closure
bodies have their own checked graphs and capture interfaces.

### Receivers

A method call saves its object and the method read before evaluating its
arguments. The saved object supplies the invocation receiver. A copied method
is a callable value, whose plain call supplies the plain-call receiver.

An ordinary function binds `this` from its receiver; an arrow captures the
enclosing `this`. The `this` expression has `k: "this"` and `pos`. Strictness
and source restrictions on the standard `call`, `apply` and `bind` operations
are part of the parser boundary. The [source closure rules](SOURCE-ELABORATION.md#source-closures-and-their-annotations)
state how receiver contracts enter checking.

### Singleton comparisons

Comparison and guard expressions retain their operands and source spans.
The source constructors include equality (`bin`), `typeofTest`, `arrayTest`,
`inTest` and `instanceTest`. The execution plan evaluates their operands and
selects the control-flow edge. The exported expression claim and each
destination's entry claim are independently checked. An observation justifies
only the refinements supported by the corresponding rule; a producer claim
cannot establish a test result.

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
