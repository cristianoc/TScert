# Fragment source format

Fragment is the source syntax the TypeScript parser writes and Lean reads. It
carries expressions, statements, annotations and source identities. Execution
plans specify their evaluation order; Lean computes the types at points in
those plans and checks them.

This document owns the source wire format's conventions and its document
fields. The constructor union, with every constructor's fields and its
evaluation order, is declared and commented in
[fragment.mts](../tools/fragment.mts), which this document does not repeat.
[Source elaboration](SOURCE-ELABORATION.md) states how source operations are
justified by calculus rules; [source contracts](SOURCE-CONTRACTS.md)
interprets declarations and annotations. [SOURCE-CLAIMS](SOURCE-CLAIMS.md)
owns the execution-plan and claim formats, and
[REQUEST-PROTOCOL](REQUEST-PROTOCOL.md) owns elaborated calculus requests. [The fragment boundary](SOURCE-FRAGMENT.md) lists source
restrictions.

## Source mode

The document (`Ast` in `fragment.mts`) has these fields:

| Field          | Meaning                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       |
| -------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `file`         | Source file identity used by the verification request.                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| `sourceSha256` | Digest of the source text parsed to obtain this document.                                                                                                                                                                                                                                                                                                                                                                                                                                                     |
| `declarations` | Resolved source type declarations and their dependencies, in the declaration-document format.                                                                                                                                                                                                                                                                                                                                                                                                                 |
| `init`         | Module-initialization statements, in source order, run once after the function declarations exist.                                                                                                                                                                                                                                                                                                                                                                                                           |
| `functions`    | Function definitions to check.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| `components`   | The family of components the file's code lies in and the [read-only frame](drafts/readonly-handles.md)'s proposals about it (`ComponentsAst`): the checked file's package, where the nearest `package.json` above it in its project states `exports` and one of the builds those exports name compiles it (its code those builds' files, else every source of the project in its directory), each module of that code and each class body, laminar by `parent`; each one's interface, its entries by module and span, or the reason it is unknown; each code's innermost component, the tag its frames carry; each code's closure site and its parameters', receiver's and result's values; each allocation site with its kind, its keys, its contents' value and its mark for each enclosing component; each value of the flow with its possible sites, the components it may enter from outside, at a writable position or reached read-only from a crossing in at a read-only type, and what the code's statements make it include; each crossing with its direction, the position owning its type and whether that type is read-only throughout, a bit the verifier derives from the shape of the position's declared type (a code's parameters and result, an exported binding, an argument of a callee of declared parameter types, and the family's named types a shape names, `types`) and refuses where they differ; the code's events, each at its module and span: its stores (receiver, key, stored value, whether an initial value), its calls (callee, receiver, arguments, result, the codes they may run, a `new`'s instance, a native's values, whether it is a method of the standard library's (of its arrays, or of another interface on the family's own storage with no key of its name, which the verifier checks), whether that member's reviewed contract states a fresh result and whether its result is an array of primitives; and, of a call TypeScript resolves to a standard library method a reviewed overlay entry states, which arguments it may call: one the reviewed declaration types a function or on which the entry states the host runs code, and one spread), its throws and catches, the bindings a module or a closure holds, the bindings a module exports, and the value of every thrown value; each `await`, `yield`, async function and generator; each code that escapes, and how; each exported type's client obligation (`@clients`, else read-only) as a frame over `this`; each type invariant, a candidate of the guarantee, as index facts of `this`; and each component's proposed protocol, a change at each part it lists (the fields of a site or of outside storage at a key or every key, their spines, their cells), `keep` at every other, which the verifier checks against every write of the component's code. At each call of code outside a component, a proposed frame: for each region of the storage a value or a site may be (a record's fields at a key or every key, an array's spine, its cells), the parts its locations may have by site (or outside storage) and whether its released and outside locations are protected, which the verifier checks against the flow. Every field is required, every index in range, each component nested as its kind is (`ComponentWire.decode`); an imported module's document is read with the empty family. The read-only frame's checks (S), (K) and (O) read it (`ComponentChecks`), each component's outcome printed beside the units' verdicts, which do not read it. |
| `omittedMentions` | The names that code the lowering leaves out mentions, sorted: each function a census omits, whole, and each statement it leaves out; empty without omissions. A module cell named here is not [the module's own object](PROGRAM-TYPING.md#key-adding-writes). |
| `modules`      | The program modules [certified imports](SOURCE-CONTRACTS.md#certified-imports) may read, each once: `location`, the module identity its declarations carry, and `sourceSha256`, the digest of the bytes lowered (its artifact), with its `declarations`, `init` and `functions` as a file's, and `absent`, each function it could not lower as `name`, `namePos` and the parser's `reason`; no function of `functions` and no code of `init` reads an absent function. A module is listed only where no code of it, lowered or absent, writes the binding of one of its function declarations. The verifier reads each apart from the document: a document decoded as a file's has an empty `modules`. |

A function (`FunctionAst`) has these fields:

| Field        | Meaning                                                                                                                                                                                                                                                                                                                                   |
| ------------ | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `name`       | The declared name.                                                                                                                                                                                                                                                                                                                        |
| `namePos`    | The name's span.                                                                                                                                                                                                                                                                                                                          |
| `typeParams` | Type parameters, each `name`, `bound` (`null` when absent) and `resolution`: `null`, or `{"observation": o, "result": r}` for a qualified parameter ([implied bounds](SOURCE-CONTRACTS.md#implied-bounds)), distinct nonempty names the parameter owns, `r` `null` for an observation-qualified one. No two owned names in one signature coincide. [ResolutionWire.lean](../lean/Verification/Source/ResolutionWire.lean) decodes it (`Slots`) and checks the ownership (`validateOwnership`). |
| `params`     | Parameters, each `name`, `pos` and `type`, with `rest: true` for a rest parameter.                                                                                                                                                                                                                                                        |
| `retType`    | The result annotation; for a guard, its plain result, `boolean` or `void`.                                                                                                                                                                                                                                                               |
| `guard`      | `null`, or the promise of a result annotation `x is T` or `asserts x is T`: `param`, the parameter's position among the actuals, `asserts`, `type` (`T`) and `span`.                                                                                                                                                                     |
| `stated`     | `null`, or the effect the result annotation states, `Modifies<P, T>` ([stated effects](SOURCE-ELABORATION.md#stated-effects)), of which `retType` is `T`, as its exits ([the serialized effect](REQUEST-PROTOCOL.md#the-serialized-effect)): on a normal return a closed frame with the spines the call positions select through fields at the call's entry at `any` (`"x[*]": "any"`, `"x.f[*]": "any"`) and a fresh result spine (`Fresh<T>`), on a throw the same frame (`onThrow`) or `⊤`; the closed frame is below `⊤` or the result is fresh; with spine regions, the result is not fresh. The unit's claim lies within it where it states no spine region; otherwise the unit's regional check establishes it.                                                                  |
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
unannotated binding, the walk
([Synthesis.lean](../lean/Verification/Source/Synthesis.lean))
computes a declaration contract keyed by its initializer span and name: the
initializer's type widened as TypeScript widens a `let`, grown in at most four
rounds where its writes need more. Lean checks it against initialization and
writes. The types at a point's entry describe current contents within that
contract.
The [source elaboration rules](SOURCE-ELABORATION.md#mutable-bindings-and-module-constants)
own the translation of `assign` and the field writes, and their obligations.
A source span alone is insufficient to identify a point-specific contents
type.

Expression annotations and the types Lean states at points have different
encodings. Fragment annotations are source type terms. Bounded record atoms in
those types
state read and write permissions; their encoding and invariant-arm absorption
law belong to [SOURCE-CLAIMS](SOURCE-CLAIMS.md#record-alternative-absorption).
An unsupported operand or union arm is refused, never discarded. The decoder
checks the complete contract before elaboration can use it.

## Expression closures and calls

A `lambda`'s `result` is a source annotation or `null`; an absent annotation
leaves the result type to the type the walk computes, which the pass checks,
and `guard` carries a
guard's promise as a function's does, `stated` its result annotation's
statement, which a signature its code is checked at covers over the
annotation's whole domain, and `completion` its completion kind as a
function's does. Its `requires` lists the call-position index facts of its
written precondition. Each offered signature assumes only facts in that list;
the graph-code checker establishes the body from its signature's entry facts.
Its `receiver` is `null` for an arrow or
`{type,strict}` for an ordinary function.

The call constructors (`apply`, `invoke`, `new`, `callWithReceiver`,
`bindWithReceiver`, `applyWithReceiver`) keep their operands distinct in the
tree. Lean's execution plans save their values in source evaluation order
before performing the invocation. Closure bodies have their own checked graphs
and capture interfaces. `applyWithReceiver` carries `callee`, `receiver`,
`list` (an expression or `null`) and the Boolean `requiredList`.
`Function.prototype.apply` sets it false, permitting a missing or nullish
list; `Reflect.apply` sets it true, requiring an array list. Expression
planning and type substitution retain the field, and both lowerings check
it. A class value is `ctor`: its constructor lambda as
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
The test's type and each destination's entry types are checked independently.
An observation justifies only the refinements supported by the corresponding
rule; a computed type cannot establish a test result.

## Verification boundary

The [source commands](REQUEST-PROTOCOL.md#run-the-verifier) consume the
Fragment and the module interfaces of its imports. Lean computes the execution
plans, the types at their points and the elaborated requests from the syntax.
Source identity, declaration dependencies, inputs, outputs and required
obligations are checked before acceptance.

The acceptance theorem (`mode8Accepted_sound`) proves each member of an
accepted unit safe: its lowered calculus program is safe from every entry
meeting its input contracts and meets its stated footprint, result and
assertions. Faithful parsing, source evaluation order and the
interpretation of external declarations remain the review obligations named
in [the trust surface](DESIGN.md#trust-surface). A well-formed Fragment document
alone establishes neither source correspondence nor program safety.
