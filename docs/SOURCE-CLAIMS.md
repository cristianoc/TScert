# Producer-independent claims documents

A source-claims document proposes types for one parsed TypeScript file. The
verifier checks those proposals against the source's declarations and runtime
operations. Evidence is a separate document: supplying a claim does not establish
that it holds.

A **source span** is `[start,end]`, a half-open interval of UTF-16 offsets in
the source. An **execution point** identifies a node of the shared execution
graph. The same source span can run at several points, for example when a
`finally` body runs on different exits. Claims name both the point and the
source site. A **type label** names a row of a type table or a type constructed
from the source's declarations. A list of labels denotes their union;
`[]` denotes the empty type, `never`.

The protocol has three documents:

- The Fragment document describes parsed source syntax and declarations.
- The execution document describes statement edges, expression evaluation,
  and lexical binding order. Lean derives it from the Fragment.
- The source-claims document proposes entry environments, expression results,
  and fixed storage contracts. Any producer can write it.

```sh
lean/.lake/build/bin/verifier --lower-control-flow ast.json
lean/.lake/build/bin/verifier --produce-source-claims \
  ast.json source-claims.json input.ts evidence.json 10
lean/.lake/build/bin/verifier --check-source-claims \
  ast.json source-claims.json input.ts evidence.json
```

`--produce-source-claims` searches for evidence of the reconstructed obligations.
`--check-source-claims` checks supplied evidence against those obligations.
`SourceClaimJson.checkJson_safe` proves calculus safety for every accepted
function, at every permitted interpretation of its type parameters. The
theorem concerns the extracted calculus graph; correspondence with the source
is a separate boundary, specified below.

## Encoding

The top-level object has required fields `file`, `sourceSha256`, `types` and
`functions`, and optional `init`. Unknown fields are rejected. `file` identifies
the source; `sourceSha256` is its lowercase SHA-256 digest. `types` is the
producer's type table. Each ordinary row is a list of clauses, also interpreted
as a union. Row operands contain label lists, so recursive rows can refer to
one another without expanding them into trees. The first four rows are
`["nul"]`, `[{"boolLit":{"value":true}}]`,
`[{"boolLit":{"value":false}}]`, and `["undef"]`, in that order.
The [source-value universe](SOURCE-MODEL.md#source-value-boundary) is the
`source` clause, shared by value claims and declaration arguments.
The table also accepts scheme rows for quantified signatures inside a type
(classes' quantified methods, fields and constructor values of generic
function and constructor types), whose binders use binder labels; their native
graph fields are specified with the clause fields below.
Scheme binders are an ordered binding list. Each bound is a pair of its binder
and a label list; canonical union order applies to that label list, as it does
to signature operands. Decoding retains the bound separately from its binder.

Each function object has these fields:

| Field | Value |
| --- | --- |
| `name` | Source function name |
| `namePos` | Name span |
| `params` | Ordered parameter points: `{name,type,current}` |
| `result` | Claimed return type |
| `contracts` | Mutable declaration contracts: `{pos,name,type}` |
| `effect` | The effect proposed for the declaration's signature: `"unrestricted"` or `"preservesInputHeap"` |
| `entries` | Entry claims: `{point,start,bindings}` |
| `expressions` | Expression claims: `{point,pos,type,current}` |
| `arrows` | Optional per-signature interior claims, described below |

A parameter point and an entry binding both carry `name`, `type` and
`current`. Entry `bindings` is a list of those named points. `start` is the
source offset associated with the graph node. Expression `pos` is a span.
Every point has an explicit `current`: `null` states that no additional
contents assertion is supplied. Expressions may also have `instantiate`,
absent or `null` except at proposed quantified-call eliminations.

A contract's `pos` is the initializer span; together with `name` it identifies
one mutable declaration. The contract fixes the allocated cell's permitted
contents for its lifetime. The initializer and every write must satisfy it.
An annotation, when present, must have the same meaning as the supplied
contract. Entry types and contents assertions describe execution points;
they do not replace this lifetime obligation.

A function's `effect` strengthens its annotated signature only as a claim:
`preservesInputHeap` is an obligation on the function's own graph, which
must establish it ([effect certification](SOURCE-ELABORATION.md#certifying-inferred-call-effects)),
and the other units then read the function at its annotation's signature
stating that effect. A guard's or an assertion function's claim states
`unrestricted`; its promise is its annotation's.

A source containing top-level executable code has an `init` object with
`contracts`, `entries`, `expressions`, and optional `arrows`. It has no
parameters and completes with `undefined`. Functions read module declarations
at their source types; an unannotated module constant uses its initializer
claim, which the initialization unit checks.

Function names, name spans, parameter names and parameter order must match
the source. Entry identities are `(point,start)`; expression identities are
`(point,pos)`. Duplicate associations are rejected. The verifier reconstructs
point ownership and allowed sites from the Fragment. A loop-head entry is an
invariant candidate checked on initial entry and every back edge. Names resolve
against initialized lexical bindings under the Fragment's shadowing rules.
A receiver `this` keeps the source signature's receiver type; an entry's
`this` binding supplies no replacement type.

For example, this document illustrates the fields rather than a complete
executable input; its identity and point associations must match a Fragment:

```json
{
  "file": "input.ts",
  "sourceSha256": "REPLACE_WITH_EXACT_SOURCE_DIGEST",
  "types": [["nul"], [{"boolLit":{"value":true}}],
            [{"boolLit":{"value":false}}], ["undef"]],
  "functions": [{
    "name": "identity", "namePos": [9,17],
    "params": [{"name":"flag","type":[1,2],"current":null}],
    "result": [1,2], "contracts": [], "effect": "preservesInputHeap",
    "entries": [{"point":"9:17:1","start":43,
      "bindings":[{"name":"flag","type":[1,2],"current":null}]}],
    "expressions": [{"point":"9:17:1","pos":[50,54],
      "type":[1,2],"current":null}]
  }]
}
```

A label has one of these spellings. Here `A` denotes a label list, `k` is a
declaration index, `i` is a table index, and `b` is a Boolean:

| Label | Meaning |
| --- | --- |
| `i` | Row `i` of `types` |
| `{"decl":k,"args":[A,...]}` | Source declaration `k` applied to its type arguments |
| `{"meet":[A,...]}` | Intersection of at least two label unions |
| `{"array":A,"readonly":b}` | Array object over the store contract `A` |
| `{"binder":"T"}` | The in-scope source binder `T`, interpreted within its source bound |

Declaration indices refer to the Fragment's `definitions`. A nullary application
omits `args`; an empty `args` field is not its spelling. Defaults and bounds
are interpreted from the source declaration. Label lists are duplicate-free
and ordered canonically: row indices, applications, intersections, arrays,
then binders; within a category, fields and lists are ordered lexicographically.

The `type` language also has these recursive forms:

| Claim type | Meaning |
| --- | --- |
| `A` | Union of labels |
| `{"param":"T"}` | Rigid source type parameter in lexical scope |
| `{"union":[C,...]}` | Union of claim types, including symbolic types |
| `{"array":C}` | Mutable homogeneous array over a symbolic element claim |
| `{"scheme":S}` | Quantified callable signature, specified below |
| `{"unavailable":"reason"}` | Explicit unavailable proposal; its use fails with that reason |

The two `array` forms serve different levels: a label's array wraps a store
contract and requires `readonly`; a claim type's array wraps an element claim.
Rigid parameters are not replaced by their bounds. A bounded parameter is
interpreted as the parameter within that bound.

Ordinary table clauses use the native graph vocabulary:

| Clause | Contract |
| --- | --- |
| `"nul"`, `"undef"`, `"bool"`, `"num"`, `"str"`, `"bigint"`, `"symbol"`, `"top"` | Primitive types and the universal type |
| `boolLit`, `numLit`, `strLit`, `bigintLit`, `symbolLit` objects | Singleton values; `symbolLit`'s `id` is the declaration document's listed symbol a symbol key `{"symbol": id}` names |
| `refs` | Required invariant fields, readonly views, and optional object capabilities |
| `dict` | Object fields plus index contracts |
| `list` | Array-store tuple contracts |
| `pack` | Argument-list tuple contracts |
| `arrs` | Call signatures |
| `ctors` | Construct signatures |
| `callable` | Object fields and call signatures together |

For example, an invariant field is
`{"refs":{"first":[["value",[1,2]]],"rest":[],"views":[]}}`.
An ordinary call signature is an object with `receiver`, `arguments`, `result`
and `effect`, inside `{"arrs":{"arrows":[signature]}}`. `arguments` is an
ordered list of label unions. A zero-argument signature uses `[]`; a signature
with one `undefined` parameter uses `[[3]]` in the illustrative table above.
Optional row fields describe variadic signatures, optional fields, host-relative
methods, and own-key bounds. The full native clause field definitions are in
[Request fields](REQUEST-PROTOCOL.md#request-fields), shared by graph requests
and this document; [type-graph.mts](../tools/type-graph.mts) declares their wire types.
The reader validates label references even in unused candidates. A label is a
name, not a guarantee that the value at a source site has that type.

## Quantified callables and their eliminations

A scheme is one callable satisfying its signature for every assignment of its
own type parameters. In this example, row `4` is `["top"]`, appended to the
primitive table above, so the receiver accepts any value. Its claim is:

```json
{"scheme": {
  "effect": "unrestricted",
  "typeParams": [{"name":"T","bound":null}],
  "this": [4], "params": [{"param":"T"}],
  "rest": null, "result": {"param":"T"}
}}
```

Every shown scheme field is required. `bound` is `null` or a claim type; a
type parameter may also carry `resolution`, `null` or
`{"observation": o, "result": r}` as in the [Fragment](FRAGMENT-FORMAT.md), which
makes `o` and `r` binders of the same scheme;
`this` is the required receiver type, `params` is the fixed parameter list,
and `rest` is `null` or the surplus-element type. Binder names resolve
lexically; a nested scheme's binders hide outer binders of the same names.
The effect is `unrestricted`, `preservesInputHeap`, `{"guards":{"param":p}}`
or `{"asserts":{"param":p}}`. `preservesInputHeap` promises that execution
preserves the input heap; `guards` and `asserts` promise the `p`-th actual a
value of the result, on a `true` result or a normal return
([user-defined guards](SOURCE-CONTRACTS.md#user-defined-guards)). Each requires
corresponding evidence.

A call expression can propose an instance with:

```json
{"point":"9:17:7","pos":[121,129],"type":[1,2],"current":null,
 "instantiate":[{"name":"T","type":[1,2]}]}
```

Its names must match the callable's binders. An entry may carry `resolution`:
`null`, or for a qualified binder `{"certificate": c}`, with `c`
one of `{"k":"stable"}`, `{"k":"native","child":c}`, `{"k":"promise"}`,
`{"k":"union","arms":[c, ...]}` or `{"k":"binder","binder":name}`; the
consumer checks the certificate against the entry's complete input type: a
union's arms against its parts in any order, `promise` against a native
promise of any payload, which it observes and gives no result, and `binder`
against the named enclosing parameter or its observation
([implied bounds](SOURCE-CONTRACTS.md#implied-bounds)). A type argument is a
type of the graph once claims are grounded: a quantified scheme is its scheme
row, and a rigid parameter no enclosing unit or closure binds is refused. The
consumer checks bounds, substitution, the instantiated signature, and the
source call. A body is certified at its quantified signature, not solely at
the instances observed at calls. Generic rests, defaults and receivers retain
the same quantified obligation.

An overloaded ground closure can supply `arrows` on its enclosing function or
initialization claim object:
`[{"pos":span,"rows":[{"contracts":[],"entries":[],"expressions":[]}]}]`.
The rows follow advertised signature order. Each body is checked separately
under that signature. Sites belong to the closure and its execution points;
duplicate associations and invalid labels are rejected. A row's `current`
value is its complete assertion at that site, including `null`. These
per-signature rows apply to ground closures; quantified schemes have their
own binder-based certification.

## Execution graph supplied to the producer

The execution document describes the order of runtime operations independently
of proposed types. `verifier --lower-control-flow ast.json` emits an array of executable-body
graphs. [source-flow.mts](../tools/source-flow.mts) declares and decodes the wire;
[FlowJson.lean](../lean/Verification/Source/FlowJson.lean) writes it.
Each graph has `owner` (its source span), `bodySpans` (the body's statement
spans), `entry` (a local node ID), `prologue` and `nodes`. Each node has `id`, `point`,
`source`, `scope`, `handler`, `action`, `executions` and `bindingPlan`. The graph owner is the function name span, the nested body span, or `[0,0]`
for module initialization. Its scope lists local bindings; parameters and
captures form the surrounding environment. IDs are contiguous from zero;
`point` is `"ownerStart:ownerEnd:id"`. A scope binding has `name` and `source`.
A handler is `null` or `{target, scope, binding}`; its target receives the
thrown value in its binding.

The action's `kind` determines its fields:

| Kind | Other fields | Execution |
| --- | --- | --- |
| `end` | none | Complete the body |
| `jump` | `target` | Transfer control |
| `declaration` | `statement`, `name`, `initializer`, `mutable`, `next` | Evaluate one initializer and bind its name |
| `stmt` | `statement`, `next` | Evaluate the referenced statement |
| `branch` | `statement`, `yes`, `no` | Evaluate its condition and choose an edge |
| `return` | `statement` | Evaluate and return its operand |
| `returnSave` | `statement`, `binding`, `next` | Save a return value before a finalizer |
| `returnHeld` | `binding` | Return the saved value |
| `rethrow` | `binding` | Throw the saved exception |
| `discardThrow` | `binding`, `next` | Resume the original exception after iterator close |
| `iteratorStart` | `statement`, `binding`, `next` | Save the iterator stepper |
| `iteratorStep` | `statement`, `binding`, `element`, `yes`, `no` | Step the iterator and choose its value or completion edge |

A `statement` is a source span identifying syntax in the Fragment. A `binding`
or `element` is a scope-binding descriptor. Every normal and handler target
names a node in its graph. The producer analyzes these edges; the verifier
reconstructs the graph from the Fragment for claim association and typed
elaboration. A supplied graph carries proposal data, with no acceptance
authority.

Each node's `executions` array contains `{source, plan}` for its expressions.
A saved value is an intermediate result retained for later operations. Its
descriptor is `{id, name, source, role}`; `id` is a local identity, `name` is
the internal binding name, `source` records its origin, and `role` records
its use. Plans contain source spans and
saved-value references; their original expressions are read from the Fragment.

| Plan kind | Other fields | Evaluation |
| --- | --- | --- |
| `observe` | `source`, `evaluate` | Check the expression result and its contents observation at its source site |
| `atom` | `source`, `operation` | Perform one operation |
| `sequence` | `source`, `binding`, `evaluate`, `next` | Evaluate, bind its result, then continue |
| `choose` | `source`, `condition`, `test`, `binding`, `evaluate`, `yes`, `no` | Evaluate and save the condition, then choose a branch |

`test` is `truthy`, `nullish` or `defined`; `yes` is the branch where that
test holds. A proved answer executes only its selected branch. Otherwise
both branches have checked entry contexts. Operations have these fields:

| Operation kind | Other fields |
| --- | --- |
| `evaluate` | `source`, `effect` |
| `methodRead` | `source`, `receiver`, `key`, `call` |
| `invokeSaved` | `source`, `receiver`, `method` |
| `snapshotSpread` | `source`, `value`, `call` |
| `snapshotObject` | `source`, `value` |
| `referenceRead` | `source`, `reference` |
| `referenceWrite` | `source`, `reference`, `value` |
| `updateSaved` | `source`, `reference`, `previous`, `rhs` |
| `positionRead` | `source`, `array`, `index` |
| `arrayRest` | `source`, `array`, `start`, `slice` |
| `emptyObject` | `source` |
| `addField` | `source`, `base`, `key`, `value`, `final` |
| `mergeObjects` | `source`, `left`, `right`, `final`, `assign` |

Operand fields `receiver`, `method`, `value`, `previous`, `array`, `base`,
`left` and `right` are saved-value descriptors. `rhs` and the key of a
`methodRead` may be `null`. `call` is a source span. A reference is `{kind:
"local", name, source}` or `{kind: "field", source, receiver, key}`, whose
`key` is a saved-value descriptor or `null`. The key of `addField` is a string
or `{symbol: number}`. `index` and `start` are natural numbers; `slice` is a
Boolean. `final` identifies the operation that completes an object expression;
`assign` identifies an `Object.assign` operation.

`bindingPlan` and `prologue` are nullable lexical binding schedules. Every
schedule object has `kind`; saved operands use the descriptors above.

| Kind | Other fields |
| --- | --- |
| `finish` | — |
| `evaluate` | `value`, `plan`, `next` |
| `defaultValue` | `value`, `result`, `fallback`, `next` |
| `bind` | `name`, `origin`, `value`, `next` |
| `input` | `name`, `index`, `value`, `next` |
| `readField` | `source`, `receiver`, `field`, `value`, `next` |
| `readPosition` | `source`, `array`, `index`, `value`, `next` |
| `objectRest` | `source`, `receiver`, `drop`, `value`, `next` |
| `arrayRest` | `source`, `array`, `start`, `slice`, `value`, `next` |

`plan` and `fallback` are expression execution plans. `next` is a binding
schedule. `defaultValue` saves the defined input or the fallback result in
`result`, then runs `next`. `name` and
`field` are strings, `origin` and `source` are spans, `drop` is a string list,
`index` and `start` are natural numbers, and `slice` is a Boolean. An
`input` index selects a source parameter after the receiver slot. `bind`
publishes its saved value as a lexical binding; reads and defaults follow
the progressive scope supplied by the schedule. Each `readField` requires an
expression claim at `source`; the graph checks that type for the field read
with the observations live at that step, then saves its result for `next`.

Effects describe what the producer must update in its knowledge of mutable
contents. `none` preserves that knowledge; `havoc` forgets it; `cellWrite`
sets a named cell's contents to the assigned expression type; `cellUpdate`
uses the update expression's type. An effect is `{kind: "none"}`, `{kind: "havoc"}`, `{kind: "cellWrite", name,
value}` or `{kind: "cellUpdate", name, source}`. A write's `value` is the
assigned expression's span, and an update's `source` is its expression's span.
Sequence and choice plans state execution order separately from the producer's
source-oriented typing choices.

## Conjunction

A label list and a table row both denote unions: their members are alternatives.
Simultaneous requirements belong inside a clause or a `meet` label. For a
record, `first` and each member of `rest` are invariant field contracts the
same object must satisfy. `views` give read capabilities without write
permission. An `arrs` clause requires every signature in its `arrows` list;
its callable body is checked under each one. Signature order also determines
the source adapter's overload choice.

For example, this clause requires both invariant contracts on `value`:

```json
{"refs":{"first":[["value",[1,2]]],
 "rest":[[["value",[1]]]],"views":[]}}
```

Structural intersections can also be written as `{"meet":[[4],[5]]}` when
those labels name the desired contracts. The decoder and typed operations
check whether a supported interpretation exists. A decodable type is not a
promise that every source operation through it is admitted.

All source functions require matching claim records. Required entry and
expression claims must exist. Extra named bindings at a valid entry are
subject to the source consumer's binding policy; success establishes the
consumed modeled obligations rather than a requirement to consume every
annotation in the document.

## Arrays

An array object is represented by an array label over a `list` store contract,
or by a source declaration application. A tuple store has this shape:

```json
{"list":{"first":{"required":[[4]],"optional":[],"rest":[4],
 "readonly":false,"presence":"readable"},"rest":[]}}
```

`required` and `optional` contain ordered element unions; `rest` is an element
union or `null` when there are no further positions. The outer `rest` is a
list of additional simultaneous tuple contracts. An element location of a
mutable store retains its invariant type across writes. A readonly contract
provides upper bounds for reads and no write permission through that contract.

`presence` is `dense`, `readable` or `sparse`. Density excludes holes below
the length. Readability permits a hole only where the position's element
type admits `undefined`; it supplies a safe in-bounds read at that type.
Sparse contracts allow holes independently of element type. Required
positions remain present in every mode. Source homogeneous arrays use
`readable`; source tuples use `dense`. Present `undefined` and absent
positions are distinct states. See [Array contracts](POSITIVE-TYPES.md) for
the semantic tuple rules.

Direct calculus store operations use an array-index singleton; their store
represents element locations. A source read `xs[k]` at a key typed as
`number` is lowered to the host intrinsic `%ElementAt%`. It can read an
element below the length, another numeric own property, or `undefined`,
under the stated host assumptions. [Source array reads](PROGRAM-TYPING.md)
defines that lowering; [the trust surface](DESIGN.md#trust-surface) states
the numeric-property assumptions. Destructuring
reads follow the modeled iterator contract. A pattern rest is a fresh array
claimed at its rest span. Slice-rest claims can carry the instance of their
rest operation, using `instantiate` as other quantified calls do.

## Current-content assertions

A location has a fixed write contract and contents that can vary within it.
`current` proposes property-read result facts at one execution point, with
the meaning in [Semantics](SEMANTICS.md#what-is-asserted-and-what-a-heap-change-can-touch).
It is `null`, or a nonempty list of distinct `[field,labels]` pairs.
Each field must be named, required or optional, by every record alternative,
and its labels name a valid type in the table. An empty inner label list denotes impossibility;
it does not mean that the assertion is absent.

For a table whose row 4 is a single invariant Boolean cell:

```json
{"name":"cell","type":[4],"current":[["value",[1]]]}
```

The binding has the Boolean write contract and currently contains `true`.
This assertion supplies no persistent permission to read `true` after a
write or call. Function parameters require `current:null`; ordinary closures
receive no creation-time heap assumption.

The decoder accepts a nonempty union of record clauses, each with one
invariant field bag, readonly views and optional fields. Every alternative must
name each asserted field in one of those components. Additional
simultaneous invariant contracts in a clause are outside this profile.

Extraction checks an assertion in one of two ways. If every plain record
alternative's declared read result implies the asserted type, an ordinary
property-read typing obligation checks it; the asserted type can be nonprimitive.
Otherwise, a point observation requires a supported finite predicate from the
[assertion grammar](POSITIVE-TYPES.md#state-assertion-grammar), justified by
the graph checkpoint. A nonprimitive candidate supplies its supported nullish
exclusions; each read must independently prove the requested result from the
storage contract and those observations. Other nonprimitive assertions require
a persistent consequence of the contracts.

Entry assertions form the graph node's interface. Each incoming normal or
exceptional edge must justify it, including loop backedges. Each entry resets
to its supplied types and contents predicates. Expression observations are
checked at the evaluated result; modeled effects determine which facts survive.
A closure's entry assumes its captured storage contracts; creation-time
contents supply no later entry assumption. Checked operations within its
body can establish observations at later graph points. The exact obligations
are in
[Source observation checkpoints](PROGRAM-TYPING.md#source-observation-checkpoints).
A failed observation is a located proof obligation.

## Record alternative absorption

For one named field, let `C(R,W)` require every possible read result to
belong to `R` and every write input in `W` to be accepted. These are
read/write capabilities in the normalization schema. With the same field
name and write requirement, the sufficient absorption law is:

```math
R_1 \subseteq R_2 \quad\Longrightarrow\quad
C(R_1,W) \lor C(R_2,W) \equiv C(R_2,W).
```

The law holds because every read result in $`R_1`$ is in $`R_2`$, for
arbitrary read and write relations; it and the union's preservation under
absorption have no Lean proof. The
record form checks the rule field by field for every field the replacement
requires (`CellUnion.covers`). Normalization (`CellUnion.normalize`) selects a covering invariant
alternative already present in the union. Every input alternative is
validated; each surviving alternative must be invariant or a supported
readonly view. Unsupported alternatives cannot disappear through absorption.
Different write requirements remain different: a Boolean
cell currently containing true need not be a cell whose world type is true.

## Source identity and trust

The claims document's file identity and digest must match the Fragment.
The pipeline compares the source bytes with that digest.
The Lean commands take a file identity as their third argument; they check
that identity and the supplied digests, without reading or hashing the source
file. Parsing and hashing form the reviewed source boundary: the parser
determines which Fragment represents those bytes. Source offsets use UTF-16; the digest uses the exact
source bytes. Editing the source requires corresponding identity and span
updates.

The verifier derives execution ownership, source annotations and type-directed
operations from the Fragment. The exported execution document guides the
producer; acceptance reconstructs the schedule and checks evidence for its
obligations. A producer's successful analysis or supplied evidence cannot
replace those checks. Calculus safety is the guarantee of the checked model,
subject to its parser and external primitive trust boundary.
