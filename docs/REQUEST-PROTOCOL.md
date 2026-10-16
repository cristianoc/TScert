# Stateful calculus request protocol

The verifier reconstructs, from a source's Fragment tree and a producer's
claims, one request of the stateful calculus per code unit, and checks it
against its derivation certificate. This is a consumer boundary for extracted
programs; it does not certify TypeScript text by itself.

This document owns the request/evidence formats, the verifier's command line;
[FRAGMENT](FRAGMENT-FORMAT.md) owns the source AST encoding. [SOURCE-CLAIMS](SOURCE-CLAIMS.md) owns the
producer-independent claim schemas;
[diagnostics](OBLIGATION-DIAGNOSTICS.md) owns failure metadata.

## Run the verifier

Build from `lean` with `lake build`, then produce evidence and
check it independently:

```sh
.lake/build/bin/verifier --produce-source-claims ast.json source-claims.json input.ts evidence.json 12
.lake/build/bin/verifier --check-source-claims ast.json source-claims.json input.ts evidence.json
```

`12` limits expression proof-search depth. It is not an execution budget and
is not part of the request, evidence or safety theorem. Production reports
failure if evidence cannot be found and checked. The checking command never
invokes the producer; exit zero means the submitted certificate passed for the
requests reconstructed from the submitted source and claims. Read, parse,
validation, checking and output-write failures return nonzero.

`--subtype-rounds <n>` precedes the mode. It sets the frontier-unfolding budget of every subtype
comparison, including declared bounds and instance-image equality during
lowering and frozen checking. The default is 4096 rounds. A frontier may
contain any finite number of comparisons. The budget is execution policy;
it is absent from the equation and evidence documents. The acceptance
soundness theorem quantifies over every budget. A smaller budget can prevent
verification; it cannot authorize a typing step.


## Request fields

All fields are explicit; object field order is immaterial.

| Field     | Meaning                                                                                                                       |
| --------- | ----------------------------------------------------------------------------------------------------------------------------- |
| `types`   | A finite array of type-graph rows: clause rows, scheme rows and parameter rows. Its array positions are type labels.          |
| `program` | A finite array of calculus nodes. Its positions are control-flow labels.                                                      |
| `claims`  | One entry context and expression-result type per program node, in the same order.                                             |
| `result`  | The required result type of the graph.                                                                                        |
| `start`   | The designated control-flow entry label.                                                                                      |
| `inputs`  | External argument types in slot order. The designated entry context must equal this contract. Use `[]` for closed invocation. |

A type is a list of type labels, interpreted as their union. The empty list
means bottom. Every label, including labels in unused type definitions and
intermediate certificate types, must index the request's `types` array.
Dangling type labels are rejected instead of acquiring the total Lean graph's
default interpretation. Control-flow target existence and expression scope are
checked by the graph consumer.

Each type-graph node is a union of clauses:

| Clause                                                                                                                                                                     | JSON example                                                                                |
| -------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------- |
| Top: every value, permitting no operation                                                                                                                                  | `"top"`                                                                                     |
| Null                                                                                                                                                                       | `"nul"`                                                                                     |
| Boolean                                                                                                                                                                    | `"bool"`                                                                                    |
| Boolean singleton                                                                                                                                                          | `{"boolLit":{"value":true}}` (or `false`)                                                   |
| Invariant reference with optional additional contract requirements, and readonly views: fields read at a sound upper bound, with no write permission through this contract | `{"refs":{"first":[["value",[1]]],"rest":[],"views":[["seen",[1]]]}}`                       |
| Optional fields: a key constrained only where the object has it, where its location holds exactly the contract; left out when there are none (also on `dict`) | `{"refs":{"first":[],"rest":[],"views":[],"optional":[["field",[4]]]}}`                       |
| Own-key bounds: each says the object's own keys are `among` its `keys`, or, with `among` false, none of them; a key one does not admit is not the object's own and a read of it continues at the prototype; left out when there are none (also on `dict`) | `{"refs":{"first":[["[]",[2]]],"rest":[],"views":[["[[proto]]",[5]]],"bounds":[{"among":false,"keys":["map"]}]}}` |
| Plain object with named contracts and readonly index views, each `[class, operand]` with class `"strings"` (every string key), `"numeric"` (the canonical numeric keys) or `"symbols"` (every symbol key); each constrains every present own field under a key of its class | `{"dict":{"first":[],"rest":[],"views":[],"indexes":[["strings",[1,3]],["numeric",[1]]]}}` |
| Writable index contracts, a mutable index signature's, `[class, operand]` as above: every present own field under a key of the class holds exactly the operand; each is also listed in `indexes`; left out when there are none | `{"dict":{"first":[],"rest":[],"views":[],"indexes":[["strings",[1,3]]],"cells":[["strings",[1,3]]]}}` |
| Intersection of callable contracts, each with a receiver, arguments, result and required effect  | `{"arrs":{"arrows":[{"receiver":[5],"arguments":[[0]],"result":[1],"effect":"unrestricted"},{"receiver":[5],"arguments":[[1]],"result":[0],"effect":"unrestricted"}]}}`                                 |
| Array store: simultaneous tuple contracts, each with required, optional and rest positions; readonly contracts give element read capabilities                              | `{"list":{"first":{"required":[[4]],"optional":[],"rest":[4],"readonly":false,"presence":"readable"},"rest":[]}}` |
| Callable with invariant bag requirements and overloads, fixed and variadic                                                                                                 | `{"callable":{"first":[["value",[1]]],"rest":[],"arrows":[{"receiver":[5],"arguments":[[0]],"result":[1],"effect":"unrestricted"}]}}`             |
| Class value: construct signatures `[params, result]`, which `new` meets; no call signature meets it; `"variadic": [[params, [rest, result]], ...]` when there are any      | `{"ctors":{"signatures":[[[[1,2]],[1,2]]]}}`             |
| Argument list: simultaneous tuple contracts on the actuals a rest parameter receives, positions compared covariantly                                                  | `{"pack":{"first":{"required":[[4]],"optional":[],"rest":[0],"readonly":false,"presence":"dense"},"rest":[]}}` |

The arrow example contains two signatures, each with one argument and the
receiver label 5. Every signature carries `effect: "unrestricted"` or
`effect: "preservesInputHeap"`; omission is refused. Host-relative method
signatures use the same record with `receiver: {}`. A record clause's
`methods` lists its members as `{"key","calls","rests","schemes","receivers"}`:
the fixed and variadic signatures, the quantified ones as scheme types, and
the types the member's host must meet (a `this` parameter's), `[]` for none. Effectful contracts use
these records in graph rows, scheme rows, code entries and subtype certificates.
A code entry must discharge both safety and its effect, as described in
[the definition rules](SOURCE-ELABORATION.md#certifying-inferred-call-effects).
Every signature states its receiver: the value a call passes
as `this`, `undefined` for a plain call. A signature indifferent to it names a
`"top"` row; there is no missing-field default. A call clause may add
`"variadic": [{"receiver": R, "arguments": [params, rest], "result": B,
"effect": effect}, ...]`, signatures taking actuals past `params` according to
the argument-list contract `rest`; the
field is left out when there are none, which is its one spelling, so strict
decoding refuses an explicit empty list. Each argument type is itself a list of union labels. References and arrow
operands may point back to the same finite graph, representing guarded regular
recursion. The request already contains normalized clauses: this grammar has no conjunction
above the clause level, so nothing here needs normalizing. A producer that
holds positive formulas normalizes them itself
([normal form](POSITIVE-TYPES.md#recursive-normalization)). No string, generic or unsupported-type
fallback is supplied by this protocol. `number` and `numberlit` are carried:
`number` is one clause and each `numberlit` is its own, interned on use rather
than given a fixed row, since the singletons are unbounded. A literal's identity
is the bit pattern of the double it denotes, so distinct spellings of one value
are one clause; two spellings a codec failed to identify would be two
singletons, which costs completeness and never soundness.

A row is a **clause row**, spelled as the array of its clauses as above; a
**scheme row** `{"scheme": {"binders": [p, ...], "signatures": [contract, ...]}}`,
a generic callable $\forall\vec p.\,\Sigma$ whose signatures are types that may
mention its binders, with `"bounds": [[p, type], ...]` when a binder is
bounded (the bound is read outside the binders; left out when none), and
`"variadic": [restContract, ...]` in the same contract-record format when it has variadic
signatures, whose rest may be a binder, a pack parameter (left out when none), and
`"resolution": [{"input": i, "observation": o, "result": r}, ...]` when binders
form resolution descriptors, each naming three positions among the binders,
or two with `r` `null` for an observation (left out when none), and
`"construct": true` for a construct scheme, a generic constructor type, whose
signatures are construct signatures, each a contract's arguments and result,
its receiver `[]` and its effect `"unrestricted"` (left out for a call scheme);
a **parameter row** `{"param": i, "name": n, "kind": "value" | "arguments"}`, which
names its own label $i$ and, in `n`, the binder it stands for (the name has no meaning). Its kind is mandatory and is preserved by instantiation and binder renaming;
or a **meet row** `{"meet": p, "clauses": [...], "also": [...]}`, the value
parameter row $p$ within the clauses (`V & DepSafe`), and the value parameter
rows `also` as well (`U ⊓ T` for `U extends T`; left out when none). Only a
clause row has clauses. The graph of a table $T$
(`RequestJson.tableGraph`) is

```math
G.\mathit{rows}(i)=\begin{cases}\vec c & T[i]=\vec c\\ [\,] & \text{otherwise}\end{cases}
\qquad
G.\mathit{schemes}(i)=(\vec p;\Sigma)\iff T[i]=\mathsf{scheme}(\vec p,\Sigma)
\qquad
G.\mathit{parameterKinds}(i)=\mathsf{some}(k)\iff T[i]=\mathsf{param}(i,n,k),
\qquad
G.\mathit{params}(i)\iff G.\mathit{parameterKinds}(i)\ne\mathsf{none},
\qquad
G.\mathit{meets}(i)=(p;\vec c)\land G.\mathit{meetParams}(i)=\vec q\iff T[i]=\mathsf{meet}(p,\vec c,\vec q).
```

with the meaning given in [Parameter and scheme rows](POSITIVE-TYPES.md#parameter-and-scheme-rows).
Validation (`validRows`) requires every label a row names to index `types`, a
parameter row to name its own label and explicitly state its kind, a scheme's binders to be parameter
rows, and a meet row's parameters to be value parameter rows. A parameter row is therefore never the same row as another, so two
distinct binders are never identified by content. A subtype instantiation
choice names a scheme row and its image types. A table with no scheme rows
has no quantified signature to instantiate.

Current-content assertions use a finite list of primitive predicates, including
`num` for any numeric value and `numLit` for an exact bit pattern, `str` for
any string and `strLit` for one string. They are
checked on every incoming edge. Unsupported predicates still require a proof
that the storage contract implies the claim; they are never silently discarded.

## Terms, targets and evidence

The JSON codecs use Lean's tagged constructor encoding: nullary constructors
are strings; other constructors are single-key objects containing named fields.
For example:

```json
{ "invoke": { "f": { "var": { "i": 0 } }, "r": "undef", "args": ["nul"] } }
```

This invokes slot zero with the receiver `undefined` and the one actual null:
a plain call. A mapped bind continuation is:

```json
{ "bind": { "next": { "label": 3, "mapping": [0, 2] } } }
```

Its map acts after pushing the result: target slot zero receives source slot
zero, and target slot one receives source slot two. `"mapping":null` means
identity selection. Missing `mapping` is rejected; the protocol does not silently
supply a default.

A node's `handler` is `null`, or a target `T` where a throw out of its
expression goes, the thrown value pushed first as a bind pushes a value
([handlers](PROGRAM-TYPING.md#checked-control-flow-graphs)). Its evidence,
`NodeEvidence.handler`, is `null` or a pair `[T, p]`: the type the thrown
value is bound at, which must have a top clause, and the handler edge's
subtype-evidence list.

The encoding follows mechanically from the
[term grammar](SEMANTICS.md#operational-language) and the
[continuations](PROGRAM-TYPING.md#checked-control-flow-graphs). In full, writing
`t` for a nested term and `T` for a target object:

| Term                                 | JSON                                                  | Continuation | JSON                                          |
| ------------------------------------ | ----------------------------------------------------- | ------------ | --------------------------------------------- |
| slot $i$                             | `{"var":{"i":0}}`                                     | `ret`        | `"ret"`                                       |
| $\mathsf{let}(t,t)$                  | `{"letE":{"a":t,"b":t}}`                              | `bind`       | `{"bind":{"next":T}}`                         |
| $\mathsf{invoke}(t,t,[t,\ldots])$   | `{"invoke":{"f":t,"r":t,"args":[t]}}`                 | `effect`     | `{"effect":{"next":T}}`                       |
| $\mathsf{construct}(t,[t,\ldots])$ | `{"construct":{"f":t,"args":[t]}}`                    | | |
| null, undefined, true, false         | `"nul"`, `"undef"`, `"tru"`, `"fls"`                  | `branch`     | `{"branch":{"yes":T,"no":T}}`                 |
| object with named locations          | `{"objAt":{"fields":[["value",0]],"call":c,"identity":1}}` | `branchBind` | `{"branchBind":{"yes":T,"no":T}}`             |
| allocation with ordered initializers | `{"makeAt":{"call":c,"names":["value"],"inits":[t]}}` | `tagBind`    | `{"tagBind":{"test":"isNul","yes":T,"no":T}}` |
| field read                           | `{"readAt":{"field":"value","a":t}}`                  |              |                                               |
| computed string-key read             | `{"indexAt":{"a":t,"key":t}}`                          |              |                                               |
| field write                          | `{"writeAt":{"field":"value","a":t,"b":t}}`           |              |                                               |
| $\mathsf{test}_k(t)$                 | `{"test":{"k":"isNul","a":t}}`                        |              |                                               |
| $\mathsf{if}\;t\;t\;t$               | `{"ite":{"c":t,"t":t,"e":t}}`                         |              |                                               |
| arithmetic                           | `{"arith":{"op":"add","a":t,"b":t}}`                  |              |                                               |
| array store with initial elements    | `{"arrLit":{"inits":[t]}}`                            |              |                                               |
| element at a numeric index           | `{"elemAt":{"a":t,"i":t}}`                            |              |                                               |
| store with an element set            | `{"setElem":{"a":t,"i":t,"v":t}}`                     |              |                                               |
| length of a store                    | `{"lenOf":{"a":t}}`                                   |              |                                               |
| store locations, a hole as `null`    | `{"arr":{"elems":[0,null]}}`                          |              |                                               |
| spread actual                        | `{"spread":{"a":t}}`                                  |              |                                               |
| throw                                | `{"throw":{"a":t}}`                                   |              |                                               |

A descriptor `c` is `"absent"`, `{"closure":{"arity":2,"body":t}}` (with
`"kind":"construct"` for a class's construct-only code, which only `new` runs;
call-only code, an arrow's or a method's, leaves the kind out),
`{"variadic":{"fixed":2,"body":t}}`,
`{"bound":{"target":t,"receiver":t,"pre":[t]}}` or
`{"graph":{"arity":1,"exprs":[t],"conts":[[k,T]],"start":0,"caps":[t]}}`, with
`"kind":"construct"` for a class's construct-only code and `"rest":true` for
code collecting a rest, each left out otherwise. Plain allocation uses the
absent descriptor; function creation uses a code descriptor and ordered field
initializers. A fixed body has the receiver's binder in slot zero, then
`arity` parameter binders in declaration order, before captures. A variadic
body has its fresh rest store in slot zero, the receiver in slot one, then
`fixed` parameters, then captures. A `bound` descriptor is what `.bind` creates: it holds the target,
the receiver and the argument prefix as values and allocates no field; its
invocation drops the receiver it is called with and invokes the target with the
saved one and the prefix before the new actuals. A `graph` descriptor is code
whose body is a control-flow graph, as a program is: its node expressions, each
node's continuation and handler (`null` for none), the entry label and the
captured values; invocation starts the graph at `start` with the receiver, the
`arity` parameters, then the captures as its slots, `new` passing `undefined`
for the receiver. Code with a rest first allocates the store of the actuals
past its parameters, found in slot zero, before the receiver. Every closure a
source program creates is graph code. The node expressions are
scoped by those slots alone. `goto` and `frame`, the terms a running graph code
steps through, are runtime forms and are rejected in supplied syntax as object
terms are. Creation evidence requires each overload to have
that many argument types. Application evidence carries every actual argument in order. Runtime object terms
are rejected in supplied graph syntax, including inside unused branches and
closure bodies.

Tests are `isNul`, `isUndef`, `isNullish`, `isBool`, `isRef` and `isFun`.
`isNullish` accepts null and undefined; false takes its negative branch. A location never appears
in a supplied program: it arises only during execution. These are Lean's derived
codecs, so the field names are the constructor's own; they live in
[RequestJson.lean](../lean/Verification/Source/RequestJson.lean), the JSON boundary of the stateful consumer.

A request may add `"codes"`: the graph code its program creates, one
`{"entry": {"arity","exprs","conts","start","captures","row","store"}, "claims": [...]}`
per code and signature, where `captures` are the captured values' types, `row`
the signature `[receiver, parameters, result]`, `store`, for code with a rest,
the rest-store type its frame starts with (`null` otherwise), and `claims` one
point claim per node of the code's graph, as `claims` is for the program.
Absent means none, its one spelling: an explicit empty list is refused.

The evidence file is an object with the field `certificate`, a list of
`NodeEvidence` objects, and, when the request has codes, `"codes"`: one such
list per code request, in its order. The codes are checked first, in order,
each at its entry `[store, receiver, parameters…, captures…]` (no store
without a rest) and its row's result,
each seeing the codes before it; the program is then checked seeing them all. Each node supplies its expression derivation tree and
one subtype-evidence list per outgoing edge. A derivation node names the
[typing rule](PROGRAM-TYPING.md#judgments-and-constructor-views) it applies:
`var`, `nul`, `undef`, `tru`, `fls`, `truLit`, `flsLit`, `numLit`, `num`,
`strLit`, `str`, `bigintLit`, `bigint`, `funGraph`, `ctorGraph`, `callableGraph`, `app`, `letE`, `alloc`,
`read`, `readOptional`, `readDict`, `indexDict`, `write`, `ifBool`, `ifTrue`, `ifFalse`, `ifKnown`, `ifBoolVar`,
`unionVar`, `callCallable`, `readCallable`, `readBagView`, `writeCallable`, `readView`, `lenView`, `readProto`, `arith`, `test`,
`arrLit`, `elem`, `elemOpt`, `elemAny`, `setElem`, `len`, `lenStr`, `elemStr`,
`callRest`, `callPacked`, `arrParts`, `bindE`, `bindRestE`, `bindMember`, `construct`, `constructRest`, `sub`,
`throw`, whose one premise types the thrown operand, `makeKey`, an allocation
at a key known only at run time, whose two premises type the key and the
initializer, or `merge`, an allocation from parts, whose two premises type
the accumulator and the source
([Allocation from parts](PROGRAM-TYPING.md#allocation-from-parts),
[at a computed key](PROGRAM-TYPING.md#allocation-at-a-computed-key)).
`alloc` at a record type is the typing rule `alloc`, whose fields, where one
is the array store key, are an array of the graph's built-ins (`allocBuiltins`); at a
dictionary type, `allocDict`, a literal allocated at a dictionary with no
own-key bound, naming neither the prototype key nor the store key.
The array rules act on a store, the value an array object holds in its store
field: `arrLit` allocates one location per element under the positions of a
tuple contract; `elem` reads a required position named by a literal index at
its contract, `elemOpt` an optional or rest position at its contract or
`undefined`, and `elemAny` any numeric index into a homogeneous array at the
element contract or `undefined`, independently of readonly and presence mode; `setElem` writes a named position, into its
location or a fresh one the store records; `len` reads the length as a number.
`lenStr` reads a string's length, and `elemStr` a string's code unit at any
numeric index or `undefined`, naming the result's string and `undefined`
types, `{"elemStr": {"str": T, "undef": U}}`.
`readView` reads a field named among a record's or a dictionary's views, at
the bound the view states, as `read` reads either's invariant fields; no rule writes through a view.
`lenView` reads a view of `length` of the object in a context slot, by the
term that tests it for an array, `{"lenView": {"slot": i}}`; `readView` reads
any other view. `readProto` reads a key one of
a record's own-key bounds does not admit from the prototype the record holds under the
reserved key `[[proto]]`, at the prototype's field or view for the key; it
names the prototype's type, `{"readProto": {"proto": P}}`.
`arith` applies a binary operator to two operands whose types it answers for
pair by pair, arithmetic on two numbers or two bigints, a comparison on two
numeric operands or two strings, strict equality (`eq`) where either operand is
a primitive or an object with a field, into the family of its result kind; `test` types a tag test whose answer the operand's type does not settle
as a Boolean holding both literals, for `ifBool` to branch on. `ifTrue` and `ifFalse` are the two answers of the single
shape-test rule `ifTag`, split so that the evidence records which answer it
relies on; `truLit` and `flsLit` are the Boolean singleton introductions, and
`numLit` and `num` the numeric ones, a literal at its own singleton and at the
family, `strLit` and `str` the same for strings, and `bigintLit` and `bigint`
for bigints. A bigint term and clause carry the integer as a JSON number of any
length, `{"bigint":{"value":-5}}` and `{"bigintLit":{"value":-5}}`. A symbol
singleton clause carries its symbol's identity, `{"symbolLit":{"id":0}}`, the
index a symbol key `{"symbol":0}` carries; no term introduces it. These names are not written anywhere: `RequestJson.lean` derives
ToJson/FromJson for `Rule`, so this list is the inductive's constructors and a
rule added there extends the protocol. `tests/rule-inventory.mts`
holds the two to the same set. Expression sequents repeat their
contexts, terms and result types. The consumer checks these against the request;
this redundancy cannot substitute a different program or different claims.

Subtype arrow certificates use ordered lists of argument types. A `source`
certificate's `p` is the complete contract record, for example
`{"source":{"p":{"receiver":[5],"arguments":[[0],[1]],"result":[1],"effect":"unrestricted"}}}` for a two-argument signature whose
receiver is label 5; the receiver is contravariant, like the domains. A `union`
certificate contains `pre`, `a`, `b`, `suffix`, `left`, and `right`: `pre` and
`suffix` are lists of unchanged argument types, and the selected argument splits
from `a ++ b` into the two branches. `combine` retains its result types `b` and
`b'`, the two premise effects `effect` and `other`, and two branches. The meet of
those effects must imply the target effect; each source/rest covering must
also imply it. `empty` requires an empty type at some argument position,
not merely a zero-length argument list; `emptyRecv` requires the target's
receiver to be empty, so that no call is named; `recvUnion` splits the target's
receiver `a ++ b` into two branches, like `union` for an argument. A `rest`
certificate's `s` is a variadic source signature
with `arguments: [params, rest]` covering the target arrow: its
first positions within `params`, the rest within the rest contract. Every label in these fields is bounds
checked. Graph subtype search supports native argument lists and splits any
position. Source function types, closures and calls preserve required parameter
lists, including empty lists for zero-argument thunks. There is one accepted certificate shape.

All node objects explicitly contain `expression`, `edges`, `knowledge`, `effect`
and `output`. `knowledge` and `output` each contain `cells`, `values`, and `links`. The first two are lists of
`{slot, contents, field}` facts. `contents` is a disjunction of primitive
predicates: `nul`, `undef`, `tru`, `fls`, `num`, `str`, `defined`, `nonNull`, `nonNullish`,
`{"numLit":{"bits":"…"}}`, with the same unsigned 64-bit decimal encoding as
numeric graph clauses, or `{"strLit":{"value":"…"}}`. The empty list is
impossible. A singleton fact can weaken to its family, never the reverse. `links` is a list of
`{cell, value, alias, field, distinct, other, optional}` objects: `alias: true` means equal
slot values; `alias: false` means the named field currently contains the other
slot's value, or, with `optional: true`, that the object lacks the key and the
other slot holds `undefined`; `distinct: true` means field `field` of the object in `cell` and
field `other` of the object in `value` are different locations, a timeless fact
established by allocation, since fresh locations differ from every field of
every record-typed slot in scope, and the reason a write to one cell keeps
facts about another. These are finite state assertions, not extra type labels.
`effect: null` selects ordinary expression evidence; a non-null effect selects
one of the checked `StepEvidence` constructors (`ordinary`, `pure`, `reading`,
`typedRead`, `observedRead`, `slicedRead`, `knownValue`, `created`, `allocated`, `written`).
`reading` carries an ordinary `proof` of a term built by field and element
reads over variables and values, and keeps every fact. `slicedRead` carries `tag`, `slot`, `proof` and `sub`: its cell observation
must exclude the tag, and `sub` proves that the negative slice of the ordinary
read contract fits the requested type. Constructor payloads use
Lean's derived JSON encoding, with strict decode/re-encode checking.

The effect checker binds to the root expression sequent and must establish exactly
`output`. Each actual outgoing edge checks fact entailment against the destination's
`knowledge`, in addition to ordinary type coverage. Effect-only continuations drop
the result slot before transferring facts. External entry requires empty knowledge.
All type labels in nested effect proofs are bounds checked. `written` carries
the written value's predicate, or `null` where it is not a known primitive.
`allocated` retains its existing payload
(`slot`, `contents`, and ordinary `proof`) for either descriptor: it requires
`make code (var slot)` and checks the entire term's scope and creation proof.
The code descriptor is part of the requested term, so changing it invalidates
the evidence. `typedRead` (`slot`, ordinary `proof`) accepts a nonempty
expansion of plain or callable bags whose first invariant operand each has the
field read, at any type. Empty expansions and non-bag alternatives are
rejected; its stored read links retain the receiver descriptor. Within a source
statement, the producer derives checked facts along administrative paths. The
source consumer additionally enforces the exact entry interfaces described below.
See the [assertion rules](PROGRAM-TYPING.md#checked-expression-postconditions).

`funGraph` creates graph code: its premises are the captures, each a slot of
the node's context at the type the code was checked with, and every signature
the created type offers must be an entry of the checked codes with those
capture types. It checks no body: the code's own certificate did. Code
without a rest offers each row of its type's `offerRows`: each fixed
signature, then each variadic signature's receiver, fixed parameters and
result, in that order; each row offers at least the code's arity. Code with a
rest offers the variadic signatures only, each taking exactly the code's
parameters, and the rule's `arrays` name their rest-store types, in order:
each is the `store` of that signature's entry. At a scheme row the signatures
are the scheme's. `ctorGraph` creates a class value's construct-only code: an
entry per construct signature, its receiver the rule's `undef`, the
`undefined` type, with the code field, then one initializer premise per
static field, then the captures. `callableGraph` creates a callable object: one initializer
premise per field, then the captures, its code's entries as `funGraph`'s.

The callable expression rules use the existing term syntax. `callableGraph`
checks the initializer premises; its code is checked in the code table, one
entry per advertised overload. Its result has a single initial bag contract; subtyping can add equivalent invariant requirements. `callCallable`
selects an advertised signature and, like `app`, carries one premise per
position that signature declares and the call omits, each proving `undefined`
at that position's contract; `readCallable` and `writeCallable` use
the first invariant bag operand, a callable object's or a class value's, and `readBagView` a class value's readonly static field, a view. Every nested operand label is bounds checked.
`app`, `callCallable` and `callRest` carry the selected signature's `effect`
and take the callee premise, then the
receiver premise at the selected signature's receiver, then the actuals: the
term is `invoke f r args`, and a plain call's receiver is `undefined`.
`bindE` has no premises: its term is `makeAt (bound (var t) (var r) pre) [] []`
with every prefix entry a slot, and the rule reads the target's type, the
receiver's and the prefix's from the context. One fixed signature of the
target must be the receiver slot's type, the prefix slots' types followed by
the result's parameters, and the result's result; the result is one signature
at any receiver.
`bindMember` has no premises either: its term is
`letE (readAt k (var i)) (makeAt (bound (var 0) (var (i + 1)) []) [] [])`,
which reads the member `k` from the object in slot `i` and binds it to that
same object. The object's type must have one object clause with a method of
key `k`; each fixed signature of the result must be covered by one of the
method's, at any receiver, by the subtyping proofs the rule carries, one per
parameter, then the result; each variadic one likewise, one per fixed
parameter, then the rest, then the result; and the object's type must be
within each type the method's host must meet, by one more proof each, in the
method's order. With no proofs, the result may
instead be one of the method's quantified signatures, a scheme row
(`HasTyUsing.bindScheme`), which a call instantiates by `sub`.
`callRest` carries the
callee premise, one premise per fixed actual, one `undefined` premise per fixed
position the call omits, then one per further part: the actual at the element
type the rule names, or, for a part the rule flags as a spread, the store the
spread reads, at a type whose elements that element type admits. `arrParts`
names the element type and flags the parts that are spreads, with one premise
per part, as `callRest`'s further parts; its result is fresh storage with the
element contract `E`, either readonly flag and any chosen presence mode; the
values fill every position, including explicit `undefined` read from source holes.
`constructRest` names how many actuals are fixed, the spread flags of the
further parts and the rest type, with the constructor's premise, one per fixed
actual and one per part, as `callRest` without a receiver.
`callPacked` names how many actuals are fixed, the packed binder and the rest
type, with premises for the callee, the receiver, each fixed actual and the
value whose store the last actual spreads.
The result graph supplies the presence mode. Tuple contracts require `presence`
with exactly `"dense"`, `"readable"` or `"sparse"`; there is no Boolean fallback.
For argument packs it has no semantic effect; producers use the canonical
`"dense"` and `readonly: false` metadata.
These rules are available to calculus requests. The OCaml producer emits a
combined callable/property type for one required `value` field on a function;
other property shapes meet the cell refusal reasons.

The `ifBool` expression rule checks an ordinary `ite` with three premises:
the Boolean condition, the true arm, and the false arm. Each arm has the root's
context and requested result type. Boolean singleton unions are allowed, while
null or mixed Boolean/non-Boolean conditions are rejected. The existing
`ifTrue`/`ifFalse` rules remain the statically decided shape-test rules.
The `ifBoolVar` rule carries `trueType` and `falseType` label lists and two
arm premises. It requires an `ite` whose condition is a variable at an existing
Boolean slot. The lists must expand to the corresponding singleton clauses;
the arms use precisely the root context with that slot replaced. All payload
labels are bounds checked. The rule cannot narrow any other binding.

Requests require explicit `inputs`. Responses carry undefined literal evidence
and undefined/nullish tests in checked heap postconditions, including
ordinary-read links and writes without an old-content premise. Source bundles
carry supplemental expression proofs alongside the graph certificates.
Decode/re-encode validation requires every field and rejects any unknown
field, recursively, so a document either has the current shape or is refused.
When a shape changes, regenerate what carries it. The JSON parser and codecs still form part of the input-meaning
boundary; round-trip tests are not a proof of fidelity to external source text.

## Equations and tree labels

A type can also be read from recursive equations
([RECURSIVE-EQUATIONS](RECURSIVE-EQUATIONS.md#2-type-definitions)), whose labels
are trees over the equations' heads. The source path (source mode below)
checks every request over them.

**Source path.** `--check-source-claims` and `--produce-source-claims` never
read equations from the wire. Lean lowers the declarations and the claims to
heads, grows them while it extracts every unit of the file, and validates
them with `Equations.ofRaw` once extraction is done
(`EquationStore.freeze`). Each request is then checked over the equations'
`Equations.graph`. The evidence bundle spells every label as a tree over
those heads and names them by index, so evidence is valid only for the
claims and the declarations it was produced for. Over other ones it fails to
decode (for example `head 65 takes 1 arguments, given 0`) or fails its
check. A tree is decoded through the validator (`Label.ofTree?`), and no
checked request holds a name placeholder.

**Tree spelling.** Each tree form has exactly one spelling
(`Tree.toJson`, `Tree.fromJson` in `Types/EquationJson.lean`):

| Tree | Spelling |
| --- | --- |
| nullary application of head `h` | `h` |
| application with arguments | `{"app": h, "args": [[…], …]}`, `args` non-empty |
| owned parameter | `{"bound": h, "args": [[…], …], "slot": j}`, `args` left out when empty |
| meet | `{"meet": [L, …]}`: flat, at least two parts, canonical order |
| template placeholder (bodies only) | `{"arg": i}`, `{"local": j}` |
| family variable (inside its entry only) | `{"var": k, "owner": o, "kind": "value" \| "arguments"}` |

Decoding refuses an unknown or missing field and a second spelling of one
tree, such as `{"app": h, "args": []}` for `h`. Heads become equations only
through the validator. It checks scope, arity and lexicality,
constructor-headed templates binding exactly their locals, meet normal form,
and a kind per parameter. A refusal names the head and the position
(`Equations.ofRaw`, `Types/EquationValidator.lean`). Variances are not on the
wire: the checker computes them from the equations when a check compares two
applications of one head (`Equations.variances`,
[RECURSIVE-EQUATIONS §4.3](RECURSIVE-EQUATIONS.md#43-variance)).

**Subtype choices.** A subtype evidence object has exactly two fields:
`instantiation`, an instance object or `null`, and `members`, a list of
supporting instance tuples for bound comparisons and prototype members. An
instance carries its finite `domain`, `table`, `instances` and `free`. Each tuple
retains the source type, fixed and variadic signatures, and the instance object.
The checker selects the rule and discovers the comparison dependencies. A
nested bound comparison selects its candidate from these tuples and validates
its kinds, images and bounds before using it. Candidate presence is not a proof.

The source path accepts an instance image when either proved image check
holds: the finite table check, or the substitution check
`EquationStore.imagesUpTo`, which requires every claimed image to be the
structural substitution image or a type proved equal to it, each below the
other by a subtype proof the checker searches for and checks
(`EquationStore.eitherImages`). Search proposes the substitution images
first (`CertificateProducer.Instantiates`), and, for a scheme's result the
target spells otherwise, the target's result as its image.

**`Var`.** Two applications of one head are related by the checker using the
head's validated variance. Each argument premise is discharged by label
inclusion or another checked variance instance. Structural coverage also uses
these premises and shares recursive dependencies up to binder renaming
(`compareUsing`,
[RECURSIVE-EQUATIONS §4.2–4.3](RECURSIVE-EQUATIONS.md#42-parametric-assumptions)).

Diagnostics show labels through a projection onto a finite table, bounded by
depth, with names for applications (`Promise<number | R>`).

## Source evidence bundle

The source commands exchange a strict object with `functions` and `obligations`
arrays. `functions` contains one graph response per reconstructed code unit in
source order. `obligations` contains one evidence list per unit, including empty
lists, in the same order. Each evidence tree must establish the corresponding
expression or annotation judgment reconstructed by extraction. Counts, graph
claims and root judgments must agree exactly with those reconstructed requests.
The order of functions in the producer's claims document does not determine
this evidence order.

[SourceRequests.Bundle](../lean/Verification/Source/SourceRequests.lean) declares
this envelope and checks its graph interfaces and expression obligations.
[SourceClaimJson.checkJson](../lean/Verification/Source/Claims/Json.lean)
reconstructs the plans from Fragment and SourceClaims, strictly decodes the
bundle and checks every certified request. Its `checkJson_safe` theorem ties
that exact acceptance condition to modeled safety. The checking command
consumes the submitted evidence independently of evidence production.

## Proved boundary and validation

`checkJson_safe` proves that acceptance yields the strictly decoded bundle
and a successful `checkRequests` over the requests reconstructed from the
source and claims. Each request's check is `verify`, which binds the
certificate to the requested point annotations (`verify_eq`, through
`acceptUsing_eq`). It establishes global modeled safety at every observation
budget and every admitted assignment of the parameter rows
(`verify_safe_at`, `verify_qualified_safe_at`), for **any** argument
environment satisfying `inputs`, admissible world and satisfying heap. The
input contract is a premise, not inferred from a producer's point claims. The
theorem reuses graph safety, including cycles, heap changes and explicit slot
maps.

`produceJson` serializes generated evidence and submits it through the same JSON
consumer before returning it. The safety theorem does not require using this
producer. Search is incomplete; failure is not a proof of untypability.
