# Stateful calculus request protocol

The verifier reconstructs, from a source's Fragment tree and a producer's
claims, one request of the stateful calculus per code unit, and checks it
against its derivation certificate. This is a consumer boundary for extracted
programs; it does not certify TypeScript text by itself.

This document owns the request and evidence formats and the verifier's
command line; [FRAGMENT](FRAGMENT-FORMAT.md) owns the source AST encoding,
[SOURCE-CLAIMS](SOURCE-CLAIMS.md) the producer-independent claim schemas, and
[diagnostics](OBLIGATION-DIAGNOSTICS.md) the failure metadata. The decoders
are [RequestJson.lean](../lean/Verification/Source/RequestJson.lean), the JSON
boundary of the stateful consumer, over the constructors of
[Calculus.lean](../lean/Verification/Semantics/Calculus.lean); the tables
below list every constructor they decode.

## Run the verifier

Build from `lean` with `lake build`; the executable is
`.lake/build/bin/verifier`. Its modes:

```sh
verifier --produce-source-claims <ast.json> <source-claims.json> <file-key> <evidence.json> <depth>
verifier --check-source-claims   <ast.json> <source-claims.json> <file-key> <evidence.json>
verifier --lower-program         <ast.json> <source-claims.json> <file-key>
verifier --lower-control-flow    <ast.json>
```

- `<file-key>` is the identity of the checked file: the key the claims and
  the requests are reconstructed under, the Fragment's `file`.
- `--produce-source-claims` searches for evidence, checks it through the
  same consumer as `--check-source-claims`, and writes it to
  `<evidence.json>`, which must differ from both inputs. `<depth>` limits
  expression proof-search depth; it is not an execution budget and is not
  part of the request, evidence or safety theorem.
- `--check-source-claims` never invokes the producer: success means the
  submitted evidence passed for the requests reconstructed from the
  submitted source and claims. It prints `accept: stateful source <file-key>`.
- `--lower-program` prints the program graph each unit lowers to, with the
  graph code it creates (`SourceClaimJson.lowerJson`), for inspection;
  `make lowering` runs it.
- `--lower-control-flow` prints the claim-independent graphs the producer
  analyzes (`SourceFlow.document`).

`--subtype-rounds <n>` before any mode sets the frontier-unfolding budget of
every subtype comparison, including declared bounds and instance-image
equality during lowering and frozen checking; the default is 4096 rounds. A
frontier may contain any finite number of comparisons. The budget is
execution policy, absent from the equation and evidence documents. The
acceptance soundness theorem quantifies over every budget, so a smaller
budget can prevent verification and cannot authorize a typing step.

Exit status: 0 on success; 1 on a refusal, which prints `reject: <reason>`
and then `end of refusal` on standard error (`RequestCli.refuse`); 2 on a
usage error; 3 on an operational failure (a file it cannot read or write,
any exception), with a first line `error: `.

## Wire text

Every document the tools exchange (the parser's fragment and declarations,
the producer's claims, the flow, the evidence, a diagnostic record) is JSON
text in UTF-8, and every string it holds, key or value, is well-formed
Unicode: a `\u` escape of a surrogate is one of a pair. Each reader refuses a
document breaking either before it reads a value: Lean (`RequestCli.readJson`
refuses bytes that are not UTF-8, and `RequestCli.loneSurrogate` a lone
surrogate escape, which Lean's JSON parser would read as U+FFFD; it reads the
text's characters only where its bytes hold a backslash, `u` and `d` or `D`
in a row, the start of every surrogate escape, `RequestCli.wireSurrogate_eq`), the
producer (`Json.parse`), and the TypeScript tools (`wireText` for the bytes,
`requireWellFormed` for the strings). A writer refuses such a string before
writing it: the parser's gate a source string holding a lone surrogate
([source fragment](SOURCE-FRAGMENT.md#refused-on-principle)).

Decoders read the value Lean's JSON parser makes of the text: key order,
whitespace and escapes are no part of a document, a key written twice holds
its last value, and a natural number is an integer literal, in exponent form
too (`0e0`, `-0`), never a fraction (`0.0`).

Decoding is strict: it decodes, re-encodes and compares, so every field is
required, an unknown field is refused, recursively, and a field whose absence
is its one spelling of "none" (stated below where it applies) is refused when
written empty. A document either has the current shape or is refused. The
JSON parser and codecs are part of the input-meaning boundary; round-trip
tests are not a proof of fidelity to external source text.

## Request fields

| Field     | Meaning                                                                                                                                                                                                                                                                       |
| --------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `types`   | The type graph: a finite array of rows (below). Its array positions are type labels.                                                                                                                                                                                         |
| `program` | A finite array of nodes `{expression, continuation, handler}`. Its positions are control-flow labels.                                                                                                                                                                       |
| `claims`  | One point claim `{context, type}` per program node, in the same order: the entry context and the expression-result type.                                                                                                                                                    |
| `result`  | The required result type of the graph.                                                                                                                                                                                                                                       |
| `start`   | The designated control-flow entry label.                                                                                                                                                                                                                                     |
| `inputs`  | External argument types in slot order. The designated entry context must equal this contract; `[]` for closed invocation. The input contract is a premise of the safety theorem, never inferred from point claims.                                                        |
| `codes`   | The graph code the program creates ([code requests](#code-requests)); left out when there is none.                                                                                                                                                                           |
| `promise` | `null`, or a guard's promise `[asserts, [slot, T]]`: the returns establish a type guard's `true` or `false` (`asserts` false) or an assertion function's `undefined` (true), each `true` or `undefined` with the input in entry slot `slot` a value of `T`; `result` is then the plain result. |

A type is a list of type labels, interpreted as their union; the empty list
is bottom. Every label, including labels in unused type definitions and
intermediate certificate types, must index the request's `types` array, so a
dangling label is refused rather than given the total Lean graph's default
interpretation. Control-flow target existence and expression scope are
checked by the graph consumer.

### Rows

A row is one of:

- a **clause row**, the array of its clauses (below);
- a **scheme row** `{"scheme": {"binders": [p, …], "signatures": [contract, …]}}`,
  a generic callable $`\forall\vec p.\,\Sigma`$ whose signatures are contract
  records ([below](#contracts-and-effects)) over types that may mention its
  binders, with `"bounds": [[p, type], …]` when a binder is bounded (the
  bound is read outside the binders), `"variadic": [restContract, …]` for
  variadic signatures, whose rest may be a binder or a packed parameter,
  `"resolution": [{"input": i, "observation": o, "result": r}, …]` when
  binders form resolution descriptors, each naming three positions among the
  binders, or two with `r` `null` for an observation, and `"construct": true`
  for a construct scheme, a generic constructor type whose signatures are
  construct signatures with receiver `[]`; each of these four left out when
  empty or false;
- a **parameter row** `{"param": i, "name": n, "kind": k}`, which names its
  own label $`i`$, in `n` the binder it stands for (the name has no
  meaning), and its mandatory kind `"value"`, `"arguments"` or `"packed"`
  ([packed binders](PROGRAM-TYPING.md#packed-binders)), preserved by
  instantiation and binder renaming;
- a **meet row** `{"meet": p, "clauses": [...], "also": [...]}`, the value
  parameter row $`p`$ within the clauses (`V & DepSafe`), and the value
  parameter rows `also` as well (`U ⊓ T` for `U extends T`; left out when
  none).

Only a clause row has clauses. The graph of a table $`T`$
(`StoreView.graph`) is

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

with the meaning given in
[Parameter and scheme rows](POSITIVE-TYPES.md#parameter-and-scheme-rows).
Validation (`StoreView.wellFormed`, which `RequestJson.validRequest` calls) requires every label a row names to index `types`,
a parameter row to name its own label and state its kind, a scheme's binders
to be parameter rows, and a meet row's parameters to be value parameter rows.
A parameter row is therefore never the same row as another, so two distinct
binders are never identified by content. A subtype instantiation choice names
a scheme row and its image types. A table with no scheme rows has no
quantified signature to instantiate.

### Clauses

A clause row is a union of clauses (`PositiveNormalization.Clause`). The
request holds normalized clauses: the grammar has no conjunction above the
clause level, and a producer holding positive formulas normalizes them
itself ([normal form](POSITIVE-TYPES.md#recursive-normalization)). No string,
generic or unsupported-type fallback is supplied by this protocol. Operands
(`[4]` below) are types, lists of labels; references and arrow operands may
point back into the same finite graph, representing guarded regular
recursion.

| Clause                                                                                                                                                                                                                                                                                                                                                                                    | JSON                                                                                          |
| ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------- |
| Top: every value, permitting no operation                                                                                                                                                                                                                                                                                                                                                 | `"top"`                                                                                       |
| Every closed JavaScript value, internal stores excluded                                                                                                                                                                                                                                                                                                                                   | `"source"`                                                                                    |
| Null; undefined                                                                                                                                                                                                                                                                                                                                                                           | `"nul"`; `"undef"`                                                                            |
| Booleans; one Boolean                                                                                                                                                                                                                                                                                                                                                                     | `"bool"`; `{"boolLit":{"value":true}}`                                                        |
| Numbers; one number, by the bit pattern of its double as an unsigned 64-bit decimal string; a tag set of numbers                                                                                                                                                                                                                                                                          | `"num"`; `{"numLit":{"bits":"4607182418800017408"}}`; `{"numIn":{"bits":["…","…"]}}`          |
| Strings; one string; a tag set of strings                                                                                                                                                                                                                                                                                                                                                 | `"str"`; `{"strLit":{"value":"a"}}`; `{"strIn":{"values":["a","b"]}}`                         |
| Bigints; one bigint, a JSON number of any length                                                                                                                                                                                                                                                                                                                                          | `"bigint"`; `{"bigintLit":{"value":-5}}`                                                      |
| Symbols; one symbol, by the identity a symbol key `{"symbol":0}` carries (no term introduces it)                                                                                                                                                                                                                                                                                         | `"symbol"`; `{"symbolLit":{"id":0}}`                                                          |
| Record: invariant reference contracts `first` and `rest`, and readonly views, fields read at a sound upper bound with no write permission through this contract                                                                                                                                                                                                                         | `{"refs":{"first":[["value",[1]]],"rest":[],"views":[["seen",[1]]]}}`                         |
| A record's optional fields: a key constrained only where the object has it                                                                                                                                                                                                                                                                                                                | `"optional":[{"key":"field","readonly":false,"type":[4]}]`                                    |
| A record's methods, host-relative members ([methods](SOURCE-MODEL.md#method-members-are-host-relative)): fixed and variadic signatures, the quantified ones as scheme types, and the types the member's host must meet (a `this` parameter's)                                                                                                                                           | `"methods":[{"key":"m","calls":[…],"rests":[],"schemes":[],"receivers":[]}]`                  |
| A record's own-key bounds: each says the object's own keys are `among` its `keys`, or, with `among` false, none of them; a key one does not admit is not the object's own, and a read of it continues at the prototype                                                                                                                                                                  | `"bounds":[{"among":false,"keys":["map"]}]`                                                   |
| A record's stable keys, each one of its readonly members ([stable keys](HOST-FAMILIES.md#stable-keys))                                                                                                                                                                                                                                                                                    | `"stable":["kind"]`                                                                           |
| Plain object: a record's contracts and readonly index views `[class, operand]`, class `"strings"` (every string key), `"numeric"` (the canonical numeric keys) or `"symbols"` (every symbol key), each constraining every present own field under a key of its class                                                                                                                    | `{"dict":{"first":[],"rest":[],"views":[],"indexes":[["strings",[1,3]],["numeric",[1]]]}}`    |
| A plain object's writable index contracts, a mutable index signature's: every present own field under a key of the class holds exactly the operand; each is also listed in `indexes`                                                                                                                                                                                                    | `"cells":[["strings",[1,3]]]`                                                                 |
| Intersection of callable contracts, fixed and variadic                                                                                                                                                                                                                                                                                                                                   | `{"arrs":{"arrows":[contract, …]}}`                                                           |
| Callable object: invariant bag contracts `first` and `rest`, and fixed and variadic signatures                                                                                                                                                                                                                                                                                            | `{"callable":{"first":[["value",[1]]],"rest":[],"arrows":[contract, …]}}`                     |
| Class value: construct signatures, receiver `{}`, which `new` meets and no call does; variadic ones; its static fields as invariant `first` and `rest` and readonly `views`                                                                                                                                                                                                              | `{"ctors":{"signatures":[contract, …]}}`                                                      |
| Array store: simultaneous tuple contracts, each with required, optional and rest positions; readonly contracts give element read capabilities                                                                                                                                                                                                                                            | `{"list":{"first":{"required":[[4]],"optional":[],"rest":[4],"readonly":false,"presence":"readable"},"rest":[]}}` |
| Argument list: simultaneous tuple contracts on the actuals a rest parameter receives, positions compared covariantly                                                                                                                                                                                                                                                                    | `{"pack":{"first":{"required":[[4]],"optional":[],"rest":[0],"readonly":false,"presence":"dense"},"rest":[]}}` |

The rows marked as a record's fields are fields of `refs` and of `dict`. A
field left out when empty: `optional`, `methods`, `bounds` and `stable` of
`refs` and `dict`, `cells` of `dict`, `variadic` of `arrs`, `callable` and
`ctors`, and `first`, `rest` and `views` of `ctors`. A variadic signature
(`"variadic": [contract, …]`) has `arguments` `[params, rest]` and takes the
actuals past `params` according to the argument-list contract `rest`.

A literal's identity is the bit pattern of the double it denotes, so distinct
spellings of one value are one clause; two spellings a codec failed to
identify would be two singletons, which costs completeness and never
soundness. A tag set lists two or more elements, sorted and distinct, its one
spelling ([tag sets](HOST-FAMILIES.md#tag-sets)). Tuple contracts require
`presence` with exactly `"dense"`, `"readable"` or `"sparse"`; for argument
packs it has no semantic effect, and producers write `"dense"` and
`readonly: false`.

### Contracts and effects

Every signature is a contract record
`{"receiver": R, "arguments": A, "result": B, "effect": e}`: `A` the list of
argument types (`[params, rest]` for a variadic one), `R` the value a call
passes as `this`, `undefined` for a plain call; a signature indifferent to it
names a `"top"` row, and there is no missing-field default. The receiver is
contravariant, like the arguments. A class value's and a method's signatures
have receiver `{}`, a construct scheme's `[]`. Effectful contracts use these
records in graph rows, scheme rows, code entries and subtype certificates;
a code entry must discharge both safety and its effect
([the definition rules](SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification)).

The effect is `{"footprint": f, "promise": p, "fresh": b, "receiverStore": c, "onThrow": o}`:

- `f`, a [closed footprint](FOOTPRINTS.md#changes-and-footprints)
  `{"value": v, "store": s}`, `v` one of `"keep"` and `"any"`, `s` one of
  `"keep"`, `"grow"` and `"any"`;
- `p`, `null`, `{"guards":{"param":i}}` or `{"asserts":{"param":i}}`, the
  last two with the promise's type as the result
  ([effect-qualified contracts](SEMANTICS.md#effect-qualified-call-contracts));
- `b`, `c` and `o`, Booleans: a fresh result, the receiver's store excepted
  from the footprint, and the footprint stated on a throw too
  ([exceptional footprints](SOURCE-ELABORATION.md#exceptional-footprints)).

## Terms

The JSON codecs use Lean's derived constructor encoding: a nullary
constructor is a string, any other a single-key object whose value holds its
named fields. For example, the plain call of slot zero with the one actual
null:

```json
{ "invoke": { "f": { "var": { "i": 0 } }, "r": "undef", "args": ["nul"] } }
```

The encoding follows the [term grammar](SEMANTICS.md#operational-language),
writing `t` for a nested term:

| Term                                                                    | JSON                                                     |
| ----------------------------------------------------------------------- | -------------------------------------------------------- |
| slot $`i`$                                                              | `{"var":{"i":0}}`                                        |
| null, undefined, true, false                                            | `"nul"`, `"undef"`, `"tru"`, `"fls"`                     |
| a number, by its bits                                                   | `{"num":{"bits":"…"}}`                                   |
| a string                                                                | `{"str":{"value":"a"}}`                                  |
| a bigint                                                                | `{"bigint":{"value":-5}}`                                |
| a symbol, by its identity                                               | `{"sym":{"id":0}}`                                       |
| $`\mathsf{let}(t,t)`$                                                   | `{"letE":{"a":t,"b":t}}`                                 |
| $`\mathsf{invoke}(t,t,[t,\ldots])`$: callee, receiver, actuals          | `{"invoke":{"f":t,"r":t,"args":[t]}}`                    |
| $`\mathsf{construct}(t,[t,\ldots])`$: `new`                             | `{"construct":{"f":t,"args":[t]}}`                       |
| allocation with call code and ordered initializers                      | `{"makeAt":{"call":c,"names":["value"],"inits":[t]}}`    |
| allocation from parts, the keys `drop` left out                         | `{"merge":{"drop":["k"],"a":t,"b":t}}`                   |
| allocation at a key known only at run time                              | `{"makeKey":{"key":t,"init":t}}`                         |
| field read                                                              | `{"readAt":{"field":"value","a":t}}`                     |
| computed string-key read                                                | `{"indexAt":{"a":t,"key":t}}`                            |
| field write                                                             | `{"writeAt":{"field":"value","a":t,"b":t}}`              |
| $`\mathsf{test}_k(t)`$                                                  | `{"test":{"k":"isNul","a":t}}`                           |
| $`\mathsf{if}\;t\;t\;t`$                                                | `{"ite":{"c":t,"t":t,"e":t}}`                            |
| binary operator                                                         | `{"arith":{"op":"add","a":t,"b":t}}`                     |
| array store with initial elements                                       | `{"arrLit":{"inits":[t]}}`                               |
| element at a numeric index                                              | `{"elemAt":{"a":t,"i":t}}`                               |
| store with an element set                                               | `{"setElem":{"a":t,"i":t,"v":t}}`                        |
| length of a store or a string                                           | `{"lenOf":{"a":t}}`                                      |
| spread actual                                                           | `{"spread":{"a":t}}`                                     |
| throw                                                                   | `{"throw":{"a":t}}`                                      |

A field key is a string or `{"symbol":i}`. The operators (`Arith`) are
`add`, `sub`, `mul`, `div`, `pow`, `xor`, `rem`, `bitAnd`, `bitOr`, `shl`,
`shr`, `ushr`, `lt`, `le`, `gt`, `ge`, `eq` (strict equality) and `looseEq`
(abstract equality). `objAt` (an object identity), `arr` (a store's
locations), `goto` and `frame` (a running graph code) are runtime forms: no
evidence rule types them, so no supplied program holds one, in unused
branches and closure bodies included, and a location never appears in a
supplied program.

The tests (`Tag`) are:

| Test                                                   | JSON                                       |
| ------------------------------------------------------ | ------------------------------------------ |
| null; undefined; null or undefined                     | `"isNul"`; `"isUndef"`; `"isNullish"`      |
| a Boolean; a number; a string; a bigint; a symbol      | `"isBool"`; `"isNum"`; `"isStr"`; `"isBigint"`; `"isSymbol"` |
| an object; an object with call code (`"function"`)     | `"isRef"`; `"isFun"`                       |
| `typeof v === "object"`: null, or an object without call code | `"typeofObject"`                    |
| `Array.isArray`: an object owning the store key        | `"isArray"`                                |
| JavaScript's `ToBoolean`                               | `"truthy"`                                 |
| equality with one number, string, Boolean or bigint    | `{"numEq":{"bits":"…"}}`, `{"strEq":{"value":"a"}}`, `{"boolEq":{"value":true}}`, `{"bigintEq":{"value":5}}` |
| `key in v`: an own key or one the prototype chain reaches | `{"hasKey":{"key":"k"}}`                |

### Nodes, continuations and targets

A node is `{"expression": t, "continuation": k, "handler": T | null}`, `T` a
target `{"label": n, "mapping": [i, …] | null}`. A mapping acts after the
result is pushed: `{"label": 3, "mapping": [0, 2]}` gives target slot zero
source slot zero and target slot one source slot two; `null` means identity
selection, and a missing `mapping` is refused. A `handler` is where a throw
out of the node's expression goes, the thrown value pushed first as a bind
pushes a value ([handlers](PROGRAM-TYPING.md#checked-control-flow-graphs)).

| Continuation                                             | JSON                                          |
| -------------------------------------------------------- | --------------------------------------------- |
| return                                                   | `"ret"`                                       |
| bind the result and continue                             | `{"bind":{"next":T}}`                         |
| discard the result and continue                          | `{"effect":{"next":T}}`                       |
| branch on a Boolean                                      | `{"branch":{"yes":T,"no":T}}`                 |
| branch on a Boolean, binding it                          | `{"branchBind":{"yes":T,"no":T}}`             |
| test the result, bind it, branch                         | `{"tagBind":{"test":"isNul","yes":T,"no":T}}` |

## Code descriptors

A descriptor `c` is the call code an allocation gives its object:

- `"absent"`: a plain object.
- `{"bound":{"target":t,"receiver":t,"pre":[t]}}`: what `.bind` creates. It
  holds the target, the receiver and the argument prefix as values and
  allocates no field; its invocation drops the receiver it is called with and
  invokes the target with the saved one and the prefix before the new
  actuals.
- `{"graph":{"arity":1,"exprs":[t],"conts":[[k,T]],"start":0,"caps":[t]}}`:
  code whose body is a control-flow graph, as a program is: its node
  expressions, each node's continuation and handler (`null` for none), the
  entry label and the captured values. `"kind"` is `"construct"` for a
  class's construct-only code, which only `new` runs, and `"sloppy"` for a
  sloppy function that reads its receiver, whose call binds an object
  receiver unchanged and has no step for another; `"rest": true` marks code
  collecting a rest. Each is left out for call code and for code without a
  rest, its one spelling.

Invocation starts graph code at `start` in the environment
`[this, parameter_0, …, parameter_{arity-1}] ++ captures ++ [self]`, self
the invoked object; `new` passes `undefined` for `this`. Code with a rest
first allocates the store of the actuals past its parameters, found in slot
zero, before the receiver. The node expressions are scoped by that
environment alone. Every closure a source program creates is graph code.

### Code requests

A request's `codes` lists the graph code its program creates, one
`{"entry": {"arity","exprs","conts","start","captures","row","store"}, "claims": [...]}`
per code and signature, nested code before the code creating it: `captures`
the captured values' types, `row` the signature as a contract record,
`store`, for code with a rest, the rest-store type its frame starts with
(`null` otherwise), and `claims` one point claim per node of the code's
graph, as `claims` is for the program.

## Evidence

The evidence for a request (`Response`) is `{"certificate": [...]}`, a list
of node evidence per program node, and, when the request has codes,
`"codes"`: one such list per code request, in its order; and, when its
derivations use any, `"readSummaries"`, the request's
[read summaries](#read-summaries). The summaries are checked first, each
once; the codes then, in order, each at its entry `[store, receiver,
parameters…, captures…]` (no store without a rest) and its row's result,
each seeing the codes before it; the program is then checked seeing them
all. The request's expression obligations in the
[bundle](#source-evidence-bundle) use the same summaries.

A node's evidence (`NodeEvidence`) has the fields:

- `ordinary`: the ordinary typing derivation of its expression, whose root
  is the node's sequent: `{"proof": {"tree": d}}`, a derivation tree `d`,
  each node `{"node": {"claim": {context, term, type}, "rule": r, "premises": [...]}}`;
  `"effect"`, the proof its step evidence carries; or `null`, none, where
  the step evidence establishes the step alone, which a node without step
  evidence never is;
- `sequent`: `{context, term, type}`, the node's sequent where `ordinary` is
  `null` and the step evidence carries no proof, and `null` otherwise, where
  the sequent is the root of `ordinary`'s derivation or of the step's proof.
  The steps carrying a proof at the node's sequent are `ordinary`, `pure`,
  `reading`, `created`, `typedRead`, `allocated` and `written`
  ([step evidence](#step-evidence)); a `slicedRead`'s proof is at the
  location's contract. A node spelling its sequent otherwise is refused,
  and every consumer reads a node as the one with its derivation written
  out (`ControlFlow.checkGraphResult_explicit`);
- `edges`: one subtype-evidence list per outgoing edge, one entry per
  destination slot;
- `knowledge`, `effect`, `output`: the [heap facts](#heap-facts) at entry,
  the step evidence, and the facts after the step;
- `handler`: `null`, or `[T, p]` for a node with a handler: the type the
  thrown value is bound at, which must have a top clause, and the handler
  edge's subtype-evidence list;
- `implies`, `yields`, `arguments`, `promise`: the
  [promise facts](#promise-facts), empty or `null` unless the request has a
  `promise`.

Expression sequents repeat their contexts, terms and result types; the
consumer checks these against the request, so this redundancy cannot
substitute a different program or different claims. Every label in the
evidence is bounds checked.

### Rules

A derivation node names the
[typing rule](PROGRAM-TYPING.md#judgments-and-constructor-views) it applies:
`var`, `nul`, `undef`, `tru`, `fls`, `truLit`, `flsLit`, `numLit`, `num`,
`strLit`, `str`, `bigintLit`, `bigint`, `funGraph`, `funGraphSelf`,
`ctorGraph`, `callableGraph`, `app`, `letE`, `alloc`, `read`, `readView`,
`write`, `arith`, `test`, `readDict`, `indexDict`, `readOptional`,
`readProto`, `arrLit`, `elem`, `setElem`, `len`, `lenStr`, `elemStr`,
`elemOpt`, `elemAny`, `ifBool`, `ifTrue`, `ifFalse`, `ifKnown`, `ifBoolVar`,
`unionVar`, `callCallable`, `readCallable`, `readBagView`, `writeCallable`,
`arrParts`, `callRest`, `callPacked`, `bindE`, `bindRestE`, `bindMember`,
`construct`, `constructRest`, `sub`, `throw`, `merge`, `makeKey`,
`lenView` or `readSummary`. `RequestJson.lean` derives the codec of `Rule`, so the rules are the
inductive's constructors and a rule added there extends the protocol;
`tests/rule-inventory.mts` holds the two to the same set. By kind:

- **Values.** `var`, `nul`, `undef`, `tru`, `fls`; `truLit` and `flsLit`, the
  Boolean singleton introductions; `numLit` and `num`, a literal at its own
  singleton and at the family; `strLit` and `str`; `bigintLit` and `bigint`.
- **Binding and control.** `letE`; `ifBool`, an `ite` with three premises
  (the Boolean condition and the two arms, each at the root's context and
  requested type; Boolean singleton unions are allowed, null or mixed
  conditions refused); `ifTrue` and `ifFalse`, the two answers of the single
  shape-test rule `ifTag`, split so that the evidence records which answer
  it relies on; `ifKnown` with its `answer`; `ifBoolVar` with `trueType`,
  `falseType` and two arm premises, an `ite` whose condition is a slot at a
  Boolean, the lists expanding to the corresponding singleton clauses, each
  arm at the root context with that slot replaced, narrowing no other
  binding; `unionVar` with its `slot`, eliminating a union member by member;
  `sub` with its subtype proof; `throw`, whose one premise types the thrown
  operand.
- **Objects.** `alloc` at a record type, whose fields, where one is the
  array store key, are an array of the graph's built-ins (`allocBuiltins`);
  at a dictionary type the typing rule `allocDict`, a literal allocated at a
  dictionary with no own-key bound, naming neither the prototype key nor
  the store key; `merge`, an allocation from parts, whose two premises type
  the accumulator and the source
  ([allocation from parts](PROGRAM-TYPING.md#allocation-from-parts));
  `makeKey`, whose two premises type the key and the initializer
  ([at a computed key](PROGRAM-TYPING.md#allocation-at-a-computed-key));
  `read`, `write`; `readOptional` with `element` and `undef`; `readDict`
  with `keys`, `element` and `undef`; `indexDict` with `keys`, `keyKeys`,
  `element` and `undef`; `readView`, a field named among a record's or a
  dictionary's views, at the bound the view states (no rule writes through a
  view); `lenView` with its `slot`, a view of `length` of the object in a
  context slot, by the term that tests it for an array; `readProto` with
  `proto`, a key one of a record's own-key bounds does not admit read from
  the prototype the record holds under `[[proto]]`; `readSummary` with its
  `index`, no premises, a read `readAt f (var x)` at entry `index` of the
  request's read summaries, whose key and result are the read's and whose
  receiver is the context's type at `x`.
- **Operators and tests.** `arith`, a binary operator on two operands whose
  types it answers for pair by pair: arithmetic on two numbers or two
  bigints, a comparison on two numeric operands or two strings, equality
  where either operand is a primitive or an object with a field, into the
  family of its result kind; `test`, a tag test whose answer the operand's
  type does not settle, as a Boolean holding both literals, for `ifBool` to
  branch on.
- **Arrays and strings.** On a store, the value an array object holds in its
  store field: `arrLit` allocates one location per element under the
  positions of a tuple contract; `elem` reads a required position named by a
  literal index at its contract, `elemOpt` (with `undef`) an optional or rest
  position at its contract or `undefined`, and `elemAny` (with `undef`) any
  numeric index into a homogeneous array at the element contract or
  `undefined`, independently of readonly and presence mode; `setElem` writes
  a named position, into its location or a fresh one the store records;
  `len` reads the length as a number. `lenStr` reads a string's length, and
  `elemStr` (with `str` and `undef`) a string's code unit at any numeric
  index or `undefined`. `arrParts` (with `elem` and `spreads`) names the
  element type and flags the parts that are spreads, with one premise per
  part as `callRest`'s further parts; its result is fresh storage with the
  element contract, either readonly flag and any chosen presence mode, the
  values filling every position, explicit `undefined` read from source holes
  included.
- **Code.** `funGraph` (with `arrays`) creates graph code: its premises are
  the captures, each a slot of the node's context at the type the code was
  checked with, and every signature the created type offers must be an entry
  of the checked codes with those capture types; it checks no body, since the
  code's own certificate did. Code without a rest offers each row of its
  type's `offerRows`: each fixed signature, then each variadic signature's
  receiver, fixed parameters and result, in that order, each offering at
  least the code's arity. Code with a rest offers the variadic signatures
  only, each taking exactly the code's parameters, and `arrays` name their
  rest-store types in order, each the `store` of that signature's entry. At
  a scheme row the signatures are the scheme's. `funGraphSelf` creates a
  recursive closure of fixed arity at an arrow type, as `funGraph`, each
  entry's capture types followed by the created type, the self entry's.
  `ctorGraph` (with `undef`) creates a class value's construct-only code: an
  entry per construct signature, its receiver the `undefined` type, its
  effect the signature's (a variadic signature's effect is plain), with the
  code field, then one initializer premise per static field, then the
  captures. `callableGraph` (with `arrays`) creates a callable object: one
  initializer premise per field, then the captures, its code's entries as
  `funGraph`'s, one per advertised overload; its result has a single initial
  bag contract, to which subtyping can add equivalent invariant
  requirements.
- **Calls.** `app` and `callCallable` carry the selected signature's
  `effect` and take the callee premise, then the receiver premise at the
  selected signature's receiver, then the actuals, then one premise per
  position the signature declares and the call omits, each proving
  `undefined` at that position's contract: the term is `invoke f r args`,
  and a plain call's receiver is `undefined`. `callRest` (with `effect`,
  `fixed`, `omitted`, `spreads` and `rest`) carries the callee premise, the
  receiver premise, one premise per fixed actual, one `undefined` premise per
  fixed position the call omits, then one per further part: the actual at
  the element type, or, for a spread, the store it reads, at a type whose
  elements that element type admits. `callPacked` (with `effect`, `fixed`,
  `packed` and `rest`) names how many actuals are fixed, the packed binder
  and the rest type, with premises for the callee, the receiver, each fixed
  actual and the value whose store the last actual spreads. `construct`
  (with `effect`, which is plain) takes the constructor's premise, then one
  per actual and one `undefined` premise per position the signature declares
  and the construction omits. `constructRest` (with `fixed`, `spreads` and
  `rest`) is `callRest` without a receiver; its signature's effect is plain.
  `readCallable` and `writeCallable` use the first invariant bag operand, a
  callable object's or a class value's, and `readBagView` a class value's
  readonly static field, a view.
- **Binding methods.** `bindE` has no premises: its term is
  `makeAt (bound (var t) (var r) pre) [] []` with every prefix entry a slot,
  and the rule reads the target's type, the receiver's and the prefix's from
  the context. One fixed signature of the target must be the receiver slot's
  type, the prefix slots' types followed by the result's parameters, and the
  result's result; the result is one signature at any receiver. `bindRestE`
  binds a variadic target likewise. `bindMember` (with `proofs`, `rests` and
  `receivers`) has no premises: its term is
  `letE (readAt k (var i)) (makeAt (bound (var 0) (var (i + 1)) []) [] [])`,
  which reads the member `k` from the object in slot `i` and binds it to that
  same object. The object's type must have one object clause with a method of
  key `k`; each fixed signature of the result must be covered by one of the
  method's, at any receiver, by the subtyping proofs the rule carries, one
  per parameter, then the result; each variadic one likewise, one per fixed
  parameter, then the rest, then the result; and the object's type must be
  within each type the method's host must meet, by one more proof each, in
  the method's order. With no proofs, the result may instead be one of the
  method's quantified signatures, a scheme row (`HasTyUsing.bindScheme`),
  which a call instantiates by `sub`.

### Read summaries

`readSummaries` lists entries `{"receiver": C, "field": f, "result": B,
"arms": [...]}`, one arm per member of `C` in `members` order, each
`{"view": A, "proof": p}`: the view the member states for `f` and the
subtype choices comparing `A` to `B`, or `null` where `A` is `B`. An
entry is checked once against the request's graph and image check: exactly
one arm per member, each member's view of `f` at `A` (a view of `length`
only at a type excluding a number) and each comparison accepted by the
ordinary subtype checker
([read summaries](PROGRAM-TYPING.md#read-summaries)). An entry states no
location, heap fact or cached value, and a summary field beside these is
refused.

### Subtype certificates

Subtype arrow certificates use ordered lists of argument types. A `source`
certificate's `p` is the complete contract record. A `union` certificate
contains `pre`, `a`, `b`, `suffix`, `left`, and `right`: `pre` and `suffix`
are lists of unchanged argument types, and the selected argument splits from
`a ++ b` into the two branches. `combine` retains its result types `b` and
`b'`, the two premise effects `effect` and `other`, and two branches; the
meet of those effects must imply the target effect, and each source or rest
covering must also imply it. `empty` requires an empty type at some argument
position, not merely a zero-length argument list; `emptyRecv` requires the
target's receiver to be empty, so that no call is named; `recvUnion` splits
the target's receiver `a ++ b` into two branches, like `union` for an
argument. A `rest` certificate's `s` is a variadic source signature with
`arguments: [params, rest]` covering the target arrow: its first positions
within `params`, the rest within the rest contract. Graph subtype search
supports native argument lists and splits any position. There is one
accepted certificate shape.

## Heap facts

`knowledge` and `output` each contain `cells`, `values` and `links`
([checked expression postconditions](PROGRAM-TYPING.md#checked-expression-postconditions)).

- `cells` and `values` are lists of `{slot, contents, field}` facts: for a
  cell, about the named field of the object in the slot; for a value, about
  the slot itself. `contents` is a nonempty disjunction of atoms: `"nul"`,
  `"undef"`, `"tru"`, `"fls"`, `"num"`, `"str"`, `"defined"`, `"nonNull"`,
  `"nonNullish"`, `{"numLit":{"bits":"…"}}`, `{"strLit":{"value":"…"}}`, and
  `{"tag":{"test":k,"answer":b}}`, a test's observed answer. A singleton fact
  can weaken to its family, never the reverse.
- `links` is a list of `{cell, value, alias, field, distinct, other, optional}`
  objects: `alias: true` means equal slot values; `alias: false` means the
  named field currently contains the other slot's value (a read link), or,
  with `optional: true`, that the object lacks the key and the other slot
  holds `undefined`; `distinct: true` means field `field` of the object in
  `cell` and field `other` of the object in `value` are different locations,
  a timeless fact established by allocation, since fresh locations differ
  from every field of every record-typed slot in scope, and the reason a
  write to one cell keeps facts about another.

These are finite state assertions, not extra type labels. Current-content
predicates are checked on every incoming edge; a predicate the rules do not
support still requires a proof that the storage contract implies the claim.

The effect checker binds to the root expression sequent and must establish
exactly `output`. Each outgoing edge checks fact entailment against the
destination's `knowledge`, in addition to ordinary type coverage.
Effect-only continuations drop the result slot before transferring facts.
External entry requires empty knowledge. Within a source statement, the
producer derives checked facts along administrative paths, and the source
consumer enforces the exact entry interfaces.

### Step evidence

`effect: null` selects ordinary expression evidence; a non-null effect
selects one of the checked `StepEvidence` constructors:

- `ordinary`, with a `proof`: any expression; it keeps the value facts and
  the stable links, and no cell fact;
- `pure`, with a `proof` of a pure term: keeps every fact, and states the
  result's value where the term is a slot or a literal;
- `reading`, with a `proof` of a term built by field and element reads over
  variables and values: keeps every fact;
- `created`, with a `proof`: graph code creation;
- `typedRead`, with `slot` and `proof`: a nonempty expansion of plain or
  callable bags whose first invariant operand each has the field read, or
  plain records stating it as a readonly view other than `length`, at any
  type; empty expansions and non-bag alternatives are refused; its stored
  read links retain the receiver descriptor;
- `observedRead`, with `slot` and `contents`: a read of a location a cell
  fact states;
- `slicedRead`, with `tag`, `answer`, `slot`, `proof` and `sub`: every atom
  of one of the location's facts answers the tag so (a nullish exclusion
  answers its test `false`; a tag atom is its answer), and `sub` proves that
  the ordinary read contract's slice by that answer fits the requested type,
  or the slice is `Array.isArray`'s, whose array the requested type holds;
- `knownValue`, with `slot` and `contents`: a slot whose value facts state
  its contents;
- `linkedRead`, with `slot`, `value` and `sub`: a read of the slot's field
  where a read link says the field holds the value of slot `value`, at that
  value's type, below the claim by `sub`
  ([linked reads](HOST-FAMILIES.md#linked-reads));
- `allocated`, with a `proof`, for either descriptor: it requires
  `make code (var slot)` and checks the entire term's scope and creation
  proof; the code descriptor is part of the requested term, so changing it
  invalidates the evidence;
- `written`, with `receiver`, `value`, `contents` and `proof`: the written
  value's predicate, or `null` where it is not a known primitive.

### Promise facts

`implies` lists `{test, target, type}`: where the Boolean in slot `test` is
`true`, slot `target` holds a `type`; incoming edges must establish them.
`yields` lists `{conditional, target, type, evidence, onFalse}`: what the
node's result promises of slot `target`, where it is `true`
(`conditional`), where it is `false` (`onFalse`) or wherever the expression
returns, with the subtype evidence a tag test's slice needs. `arguments`
lists the entry slots holding the promised input. At a return, `promise` is
`null` or `[slot, proof]`: one of those slots and a subtype proof that its
type, refined by the yields, is within the promise.

## Equations and tree labels

A type can also be read from recursive equations
([RECURSIVE-EQUATIONS](RECURSIVE-EQUATIONS.md#2-type-definitions)), whose
labels are trees over the equations' heads. The source path checks every
request over them.

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

| Tree                                    | Spelling                                                                                  |
| --------------------------------------- | ----------------------------------------------------------------------------------------- |
| nullary application of head `h`         | `h`                                                                                       |
| application with arguments              | `{"app": h, "args": [[…], …]}`, `args` non-empty                                          |
| owned parameter                         | `{"bound": h, "args": [[…], …], "slot": j}`, `args` left out when empty                   |
| meet                                    | `{"meet": [L, …]}`: flat, at least two parts, canonical order                             |
| template placeholder (bodies only)      | `{"arg": i}`, `{"local": j}`                                                              |
| family variable (inside its entry only) | `{"var": k, "owner": o, "kind": "value" \| "arguments" \| "packed"}`                      |

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
instance carries its finite `domain`, `table`, `instances` and `free`. Each
tuple retains the source type, fixed and variadic signatures, and the
instance object. The checker selects the rule and discovers the comparison
dependencies. A nested bound comparison selects its candidate from these
tuples and validates its kinds, images and bounds before using it. Candidate
presence is not a proof.

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
depth, with names for applications
([the label projection](OBLIGATION-DIAGNOSTICS.md#the-label-projection)).

## Source evidence bundle

The evidence file of the source commands is
`{"main": bundle, "modules": [{"location": l, "evidence": bundle}, …]}`: the
checked file's bundle, and one per module run of its
[certified imports](SOURCE-CONTRACTS.md#certified-imports), in the order of the
Fragment's `modules`, each named by its location
(`SourceClaimJson.evidenceParts`). Each module run is checked as a document
of its own, over its own store.

A bundle is a strict object with `functions` and `obligations` arrays.
`functions` contains one response per reconstructed code unit in source
order. `obligations` contains one evidence list per unit, including empty
lists, in the same order. Each evidence tree must establish the corresponding
expression or annotation judgment reconstructed by extraction. Counts, graph
claims and root judgments must agree exactly with those reconstructed
requests. The order of functions in the producer's claims document does not
determine this evidence order.

[SourceRequests.Bundle](../lean/Verification/Source/SourceRequests.lean)
declares the bundle and checks its graph interfaces and expression
obligations.
[SourceClaimJson.checkJson](../lean/Verification/Source/Claims/Json.lean)
reconstructs the plans from Fragment and SourceClaims, strictly decodes the
bundles and checks every certified request.

## Proved boundary and validation

`checkJson_safe` proves that acceptance yields the strictly decoded bundle
and a successful `checkRequests` over the requests reconstructed from the
source and claims. Each request's check is `verify`, which binds the
certificate to the requested point annotations (`verify_eq`, through
`acceptUsing_eq`). It establishes global modeled safety at every observation
budget and every admitted assignment of the parameter rows
(`verify_safe_at`, `verify_qualified_safe_at`), for **any** argument
environment satisfying `inputs`, admissible world and satisfying heap. The
theorem reuses graph safety, including cycles, heap changes and explicit slot
maps.

`produceJson` serializes generated evidence and submits it through the same
JSON consumer before returning it. The safety theorem does not require using
this producer. Search is incomplete; failure is not a proof of untypability.
