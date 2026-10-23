# Callables

Callable verification requires a distinction between object identity, invocation
code, mutable properties and the contracts permitting each operation. This
document specifies the proved callable fragment and the proposed extension to
construction, exception bounds and stateful invocation contracts. The proposed
rules state design requirements; their soundness is not established here.

The prerequisites are the ordinary and state judgments in
[Program typing](PROGRAM-TYPING.md), object values and graph code in
[Semantics](SEMANTICS.md), and graph clauses and checked subtyping in
[Positive types](POSITIVE-TYPES.md). Types are finite unions of graph labels;
$`\Gamma`$ assigns types to variables, and $`\Gamma\vdash_G t:A`$ is the ordinary
term judgment. Declaration lowering and native contracts are specified in
[Source contracts](SOURCE-CONTRACTS.md); source closure evidence in
[Source elaboration](SOURCE-ELABORATION.md).

## What a function is, and what the calculus has

A JavaScript function value is three things: **code** — its `[[Call]]`
behaviour, which cannot be changed after creation; a **property bag** —
`f.cancel = …` is an ordinary object write; and an **identity** — `f === g`.
A value is a function exactly when it has `[[Call]]`, which is what
`typeof f === "function"` tests. Having `[[Call]]` does not make a call safe: a
class constructor's `[[Call]]` always throws, and a value of TypeScript's
`Function` type has `[[Call]]` and no known signature. Every constructor also has
`[[Call]]`, so constructibility implies `typeof "function"`.

The [operational language](SEMANTICS.md#operational-language) has object values for both
plain objects (`objAt fields absent identity`) and functions (`objAt fields code identity`, graph
code for every source function), where `fields` is the finite map from field names to the locations
they stand for and `identity` the object's identity cell, both fixed at allocation. `CallCode` is a separate descriptor type;
its body is not a runtime value. `makeAt code names inits` takes one fresh
location per named field, then the identity cell; a source function is the one-field case,
`makeFn code null`, a null-initialized bag under the key `[[code]]`, which no
source key spells and a copy does not take: a function has no properties of
its own.
`letE` binds without allocation. Plain allocation and one-field function
creation are abbreviations of `makeAt`, with one congruence rule, one
allocation step, and the shared semantic proofs `make_fields_rule` and
`makeFn_rule`. `isFun` recognizes function objects and
`isRef` recognizes plain objects, both independently of the heap.

[CallableObjects.lean](../lean/Verification/Programs/CallableObjects.lean) proves that a callable object's fields are read and written as a record's.
`bagT P` describes an object's writable fields independently of its call code,
read and written as a record's (`bag_read`, `bag_write`); the call contracts
(`callsT`, `restsT`) hold of the same value. `EnvOk.prepend` extends environments with ordered
parameter lists, `frame_envOk` builds the frame graph code is entered with
from the receiver, the parameters the code takes and the captured values, and
`graph_invoke` and `graphRest_invoke` derive the native call contract from a
checked code. Source functions lower to graph code, and the certificate
producer and consumer use its allocating typing rules (`funGraph`,
`funScheme`, `ctorGraph`, `callableGraph`). A checked creation effect preserves existing heap knowledge without
executing the body. Allocation, application, bag reads and writes,
and overload conjunction have safety proofs. The graph clause
`callable first rest arrows variadic` combines a nonempty conjunction of bag
invariants with fixed and variadic call promises on one object. Normalization
merges the corresponding lists; structural
subtyping checks invariant bag coverage and arrow coverage separately, and can
forget properties to obtain `arrs`. The producer and consumer support
`callableGraph`, `callCallable`, `readCallable`, and `writeCallable` evidence.

Every signature carries its
receiver, and every call its receiver premise; an ordinary function expression
or object-literal method binds the receiver of each call as `this`, and an
arrow's `this` is a capture of the enclosing one. A method call saves the
object, reads and saves the method, evaluates the actuals, then invokes the
saved method with the saved object, so an actual that replaces the method
field changes only later calls and one that writes a receiver field is seen by
the body. The receiver each call passes is also a located `method-receiver`
obligation. `.bind` allocates the forwarding descriptor `bound(f, r, p⃗)`
(`bindE`), whose invocation ignores its own receiver: a second `.bind` or a
`.call` on it cannot replace the first receiver, and a write to the receiver's
field after binding is seen, since the descriptor saves the object, not its
fields. A quantified ordinary function may name its binder as its receiver; its
body is checked once under the binder and each call is an instance at the
receiver it passes. The witnesses are `pipeline/examples/callables/methods.ts`,
`call-objects.ts`, `apply.ts` and `generic-receivers.ts`.
The pipeline case `recursive-callable` holds the recursive contract
`R = callable(null | R; Boolean → Boolean)`: a function is written into its
own bag, read back, narrowed and called, and passed and returned at `R`;
`invalid-recursive-callable` refuses a view of the bag that also admits
`true`, as the bag's field is invariant. These use the existing rules; no
recursive-callable special case or additional semantic axiom is needed.
The safety contract guarantees progress, not termination.
Graph reference clauses mean plain objects. A callability-neutral
bag view can be expressed as `refs P Ps | callable P Ps []` using two graph
labels; the union forgets invocation promises without changing the object. The pipeline case
`callable-bag-union` reads and writes a field through a union of a record and
a function carrying it, and `invalid-callable-bag-union` refuses a write the
function's bag does not admit. Proof search first tries a single
constructor view, then splits an explicitly union-typed receiver variable for
reads, writes, and calls, using the existing `unionVar` evidence. Every alternative
must check; a null alternative cannot be ignored. Both allocation shapes run
through the same read/write graph and JSON protocol without a runtime tag
branch. The view makes no invocation promise.
A call through a union of known signatures needs every alternative to accept
the actual argument and produce a result covered by the requested type. The
producer states no claim for a call through a union of functions carrying
different fields (`callable-bag-union-call-refused`). This does
not invent a signature from `typeof`, pick a successful alternative, or require
a common arrow label in the graph. The producer emits ordinary `unionVar`
evidence; the consumer and wire format are unchanged.
The pipeline case `callable-union-capture` is the source-closure path for
unions of primitive-only function signatures. The direct recipe saves the
callee and argument in order, then checks each alternative at the saved
callee slot and joins the signature results; `pipeline/test.mts`
refuses a result claim narrowed to one alternative at the call.
Single-arrow call recipes keep their existing form.
Explicit normalized source claims also exercise unions of overloaded functions:
the applicable signature occurs at different positions in the two alternatives,
and changing from a null to a Boolean argument reverses those positions. Both
calls verify; discarding a possible result or omitting one alternative's applicable
signature fails. This validates the source adapter and independent consumer.
Null-guard regressions retain every callable alternative on the non-null arm
for both comparison polarities and operand orders. Calls on the null arm and
unjustifiably narrow results fail. The `guardedCallableUnion` TypeScript fixture
also runs through the parser, the OCaml producer and the independent source
consumer.
The `coalescedCallable` fixture selects between a null/undefined-or-callable
input and a fallback before invocation. Both distinct return contracts survive
export and verification. Producer and consumer regressions reject a discarded
fallback alternative, a narrowed result, reuse of the nullish input as the
fallback, a null fallback, and an incompatible argument.
These sources are the [callable examples](../pipeline/examples/callables/README.md),
each a pipeline case.
The `andGuardedCallable` and `orGuardedCallable` examples exercise short-circuit
calls with singleton call results. Their full expression results also include
the skipped branch. Reversing the guard, changing the short-circuit operator,
or discarding the skipped result fails both production and independent checking.
`capturedGuardedCallable` returns a closure from a guarded branch, retaining the
immutable capture's non-null refinement for later calls. Both callable alternatives
remain possible. A reversed guard, discarded alternative, narrowed closure
signature, or narrowed inner call result fails producer and consumer checks.
`aliasedCallableSelection` selects an immutable local alias with a ternary and
captures it in a nested closure. Both alternatives survive the selection and
the next statement's environment. False initializer and entry claims, reversed
selection, reuse of the original nullable input, and narrowed nested-call results
fail independently checked obligations.
`sharedCallableDomain` selects between Boolean-accepting and true-only functions.
The shared true argument verifies. A false argument, forged widening of the
callee's domain, removal of its restrictive alternative, or narrowed result
fails both production and independent consumption.
`branchLocalCallableDomains` uses the tested Boolean as the argument inside
each branch: its true refinement satisfies a true-only domain, while its false
refinement requires the wider Boolean domain. Both singleton results reach the
join. Forged argument refinements, an incompatible false-branch callee, false
branch-result claims, and a narrowed join fail producer and consumer checks.
`callableArgumentWrite` writes a captured Boolean cell in a call's argument.
Storage and parameter obligations both remain checked, and the assignment
returns its RHS. The original Boolean export verifies; an explicit false-result
refinement also verifies with a false-only callee view and fresh evidence.
The original evidence cannot justify that stronger request. Captured reads
continue to use the Boolean invariant rather than an invented singleton.
`nestedCallableArgumentWrite` exercises the compositional closure path for an
argument write. Its exact expression proof saves the receiver, binds the named
RHS at the shifted position, writes once, and returns that saved RHS. Corrupting
the evidence to use the Boolean seed capture instead of the Boolean parameter
fails, even though their types agree. Wrong receiver and narrowed RHS/result
claims also fail production and independent consumption.
The pipeline cases `cell-union-capture` and `invalid-cell-union-write` check
reads and writes through unions of locally
allocated invariant cells inside source closures. Reads join possible contents. Writes check the saved
RHS against every alternative, evaluate each operand once, and return that RHS
as the source assignment value. Direct recipes need no expression-search fuel.
A write accepted by only one alternative fails the source consumer.
`pipeline/test.mts` adds current-content assertions to the producer's
claims, each a located obligation over the union of invariant contents: a
broad observation verifies at the closure's read, one narrowed to the
allocation's initial value fails there, a null-only statement-entry
observation holds after the closure writes `null` and fails where nothing
wrote it, and an entry environment that narrows the captured storage contract
fails its own obligation even when its contents observation holds.
Typed reads retain current heap
facts and read links when every alternative has the same invariant operand.
The regression keeps a known `false` fact about another cell across a neutral
read, then checks a singleton result from that cell through the JSON pipeline. Source export of a combined callable/property type covers one required `value`
field on a function.
Source integration also needs explicit property-presence/initialization rules:
the model's initial function bag does not establish a source `value` field.
Object parameters are admitted at their annotation: the interpretation of a
structural annotation as a plain data object is part of the caller contract,
as the arrow interpretation already was (DESIGN.md, the trust surface). The
heap evidence is stated over locations and so covers aliased parameters.
The consumer checks that graph syntax embeds no runtime identity
(`ObjectCoherence.sourceTerm`). The construction, receiver, exception and richer property-operation
rules of C* in [Typing rules](#typing-rules) are proposed extensions.

The model has no separate function type. A function type is an object type whose
fields carry a `call` member, and every object type carries a call mode from a
four-point lattice: `CPresent(L)`, invocable with the signatures in $`L`$;
`CFunction`, which has `[[Call]]` and no known signature (`Function`, a class
constructor); `CAbsent`, provably not callable (object literals, class
instances, arrays); and `CUnknown`, a structural object type — `{}`, an
interface — which width subtyping lets a function inhabit. The
[views these modes obtain](#shape-tests-and-identity) are given with the rules.
The producer refuses positive callability on cells and function
shape without a signature. Ordinary exported function signatures already run
through the allocated-function path.

## Callable pairs and operation descriptors

A callable pair consists of a closure body and a location for its properties, $`\mathsf{callable}(b,\ell)`$, created by
$`\mathsf{attach}(\lambda x.t,\,v)`$, which allocates the bag as $`\mathsf{alloc}`$
does; a call on it is one beta step, reads and writes go to the bag, and
$`\mathsf{isFun}`$ answers true for it. Its type $`\mathsf{Callable}(L;C)`$ is the
arrow family over $`L`$ intersected with the bag's reference contract, every
callable is a function, and $`\mathsf{isFun}`$ stays total and heap-independent.
The proposed design **C\*** generalizes the callable pair to a uniform object
model with identity, property operations, and separate call and construction
behaviours. Its operations, types and rules include those of the callable pair
as special cases.

| Notation                                                                                | Meaning                                                                                                           |
| --------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------- |
| $`\Gamma\vdash_G t:A\;!E`$                                                                | a computation whose normal results have type $`A`$ and whose thrown values have type $`E`$; $`E=\bot`$ when unannotated |
| $`\vdash_G^{\mathsf{call}}`$, $`\vdash_G^{\mathsf{construct}}`$, $`\vdash_G^{\mathsf{init}}`$ | auxiliary judgments on invocation programs and initial property layouts                                           |
| $`\sigma=(R;\alpha)\xrightarrow{E}B`$                                                     | a call signature: receiver contract $`R`$, argument-list contract $`\alpha`$, exception bound $`E`$, result $`B`$         |
| $`\nu=(N;\alpha)\xRightarrow{E}B`$                                                        | a construction signature, with $`N`$ the contract on `new.target`                                                   |
| $`\bar a`$, $`\bar p`$                                                                      | an actual argument list, and stored bound arguments                                                               |
| $`\mathsf{Obj}(P)`$, $`\mathsf{Fun}`$, $`\mathsf{Ctor}`$                                      | objects meeting the property contract $`P`$; objects with `[[Call]]`; objects with `[[Construct]]`                  |
| $`\top_p`$                                                                                | the property contract imposing no requirement                                                                     |
| $`\ell`$, $`\delta`$, $`\pi`$, $`\kappa`$, $`\eta`$                                               | an identity, an operation descriptor, and its property, call and construction components                          |

## One object identity, several operations

Every source-level object, including every function, has an identity.
Represent an object value schematically as

```math
\mathsf{object}(\ell,\delta),
```

where $`\ell`$ is its identity and $`\delta`$ is an internal operation descriptor:

```math
\delta =
\left\langle
  \mathsf{properties}:\pi,\quad
  \mathsf{call}:\mathrm{Option}(\kappa),\quad
  \mathsf{construct}:\mathrm{Option}(\eta)
\right\rangle.
```

The descriptor determines **how operations are dispatched**. The heap contains
the mutable state those operations use. Neither the descriptor nor its
components are ordinary, source-visible properties.

This follows the relevant distinction in ECMAScript: objects support property
operations, while function objects additionally have `[[Call]]` and possibly
`[[Construct]]`. Those internal operations are not properties named `call` or
`construct`. ([ECMA-262](REFERENCES.md#ecma-262))

Once creation is complete, the presence of the call and construction operations
is stable. Their behaviour need not be independent of mutable state.

In this representation,

```math
\mathsf{isFun}(\mathsf{object}(\ell,\delta))
\iff
\delta.\mathsf{call}\ne\mathsf{None},
```

and source-level object equality compares identities:

```math
\mathsf{object}(\ell,\delta)
  ===
\mathsf{object}(\ell',\delta')
\iff
\ell=\ell'.
```

Well-formedness requires a unique descriptor for each identity. Thus
function-shape tests can remain heap-independent without making function
behaviour heap-independent.

**All functions receive this representation at creation, not when their first
custom property is added.** A plain function type, a callable-with-properties
type, and a property-only type are views of the same value. Subsumption never
allocates, wraps, or replaces it.

That is the principal coherence requirement.

## Invocation is not restricted to beta reduction

The operational interface contains

```math
\begin{aligned}
&\mathrm{Call}(f,r,\bar a),\\
&\mathrm{Construct}(f,\bar a,n),\\
&\mathrm{Get}(o,k,r),\\
&\mathrm{Set}(o,k,v,r).
\end{aligned}
```

Here $`r`$ is the receiver, $`\bar a`$ is the actual argument list, and $`n`$ is
`new.target`.

A call descriptor specifies an invocation algorithm. Entering a closure body is
one such algorithm — not the definition of invocation for every callable.

The following are cases of that interface, rather than competing
representations:

| Source form                                 | Account in C\*                                                                                                                                                          |
| ------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Ordinary function declaration or expression | A closure with an environment and the appropriate strict or non-strict receiver discipline. Declaration versus expression also affects when its binding is initialized. |
| Arrow function                              | A closure whose references to `this`, `arguments`, `super`, and `new.target` resolve through the enclosing lexical environment. It has no construction operation.       |
| Object or class method                      | A function whose invocation receives the call-site receiver; its home-object association supports `super`. Extracting the function does not bind that receiver.         |
| Class-field arrow                           | Arrow creation performed during instance initialization, producing a distinct function identity for each instance.                                                      |
| Bound function                              | A fresh object whose call operation forwards to a target with stored receiver and arguments. Construction, when supported, has its own forwarding rule.                 |
| Class constructor                           | An object with a construction operation and a call operation that throws. Function shape therefore does not imply a successful ordinary call.                           |
| Callable proxy                              | A fresh object whose operations dispatch through proxy algorithms, consulting its target, handler, and revocation state.                                                |
| Async or generator function                 | A function whose invocation uses the corresponding promise or suspended-computation semantics.                                                                          |

The ordinary-function, arrow, method, and class distinctions come from the
function-creation and invocation rules; in particular, an arrow captures an
environment for the special bindings, not merely a copied receiver value.
([ECMA-262](REFERENCES.md#ecma-262)) Bound functions and proxies have distinct forwarding algorithms.
([ECMA-262](REFERENCES.md#ecma-262)) Async and generator behaviour requires the corresponding
control-state semantics. ([ECMA-262](REFERENCES.md#ecma-262))

The important consequence is that **there is no need for a separate source type
constructor for "arrow-function values"**. Their creation and invocation rules
differ, but they may satisfy the same call contracts as ordinary functions.

Similarly, a TypeScript object type containing a call signature describes an
interface. It is not another runtime creation mechanism. TypeScript explicitly
permits call signatures, properties, and construct signatures to coexist in one
type. ([TypeScript](REFERENCES.md#typescript))

## Properties must mean object operations, not just a bag of cells

For the complete account, the property component cannot be specified solely by

```math
\mathrm{Get}(o,k)=H(o)[k].
```

An object may have data properties, accessors, inherited properties, and
symbol-keyed properties. Property operations can invoke code; proxies can
intercept them. ECMAScript accordingly specifies property descriptors and
internal property operations separately from a simple field store. ([ECMA-262](REFERENCES.md#ecma-262))

C\* should therefore distinguish two semantic assertions:

```math
\mathsf{OwnData}(o,k,A)
```

for a particular kind of stored property, and

```math
\mathsf{Readable}(o,k,A)
```

for an appropriate contract on reading the property.

They are not interchangeable. The latter may require a computation contract,
including effects and exceptions. Writable properties require corresponding
write permissions and preservation obligations.

Ordinary data properties can retain the simpler reference-based rules. They
become a **verified special case** of the general object interface.

This also explains how decoration and wrapping differ in the design. Decoration
operates on an existing object identity. Wrapping creates a new object with a
forwarding call operation; sharing or copying properties is a separate action.
`Object.assign`, for example, returns its target rather than replacing its
identity. ([ECMA-262](REFERENCES.md#ecma-262))

## Types describe behaviour, not internal storage

Keep shape, properties, calls, and construction as separate predicates.

For shape,

```math
\mathsf{Ctor}<:\mathsf{Fun}<:\mathsf{Obj}.
```

The first inclusion reflects the ECMAScript invariant that an object with
`[[Construct]]` also has `[[Call]]`; it does **not** assert that ordinary
invocation succeeds. ([ECMA-262](REFERENCES.md#ecma-262))

For callable contracts,

```math
\mathsf{Callable}(L;P)
=
\mathsf{Fun}
\cap \mathsf{Props}(P)
\cap \bigcap_{\sigma\in L}\mathsf{CallSpec}(\sigma).
```

This is the organizing equation of the implemented model. [SEMANTICS.md](SEMANTICS.md#one-meaning-for-callable-contracts)
states the indexed call promise precisely and maps each component to Lean.
Fixed and variadic signatures share that promise; code-specific binding rules
establish it at creation. The construction and receiver judgments of C* in
[Typing rules](#typing-rules) are proposed extensions. Quantified rest signatures use the same universal introduction
and instantiated call promises as fixed signatures.

For construction contracts,

```math
\mathsf{Constructible}(M)
=
\mathsf{Ctor}
\cap \bigcap_{\nu\in M}\mathsf{ConstructSpec}(\nu).
```

A value usable both ways has their intersection. A property-only view drops the
call and construction requirements without asserting their absence.

The empty call family still means function shape with no supplied call
contract:

```math
\mathsf{Callable}([];P)
=
\mathsf{Fun}\cap\mathsf{Props}(P).
```

This preserves the distinction between `CFunction` and `CUnknown` above:
knowing that a value is a function is different from merely not excluding
functions.

**Overloads.** Several call contracts are conjunctions of behavioural
obligations:

```math
\mathsf{CallSpec}(L)
\cap
\mathsf{CallSpec}(M)
=
\mathsf{CallSpec}(L\mathbin{+\!+}M).
```

They are **not** assertions that a writable internal cell has two different
invariant content types. This is the law
[`CallEffects.callsT_append`](../lean/Verification/Semantics/CallEffects.lean)
proves for `callsT`.

Consequently, placing the implementation in the heap does not itself damage
overloads. The difficulty with A — boxing every function as an ordinary
reference — was typing the implementation through an ordinary writable
reference. A\* avoids that by separating the internal invocation mechanism from
source-level mutation.

**Generics and argument lists.** A call contract must be able to express a
quantified relationship, schematically

```math
\forall\bar X.\;
(R;\alpha)\Rightarrow B,
```

where $`R`$ describes the receiver and $`\alpha`$ describes an argument list.

Quantification is needed for generic input/output relationships; argument-list
contracts handle optional and rest parameters. These are features of the
contract language, not new runtime callable shapes. TypeScript exposes both
generic signatures and these parameter forms. ([TypeScript](REFERENCES.md#typescript))

This means the complete account needs more than the finite families of
monomorphic arrows this document has so far. It needs a specified
quantification discipline and rules connecting those richer contracts to the
existing type fragment.

Quantified contracts are scheme rows
([quantified schemes](POSITIVE-TYPES.md#quantified-scheme-layer)): a generic
unit is a graph request over parameter rows, and a generic closure is graph
code at a scheme row (`funScheme`), both certified at every assignment of the
rows ([Generic-Body](#overloads-polymorphism-and-binding)). There is no second
checker for generic bodies.

**Effects and state.** The behavioural obligation must use the computation
semantics, not just a relation between input and output values. Schematically,

```math
\{\mathcal P\}\;
\mathrm{Call}(f,r,\bar a)
\;\{\mathsf{return}\ v.\mathcal Q;\;
    \mathsf{throw}\ e.\mathcal E\}.
```

An ordinary arrow can abbreviate a suitable special case. Contracts for promises
and generators additionally describe subsequent interactions with the returned
objects.

This is where mutable captured state, callback protocols, and revocable
capabilities belong.

For example, revoking a callable proxy leaves its function shape intact, but
subsequent calls throw. Its callability is therefore a stable shape fact; a
guarantee that invocation will not throw requires stronger assumptions about
state. ([ECMA-262](REFERENCES.md#ecma-262))

A contract saying "every normal return is a number" may survive revocation. A
contract promising a successful numeric return does not follow merely from the
same shape information. The design must state which guarantee its arrows
express.

C\* carries the invocation descriptor in the value and keeps mutable object
state in the heap. Its general interface includes beta reduction and bag
access as special cases.

## Typing rules

The proposed rules specify callable introduction, application, property
access, and subsumption. They retain the ordinary
judgment $`\Gamma\vdash_G t:A`$; exception bounds, construction contracts, and the
stateful judgments are explicit additions. Their soundness is not established
here. The implemented and proved callable rules are stated in
[Judgments and constructor views](PROGRAM-TYPING.md#judgments-and-constructor-views) —
`callableGraph`, `callCallable`, `readCallable` and `writeCallable`, over the
$`\mathsf{Callable}(\varphi;L)`$ clause.

The principal distinction is between checking an invocation implementation,
allocating an object carrying that implementation, and using the resulting
object through a contract.

### Judgments and types

Write

```math
\Gamma\vdash_G t:A\;!E
```

for a computation whose normal results have type $`A`$ and whose thrown values
have type $`E`$. This is a safety judgment, not a termination guarantee. The
annotation bounds exceptions, not mutation. The unannotated judgment
abbreviates $`E=\bot`$.

Assumptions in $`\Gamma`$ are stable under permitted heap evolution. Assertions
about current contents belong in the state judgment introduced below.

Call and construction signatures are, respectively,

```math
\sigma=(R;\alpha)\xrightarrow{E}B,
\qquad
\nu=(N;\alpha)\xRightarrow{E}B.
```

Here $`R`$ constrains the supplied receiver, $`\alpha`$ constrains the actual
argument list, and $`N`$ constrains `new.target`. Construction signatures require

```math
N<:\mathsf{Ctor},
\qquad
B<:\mathsf{Obj}(\top_p).
```

Argument-list contracts need not specify an exact arity. Parameter binding,
defaults, and destructuring are computations in the function's entry program.

Define the constructor views

```math
\begin{aligned}
\mathsf{Calls}(L)
&=
\mathsf{Fun}\cap
\bigcap_{\sigma\in L}\mathsf{CallSpec}(\sigma),\\[2mm]
\mathsf{Callable}(L;P)
&=
\mathsf{Calls}(L)\cap\mathsf{Obj}(P),\\[2mm]
\mathsf{Constructor}(M;P)
&=
\mathsf{Ctor}\cap\mathsf{Obj}(P)\cap
\bigcap_{\nu\in M}\mathsf{ConstructSpec}(\nu).
\end{aligned}
```

$`P`$ is a property contract; $`\top_p`$ imposes no property requirement. In
particular,

```math
\mathsf{Calls}([])=\mathsf{Fun}.
```

An empty family supplies shape but no invocation contract.

Write $`\mathsf{Plain}(P)`$ for non-function objects satisfying $`P`$, and
$`\mathsf{NoCtor}`$ for objects without a construction operation. Neither asserts
an empty property store.

All operands in the operation rules below are values or previously bound
variables. Effectful operands are evaluated once, in source order, using
sequencing.

### Structural views and intersections

**Forget-Properties** and **Forget-Calls** are the two essential forgetful
rules:

```math
\frac{\Gamma\vdash_G f:\mathsf{Callable}(L;P)}
{\Gamma\vdash_G f:\mathsf{Calls}(L)}
\qquad
\frac{\Gamma\vdash_G f:\mathsf{Callable}(L;P)}
{\Gamma\vdash_G f:\mathsf{Obj}(P)}.
```

These change the available view, not the value. Neither allocates nor wraps.

**Constructor-Shape.** Construction implies function shape, but supplies no
successful ordinary-call contract:

```math
\frac{\Gamma\vdash_G f:\mathsf{Constructor}(M;P)}
{\Gamma\vdash_G f:\mathsf{Callable}([];P)}.
```

**Sub.** The ordinary subsumption rule is

```math
\frac{
\Gamma\vdash_G t:A\;!E
\qquad G\vdash A<:B
\qquad G\vdash E<:F
}{
\Gamma\vdash_G t:B\;!F
}.
```

**Call-Sub.** For unconditional call signatures,

```math
\frac{
\begin{gathered}
G\vdash R_2<:R_1
\qquad G\vdash\alpha_2<:\alpha_1\\
G\vdash B_1<:B_2
\qquad G\vdash E_1<:E_2
\end{gathered}
}{
G\vdash
(R_1;\alpha_1)\xrightarrow{E_1}B_1
<:
(R_2;\alpha_2)\xrightarrow{E_2}B_2
}.
```

Construction signatures have the corresponding variance in `new.target`,
arguments, normal results, and exceptions.

The intended intersection laws are

```math
\mathsf{Calls}(L)\cap\mathsf{Obj}(P)
=
\mathsf{Callable}(L;P),
```

```math
\mathsf{Callable}(L;P)\cap\mathsf{Callable}(M;Q)
=
\mathsf{Callable}(L{+\!\!+}M;P\wedge Q).
```

Here $`P\wedge Q`$ is a conjunction of property contracts. It is not a pointwise
intersection of writable-cell content types.

**Value-Meet.** Intersection introduction on an already obtained value is

```math
\frac{\Gamma\vdash_G v:A\qquad\Gamma\vdash_G v:B}
{\Gamma\vdash_G v:A\cap B}.
```

Both premises concern the same value under compatible heap invariants.
Independently checking two allocations does not establish an intersection on
one allocated object.

### Checking code and creating functions

Internal invocation descriptors are not source-level function values. Introduce
auxiliary judgments

```math
\Gamma\vdash_G^{\mathsf{call}}\kappa:L,
\qquad
\Gamma\vdash_G^{\mathsf{construct}}\eta:M,
\qquad
\Gamma\vdash_G^{\mathsf{init}}d:P.
```

The first two check invocation programs. The third checks an initial property
layout and the invariants it establishes. Initializer expressions have already
been evaluated.

**Ordinary functions: a dynamic receiver.** For strict ordinary-function code,
the rule **Dynamic** is

```math
\frac{
\left(
\Gamma,\mathsf{this}:R_i,\mathsf{argv}:\alpha_i
\vdash_G t:B_i\;!E_i
\right)_{i\in I}
}{
\Gamma\vdash_G^{\mathsf{call}}
\mathsf{dyn}(\mathsf{this},\mathsf{argv}.t):
\left[(R_i;\alpha_i)\xrightarrow{E_i}B_i\right]_{i\in I}
}.
```

The entry program $`t`$ includes parameter initialization and the normal-return
convention.

For non-strict functions, the entry program first performs the specified
receiver conversion. The supplied receiver and the body's `this` value must not
simply be identified. ECMAScript distinguishes strict, non-strict, and lexical
receiver binding.

**Arrow functions: a lexical receiver.** The rule **Lexical** is

```math
\frac{
\left(
\Gamma,\mathsf{argv}:\alpha_i
\vdash_G t:B_i\;!E_i
\right)_{i\in I}
}{
\Gamma\vdash_G^{\mathsf{call}}
\mathsf{lex}(\mathsf{argv}.t):
\left[(\top;\alpha_i)\xrightarrow{E_i}B_i\right]_{i\in I}
}.
```

The enclosing lexical environment in $`\Gamma`$ is captured. The rule introduces
no new source binding for `this`, `arguments`, `super`, or `new.target`;
$`\mathsf{argv}`$ is an internal parameter, not the source identifier
`arguments`. This corresponds to the lexical binding discipline of arrows.

A method uses Dynamic, with its home-object association in the captured
environment. A class-field arrow uses Lexical, with allocation performed during
instance initialization.

The stateful variants check the body under its invocation precondition. In
particular, capturing an initialization-sensitive lexical binding does not
require pretending that it was read at function creation.

**Allocation.** A callable without construction behaviour is introduced by
**Make-Function**,

```math
\frac{
\Gamma\vdash_G^{\mathsf{call}}\kappa:L
\qquad
\Gamma\vdash_G^{\mathsf{init}}d:P
}{
\Gamma\vdash_G
\mathsf{make}(\kappa,\mathsf{none},d):
\mathsf{Callable}(L;P)\cap\mathsf{NoCtor}
}.
```

A callable with construction behaviour is introduced by **Make-Constructor**,

```math
\frac{
\begin{gathered}
\Gamma\vdash_G^{\mathsf{call}}\kappa:L
\qquad
\Gamma\vdash_G^{\mathsf{construct}}\eta:M\\
\Gamma\vdash_G^{\mathsf{init}}d:P
\end{gathered}
}{
\Gamma\vdash_G
\mathsf{make}(\kappa,\eta,d):
\mathsf{Callable}(L;P)\cap
\mathsf{Constructor}(M;\top_p)
}.
```

An ordinary non-callable object is introduced by **Make-Object**,

```math
\frac{\Gamma\vdash_G^{\mathsf{init}}d:P}
{\Gamma\vdash_G
\mathsf{make}(\mathsf{none},\mathsf{none},d):
\mathsf{Plain}(P)}.
```

Every application of a make rule allocates one fresh object identity. There is
no rule with a construction descriptor but no call descriptor.

The callable pair's $`\mathsf{attach}`$ operation is a special case of allocation.
Decoration of an existing source function uses the Decorate rule.

### Invocation, property calls, and extraction

**Call.** The ordinary application rule is

```math
\frac{
\begin{gathered}
\Gamma\vdash_G f:\mathsf{Callable}(L;P)
\qquad (R;\alpha)\xrightarrow{E}B\in L\\
\Gamma\vdash_G r:R
\qquad \Gamma\vdash_G\bar a:\alpha
\end{gathered}
}{
\Gamma\vdash_G\mathsf{invoke}(f,r,\bar a):B\;!E
}.
```

**Bare-Call.** For a bare call in the strict/module fragment,

```math
\frac{
\begin{gathered}
\Gamma\vdash_G f:\mathsf{Calls}(L)
\qquad (R;\alpha)\xrightarrow{E}B\in L\\
G\vdash\mathsf{Undefined}<:R
\qquad\Gamma\vdash_G\bar a:\alpha
\end{gathered}
}{
\Gamma\vdash_G f(\bar a):B\;!E
}.
```

**Method-Call.** A method call is lookup followed by invocation:

```math
\frac{
\begin{gathered}
\Gamma\vdash_G\mathsf{get}(o,k,o):
\mathsf{Calls}(L)\;!E_g\\
(R;\alpha)\xrightarrow{E_c}B\in L
\qquad\Gamma\vdash_G o:R
\qquad\Gamma\vdash_G\bar a:\alpha
\end{gathered}
}{
\Gamma\vdash_G o[k](\bar a):B\;!(E_g\vee E_c)
}.
```

For effectful source expressions, the elaboration evaluates the base and key,
performs lookup, evaluates the arguments, and invokes the retrieved function
with the saved base as receiver. It neither reevaluates the base nor binds a
receiver during lookup.

Method extraction is only lookup. Consequently, extraction preserves the
receiver requirement in the function's contract; it does not transform that
contract into a bound-function contract.

### Properties

Property contracts expose operation signatures. For example,

```math
P\vdash_G\mathsf{get}(k):(R;[])\xrightarrow{E}A
```

states a contract for lookup at $`k`$, starting from an object satisfying $`P`$,
with a receiver in $`R`$.

The general rules are **Get** and **Set**:

```math
\frac{
\begin{gathered}
\Gamma\vdash_G o:\mathsf{Obj}(P)
\qquad\Gamma\vdash_G r:R\\
P\vdash_G\mathsf{get}(k):(R;[])\xrightarrow{E}A
\end{gathered}
}{
\Gamma\vdash_G\mathsf{get}(o,k,r):A\;!E
},
```

```math
\frac{
\begin{gathered}
\Gamma\vdash_G o:\mathsf{Obj}(P)
\qquad\Gamma\vdash_G r:R
\qquad\Gamma\vdash_G a:A\\
P\vdash_G\mathsf{set}(k):(R;[A])
\xrightarrow{E}\mathsf{Bool}
\end{gathered}
}{
\Gamma\vdash_G\mathsf{set}(o,k,a,r):
\mathsf{Bool}\;!E
}.
```

Set returns an internal success flag. A strict source assignment throws on
failure and returns the assigned value on success. That differs from the
calculus's `write`, which returns $`\mathsf{Null}`$.

**Ordinary data properties.** For a stable, writable own-data-property
invariant, the reference-style rules are recovered as **Read-Cell** and
**Write-Cell**:

```math
\frac{
\Gamma\vdash_G o:\mathsf{Obj}(\{k:\mathsf{cell}(A)\})
}{
\Gamma\vdash_G\mathsf{read}_k(o):A
},
\qquad
\frac{
\Gamma\vdash_G o:\mathsf{Obj}(\{k:\mathsf{cell}(A)\})
\qquad\Gamma\vdash_G a:A
}{
\Gamma\vdash_G\mathsf{write}_k(o,a):\mathsf{Null}
}.
```

These apply to callables through Forget-Calls. The cell contract is invariant
and also protects the descriptor assumptions against unchecked deletion or
redefinition.

For a fresh property layout, **Init-Data** is

```math
\frac{\Gamma\vdash_G v:A}
{\Gamma\vdash_G^{\mathsf{init}}
[k\mapsto\mathsf{data}(v)]:
\{k:\mathsf{cell}(A)\}}.
```

**Accessors.** An own getter is checked by **Init-Getter**:

```math
\frac{
\Gamma\vdash_G g:
\mathsf{Calls}([(R;[])\xrightarrow{E}A])
}{
\Gamma\vdash_G^{\mathsf{init}}
[k\mapsto\mathsf{accessor}(g,\mathsf{none})]:
\{\mathsf{get}(k):(R;[])\xrightarrow{E}A\}
}.
```

Dually, a setter with call contract

```math
(R;[A])\xrightarrow{E}\top
```

supplies a set contract returning $`\mathsf{True}`$ on normal completion: the
setter's returned value is discarded. These rules assume the corresponding
descriptor invariants; inherited lookup additionally requires the
prototype-chain obligations.

General accessors and proxies use Get/Set, not Read-Cell/Write-Cell.

An ordinary property named `call` or `apply` supplies no premise for Call.

### Construction

**Construct.**

```math
\frac{
\begin{gathered}
\Gamma\vdash_G f:\mathsf{Constructor}(M;P)
\qquad (N;\alpha)\xRightarrow{E}B\in M\\
\Gamma\vdash_G n:N
\qquad\Gamma\vdash_G\bar a:\alpha
\end{gathered}
}{
\Gamma\vdash_G
\mathsf{construct}(f,\bar a,n):B\;!E
}.
```

**New.** Ordinary `new` uses the constructor itself as `new.target`:

```math
\frac{
\begin{gathered}
\Gamma\vdash_G f:\mathsf{Constructor}(M;P)
\qquad (N;\alpha)\xRightarrow{E}B\in M\\
\Gamma\vdash_G f:N
\qquad\Gamma\vdash_G\bar a:\alpha
\end{gathered}
}{
\Gamma\vdash_G\mathsf{new}\ f(\bar a):B\;!E
}.
```

**Construction-Code.** The introduction rule checks the complete construction
program:

```math
\frac{
\begin{gathered}
\left(
\Gamma,\mathsf{newTarget}:N_i,\mathsf{argv}:\alpha_i
\vdash_G t_\eta:B_i\;!E_i
\right)_{i\in I}\\
(G\vdash N_i<:\mathsf{Ctor})_{i\in I}
\qquad
(G\vdash B_i<:\mathsf{Obj}(\top_p))_{i\in I}
\end{gathered}
}{
\Gamma\vdash_G^{\mathsf{construct}}
\mathsf{constructCode}(\mathsf{newTarget},\mathsf{argv}.t_\eta):
[(N_i;\alpha_i)\xRightarrow{E_i}B_i]_{i\in I}
}.
```

This program includes receiver allocation, prototype lookup, instance
initialization, and explicit-return handling. Derived constructors additionally
require `super` and initialization of `this`. Checking the source body as an
ordinary function returning $`B`$ is insufficient.

A contract proved only for ordinary `new` may restrict $`N`$ to the constructor's
own identity. It must not silently become a guarantee for arbitrary
`Reflect.construct` calls.

A class's ordinary-call descriptor can have the exception-aware signature

```math
(\top;\mathsf{Args})
\xrightarrow{\mathsf{TypeError}}\bot.
```

Thus it has function shape without a successful ordinary-call contract.

### Overloads, polymorphism, and binding

**Overloads.** The premises of Dynamic and Lexical check the same code against
every advertised signature before allocating one function object. Call selects
an applicable member. Forgetting members is subsumption; no writable
implementation cell is retyped.

**Generic signatures.** Let $`S`$ be a scheme row, $`\eta_0`$ the assignment
outside its binders, and $`\mathsf{Instance}_{G,P}(\eta_0,S,\eta)`$ the
reassignments of its binders within their bounds, $`\eta_0`$ unchanged outside
them (`Bounded`), as
[POSITIVE-TYPES.md](POSITIVE-TYPES.md#quantified-scheme-layer) defines. The exact
introduction rule **Call-Scheme-I**, which unfolds the definition of scheme
membership (`schemeSemWithArgs`), is

```math
\frac{
\mathsf{Invocable}(v)
\qquad
\forall\eta.\;
\mathsf{Instance}_{G,P}(\eta_0,S,\eta)
\Rightarrow
(\mathsf{Calls}(\mathsf{Sig}_{G,P,\eta}(S),n,W,v)
\land\mathsf{Rests}(\mathsf{RestSig}_{G,P,\eta}(S),n,W,v))
}{
⟦S⟧^{\mathsf{scheme}}_{G,P,\eta_0}(n,W,v)
}.
```

The value $`v`$, step index $`n`$, world $`W`$, and outer assignment $`\eta_0`$ are
outside the quantifier. The proof is therefore uniform in the binders, and
captured mutable cells retain the same invariant at every instantiation.
Fixed-signature elimination **Call-Scheme-E**, by the same unfolding, is

```math
\frac{
⟦S⟧^{\mathsf{scheme}}_{G,P,\eta_0}(n,W,v)
\qquad
\mathsf{Instance}_{G,P}(\eta_0,S,\eta)
}{
\mathsf{Calls}(\mathsf{Sig}_{G,P,\eta}(S),n,W,v)
}.
```

The same premises give the corresponding conclusion for the rest
signatures, $`\mathsf{Rests}(\mathsf{RestSig}_{G,P,\eta}(S),n,W,v)`$, from the
same premises: an instance's contract is both (`instanceTWithArgs`).

A call names its instance: the callee is read at the instance's signatures,
below the scheme by a checked instance table (`compareInstArrsState`), which constructs one
such $`\eta`$ after the type arguments' bounds are checked. It selects a
signature of the same callable; it neither allocates a new value nor changes
the outer assignment. These are rules for quantified invocation contracts, not
unrestricted generalization of an effectful allocation expression. One
callable value and one captured world satisfy every admissible assignment,
while elimination selects a signature only afterwards. A generic closure is
graph code at a call scheme row (**funScheme**,
[core rules](PROGRAM-TYPING.md#judgments-and-constructor-views)), its introduction the table's check
of its code, which holds at every assignment, a rest, a default or a binder
bounded by another included; a construct scheme's members are class values
([scheme rows](POSITIVE-TYPES.md#parameter-and-scheme-rows)), which no closure
is.

**Generic bodies.** A generic function's body is a graph request whose
binders are parameter rows $`\vec p`$: rows the graph's assignment interprets,
which no rule reads (a type holding one has no expansion). Acceptance does not
read the assignment (`accept_reassign` in [Parametricity.lean](../lean/Verification/Programs/Parametricity.lean)), so the rule
**Generic-Body** is the ordinary safety theorem at every reassignment:

```math
\frac{
\mathsf{accept}(G,R,P,\mathit{claims},C,s,\vec I)=\mathsf{true}
\qquad
\mathsf{EnvOk}_{G[\mathit{env}:=\eta]}(\vec I,\rho,n,W)
\qquad \mathsf{WorldAdm}(W)\qquad \mathsf{HeapOk}(n,W,h)
}{
\mathsf{SafeGraph}\bigl(P,⟦R⟧^{\eta},n,W,h,\mathsf{at}(s,\rho)\bigr)
}
\quad\text{for every }\eta .
```

One derivation, checked once, covers every instantiation of the binders: the
inputs and the result are read at the same $`\eta`$. A bounded binder is read as
the meet of its row and its bound, and one bounded by another binder as the
meet of the two ([binders met](SOURCE-CONTRACTS.md#binders-met-with-ground-types)); at every
instantiation within the bounds the meets are the binders, and the body is
certified at the others too. Every generic unit takes this one path. The
binders of a generic class are those of the unit that declares it, the
module's initialization unit, so its constructor and methods are certified at
every instantiation the same way. Lean:
`Parametricity.accepted_at`, `RequestJson.verify_safe_at`,
`SourceExtraction.checkRequests_safe_at`.

**Bound functions.** The internal bound-call descriptor has the rule
**Bound-Code**:

```math
\frac{
\begin{gathered}
\Gamma\vdash_G f:
\mathsf{Calls}([(R;\alpha{+\!\!+}\beta)
\xrightarrow{E}B])\\
\Gamma\vdash_G r:R
\qquad\Gamma\vdash_G\bar p:\alpha
\end{gathered}
}{
\Gamma\vdash_G^{\mathsf{call}}
\mathsf{bound}(f,r,\bar p):
[(\top;\beta)\xrightarrow{E}B]
}.
```

Allocation gives this descriptor a fresh identity and its own properties. The
target's property contract is not copied.

For construction, a bound object $`g`$ forwards as

```math
\begin{aligned}
&\mathsf{construct}(g,\bar a,n)\\
&\quad\rightsquigarrow
\mathsf{construct}\left(
f,\bar p{+\!\!+}\bar a,\,
\mathsf{if}\ \mathsf{same}(n,g)\
\mathsf{then}\ f\
\mathsf{else}\ n
\right).
\end{aligned}
```

Its construction contracts must be checked against this program; the bound
receiver is not used as the constructed receiver.

Source `f.call`, `f.apply`, and `f.bind` remain property lookups followed by
calls. Specialization requires the retrieved operation to be the standard
intrinsic. Argument extraction and the prototype, name, and length operations
of the full binding algorithm are separately checked computations. Bound-Code
is not a blanket no-effect rule for `.bind`.

### Stateful contracts

Use the additional judgment

```math
\Gamma\vdash_G
\{\Phi\}\ t\
\{z:B.\Psi\mid e:E.\Xi\}.
```

It specifies normal and exceptional postconditions. The ordinary judgment is the
special case with no additional precondition or postcondition beyond type
safety and the ambient invariants. It is the exception-aware form of the
[Hoare typing](PROGRAM-TYPING.md#checked-expression-postconditions), whose $`\Pi`$ and
$`\Sigma`$ are one way of writing $`\Phi`$ and $`\Psi`$.

A stateful call signature is

```math
\sigma=
(r:R;\mathsf{argv}:\alpha)
\{\Phi\}
\Rightarrow
\{z:B.\Psi\mid e:E.\Xi\}.
```

Contracts may refer to a distinguished $`\mathsf{self}`$ denoting the callable.
Let $`\theta`$ substitute the actual callable, receiver, and argument list for
these formal names. **Call-State** is

```math
\frac{
\begin{gathered}
\Gamma\vdash_G f:\mathsf{Callable}(L;P)
\qquad \sigma\in L\\
\Gamma\vdash_G r:R
\qquad\Gamma\vdash_G\bar a:\alpha
\qquad\Phi_0\vdash\Phi\theta
\end{gathered}
}{
\Gamma\vdash_G
\{\Phi_0\}\mathsf{invoke}(f,r,\bar a)
\{z:B.\Psi\theta\mid e:E.\Xi\theta\}
}.
```

The corresponding introduction rule checks the entry body under $`\Phi`$ and
establishes $`\Psi,\Xi`$. Construction, lookup, and update have the same stateful
form.

Only facts supported by postconditions, stable invariants, or a justified frame
rule survive a call. A transient observation is not promoted into a permanent
callable or property type.

**Decoration.** A representative strong property-addition rule is

```math
\frac{
\begin{gathered}
\Gamma\vdash_G f:\mathsf{Callable}(L;P)
\qquad\Gamma\vdash_G a:A\\
\mathsf{AddOK}_G(\Phi,f,k,A;P)
\end{gathered}
}{
\begin{gathered}
\Gamma\vdash_G
\{\Phi\}\mathsf{defineOwn}(f,k,a)\\
\{z:\mathsf{Callable}(L;P\wedge\{k:\mathsf{cell}(A)\}).
\ z=f
\mid e:\bot.\bot\}
\end{gathered}
}.
```

Here `defineOwn` is a core operation returning its target.

$`\mathsf{AddOK}`$ is a checked object-store obligation: the target is eligible,
the slot is available, the update is permitted, and the invariant extension
preserves established contracts. It cannot be discharged merely because the
call descriptor is immutable: behaviour can depend on properties.

Without those conditions, the general stateful property-definition contract is
required instead.

The postcondition $`z=f`$, rather than freshness, distinguishes decoration from
wrapping.

**Proxies and revocation.** The shape-only creation rule, **Proxy-Shape**, is

```math
\frac{
\Gamma\vdash_G f:\mathsf{Fun}
\qquad\Gamma\vdash_G h:\mathsf{Obj}(\top_p)
}{
\Gamma\vdash_G\mathsf{proxy}(f,h):\mathsf{Fun}
}.
```

There is no rule automatically copying the target's signatures. A stronger
contract requires checking the dispatch program: revocation check, handler
lookup, and target or trap invocation. Those operations can change the
behaviour relative to the target.

For a callable revocable proxy $`q`$, the state rules include

```math
\Gamma\vdash_G
\{\mathsf{Revocable}(q)\}\mathsf{revoke}(q)
\{z:\mathsf{Undefined}.\mathsf{Revoked}(q)
\mid e:\bot.\bot\},
```

```math
\Gamma\vdash_G
\{\mathsf{Revoked}(q)\}\mathsf{invoke}(q,r,\bar a)
\{z:\bot.\bot
\mid e:\mathsf{TypeError}.\top\}.
```

The core revocation operation requires the associated revocation capability.
The stable fact $`q:\mathsf{Fun}`$ survives. Liveness alone does not establish a
nonthrowing signature; handler and target obligations remain.

### Shape tests and identity

The call modes obtain the following views:

| Mode          | View                                                 | $`\mathsf{isFun}`$ |
| ------------- | ---------------------------------------------------- | ---------------- |
| `CPresent(L)` | $`\mathsf{Callable}(L;P)`$, with advertised signatures | true             |
| `CFunction`   | $`\mathsf{Callable}([];P)`$                            | true             |
| `CAbsent`     | $`\mathsf{Plain}(P)`$                                  | false            |
| `CUnknown`    | $`\mathsf{Obj}(P)`$                                    | unknown          |

This retains the distinction between known function shape and unknown
callability, while supplying the structural object view.

**Function-Test.** For an unknown-callability object,

```math
\frac{
\begin{gathered}
\Gamma,x:\mathsf{Callable}([];P)
\vdash_G t:B\;!E_t\\
\Gamma,x:\mathsf{Plain}(P)
\vdash_G u:B\;!E_u
\end{gathered}
}{
\Gamma,x:\mathsf{Obj}(P)\vdash_G
\mathsf{if}\ \mathsf{isFun}(x)\
\mathsf{then}\ t\
\mathsf{else}\ u
:B\;!(E_t\vee E_u)
}.
```

The true branch gains shape, not an arbitrary signature. Graph slicing must
represent or safely approximate the refined views.

**Identity.** Object identity has the rule

```math
\frac{
\Gamma\vdash_G f:\mathsf{Obj}(\top_p)
\qquad
\Gamma\vdash_G g:\mathsf{Obj}(\top_p)
}{
\Gamma\vdash_G\mathsf{same}(f,g):\mathsf{Bool}
}.
```

Its refinement postcondition is

```math
b\iff\mathrm{id}(f)=\mathrm{id}(g).
```

Allocation additionally establishes freshness relative to identities existing
at entry. Subsumption establishes neither allocation nor freshness.

### Async and generator callables

Their application uses Call. Their introduction needs additional computation
judgments, not additional callable-object representations.

What is implemented is weaker and trusted: `await` and an async body's returns
are calls of intrinsic values at declared signatures, and **Await**,
**Async-Return** and **Async-Complete** are instances of Call
([async functions and await](SOURCE-CONTRACTS.md#async-functions-and-await)).
The judgments below remain the target that would discharge that trust.

An asynchronous entry judgment

```math
\Gamma,\mathsf{this}:R,\mathsf{argv}:\alpha
\vdash_G^{\mathsf{async}}
t:\mathsf{PromiseSpec}(B,E)
```

must check entry and resumption, including parameter initialization, promise
resolution, thenable assimilation, rejection, and state invariants across
suspension. These are obligations of the asynchronous execution semantics.

Its introduction schema, **Async-Code**, is

```math
\frac{
\Gamma,\mathsf{this}:R,\mathsf{argv}:\alpha
\vdash_G^{\mathsf{async}}
t:\mathsf{PromiseSpec}(B,E)
}{
\Gamma\vdash_G^{\mathsf{call}}
\mathsf{asyncCode}(t):
[(R;\alpha)\xrightarrow{\bot}
\mathsf{PromiseSpec}(B,E)]
}.
```

This schema assumes the entry proof accounts for ordinary entry failures as
rejections; other synchronous failure paths must be advertised separately.
$`\mathsf{PromiseSpec}`$ constrains fulfillment and rejection, not eventual
settlement.

For generators, let $`\Pi`$ be a protocol describing operations and transitions,
including `next`, `throw`, and `return`. Then **Generator-Code** is

```math
\frac{
\Gamma,\mathsf{this}:R,\mathsf{argv}:\alpha
\vdash_G^{\mathsf{generator}}
t:\Pi\;!E_{\mathrm{entry}}
}{
\Gamma\vdash_G^{\mathsf{call}}
\mathsf{generatorCode}(t):
[(R;\alpha)\xrightarrow{E_{\mathrm{entry}}}
\mathsf{Generator}(\Pi)]
}.
```

A protocol transition supplies a stateful contract for the corresponding
method. It must account for suspension, completion, and subsequent operations
on a completed generator.

These last two are module interfaces. Defining their premises requires an
async/coroutine logic; merely giving the names of those judgments does not
provide that logic.

### A distinguishing instance

Let

```math
D=\mathsf{Obj}(\{n:\mathsf{cell}(\mathsf{Number})\}),
```

```math
M=(D;[])\to\mathsf{Number},
\qquad
A=(\top;[])\to\mathsf{Number}.
```

For a checked incrementing body, Dynamic gives $`M`$ to an ordinary method.
Lexical gives $`A`$ to an arrow capturing an instance of $`D`$.

After allocation, suppose

```math
m:\mathsf{Calls}([M]),
\qquad
a:\mathsf{Calls}([A]),
\qquad
o:D.
```

Then

```math
\Gamma\vdash_G
\mathsf{invoke}(m,o,[]):\mathsf{Number},
```

```math
\Gamma\vdash_G
\mathsf{invoke}(a,\mathsf{undefined},[]):\mathsf{Number}.
```

The available contract for $`m`$ does not justify supplying `undefined` instead
of $`o`$. Binding $`m`$ to $`o`$ produces a fresh function with a top-receiver
contract. Decorating $`m`$, under Decorate, preserves its identity. A plain
object containing $`m`$ in a property has a property-read rule, but no Call rule
for the object itself.

That is the intended separation: creation determines identity and dispatch;
contracts determine permitted operations; subsumption changes neither.

## Soundness and completeness scope

There are three distinct deliverables.

**A complete callable architecture** gives every pattern above a place without
changing representations when types change. C\* provides that target.

**A sound verification account** defines the operations and contracts, proves
the typing and state rules sound, and proves source elaboration preserves the
chosen observations. That includes identity, receiver binding, mutation,
exceptions, and any admitted asynchronous observations.

**A complete automated checker** is a separate claim. Neither object
representation establishes that the current certificate language can express
every required property or that its checker can discharge every valid
obligation.

The one-cell callable slice has the Lean safety proofs cited in
[the calculus account](#what-a-function-is-and-what-the-calculus-has). The fuller
architecture and rules are proposed extensions whose soundness and automated
completeness are not established here.

