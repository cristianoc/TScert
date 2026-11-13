# Callables

A JavaScript function is an object with an identity, mutable properties and
invocation code. This document states what a callable is in JavaScript, how the
calculus represents one, what a callable type promises, and how overloads and
generic functions are certified. The typing rules for creating, calling,
binding and constructing callables are in [Program typing](PROGRAM-TYPING.md#expressions);
the meaning of a call contract is in
[Semantics](SEMANTICS.md#one-meaning-for-callable-contracts).

The prerequisites are the term judgment $`\Gamma\vdash_G t:A`$ of
[Program typing](PROGRAM-TYPING.md), object values and graph code in
[Semantics](SEMANTICS.md), and graph clauses and checked subtyping in
[Positive types](POSITIVE-TYPES.md). Types are finite unions of graph labels.
Declaration lowering and native contracts are specified in
[Reading the source](SOURCE-CONTRACTS.md); the source closure rules in
[Source elaboration](SOURCE-ELABORATION.md#source-closures-and-their-annotations).

## What a function is

A JavaScript function value is three things: **code**, its `[[Call]]`
behaviour, fixed at creation; a **property bag**, written by ordinary object
writes such as `f.cancel = …`; and an **identity**, compared by `f === g`. A
value is a function exactly when it has `[[Call]]`, which is what
`typeof f === "function"` tests. Having `[[Call]]` does not make a call safe: a
class constructor's `[[Call]]` always throws, and a value of TypeScript's
`Function` type has `[[Call]]` and no known signature. Every constructor also
has `[[Call]]`, so constructibility implies function shape
([ECMA-262](REFERENCES.md#ecma-262)).

The call and construction operations are internal methods, not properties
named `call` or `construct`; their presence is fixed once the object is
created, while their behaviour may depend on mutable state. Ordinary
functions, arrows, methods, bound functions and class constructors differ in
how they are created and how they bind `this`, `arguments` and `new.target`,
and may satisfy the same call contracts. The calculus therefore has one
representation of function values and no separate type of arrow-function
values. A TypeScript object type with call signatures, construct signatures
and properties describes one such object
([TypeScript](REFERENCES.md#typescript)).

## How the calculus represents a callable

The [operational language](SEMANTICS.md#operational-language) has object
values for plain objects (`objAt fields absent identity`) and functions
(`objAt fields code identity`, graph code for every source function), where
`fields` is the finite map from field names to the locations they stand for
and `identity` the object's identity cell, both fixed at allocation. `CallCode`
is a separate descriptor type; its body is no runtime value. `makeAt code names
inits` takes one fresh location per named field, then the identity cell; a
source function is the one-field case, `makeFn code null`, a null-initialized
bag under the key `[[code]]`, which no source key spells and a copy does not
take: a function has no properties of its own. Plain allocation and function
creation are abbreviations of `makeAt`, with one congruence rule, one
allocation step and the shared proofs `make_fields_rule` and `makeFn_rule`
([Rules.lean](../lean/Verification/Semantics/Rules.lean)). `isFun` recognizes
function objects and `isRef` plain objects, both independently of the heap.

Every function receives this representation at creation. A plain function
type, a callable type with properties and a property-only type are views of
the same value, and subsumption never allocates, wraps or replaces it. Object
equality compares identities, and each identity has one code descriptor, so
shape tests are heap-independent while behaviour may read the heap.
[ObjectCoherence.lean](../lean/Verification/Semantics/ObjectCoherence.lean)
checks that graph syntax embeds no runtime identity (`sourceTerm`).

[CallableObjects.lean](../lean/Verification/Programs/CallableObjects.lean)
proves that a callable object's fields are read and written as a record's
(`bag_read`, `bag_write`): `bagT P` describes the writable fields independently
of the call code, and the call contracts (`callsT`, `restsT`) hold of the same
value. `EnvOk.prepend` extends environments with ordered parameter lists,
`frame_envOk` builds the frame graph code is entered with from the receiver,
the parameters and the captured values, and `graph_invoke` and
`graphRest_invoke` derive the call contract from checked code
([TypingBasics.lean](../lean/Verification/Programs/TypingBasics.lean),
[VariadicTyping.lean](../lean/Verification/Programs/VariadicTyping.lean)).
The graph clause `callable first rest arrows variadic methods` combines a
nonempty conjunction of bag invariants with fixed and variadic call promises
and host-relative methods, as a record's (`methodT`), on one object;
normalization merges the lists, and structural subtyping checks bag, arrow and
method coverage separately and can forget the bag and the methods to obtain
`arrs`. A method of a callable is found by its key as a record's is
(`memberOf`), so `Number.isFinite(n)` beside `Number(text)` reads the method
from `Number` and invokes it on `Number`.

The calculus's properties are own data properties, read and written as cells;
accessors, inherited lookups and proxies, whose property operations run code,
are outside the fragment ([model limits](SOURCE-FRAGMENT.md#model-limits)).

The rules of [Program typing](PROGRAM-TYPING.md#expressions) cover:

- creation: `funGraph`, `funScheme` and `callableGraph` allocate graph code,
  checked once per advertised signature, at a fresh identity; creation
  preserves existing heap knowledge without executing the body;
- calls: `app`, `callCallable`, `callRest` and `callPacked`, with the receiver
  each signature names, the source's evaluation order for method calls, and
  bag reads and writes `readCallable` and `writeCallable`;
- `.bind`: `bindE` allocates the forwarding descriptor
  $`\mathsf{bound}(f,r,\vec p)`$, whose invocation ignores the receiver it is
  given (`callsT_bound` in
  [CallEffects.lean](../lean/Verification/Semantics/CallEffects.lean));
- construction: `ctorGraph` and `construct`, with variadic construct
  signatures;
- unions of callables: `unionVar` splits a union-typed receiver or callee, and
  every alternative must check.

A throw is an outcome safety admits ([throwing](PROGRAM-TYPING.md#throwing)). A call contract
qualified by an effect on the heap is defined in
[effect-qualified call contracts](SEMANTICS.md#effect-qualified-call-contracts),
and the operations a callback may perform without invalidating a caller's
facts in [Footprints](FOOTPRINTS.md#the-checked-callback-contract). The safety
contract guarantees progress, not termination.

The [callable examples](../pipeline/examples/callables/README.md) are
pipeline cases. Among the other cases, `recursive-callable` holds the
recursive contract $`R=\mathsf{callable}(\mathsf{null}\mid R;\ \mathsf{Boolean}\to\mathsf{Boolean})`$,
a function written into its own bag, read back, narrowed and called, and
`invalid-recursive-callable` refuses a view of the bag that also admits
`true`, as the bag's field is invariant; `callable-bag-union` reads and writes
a field through a union of a record and a function carrying it, and
`invalid-callable-bag-union` refuses a write the function's bag does not
admit.

## Types describe behaviour, not internal storage

A callable type is an intersection of separate predicates for shape,
properties and calls:

```math
\mathsf{Callable}(L;P)
=
\mathsf{Fun}
\cap \mathsf{Props}(P)
\cap \bigcap_{\sigma\in L}\mathsf{CallSpec}(\sigma).
```

[Semantics](SEMANTICS.md#one-meaning-for-callable-contracts) states the call
promise $`\mathsf{CallSpec}`$ precisely and maps each component to Lean. Fixed
and variadic signatures share that promise, and the creation rules establish
it. A property-only view drops the call requirements without asserting their
absence. The empty family means function shape with no call contract,
$`\mathsf{Callable}([\,];P)=\mathsf{Fun}\cap\mathsf{Props}(P)`$: knowing that a
value is a function differs from not excluding functions.

A call contract describes the computation, not a relation between values: a
call may allocate, write, call back or throw, and a fact about the heap
survives a call only through the call's stated effect or a stable invariant.
Ordinary data properties are a special case of property operations: their
cells are invariant, which also protects a call contract that reads them.

## Overloads, polymorphism, and binding

**Overloads.** Several call contracts are a conjunction of behavioural
obligations on one value:

```math
\mathsf{CallSpec}(L)\cap\mathsf{CallSpec}(M)=\mathsf{CallSpec}(L\mathbin{+\!+}M),
```

proved for `callsT` as `callsT_append`
([CallEffects.lean](../lean/Verification/Semantics/CallEffects.lean)). The
creation rules check the same code against every advertised signature before
allocating one function object; a call selects an applicable member, and
forgetting members is subsumption. No writable cell is retyped.

**Generic closures.** A quantified call contract is a scheme row
([quantified schemes](POSITIVE-TYPES.md#quantified-scheme-layer)), and a
generic closure is graph code at a scheme row (`funScheme`). Its introduction
and elimination rules, **Call-Scheme-I** and **Call-Scheme-E**, are in
[call schemes](PROGRAM-TYPING.md#call-schemes). A construct scheme's members
are class values ([scheme rows](POSITIVE-TYPES.md#parameter-and-scheme-rows)),
which no closure is.

**Generic bodies.** A generic function's body is a graph request whose
binders are parameter rows $`\vec p`$: rows the graph's assignment interprets,
which no rule reads (a type holding one has no expansion). The pass's acceptance does not
read the assignment (`nodeChecked_reassign` and `codesSound_reassign` in
[TolerantFramesWalkReassign.lean](../lean/Verification/Programs/TolerantFramesWalkReassign.lean)
and its companions), so the
body is certified at every assignment of its binders it admits, the inputs and
the result read at the same assignment: the rule **Generic-Body**, with its
premises and proofs, is stated in [call schemes](PROGRAM-TYPING.md#call-schemes).
One derivation, checked once, covers every admitted instantiation, and
every generic unit takes this one path; bounded binders and the binders of a
generic class are read as that section states.

**Binding.** `f.call`, `f.apply` and `f.bind` are property reads followed by
calls; the parser identifies the standard intrinsic by its declaration
([trust surface](DESIGN.md#trust-surface)), and a fresh callable given an own
`call` or `bind` field is refused
([refused on principle](SOURCE-FRAGMENT.md#refused-on-principle)). A bound
function has a fresh identity and its own bag; the target's properties are not
copied, and a second `.bind` or a `.call` on it cannot replace the first
receiver.

**Parameter defaults.** A default is an entry node of the code's graph: a
tag dispatch on `undefined` at the parameter's slot, the default's
evaluation on one arm. The slot's type is $`T\cup\{\mathsf{undefined}\}`$
and the initialized binding's $`T`$. In a generic closure the code is
checked at its scheme row, so initialization establishes $`T`$ for every
assignment of the binders, which observed calls cannot justify. It never
obtains $`T`$ by deleting `undefined` from the input, since $`T`$ may itself
contain `undefined`. The order of entry nodes and the closure conversion of
defaults capturing later parameters are
[parameter initialization order](SOURCE-ELABORATION.md#parameter-initialization-order).
