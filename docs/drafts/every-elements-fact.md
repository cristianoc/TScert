# Draft: a current-heap fact about all elements of an array

The design of the route chosen for `blocker-every-promise`; its status is
the Guard overloads row of [WORK](../../WORK.md#status), its motivation the
paragraph on [guard overloads](../../WORK.md#guard-overloads). Claims are
labelled **proved** (with a Lean name that exists), **to prove** (a
statement this design adds, with its proposed name), **audited** (a native
contract, stated as a row of
[native footprints](../SOURCE-CONTRACTS.md#native-footprints)) or
**cited**.

## 1. The case

```ts
export function use(parts: (string | null)[]): string[] | null {
  return parts.every((p): p is string => p !== null)
    ? parts.map((p) => `(${p})`)
    : null;
}
```

TypeScript reads `every`'s guard overload,
`every<S extends T>(pred: (v: T, i: number, a: readonly T[]) => v is S): this is readonly S[]`,
and types `parts` as a `readonly string[]` in the `true` arm, so the
closure passed to `map` takes `p: string`. TScert refuses that closure: the
only `map` signatures at the receiver `(string | null)[]` pass
`string | null`. The census functions this case stands for
(`shadow-contracts.mts`'s `print`, `printSignature`, `statedSignatures`,
and `prelude` and `shadowText`, which the census attributes to the same
cause) use the same pattern.

The overload states a fact about the heap at `every`'s return, at a
callback that changes no element and no store. It is no type of the
receiver: the receiver's store keeps its contract `T`, and a later write
through any reference to the array may store a `T` outside `S`. TypeScript
accepts the following, and Node throws at the last line
(`Cannot read properties of null`):

```ts
function view(xs: (string | null)[]): readonly string[] {
  return xs.every((x): x is string => x !== null) ? xs : [];
}
const a: (string | null)[] = ["a"];
const v = view(a);
a.push(null);
v[1].length;
```

So the design is a fact of the current heap, established by `every`, kept
by the steps that cannot change the array's elements, and read by the
operations that read elements while it holds.

## 2. The fact

Write $`\sigma`$ for the store key, $`\mathsf{own}(o)`$ for the own
locations of an object $`o`$ (the locations its fields name, $`\sigma`$'s
included), and $`\mathsf{locs}(ls)`$ for the locations a store list
$`ls`$ lists. The **element fact** $`x \mapsto^{\ast} S\,[C]`$ about slot
$`x`$, at a type $`S`$ and an apart set $`C`$ of slots, holds at level
$`n`$, world $`W`$, heap $`h`$ and environment $`\rho`$ when $`\rho(x)`$ is
an array whose store and listed elements are locations of $`h`$, every
listed element holds a value of $`S`$, and no own location of an object a
slot of $`C`$ holds is one of them:

```math
\begin{aligned}
\mathrm{Elems}_n(W,h,\rho)(x,S,C) \iff{} & \exists\,\mathit{flds}\ \ell\ ls.\ \rho(x)=\mathsf{obj}(\mathit{flds},\_)\land \mathit{flds}(\sigma)=\ell\land \ell<|h|\land h[\ell]=\mathsf{arr}\,ls\\
& \land\ \forall l.\ \mathsf{some}\,l\in ls\Rightarrow l<|h|\land h[l]\in S_n(W)\\
& \land\ \forall c\in C.\ \mathsf{own}(\rho(c))\cap(\{\ell\}\cup\mathsf{locs}(ls))=\varnothing
\end{aligned}
```

It reads the store's location and the listed element locations, and no
other location of the heap. $`S`$ is a type of the graph, judged at the
state's world: membership of a type is kept by world extension and holds at
every lower level ([Types.lean](../../lean/Verification/Types/Types.lean),
`Adm`'s `mono` and `down`), so the fact transfers from a state to its
successor as the environment's types do (to prove: `Elems.transfer`).

**Presence.** The fact is about the present elements alone: a hole holds no
location, so it holds no value of $`S`$, and a read at a hole gives
`undefined`. Density stays a separate fact, $`D_n`$ of
[the fact](../FOOTPRINTS.md#the-fact), and stays what the store's contract
and `map`'s dense signatures state; the element fact neither implies nor
requires it.

**The apart set.** $`C`$ lists slots holding objects allocated while the
fact held, each therefore disjoint from the array's store and elements. A
write to one of their fields keeps the fact (§4). This is a provenance
stamp ([deferred precision](../FOOTPRINTS.md#deferred-extra-precision))
local to one fact: it is claimed only while the fact holds, so the fact's
locations are fixed while it is.

**Alias classes.** A node's knowledge states each element fact about the
slot's alias class ([stored knowledge](../PROGRAM-TYPING.md#stored-knowledge-and-how-it-is-read)),
and $`C`$ by classes too: two slots of one class hold one object.

## 3. The footprints that keep it

Of the six closed footprints
([changes and footprints](../FOOTPRINTS.md#changes-and-footprints)), only
the empty one keeps the fact:

| Footprint | Keeps the element fact | Why |
| --- | --- | --- |
| `{value: keep, store: keep}` | yes | every old location's contents are unchanged |
| `{value: any, store: keep}` | no | an element location is of `class(value)`: it may get a value outside $`S`$ |
| `{value: keep, store: grow}` | no | the store may list a fresh location holding a value outside $`S`$ |
| `{value: any, store: grow}`, `{value: keep, store: any}`, `{value: any, store: any}` | no | both of the above |

```math
\frac{\mathrm{Elems}_n(W,h,\rho)(x,S,C)\qquad \emptyset.\mathrm{Holds}(h,h')\qquad j\le n\qquad W'\sqsupseteq W|_j}
     {\mathrm{Elems}_j(W',h',\rho)(x,S,C)}\ \textsf{elems-keep}
```

To prove: `Elems.keep` (the rule, from `Closed.holds_empty`: $`h'`$
extends $`h`$, and every location the fact reads lies below $`|h|`$), and
`Elems.stable_exact`, a one-array heap per other footprint on which the fact
holds before and fails after, the controls added to
`FootprintControls.lean`. A footprint that keeps the fact keeps density
(the empty footprint is in `stableDenseClosed`, proved:
`stableDenseClosed_sound`).

A callback writing a captured counter is within `{value: any, store: keep}`
and so keeps no element fact through a native's traversal; separating the
counter's cell from the elements needs footprints over regions
([deferred](../FOOTPRINTS.md#deferred-extra-precision)). Within the
caller's own graph, a write to a cell of $`C`$ keeps the fact (§4).

## 4. Where the fact comes from, and what keeps it

A node's state gains a list $`\Theta`$ of element facts, each
unconditional or conditional on a Boolean slot,
$`b = \mathsf{true} \Rightarrow x \mapsto^{\ast} S\,[C]`$, beside the
implications between immutable slots
([promises between slots](../PROGRAM-TYPING.md#refinement-by-a-fact)).
$`\Theta`$ is interpreted at the state's level, world and heap; the node's
`StateOk` gains the conjunct $`\mathrm{ElemsOk}_n(W,h,\rho)(\Theta)`$.

**An indexed postcondition.** A node's evaluation is stated by
$`\mathrm{SafePost}(T,Q,n,W,h,t)`$, whose postcondition $`Q(h',v)`$ reads
the final heap and value, and a call's guarantee by $`\mathrm{SafePostExc}`$
with the effect's $`Q_\epsilon(r,h)`$
([effect-qualified call contracts](../SEMANTICS.md#effect-qualified-call-contracts));
a result family reads the world and no heap. $`\mathrm{Elems}`$ reads all
three, so neither the `every` promise nor the `.eval` case of `StateOk` can
state it through them. The design adds an indexed postcondition
$`Q(j,U,h',v)`$, read at the level $`j`$ and world $`U`$ the value is
produced at, closed under lower levels and world extension:

```math
\mathrm{SafePost}^{\mathsf{ix}}_\Xi(T,Q)(n{+}1,W,h,t)\iff
\bigl(t\in T(n{+}1,W)\land Q(n{+}1,W,h,t)\bigr)\lor\bigl(\exists v.\ t\ \text{raises}\ v\land v\in\Xi(n{+}1,W)\bigr)\lor
\exists W',h',t'.\ h,t\to h',t'\land\cdots\land\mathrm{SafePost}^{\mathsf{ix}}_\Xi(T,Q)(n,W',h',t')
```

with its step, consequence and bind rules, and its embedding of
$`\mathrm{SafePost}`$, a $`Q`$ reading neither $`j`$ nor $`U`$ (to prove:
`SafePostIx.ofSafePost`, `.bind`, `.consequence`, `.erase`). `PromiseWith`
states an effect's postcondition in it, the elements promise being its one
indexed conjunct, and `StateOk`'s `.eval` case states $`\Theta`$'s output
in it. The overload combination transports a postcondition between the
runs of two signatures of one call (`cross_upto`), which holds of a
postcondition that reads no world. Two runs may end in worlds with no
common extension, giving one fresh location different contracts, so an
indexed postcondition is transported only where it is proved compatible
across the two worlds. The elements promise is: it reads the contents of
locations below the call's entry heap, whose contracts both worlds keep,
and the membership of those contents in $`S`$, which reads the world only
through those contracts (to prove: `elemsPromise_cross`). A combination of
signatures whose indexed postconditions have no such proof is refused. This is the
design's first stage, prototyped before the graph rules (§10).

**`every` at a guard.** The overlay states `every`'s guard overload at the
empty footprint, its promise about the receiver's elements:

```math
\frac{f:(T,\ \mathsf{number},\ \mathsf{ReadonlyArray}(T))\Rightarrow_{\emptyset} S\,[\mathsf{guards}\ 0]}
     {\mathit{xs}.\mathsf{every}(f):S\,[\mathsf{guards\ elements}]\;!\;\emptyset}\ \textsf{native-guard-every}
```

As a guard's signature states its promise's type as its result, the result
$`S`$ here is the promise's type, the value `true` or `false`. The promise's
meaning, at the world and heap the call returns in, with $`r`$ the
receiver:

```math
R^{\mathsf{guards\ elements}}(v) = (v=\mathsf{true}\land \mathrm{Elems}(r,S,\varnothing))\lor v=\mathsf{false}
```

Audited: `every` reads the receiver's length $`len`$ once, then for each
$`k<len`$ tests whether index $`k`$ is present, and calls $`f`$ with the
element, $`k`$ and the receiver where it is, returning `false` at the first
answer converting to `false` and `true` after the last index
([ECMA-262](../REFERENCES.md#ecma-262), `Array.prototype.every`). At a
callback within the empty footprint, every location's contents stay as
they were from the call's start to its return, so the store and its listed
locations stay the same, every present index below $`len`$ is visited, and
each listed location still holds the value the callback was given; the
callback's `true` leaves that value in $`S`$, kept by world extension. On a
`true` result each listed element is in $`S`$ in the return's heap. At any
other footprint `every` keeps the plain signatures, whose result is
`boolean`. A guard closure states its promise at its body's footprint
(the rule `declaration-effect` of [the checked callback contract](../FOOTPRINTS.md#the-checked-callback-contract),
proved: `codeChecked_sound`), so a closure such as
`(p): p is string => p !== null`, an inspection, meets the signature; a
guard read as a value meets it at its own footprint.

The call node's output carries the conditional fact on its result slot:

```math
\frac{\Gamma\vdash_G r\leftarrow\mathrm{invoke}(\mathit{every},x,f):A\ \text{at}\ \textsf{native-guard-every}\ \text{at}\ S}
     {\Theta \leadsto \Theta,\ (r=\mathsf{true}\Rightarrow x\mapsto^{\ast}S\,[\varnothing])}\ \textsf{every-elements}
```

and keeps $`\Theta`$, by `call-keep`'s condition (its footprint within the
empty one). A branch on $`r`$ makes the fact unconditional on its `true`
edge; a negation $`u \leftarrow\ !r`$ restates it on $`u`$ at `false`, as an
`onFalse` yield does. To prove: `everyCall_sound`, from `selectedCall_sound`
with the promise's meaning, and `elemsBranch_sound`.

**What keeps it.** Each node rule states what it does to $`\Theta`$;
every rule not listed drops it.

- *Inspections* (reads, tests, arithmetic, an array literal's spreads) keep
  $`\Theta`$: the heap is unchanged (`inspect_safe`, proved).
- *Allocation* of $`r`$ keeps $`\Theta`$ and adds $`r`$ to each fact's
  apart set: every own location of the fresh object lies at or past the old
  heap's length, and every location a fact reads lies below it (to prove:
  `Elems.alloc_apart`). A closure, an object or array literal and a `let`'s
  cell are allocations.
- *A call keeping the heap* (`call-keep`: footprint within the empty one,
  no receiver store excepted) keeps $`\Theta`$; one stating `freshObject`
  (`call-fresh`) adds $`r`$ to each apart set as allocation does (to prove:
  `Elems.call_keep`, `Elems.call_fresh`).
- *A call changing only its receiver* $`y`$ (`call-own`: within the empty
  footprint on every old location but $`y`$'s own ones) keeps each fact
  whose apart set holds $`y`$'s class: none of the locations it may change
  is one the fact reads (to prove: `Elems.call_own`). A signature excepting
  its receiver's store (`pop`, `shift`, `reverse`, `splice`) states
  `{value: any, store: keep}` outside that store, which lets any element
  location change, so it drops $`\Theta`$ like every call outside the empty
  footprint.
- *A field write* $`\mathrm{write}_f(y,v)`$ keeps each fact whose apart set
  holds $`y`$'s class: the written location is an own location of
  $`\rho(y)`$ (to prove: `Elems.write_apart`). A cell's write is one.
- *An element write*, `a[b] = v`, drops $`\Theta`$: its location is an
  element location of some array, which may be one a fact reads.
- *Every other node*, a call at a footprint outside the empty one included,
  drops $`\Theta`$; so does a handler's edge, the throw having left its
  expression midway.

```math
\frac{\Gamma\vdash_G r\leftarrow\mathrm{write}_f(y,v):\mathsf{Null}\qquad [y]\in C}
     {x\mapsto^{\ast}S\,[C]\ \text{kept}}\ \textsf{elems-write-apart}
\qquad
\frac{\Gamma\vdash_G r\leftarrow\mathrm{alloc}(\ldots):A}
     {x\mapsto^{\ast}S\,[C]\ \leadsto\ x\mapsto^{\ast}S\,[C\cup\{r\}]}\ \textsf{elems-alloc}
```

**Edges, joins, cuts and back edges.** An edge from a state $`a`$ to a
target stating $`\Theta_b`$, under slot map $`m`$, establishes each target
fact from a source fact about the mapped slot's class at a type within the
target's, whose apart set covers the target's:

```math
\frac{\forall (i,S,C)\in\Theta_b.\ \exists (j,S',C')\in\Theta_a.\ j\in[m(i)]_a\land S'\le S\land \forall c\in C.\ [m(c)]_a\in[C']_a}
     {\mathrm{ElemsOk}(\Theta_a)(\rho)\Longrightarrow\mathrm{ElemsOk}(\Theta_b)(\mathrm{mapEnv}(m,\rho))}\ \textsf{elems-edge}
```

and a conditional target fact from a conditional source fact on the mapped
test slot, or from an unconditional one. $`S'\le S`$ is the subtype
decision the edges already use for slot types. To prove: `elemsCheck_sound`.
A merge that is not a cut keeps a fact where every incoming edge states one
about the same class, at the union of their types and the intersection of
their apart sets; the meet is untrusted, every edge checked. A cut states
its facts as its implications are stated: a further round of Lean's search
proposes them where a round fails and the edges into the cut meet new ones.
A back edge establishes a cut's fact only if the loop's body keeps it, so a
loop writing an element of any array, or calling at a footprint beyond the
empty one, holds no element fact at its head.

## 5. Where the fact is used

**Native traversals at the element view.** A contract gains an optional
precondition, its **element view** $`S`$: the call requires the
receiver's present elements to be in $`S`$ in the heap it starts in. Its
meaning restricts the entry heaps the arrow's guarantee quantifies over
([effect-qualified call contracts](../SEMANTICS.md#effect-qualified-call-contracts)):

```math
\mathcal F^{\,S}_\epsilon(R_c,\mathcal A,R)\ \text{holds of}\ f \iff
\forall j\ W'\ h\ r\ \vec v.\ \ldots\land \mathrm{Elems}_j(W',h)(r,S,\varnothing)\Rightarrow \exists t.\ \mathrm{Invoke}(f,r,\vec v,t)\land\mathrm{SafePostExc}(\ldots)
```

It stays a value type: the precondition is kept by world extension and holds
at lower levels, so the family is admissible (to prove: `callsT_adm` and
`restsT_adm` extended, `PromiseWith.weaken` with the precondition). One
signature covers another where its view is none or the other's view is
within its own (`Effect.covers` extended).

Each `ArrayProto` member below is stated, beside its signatures, at the
empty footprint with a binder $`S`$ as its element view, its element
positions at $`S`$ and its receiver positions (the receiver, and the
callback's `array` parameter) at $`T`$:

| Member | At the element view |
| --- | --- |
| `map` (dense and sparse) | callback `(S, number, ReadonlyArray<T>) => U` within $`\emptyset`$; result as the plain signature at $`\emptyset`$ |
| `forEach`, `some`, `every` | callback at `S` within $`\emptyset`$ |
| `findIndex` | callback at `S` (dense receiver) or `S \| undefined` within $`\emptyset`$ |
| `filter` | callback at `S` within $`\emptyset`$; result `S[]`, fresh |
| `find` | callback at `S` (dense receiver) or `S \| undefined` within $`\emptyset`$; result `S \| undefined` |
| `flatMap` | callback at `S` within $`\emptyset`$ |
| `slice` | result `S[]` at the receiver's presence, fresh |
| `at` | result `S \| undefined` |

A member that visits every index below the length (`find`, `findIndex`)
passes `undefined` at a hole, so its callback takes $`S`$ where the
receiver's contract is dense, and $`S\cup\mathtt{undefined}`$ otherwise;
`slice` keeps the receiver's holes, so its result has the receiver's
presence mode; `at` gives $`S\cup\mathtt{undefined}`$ whatever the
presence. The members skipping holes (`map`, `forEach`, `filter`, `some`,
`every`, `flatMap`) pass $`S`$ at either presence; `map`'s result keeps the
presence its plain signature at the empty footprint states.

Audited, one row each: at the empty footprint the member reads the
receiver's length and present elements, passes the receiver itself only as
the callback's `array`, allocates only its result, and runs no client code
but callbacks within the empty footprint; so from the call's start to its
return the store and every listed location keep their contents, and every
element it reads, passes or returns is one the precondition states in
$`S`$. A member that writes its receiver (`push`, `pop`, `sort`, `splice`,
...) has no element view.

The call node is checked where its state's $`\Theta`$ holds an
unconditional fact about the receiver's class at a type within the view:

```math
\frac{\Gamma\vdash_G r\leftarrow\mathrm{invoke}(m,x,\vec u):A\ \text{at a signature with element view}\ S\qquad (x,S',C)\in\Theta\qquad S'\le S}
     {\Gamma;\Theta\vdash_G r\leftarrow\mathrm{invoke}(m,x,\vec u):A\dashv \Theta}\ \textsf{native-element-view}
```

The node keeps $`\Theta`$ by `call-keep`. To prove: `viewCall_sound`, from
`selectedCall_sound` with the precondition discharged by
`ElemsOk`. Lean refuses a code entry or a declaration stating an element
view or the elements promise, as it refuses one stating `freshObject`
(`effectChecked`; to prove: `effectChecked_noElements`): only an
intrinsic's declaration states them.

**Element reads at a literal index.** A read `x[k]`, $`k`$ a literal array
index, at a state holding $`(x,S,C)\in\Theta`$, yields $`r : S\cup
\mathtt{undefined}`$, filtered by the read's type
([refinement by a fact](../PROGRAM-TYPING.md#refinement-by-a-fact)): at an
array index the read takes the store's element, or `undefined` at a hole
or past the end. A read at a computed index stays at the store's contract:
a number that is no array index reads an own numeric field, which
`every` never visits (`numericOwn`, [the array invariant](../SEMANTICS.md#the-array-invariant)).
To prove: `elemsRead_sound`.

**`for...of`.** The array iterator's step reads the iterated array's store
at the iterator's index. At a state holding the fact about the iterated
array, the step's yield is in $`S`$ where the array is the one the
iterator was created from and its contract is dense, and in
$`S\cup\mathtt{undefined}`$ otherwise, since the iterator reads a hole as
`undefined`. That needs a link from the iterator to its
array, kept across the loop's steps, and the step stated at an element
view of that array: the last stage (§10), after the native traversals and the
literal reads.

**No type view.** No rule gives the slot $`x`$ a type from $`\Theta`$. A
type's meaning is independent of the heap, so a value of
`readonly S[]` stays one after any write, while the fact is about the
current heap only: returning the array at `readonly S[]`, storing it in a
field, or passing it to a function at such a parameter would let a later
read through that reference see an element written after the fact lapsed
(`view` in §1). Where an expression's type requires `S[]` of the array
itself, the claim stays refused.

## 6. What this closes

- `print` (`all`: `parts.every(g) ? parts.map(...)`) and the case: the
  `map` call at its element view, the callback at `string`.
- `printSignature`: the fact holds from the edge where `params.every(g)`
  answered `true` (the `||` condition's fall-through), across the
  allocation of `admitsUndefined` and of the `let required` cell, which
  join its apart set, the `while` loop writing that cell and calling the
  closure, itself certified at the empty footprint (its body reads, tests
  and calls `some` with itself), to `params.map(...)`. The loop's
  cut states the fact with `required` in its apart set.
- `prelude` calls `print`.
- `statedSignatures` returns `printed` at `string[]`: an escape (§5, no
  type view), outside what the fact gives. Its route is a repair of the
  source, `printed.filter((p): p is string => p !== null)` compared by
  length, at `filter`'s guard overload ([the deciding rules](../SOURCE-REWRITES.md#deciding-what-a-refusal-of-tscerts-code-calls-for));
  `shadowText`, which the census attributes to this cause, calls it.
  Whether `shadowText`'s slice verifies with its callees is measured by
  the slices of the change, not predicted here.

## 7. Lean changes

- `Semantics/HeapElements.lean` (new): `Elems`, `ElemsOk`, `Elems.transfer`,
  `Elems.keep`, `Elems.stable_exact`, `Elems.alloc_apart`, `Elems.write_apart`,
  `Elems.call_own`; controls in `FootprintControls.lean`.
- `Semantics/HeapObservations.lean`, `ExceptionalPosts.lean`: the indexed
  postcondition of §4 and its rules.
- `Semantics/CallEffects.lean`: the promise form `guards elements`
  (`TypePromise`), the contract's `elementView : Option Result`, their
  meanings in `PromiseWith` through the indexed postcondition;
  `callsT_adm`, `restsT_adm`, `Effect.covers_sound`, `cross_upto`,
  `call_safe` and `construct_safe` carried through. The contract operations
  refuse the two forms where they cannot keep them: erasing a signature
  with an element view to an ordinary arrow, and binding a receiver
  (`Effect.drop`), after which the elements promise would be about the
  bound call's receiver. `Contract` is read by
  most modules, so adding the field rebuilds them; it has a default
  (`none`), and pattern matches on the structure name its fields.
- `Programs/PromiseCalls.lean`, `ControlFlow.lean`: `NodeEvidence.elements`
  ($`\Theta`$ at the entry) and its output; `StateOk`'s conjunct;
  `elemsCheck` and `elemsCheck_sound` in `carries`; `everyCall_sound`,
  `elemsBranch_sound`, `viewCall_sound`, `elemsRead_sound`. The node rules
  that drop $`\Theta`$ discharge the conjunct by `ElemsOk []`; only the
  rules of §4 and §5 need proofs of their own.
- `Programs/CertificateProducer.lean` (untrusted search): $`\Theta`$
  inferred forward from each `every` call and carried by the rules of §4;
  the merge's meet; cut facts by the round that proposes cut implications;
  the element-view signature tried at a call whose receiver's class has a
  fact.
- `Programs/GraphCode.lean`: `effectChecked` refuses the two new forms on
  code.

`checkJson_safe` keeps its premise and conclusion; its proof threads the
new conjunct through `StateOk`. The axiom check covers the new theorems.

## 8. Producer, wire and overlay

- **Overlay** (`tools/`'s globals overlay): `every`'s guard signature at
  the empty footprint, and the element-view signatures of §5, each with its
  audited row in [native footprints](../SOURCE-CONTRACTS.md#native-footprints).
- **Wire.** The declaration document's effect gains the promise
  `{"guards":{"elements":true}}`, beside `{"guards":{"param":i}}`, and a
  signature gains `"elementView"`, `null` or a type's labels
  ([source claims](../SOURCE-CLAIMS.md#quantified-callables-and-their-eliminations)).
  `tools/source-claims.mts`, the Lean decoder and the producer's reader
  change together; `tests/json-field-names.mts` checks the names. The
  claims document is unchanged: $`\Theta`$ is evidence Lean's search
  infers.
- **Producer** (`ocaml-producer/`): the closures and calls after an
  `every` guard are claimed at TypeScript's narrowed element type, which
  the producer reads already; it proposes the element-view signature where
  TypeScript's receiver is the narrowed `readonly S[]`, and the empty
  footprint for the guard closure (an inspection). An escape (§5) keeps
  the claim TypeScript gives, which Lean refuses.

## 9. Cases and controls

Positive (pipeline cases):

- `blocker-every-promise`: gap → verified.
- `every-elements-record-guard`: a guard narrowing a union of records,
  `nodes.every((n): n is Leaf => n.k === "leaf") ? nodes.map((n) => n.v) : []`.
- `every-elements-negated`: `if (!xs.every(g)) return null;` then
  `xs.filter(...)` at `S[]` and `xs.find(...)` at `S | undefined`.
- `every-elements-cell-loop`: `printSignature`'s shape, a captured `let`
  written in a loop between the test and the `map`.
- `every-elements-guard-value`: a module guard read as a value,
  `xs.every(isName)`.
- `every-elements-sparse-find`: `find` over a receiver whose contract
  admits holes, its callback at `S | undefined` testing for `undefined`.

Negative (refused; each run under Node in `tests/node-runs.mts`, where it
throws a `TypeError` TypeScript does not predict):

- `invalid-every-elements-element-write`: `xs[0] = null` between the test
  and `xs.map((p) => p.length)`.
- `invalid-every-elements-alias-write`: the same write through
  `const ys = xs`.
- `invalid-every-elements-push`: `xs.push(null)` between them.
- `invalid-every-elements-call`: a call of an unknown function given `xs`.
- `invalid-every-elements-guard-mutates`: an `every` callback that sets
  `xs[1] = null` after testing index 0: only the plain signatures apply.
- `invalid-every-elements-map-callback-writes`: a `map` callback writing
  `xs[i + 1] = null`: the element view needs a callback within the empty
  footprint.
- `invalid-every-elements-loop`: a loop between the test and the use whose
  body writes an element.
- `invalid-every-elements-escape`: `view` of §1.
- `invalid-every-elements-hole-find`: `[, "ok"]` at `(string | undefined)[]`,
  `every` at `typeof x === "string"`, then `find((x) => x.length > 0)`:
  `find` passes the hole.

Forged-claim controls (`pipeline/test.mts`, through evidence production and
consumption): an element fact stated at a node after an element write; an
apart set naming a slot allocated before the fact; the conditional fact
used on the `false` edge; an `every` call selected at the elements promise
with a callback outside the empty footprint; an element-view call at a
receiver with no fact; a closure's code entry claiming an element view or
the elements promise.

## 10. Cost and risks

Estimated, by the size of comparable work
([fresh array storage](../FOOTPRINTS.md#fresh-array-storage),
[separation facts](heap-freshness.md)), in stages:

1. The indexed postcondition and the contract's two forms
   (`HeapObservations`, `ExceptionalPosts`, `CallEffects`): Lean
   1,500–2,500 lines. It is prototyped first, and the later estimates are
   revised from its size.
2. The fact, its keeping rules and edges, `every`, and `map`, `forEach`,
   `filter`, `some` and `every` at the element view: Lean 1,500–2,000
   lines, the search 400; the producer 200–400; overlay, wire and decoders
   250; docs 300. This stage closes `print` and `printSignature`.
3. `find`, `findIndex`, `slice`, `at` and literal-index reads: Lean about
   500.
4. `for...of`: not estimated.

Altogether 4,000–5,500 Lean lines for stages 1–3, 15 cases and 6
controls.

Risks:

- **The indexed postcondition.** Every composition lemma of `SafePost`
  has its indexed twin; where a lemma reads the postcondition's
  independence of the world, its twin needs admissibility instead.
- **Rebuild time.** `Contract`'s new field touches most modules; the
  default value keeps proofs that construct contracts unchanged, but
  `DecidableEq` and structure-eta proofs rebuild.
- **The native audits.** Eleven rows of §5 and `every`'s; each rests on the
  member running no client code but its callback, the same host premise as
  [ordinary array construction](../SOURCE-MODEL.md#exact-contracts-and-native-effects).
- **Search cost.** Each `every` call adds facts the search carries to every
  later node; a fact is dropped at the first node outside §4's list, so in
  the census functions it lives across a few nodes. The cut round runs only
  where a round fails.
- **Coverage.** A callback writing a captured cell keeps no fact through a
  traversal (§3); `statedSignatures` needs its repair (§6).

## 11. Alternatives considered

- **A footprint-keeping callback alone** gives the fact at `every`'s
  return and nothing after it ([guard overloads](../../WORK.md#guard-overloads)).
- **Narrowing the store's contract** to `S`: a location's contract is
  fixed by its allocation and a world never replaces one
  ([the array invariant](../SEMANTICS.md#the-array-invariant)), and the
  other references to the array keep `T`.
- **A view type for the slot** (the slot typed `readonly S[]` for a
  region): unsound at every escape (§5, `view`).
- **A primitive predicate in place of $`S`$**, a cell fact of
  [current-content assertions](../SEMANTICS.md#current-content-assertions-and-postconditions):
  heap knowledge stays world-free and cheaper, and the census's guards
  (`string` from `string | null`) fit, but a guard narrowing a union of
  records or of compiler nodes does not.
- **Regional footprints** (`own(x)`, `store(x)`, `elems(x)`,
  [deferred](../FOOTPRINTS.md#deferred-extra-precision)) would subsume the
  apart set and admit callbacks writing captured cells; they are the larger
  general mechanism, which this fact's rules fit into later.
- **Rewriting the five functions** (`filter` at its guard overload with a
  length comparison) needs no model change and is the route for
  `statedSignatures` alone.

## 12. Decisions

- **D1.** $`S`$ is a type of the graph (§2), over a primitive predicate.
- **D2.** `statedSignatures` takes the repair of §6.
- **D3.** `for...of` at the element view is the last stage (§10).
