# Draft: the elements fact, one more instance of footprints

The design of the route chosen for `blocker-every-promise`; its status is
the Guard overloads row of [WORK](../../WORK.md#status), its motivation the
paragraph on [guard overloads](../../WORK.md#guard-overloads). It is an
instance of the four-part mechanism of [footprints](../FOOTPRINTS.md): a
fact with the locations it reads, the stable operations stated as closed
footprints, a contract Lean checks node by node, and the construct's rule
that ignores side effects. The signatures stating the fact extend the
receiver-relative parts of a call effect (`receiverStore`, `receiverOwn`):
like them, they are about the call's receiver (§5). Claims are labelled
**proved** (with a Lean name that exists), **to prove** (a statement this design adds, with its
proposed name) or **audited** (a native's behaviour, as a row of
[native footprints](../SOURCE-CONTRACTS.md#native-footprints)).

## 1. The case and the census sites

```ts
export function use(parts: (string | null)[]): string[] | null {
  return parts.every((p): p is string => p !== null)
    ? parts.map((p) => `(${p})`)
    : null;
}
```

TypeScript reads `every`'s guard overload,
`every<S extends T>(pred: (v: T, i: number, a: readonly T[]) => v is S): this is readonly S[]`,
and types `parts` as `readonly string[]` in the `true` arm, so the closure
passed to `map` takes `p: string`. TScert refuses that closure ("closure
signature claim is outside the source annotation"): `map` passes the
receiver's element type, `string | null`.

The sites in `tools/shadow-contracts.mts` the census attributes to this
cause all test a local array at a guard that only reads (`p !== null`):

| Line | Array tested | Between the test and the use | Use |
| --- | --- | --- | --- |
| 122 (`print`) | `terms.map(print)` | nothing | `parts.map((p) => …)` reads `p` at `string` |
| 137 (`print`) | a spread literal | the test's array is not used again | none |
| 180 (`print`) | `term.args.map(print)` | reads and string natives | `args.join(", ")` |
| 195 (`printSignature`) | `stated.params.map(print)` | a closure, a `let` and a loop writing it | `params.map((p, i) => …)` reads `p` at `string` |
| 215 (`statedSignatures`) | `[…].map(printSignature)` | nothing | `return printed` at `string[]` |

`prelude` and `shadowText` reach these through their calls.

## 2. The fact

The **elements fact** $`\mathrm{elems}(x,R)`$ says that every present
element of the array slot $`x`$ holds currently satisfies $`R`$, a
predicate of a value's runtime kind, as a tag test reads it: a set of the
kinds null, undefined, boolean, number, string, bigint, symbol and object
(`CallEffects.ElemPred`). The signatures of §5 state it at the fixed set
{`string`, `number`, `boolean`}. Like density
(`Dense`, `FootprintProvenance.lean`), it requires the store to exist in
the heap, so that a heap extension cannot fill a store location the fact
held of vacuously:

```math
\mathrm{elems}(x,R)(\rho,h)\iff\exists\,\ell\ ls.\ \mathrm{store}(\rho(x))=\ell\land h[\ell]=\mathsf{arr}\,ls\land\forall l.\ \mathsf{some}\,l\in ls\Rightarrow\exists v.\ h[l]=v\land v\in R
```

where $`\mathrm{store}(v)`$ is the location of $`v`$'s field `[]`
(`storeOf`).

It is a new kind of the facts the stability check is generic in
(`FootprintStability.FactKind`, beside `cell`, `link`, `value` and
`dense`), and its support is the store's location and the element
locations, each kept:

```math
\mathrm{support}(\mathrm{elems}(x,R))=[(\mathsf{field}(x,\mathtt{[]}),\mathsf{keep}),\ (\mathsf{elems}(x),\mathsf{keep})]
```

The regions are the existing `Region.field` and `Region.elems`. To prove:
`FactKind.support_sound` for the new kind: a heap change within the
support keeps the fact, since the store's location keeps its list and each
listed location its value.

**Why a predicate and not a type.** $`R`$ reads no world, so the fact
holds of a heap alone, as every atom of heap knowledge does
(`HeapKnowledge.Holds`): it is kept by heap extension, compared along edges
and met at joins by the existing knowledge rules, and a call's
postcondition stating it reads only the heap, as the effect postconditions
do. Every census guard is `p !== null` at `string | null`, whose
predicate is `string`. A guard narrowing a union of records by a field's
literal has no predicate here, and gives no fact.

**Presence.** The fact is about present elements: a hole lists no
location. Density stays its own fact, $`\mathrm{dense}(x,n)`$, and the
store's contract states it as before.

## 3. The stable set

A closed footprint keeps the fact where the stability check passes for its
support (`stable`; proved: `stable_sound`), which, both entries being
`keep`, is exactly where every change it allows is `keep`: the empty
footprint `{value: keep, store: keep}` alone. To prove:
`elemsCheck_stable` (the empty footprint passes, as `denseCheck_stable`
shows for density's four), and controls in `FootprintControls.lean`, one
heap per other footprint on which a change it allows falsifies the fact
(`{value: any, store: keep}` replaces an element, `{value: keep, store: grow}`
lists a fresh location holding a value outside $`R`$).

The check also takes separation knowledge (`SepKnowledge`): a write to
locations known apart from the array's store and elements keeps the fact.
The graph checker states no separation of element locations, so that use
waits for [regional footprints](../FOOTPRINTS.md#deferred-extra-precision).

## 4. The checked contract

Three pieces of code must run within the empty footprint, and each is
certified node by node by the existing rules
([the checked callback contract](../FOOTPRINTS.md#the-checked-callback-contract)):

- **The guard.** A guard closure states its promise at its body's
  footprint (`declaration-effect`; proved: `codeChecked_sound`), so
  `(p): p is string => p !== null`, an inspection, is a guard within the
  empty footprint; a guard read as a value states its own footprint.
- **The callbacks of the uses.** The template callback of line 122 reads
  and allocates;
  line 195's callback also reads the `let`'s cell.
- **The caller's nodes between the test and the use.** The elements fact
  is an atom of the node's heap knowledge, and the knowledge's rules keep
  an atom exactly at the nodes whose step is within the empty footprint:
  inspections (proved: `inspect_safe`), allocations (proved:
  `HeapKnowledge.alloc_frames`), and calls at a signature within the empty
  footprint stating no change of its receiver's store (`call-keep`; proved:
  `PromiseCalls.keepsCall_sound`). Every other node drops it: a write, a
  call beyond the empty footprint, and a handler's edge (a throw keeps
  nothing).

The atom is about the slot's alias class, as every atom is
([stored knowledge](../PROGRAM-TYPING.md#stored-knowledge-and-how-it-is-read)).
An edge establishes a target's atom $`\mathrm{elems}(i,R)`$ from a source
atom $`\mathrm{elems}(j,R')`$ with $`j`$ in the class of the mapped slot
and $`R'\subseteq R`$, as it establishes a cell fact (`knowledge-edge`;
proved for cells: `HeapKnowledge.check_sound`, `checkIn_sound`); a merge
keeps an atom every incoming edge states, at the join of the predicates;
a cut states it where a further round of the search proposes it, and every
edge into the cut, the back edges included, is checked by the same rule.
So a loop body within the empty footprint keeps it, and a body that
re-tests the array may establish it again.

## 5. The construct's rules

**The signatures' two new parts.** A call signature's effect states, beside
its footprint and promise, two optional predicates of the
[elements fact's grammar](#2-the-fact): `requires R`, a precondition, that
the elements of the call's receiver satisfy $`R`$ in the heap the call starts in;
and `elements R`, a promise, that a normal return of `true` leaves them
satisfying $`R`$. Proved (`CallEffects.PromiseWith`, `Effect.post`): a
signature's guarantee quantifies over the entry heaps meeting its
`requires`, and its postcondition reads the heap and the value only, the
form of every effect postcondition, so the existing combination of two
signatures' runs (`cross_upto`, `Effect.cross_result`) applies unchanged.
The predicates read no world, so a signature stating them is still a value
type (`callsT_adm`).

**The receiver.** The two parts extend the existing receiver-relative
parts of an effect, `receiverStore` and `receiverOwn`, which state what a
call may change of the receiver it is invoked with (`Effect.within`), and
like them they are about that receiver. `Array.prototype`'s members are
fields of the prototype (`ArrayProto`), each typed by a scheme over the
element type $`T`$ whose signatures state their array receiver:
`xs.every(g)` reads the field and invokes its value with `xs` as receiver,
in the lowered graph `x1.call(x4, x0)` with `x4` the array's slot. The
receiver's own type, a dense or a readable array, is the signature's
receiver contract, so `map`'s dense signatures keep reading density from
it. Binding a signature (`.bind` in source, and a method member's
binding to its host, `bindMember` and `bindScheme`) keeps neither part
(`Effect.keeps`, proved in commit `1ac22b78`): a bound call does not pass
the receiver the parts are about. So a call relying on either part invokes
the native with the array as its receiver, and the call node's knowledge
names that receiver's slot.

**`every` at a guard.** The overlay states, in `every`'s scheme beside its
predicate signatures, for
each predicate $`R`$ of the fixed set {`string`, `number`, `boolean`}, one
signature at the empty footprint whose callback promises $`R`$ of its
first parameter and which promises the receiver's elements satisfy $`R`$:

```math
\frac{f:(T,\ \mathsf{number},\ \mathsf{ReadonlyArray}(T))\Rightarrow_{\emptyset} R\,[\mathsf{guards}\ 0]}
     {\mathit{xs}.\mathsf{every}(f):\mathsf{boolean}\,[\mathsf{true}\Rightarrow\mathrm{elems}(\mathit{xs},R)]\;!\;\emptyset}\ \textsf{native-guard-every}
```

A guard closure `(p): p is string => …` meets the callback's type at
$`R=\mathtt{string}`$; one promising a narrower type, a literal, meets it
by the promise's covariance. A guard's answer is a Boolean, `true` or
`false` (`TypePromise.result`), so `every`'s truthiness test of it reads
`true` exactly where the promise holds.

Audited: `every` reads the receiver's length once, then for each index
below it tests presence and calls $`f`$ with the element where it is
present, returning `false` at the first answer converting to `false`
([ECMA-262](../REFERENCES.md#ecma-262), `Array.prototype.every`). At a
callback within the empty footprint, the store and every listed location
keep their contents from the call's start to its return
(`Closed.holds_empty`), so every listed location is visited, its value is
the one the callback was given, and the callback's `true` leaves that value
in $`R`$. The call is within the empty footprint, so it keeps the caller's
knowledge.

The call's output carries the atom conditionally on its result slot,
$`0=\mathsf{true}\Rightarrow\mathrm{elems}(x,R)`$, where $`x`$ is the
call's receiver slot; a branch on the result keeps it
unconditionally on its `true` edge, as a Boolean observation refines
knowledge on its edge (proved for cells: `observeBoolean_holds`), and a
negated test takes the edges swapped. To prove: `everyCall_sound`.

**`map` at the fact.** `map` relies on the fact between callbacks, as it
relies on density. For each predicate $`R`$ of the fixed set the overlay
states two more signatures of `map`'s scheme at the empty footprint,
stating `requires R` and a callback whose first parameter is $`R`$'s type
(`string`, `number` or `boolean`):

- at a dense receiver, a dense result;
- at any receiver, a result that may hold holes, where the receiver has
  them: `map` skips a hole and leaves it in its result.

```math
\frac{\mathit{xs}:\mathsf{ReadonlyArray}^{\pi}(T)\qquad\mathrm{elems}(\mathit{xs},R)\ \text{at the call}\qquad f:(R,\ \mathsf{number},\ \mathsf{ReadonlyArray}(T))\Rightarrow_{\emptyset} U}
     {\mathit{xs}.\mathsf{map}(f):\mathsf{Array}^{\pi}(U)\;!\;\emptyset}\ \textsf{native-map-elems}
```

where the presence $`\pi`$ is `dense` for the dense signature, and
`sparse` (holes admitted) for the other, whose receiver is any array.

Audited: at a callback within the empty footprint, `map` reads the length
once and passes each present element, and the fact holds at every visit
(to prove: `elems_rely`, the instance of `rely_chain` at the new kind, as
`map_rely` is at density), so each element passed is in $`R`$. The
result's elements are the callback's, at $`U`$, its holes the receiver's,
under the ordinary array construction the other `map` signatures assume
([ordinary array construction](../SOURCE-MODEL.md#exact-contracts-and-native-effects)).

A call node selecting a signature with `requires R` is accepted where its
receiver slot's class has an atom
$`\mathrm{elems}(x,R')`$ with $`R'\subseteq R`$ (to prove:
`requiresCall_sound`, from `call_safe` with the precondition). The
ordinary call rules select no signature with a precondition.

**The operations on signatures.** One signature covers another where its
precondition is weaker and its elements promise stronger (`Effect.covers`);
two signatures of one call combine where both state the same parts
(`PromiseWith.combine`); erasing a signature to an ordinary arrow
(`PromiseWith.erase`, `Effect.plain`) and binding it (`Effect.keeps`) are
refused for both. Lean refuses graph
code stating either part, as it refuses `freshObject` on code
(`effectChecked`). Proved for all of these (commit `1ac22b78`).

**Where the fact is not used.** No rule gives the slot $`x`$ a type from
the fact: a type's meaning is independent of the heap, and the array,
returned or stored at `readonly S[]`, would keep that type after a later
write. TypeScript accepts the following, and Node throws at its last line:

```ts
function view(xs: (string | null)[]): readonly string[] {
  return xs.every((x): x is string => x !== null) ? xs : [];
}
const a: (string | null)[] = ["a"];
const v = view(a);
a.push(null);
v[1].length;
```

## 6. The sites

- **122** (`print`) and the case: the fact from the test's `true` edge,
  `map` at it. Closed.
- **137**: no use relies on the fact; the call needs `every` at a guard
  closure, which its plain signatures take.
- **180**: `join` converts each element by the conversion contract, which
  `string | null` meets, so its plain signature applies at the receiver's
  declared type; the producer claims the receiver there rather than at
  TypeScript's narrowed `readonly string[]`.
- **195** (`printSignature`): between the test and the use the loop writes
  the `let required` cell, a write outside the empty footprint, so the fact
  is dropped. The loop reads only `stated`, so the route is a
  [reordering](../SOURCE-REWRITES.md#deciding-what-a-refusal-of-tscerts-code-calls-for):
  compute `required` before the test; then only reads lie between. Keeping
  the fact across the write needs the separation of the cell from the
  elements (§3), with regional footprints.
- **215** (`statedSignatures`): `return printed` at `string[]` is an
  escape (§5); the route is the rewrite to `filter` at its guard overload
  compared by length.

## 7. What the existing lemmas give, and what is new

Existing, used unchanged: the guard closure's footprint and promise
(`codeChecked_sound`); the stability check and its soundness
(`stable_sound`, `FactKind.support_sound` for the other kinds); the rely
along callbacks (`rely_chain`); the empty footprint as heap extension
(`Closed.holds_empty`) and the knowledge kept by it (`alloc_frames`,
`keepsCall_sound`, `inspect_safe`); the edge, merge and cut rules of heap
knowledge (`check_sound`, `checkIn_sound`, `shift_holds`,
`dropResult_holds`); the combination of two signatures' runs
(`cross_upto`, `Effect.cross_result`).

Proved (commit `1ac22b78`): the effect's `requires` and `elements` through
`Effect.post`, `PromiseWith`, `Effect.covers`, `PromiseWith.combine`,
`.erase`, `.weaken`, `Effect.drop`/`keeps` and the application rules, and
`effectChecked`'s refusal of both on code.

New:

- `FactKind.elems`, its support and `support_sound` case;
  `elemsCheck_stable`; the footprint controls.
- In `HeapKnowledge.Knowledge`: the atom (slot and predicate,
  unconditional or on a Boolean slot), with its cases of `Holds`,
  `alloc_frame`, `shift`, `check`, `meet`, `project`, `dropResult` and
  `observeBoolean`; a conditional atom tracks both its slots through
  projections and joins, and is dropped by a step that drops the
  unconditional one, whatever happens to its Boolean slot.
- `everyCall_sound` (the conditional atom from the promise), `elems_rely`,
  `requiresCall_sound` (the precondition discharged by the node's
  knowledge).
- The search (`CertificateProducer`): the link and the atom carried forward
  by the knowledge rules, met at merges, proposed at cuts, and a signature
  with a precondition tried where the receiver's class has an atom; at a
  cut, the entry edge and every back edge checked.

`checkJson_safe` keeps its premise and conclusion.

## 8. Producer, overlay and wire

- **Overlay**: `every`'s three elements signatures; `map`'s six signatures at a precondition;
  with their audited rows.
- **Wire** (an effect,
  [source claims](../SOURCE-CLAIMS.md#quantified-callables-and-their-eliminations)):
  two fields, `"requires"` and `"elements"`, each `null` or a list of the
  kinds the predicate admits (`"string"`, `"number"`, `"boolean"`, …).
  Typed in `tools/source-claims.mts`, decoded in Lean and OCaml, checked by
  `tests/json-field-names.mts`. The producer states both `null` on every
  effect it writes, and copies a declaration's.
- **Producer**: the closures after the test are claimed at TypeScript's
  narrowed element type, as now; a receiver is claimed at its declared
  type, never at the narrowed `readonly S[]`.

## 9. Cases and controls

Positive: `blocker-every-promise` (gap → verified);
`every-elements-negated` (`if (!xs.every(g)) return null;` then
`xs.map(…)`); `every-elements-loop-reads` (a loop of reads between the test
and the use); `every-elements-sparse` (a receiver typed with holes, the
result keeping them, read at `(U | undefined)[]`); `every-elements-number`
(the `number` instance).

Negative, each run under Node in `tests/node-runs.mts`, where it throws a
`TypeError` TypeScript does not predict: `invalid-every-elements-element-write`
(`xs[0] = null` between); `invalid-every-elements-alias-write` (the same
through `const ys = xs`); `invalid-every-elements-push`;
`invalid-every-elements-call` (an unknown function given `xs`);
`invalid-every-elements-guard-mutates` (the guard writes `xs[1] = null`);
`invalid-every-elements-map-callback-writes` (the `map` callback writes
`xs[i + 1] = null`); `invalid-every-elements-other-array` (the test of one
array, `map` of another); `invalid-every-elements-escape` (`view` of §5).

Forged-claim controls (`pipeline/test.mts`, through evidence production
and consumption): an atom stated after an element write; an atom about the
other of two swapped slots; the conditional atom used on the `false` edge; `every`'s result saved,
the array written, then the saved result tested;
a sparse receiver selected at `map`'s dense signature at a precondition; a bound `map` at the
precondition, and its erasure to an ordinary arrow; a cut atom justified
only by its own back edge through a body that writes an element; `every`
selected at the elements promise with a callback beyond the empty
footprint; `map` at the precondition with no atom; graph code claiming the
promise or the precondition.

## 10. Cost and risks

Lean: the effect's two parts, measured +254 −101 lines (commit
`1ac22b78`); the fact kind, its
stability and controls 250; the knowledge atom 400; the call rules 300;
the search 200; at most 1,500 lines beyond `1ac22b78`. The producer and
the wire 150; the overlay and its audits 100; docs 200; 7 positive and
negative cases each class, 10 controls; the two source rewrites of §6.

Risks: each extra overload is one more signature the search tries at an
`every` or `map` call.

## 11. Deferred

- Predicates outside the fixed set: literals, the nullish exclusions
  (`Node | undefined` at a guard excluding `undefined`), whose callback
  type is the element type filtered by the predicate, which a stated
  signature can write only as an intersection with the type parameter.
  Deriving each instance in Lean from the stated signature would cover
  every predicate, at the cost of a member contract quantified over
  predicates, read through the meaning of scheme rows.
- The other natives at the precondition (`forEach`, `filter`, `some`,
  `find`, `findIndex`, `slice`, `at`), element reads at a literal index and
  `for...of`: each another construct over the same fact, with its audit;
  `find`, `findIndex` and the iterator visit holes, so they read
  `undefined` too; `slice` skips them and keeps them as holes in its
  result.
- Guards whose type has no predicate (a union of records by a field's
  literal): a fact about a type needs a postcondition reading the world.
- Writes between the test and the use: regional footprints and separation
  of element locations (§3).

## 12. Alternatives considered

- **A footprint-keeping callback alone** gives the fact at `every`'s
  return and nothing after it ([guard overloads](../../WORK.md#guard-overloads)).
- **Narrowing the store's contract** to `S`: a location's contract is
  fixed at its allocation ([the array invariant](../SEMANTICS.md#the-array-invariant)).
- **A view type for the slot**: unsound at an escape (§5).
- **The fact at a type $`S`$**, with a postcondition reading the level and
  the world, an apart set per fact and a precondition on many natives:
  more general, and several times the size; no census site needs it.
- **Instances derived in Lean** at the guard's predicate (§11): every
  predicate, with a member contract over all of them.
- **Rewriting all five sites** to `filter` with a length comparison: no
  model change, and the route for line 215 alone.
