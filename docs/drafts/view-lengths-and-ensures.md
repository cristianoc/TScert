# View lengths and result facts

Part of [checked bound annotations](checked-bound-annotations.md) (#115): the
facts a typed array's reads below its length need, and the facts a signature
states of its result.

## The existing mechanism this extends

- **Signature facts on the call's values** ([reads below the
  length](../PROGRAM-TYPING.md#reads-below-the-length)): `Effect.pre`, index
  facts at the call's positions (`CallEffects.callEnv`), assumed by the
  arrow's meaning (`Effect.Requires`) and checked at each call
  (`call-requires`, `PromiseCalls.preconditionHolds`).
- **A fact a signature states on return**: `Effect.elements`, the kinds of the
  receiver's elements where the call returns `true` (`Effect.post`'s last
  conjunct), added to the caller's knowledge at the return. It is one
  instance of a post-fact about one position; the result facts below are the
  same kind of conjunct of `Effect.post` over index facts.
- **Terms of linear facts** ([linear facts](../PROGRAM-TYPING.md#linear-facts)):
  `HeapKnowledge.Term` (`value x`, `length x`), each reading the environment
  or one heap location, its preservation the heap-reading index facts'.
- **Host objects** (`Calculus.hostKey`): objects owning a model key no source
  property names (`RequestJson.reservedKey`), whose field map is fixed at
  allocation.
- **Typed arrays** ([byte reads](../SOURCE-CONTRACTS.md)): host views read
  through `%ByteAt%`, `%ByteLength%`, `%ByteSet%`, trusted declarations.

No new mechanism is proposed: a term kind, a conjunct of `Effect.post`, and
two trusted signatures.

## 1. The view-length term

`HeapKnowledge.Term.view x`: the element count of the typed array slot `x`
holds. Its meaning reads the location of a model key `[[viewLength]]` of the
object (`Calculus`, beside `hostKey`):

```math
⟦\mathrm{view}(x)⟧_{\rho,h}=n\iff \rho(x)=\mathsf{objAt}\,fs\,c\,i\land fs([[\mathrm{viewLength}]])=\ell\land h(\ell)=\mathsf{num}\,b\land\mathrm{SafeInt}(b,n)\land 0\le n
```

The term is defined only of a host object (one owning `hostKey`): a copy of
own keys skips model keys (`copiedKey` gains `[[viewLength]]`), and no
allocation of the program makes a host object, so no program value forges a
view's length. An immutable field map does not make the location's
contents immutable: a step given the location could write it
(`Step.writeField`, `setPresent`). So a fact naming `view(x)` is a
heap-reading fact (`IndexFact.envOnly` false), kept only where a proof shows
the location unchanged: a heap extension, and a call keeping the heap
(`call-keep`, `Closed.holds_empty`).

Trust (owner-approved 2026-11-07): every typed array, the program's or
external code's, views a fixed-size `ArrayBuffer` that is never detached;
the host owns `[[viewLength]]`, at a location no other object's field or
store shares, holding the view's element count. The trusted signatures of
section 3 state the host's reads against it. Audit: `copiedKey`, `ownAll`,
`ownData`, `storeData`, `mergeParts`, `ComputedKey.Unreserved`, `ObjectMerge`,
`Object.assign`, spread and rest, JSON: none copies or reconstructs the key.

## 2. Result facts: `Effect.ensures`

`Effect.ensures : List IndexFact` at positions `0` the result, `i + 1` the
call's position `i` (`push v (callEnv r args)`), holding in the heap a
normal return leaves:

```math
\mathrm{post}_\epsilon(r,\vec a,h,h',v)\ \text{gains}\ \forall F\in\epsilon.\mathsf{ensures}.\ F(\mathrm{push}\,v\,(\mathrm{callEnv}\,r\,\vec a),h')
```

`Effect.post` gains the actuals (`args`); every use is audited. A first
version states `ensures` on trusted signatures alone: checked code and a
written signature state none (`LocalUsing`, `Effect.below`), since a
definition's facts over its parameters need their entry values, which a
reassigned parameter no longer holds. `Effect.covers` asks the covering
signature's `ensures` to contain the covered one's; `Effect.keeps` and
`Effect.drop` refuse an effect stating any; `Effect.plain` forgets them.
Ensures holds on normal return only. At a call,
the caller's knowledge after the return gains each fact renamed from
positions to the result slot and the slots of the receiver and actuals
(`call-ensures`), where those slots are kept; the definition side
(code, units) proves them at each return. Positions name values: a fact over
an actual's value reads the value passed; a length term reads the heap the
call returns in. `old(…)` is a later extension (ghost slots). `ensures` on a
written signature (`@ensures`) is the clause language of `@requires` with
`result`.

## 3. The typed-array signatures (trusted)

```math
\%\mathrm{ByteLength}\%\colon(\mathit{View})\Rightarrow_\emptyset^{\ \mathsf{ensures}\ [\mathrm{int}(0),\ 0=\mathrm{view}(1)]}\mathtt{number}
```

```math
\%\mathrm{ByteAt}\%\colon(\mathit{View},\ \mathtt{number})\Rightarrow_\emptyset T\mid\mathtt{undefined}\ \land\ (\mathit{View},\ \mathtt{number})\Rightarrow_\emptyset^{\ \mathrm{int}(2),\ 0\le 2,\ 2-\mathrm{view}(1)\le -1}T
```

with `T` the view's element type (a `Float64Array`'s any double, NaN
included). Audit: a safe integer below the count is a valid integer index
(`IsValidIntegerIndex`: integral, not `-0`, below the length; the numeric key
`-0` is `0` after `ToPropertyKey`'s canonical numeric string, so the read is
the element 0's); the read runs no code and reads no prototype.

## 4. Order of work

1. `Effect.ensures`, `Effect.post` over the actuals, `call-ensures`; the
   definition side for code; wire; producer reading it. Cases through a
   trusted signature first (`%ByteLength%`).
2. `Term.view`, `[[viewLength]]`, the reserved-key audit, trust row in
   DESIGN.md and the contract in SOURCE-CONTRACTS.md.
3. The two signatures; producer `view` terms (`b.length` of a view); cases:
   a loop reading a `Uint8Array` below its length, negatives under Node
   (past the end, a different view's length).
