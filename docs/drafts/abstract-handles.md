# Draft: abstract handles

A design for abstract types whose representation and invariant belong to an
owner, a set of modules of the analysed sources: a handle such as
upstream pretext's `PreparedText`, `{ readonly [brand]: true }`, which its
owner casts to its record (`prepared as InternalPreparedText`) and external
code holds only at the opaque type or at read-only views. It answers
pattern P22 of [Tolerant frames II](tolerant-frames-2-note/note.tex) at
its handle sites (form (b) of the
[dossier](callback-frames-dossier.md)) and states what it gives P15, P16,
P18 and P20.

Base: TScert `single-pass` at `ac7ec4f9`; upstream pretext is
chenglou/pretext at `0d102a5`, its files under `src/`; "Paper I" is
[Tolerant frames](tolerant-frames-note/note.tex). Claims are labelled
**proved** (with the Lean name), **cited** (a document with its scope, or a
source file and line at the stated commit) or **conjectured**. Everything
this draft defines is conjectured until the Lean of
[what Lean proves](#what-lean-proves) exists.

## The existing mechanism this extends

[The general mechanisms](../DESIGN.md#general-mechanisms) give a fact a
construct relies on while other code runs to
[footprints](../FOOTPRINTS.md) (cited): the fact, its stable operations as
closed footprints, Lean certifying the code within them, the construct's
rule. This design is that mechanism with one more source of stability: the
owner's own code, certified within one footprint, the owner's protocol.

It extends four existing pieces:

- **Sealed handles** (cited:
  [a handle means its representation](../PROGRAM-TYPING.md#a-handle-means-its-representation),
  rule `handle-meaning`; [type invariants](../ARITHMETIC.md#type-invariants);
  [`@representation`](../ANNOTATIONS.md#representation-t)). A type `H`
  stating `@representation T` means `T`, so a cast out holds of every value
  of `H`; its `@invariant` is a contract of function boundaries
  (`invariant-requires`, `-ensures`, `-returns`). A sealed handle that also
  states `@opaque` is an abstract type: `handle-meaning` holds inside its
  owner, and the owner tag, the sealed map, the protocol and the invariant
  as a property of every state, (W6), hold of it. A sealed handle without
  `@opaque` keeps its meaning and its trust rows.
- **Contracts fixed at allocation** (cited: Paper I, Definition "World";
  [density belongs to a contract](../DESIGN.md#lasting-decisions)). A
  location's kind and contract are chosen where it is allocated and never
  change; the owner tag is one more component, as an array's presence mode
  is, and a location's protocol entry is fixed where it is sealed.
- **Support, respect and Reliance** (proved: Paper I, Definitions "Support"
  and "Respect", Proposition "Reliance"; Lean `respect_sound`,
  `rely_chain`). The frame consequence at a callback is Reliance with the
  callback's effect, under an admissibility that bounds sealed locations
  by their protocol entries.
- **Inferred effects certified per function** (cited:
  [inferred call effects](../SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification)).
  The front proposes the protocol, the tags and the seal points; Lean
  certifies each function at them.

New machinery: one contract component, two world components (the sealed
map and the sealed roots), two clauses of well-formedness, one clause of
admissibility, one ghost command, and world entries in the effect
language, whose action is on pairs of a heap and a world. No new judgment
form and no new modality.

## The example

```ts
declare const brand: unique symbol
/** @opaque Pass back only a value this package gave you at this type, never a
 *  copy or a substitute. Of it and of anything reached from it, read only the
 *  members its type states; change nothing.
 *  @invariant this.flags.length === this.widths.length
 *  @representation Rep */
export type Handle = { readonly [brand]: true }
type Rep = { widths: number[]; flags: number[] }

export function prepare(n: number): Handle {
  const r: Rep = { widths: new Array(n).fill(1), flags: new Array(n).fill(0) }
  return r as unknown as Handle
}

export function walk(h: Handle, visit: (w: number) => void): number {
  const r = h as unknown as Rep
  let s = 0
  for (let i = 0; i < r.widths.length; i++) { visit(r.widths[i]!); s += r.flags[i]! }
  return s
}
```

`visit` is external code and may hold `h`, at `Handle`. The read
`r.flags[i]!` needs $`i<|r.\mathit{flags}|`$ after `visit`.

## The definition

Paper I's notation throughout: a world $`W`$, a heap $`h`$, changes
$`\mathsf{keep}\sqsubseteq\mathsf{init}\sqsubseteq\mathsf{scalar}\sqsubseteq\mathsf{grow}\sqsubseteq\mathsf{any}`$,
regions read at the entry heap, $`\Phi\triangleleft S`$ for respect.

**Owners and abstract types.** An owner $`O`$ is a set of modules of the
analysed sources, its boundary as [decision 1](#decisions) fixes it. An
abstract type $`A`$ of $`O`$ is a type exported by an entry of $`O`$ that
states `@opaque` and `@representation R_A`, and declares no member but a
brand under a `unique symbol` key no module exports; $`I_A`$ is its
invariant (`true` where none is stated).

**Intersected handles.** A type $`A\mathbin{\&}V`$ an entry exports, with
$`V`$ a record of read-only members, is an abstract type of $`O`$ when it
states its own `@representation R'` with $`R'`$ a subtype of $`R_A`$, and
`@opaque`. Its roots are $`(o,A\mathbin{\&}V)`$, each also a root of $`A`$;
its paths are $`\mathit{Path}(R')`$, with $`\delta_{A\&V.p}=\delta_{A.p}`$
on the paths it shares with $`R_A`$; each member of $`V`$ is checked as a
read-only view, at every depth, of the field of $`R'`$ with that name.
Upstream's `PreparedTextWithSegments` is
`PreparedText & { readonly segments; readonly kinds; readonly widths }`
(cited: `layout.ts:53–57`) over the representation
`PreparedSegments & { kinds }` (cited: `layout.ts:64`), so `segments` and
`kinds` are paths of it and get entries.

**The admitted types.** The types an abstract type's representation, and a
signature crossing the owner's boundary, may use are given by

```math
T ::= \beta \mid A \mid \{f_i:T_i\}_i \mid \mathsf{readonly}\ T \mid E[\,] \mid T_1\mid T_2 \mid T_1\mathbin{\&}T_2 \mid (\vec T)\Rightarrow_\Phi T
```

with $`\beta`$ a scalar type, a typed array, or a type no clause names
(a collection, a class instance): a leaf. Any other form (a generic, a
conditional or mapped type, an index signature) that names an abstract
type is refused where it names it (`invalid-abstract-type-form`).

**Paths.** The paths of a type, by induction on the grammar:

```math
\begin{aligned}
\mathit{Path}(\{f_i:T_i\}_i) &= \{f_i\}\cup\{f_i.q \mid q\in\mathit{Path}(T_i)\}\\
\mathit{Path}(E[\,]) &= \{\mathsf{spine},\ \mathsf{cells}\}\cup\{[*].q\mid q\in\mathit{Path}(E)\}\\
\mathit{Path}(T_1\mid T_2) &= \mathit{Path}(T_1)\cup\mathit{Path}(T_2)\\
\mathit{Path}(T_1\mathbin{\&}T_2) &= \mathit{Path}(T_1)\cup\mathit{Path}(T_2)\\
\mathit{Path}(T) &= \emptyset\ \text{for every other type}
\end{aligned}
```

A path ends at a leaf, an abstract type, a read-only type or a function:
such a value is tagged where it is the owner's and never sealed, and
$`I_A`$ reads nothing of it. A field holding a typed array is a path; the
typed array's view spine carries no owner tag, so a write through a typed
array is an ordinary write, and its length is kept by every transition, by
Paper I's rule (View) (cited: Paper I, §"Entering the modality", (View)).
So nested arrays such as `breakableFitAdvances: (number[] | null)[]` have
paths through their inner arrays, and no path reads a typed array's
elements.

**Owner tags.** A contract may carry an owner $`O`$:
$`W(l)=(\kappa,T,O)`$, fixed by world extension as $`\kappa`$ and $`T`$
are. A writable type tagged $`O`$ is a subtype of its untagged read-only
views at every depth (`readonly (readonly number[] | null)[]`,
`ArrayLike<T>`, a `readonly` field) and of no untagged writable type, in
either direction, as presence modes are. The front proposes each
allocation's tag from the flow of its value into a representation; Lean
checks the function at it.

**Sealed roots and the sealed map.** A sealed root is a pair $`(o,A)`$ of a
handle's identity location and its abstract type. The world carries, for
each owner, a finite map $`\Sigma_O`$ from locations to changes and a set
$`\mathit{Roots}_O`$ of sealed roots. Extension only extends both:
$`W\sqsubseteq W'`$ requires $`\Sigma_O\subseteq\Sigma'_O`$ as maps and
$`\mathit{Roots}_O\subseteq\mathit{Roots}'_O`$. A location's entry is fixed
where it is sealed, as its contract is where it is allocated. For a root
$`(o,A)`$ and a path $`p\in\mathit{Path}(R_A)`$, $`o.p(h)`$ is the set of
locations $`p`$ reaches from $`o`$ in $`h`$.

**The protocol.** Each owner has an effect
$`\Gamma_O=\{A.p:\delta_{A.p}\}`$ over the paths of its abstract types.

**Well-formed state** gains:

- **(W5) protocol.** For every $`(o,A)\in\mathit{Roots}_O`$, every
  $`p\in\mathit{Path}(R_A)`$ and every $`l\in o.p(h)`$:
  $`l\in\mathrm{dom}\,\Sigma_O`$ and $`\Sigma_O(l)=\delta_{A.p}`$.
- **(W6) invariants.** For every $`(o,A)\in\mathit{Roots}_O`$:
  $`I_A(o,h)`$.

**Admissible transition** gains: every $`l\in\mathrm{dom}\,\Sigma_O`$ of the
entry world with $`l<|h|`$ satisfies $`\Sigma_O(l)_{|h|}(h(l),h'(l))`$. The
clause reads no heap to find a location's bound, so it is transitive, each
change being a preorder, and rigid.

**Meaning of an abstract type, and the boundary conversion.** Inside its
owner, `handle-meaning` holds: $`⟦A⟧=⟦R_A^O⟧`$, the representation at
contracts tagged $`O`$. Outside it, $`A`$ means its sealed roots, and the
external meaning of every admitted type follows by structure:

```math
\begin{aligned}
v\in⟦A⟧^{\mathrm{ext}} &\iff v\in⟦R_A^O⟧ \land (\mathrm{id}(v),A)\in\mathit{Roots}_O\\
⟦\{f_i:T_i\}⟧^{\mathrm{ext}},\ ⟦E[\,]⟧^{\mathrm{ext}},\ ⟦T_1\mid T_2⟧^{\mathrm{ext}},\ ⟦T_1\&T_2⟧^{\mathrm{ext}} &= \text{the same constructor over the parts' external meanings, at untagged contracts}\\
v\in⟦(\vec S)\Rightarrow_\Phi T⟧^{\mathrm{ext}} &\iff \text{every call of } v \text{ with arguments in } ⟦\vec S⟧^{\mathrm{ext}} \text{ ends in } ⟦T⟧^{\mathrm{ext}} \text{ within } \Phi
\end{aligned}
```

A value of $`R_A^O`$ has the external meaning of no type but a read-only
view, since its contracts are tagged. The boundary conversion is the
identity on values with one obligation: a value the owner gives code
outside it, at any position (a result, an argument of an external call,
an exported binding, a store where external code reads, a throw), is in
the external meaning of the type there. For a function the owner gives
out, the obligation is its certificate at the external meaning of its
type: an escaped closure returning $`A`$ seals its result before each
return. Every value of $`A`$ that crosses the boundary meets $`I_A`$, by
(W6).

**Undeclared views are refused.** A representation part may cross the
boundary only as a member $`V`$ declares on an abstract type's
intersection: an outward transfer of a representation part at any other
read-only type is refused (`invalid-abstract-undeclared-view`). **This is
an explicit restriction**: assumption (ii) of the [trust](#trust) covers
only values reached from an abstract type, so a view given out otherwise
has no assumption behind it. It is documented in SOURCE-FRAGMENT.md.

**Declaration side conditions** (refused otherwise):

- *Closed.* $`\mathrm{supp}(I_A)`$ names only regions $`\mathtt{this}.p`$
  for paths $`p`$ of $`R_A`$, and typed-array lengths.
- *Tolerant.* $`\Gamma_O\triangleleft\mathrm{supp}(I_A)`$ at every path:
  each change the protocol allows on a path the invariant reads is one its
  support tolerates. **This is an explicit restriction** ([decision
  2](#decisions)): an invariant that a write breaks and a later write
  restores is refused, as Paper I's limit "Broken and restored invariants"
  states for assertions. It is documented in SOURCE-FRAGMENT.md and
  enforced at the declaration.

**(W6) is preserved without circularity.** Support is stated over the
transitions between states meeting (W1) to (W5), admissible with the
protocol clause; *Tolerant* gives that each such transition keeps
$`I_A`$ of every sealed root; (W6) after the transition follows. No step of
the argument assumes (W6) of the endpoint (conjectured; Lean item 1).

**Sealing.** A step seals when it makes a location reachable at a path of
a sealed root that was reachable at none: the ghost command
$`\mathsf{seal}_A(e)`$, its place proposed by the front at or before the
first point where the value reaches code outside the owner; a store into a
location at a path of a sealed root; and any write that extends some
$`o.p(h)`$, a `push` adding a cell to a sealed spine included. Its
obligations are collected over the heap after the step, from every root
and every path:

- every location newly reached at some path $`p`$ of some root $`(o,A)`$
  is unsealed or already in $`\Sigma_O`$, and every path of every root
  reaching it, the new root's included, has the same entry
  $`\delta_{A.p}`$, equal to its existing entry where it has one;
- for $`\mathsf{seal}_A(e)`$: $`e`$ meets $`R_A^O`$ and $`I_A(e,h)`$.

Its world change maps each newly reached location to that entry and, for
$`\mathsf{seal}_A(e)`$, adds $`(\mathrm{id}(e),A)`$ to
$`\mathit{Roots}_O`$. (W5) after the step follows from the agreement
obligation, since the entries of every other location and every other
root are unchanged (conjectured; Lean item 2).

**Effects on the world.** An effect acts on pairs of a heap and a world.
Its heap entries act as Paper I states. Its world entries are regions
$`\Sigma_O[r]`$ and $`\mathit{Roots}_O[r]`$ of locations, at one change,
$`\mathsf{init}`$-shaped: a location of $`r`$ with no entry may gain one,
and an entry, once present, is fixed; a location outside every world entry
gains none:

```math
(h,W)\xrightarrow{\Phi}(h',W') \iff h\xrightarrow{\Phi_{\mathrm{heap}}}h' \land W\sqsubseteq W' \land \mathrm{dom}\,\Sigma'_O\setminus\mathrm{dom}\,\Sigma_O\subseteq\textstyle\bigcup\{r(\rho,h)\mid\Sigma_O[r]\in\Phi\}
```

and the same for $`\mathit{Roots}_O`$. A seal's effect is
$`\{\Sigma_O[e.\mathit{paths}]:\mathsf{init},\ \mathit{Roots}_O[\mathrm{id}(e)]:\mathsf{init}\}`$.
Effects compose per exit as Paper I's do: a call's normal exit and its
exceptional exit each carry their world entries, `seq_eff` joins them, and
`fresh_eff` drops entries on locations above the caller's mark. A callee
that seals and then throws carries its world entry on its exceptional
exit, so the caller's handler holds no $`\mathsf{unsealed}`$ fact the seal
falsified. Independence of the world (cited: Paper I, Definition
"Independence of the world") holds of every assertion without a world
fact; the two facts below read the world and are kept by their world
supports.

**Sealed and unsealed facts.** The fact
$`\Sigma_O(x.p)\sqsubseteq\delta`$, the location $`x.p`$ reaches is sealed
with an entry at most $`\delta`$, is monotone in the world; it is kept by
every transition that keeps the path's proper prefixes, and a prefix
sealed at $`\mathsf{keep}`$ is kept by every admissible transition. The
fact $`\mathsf{unsealed}(x.p)`$ holds of a fresh allocation; its support
is $`\{x.q:\mathsf{keep}\mid q\ \text{a proper prefix of}\ p\}\cup\{\Sigma_O[x.p]:\mathsf{keep}\}`$:
a write to a prefix, or a world entry that may cover $`x.p`$, removes it,
unless $`x.p`$ is known separate from that entry's region by Paper I's
separation facts. A call's summary carries its world entries, composed as
above. An external call's $`\Sigma_O`$ entry is empty when every entry of
the owner has an empty $`\Sigma_O`$ entry after `fresh_eff`, and otherwise
covers every location tagged $`O`$, since external code seals only by
calling the owner's entries ([trust](#trust)) with arguments it chooses.
For pretext it is empty: its one sealing store after preparation,
`rich-inline.ts:1176–1178`, seals arrays fresh in the call. Both facts are
ordinary preconditions and postconditions, inferred.

**Elimination**, `h as R_A` or `h as A & R_A`, only in the owner: the
identity, as `handle-meaning` gives it. Where $`(\mathrm{id}(h),A)`$ is a
sealed root it gives $`I_A(h,h)`$, by (W6), and the facts
$`\Sigma_O(h.p)=\delta_{A.p}`$, by (W5). A cast out written outside the
owner is refused.

**Writes.** A write whose target location is tagged $`O`$ is checked as one
of: the target is $`\mathsf{unsealed}`$, and the write is an ordinary one;
or $`\Sigma_O(\mathit{target})\sqsubseteq\delta`$ is known, and the write is
within $`\delta`$. A walker or helper holding only location facts at a
structural type writes by the second. The target's path is needed only
where the written value has continuing paths, for the sealing obligation
above. A write to a target with neither fact is charged in $`\Gamma_O`$ to
every path of $`O`$ whose contract admits the target; a $`\Gamma_O`$ that
this makes intolerant is refused at that write.

**Effects of class entries.** A class entry $`(c:\delta)`$ of any effect,
stated or inferred, bounds a location $`l`$ of class $`c`$ outside
$`\mathrm{dom}\,\Sigma_O`$ by $`\delta`$ and a location
$`l\in\mathrm{dom}\,\Sigma_O`$ by $`\delta\sqcap\Sigma_O(l)`$. This is a
consequence of the admissibility clause, which every transition already
meets. So `{ values: "any"; spines: "grow" }` bounds a sealed location by
its entry, and `{}` keeps it.

**The protocol is inferred, and closed under the owner's operations.** The
front proposes the least $`\Gamma_O`$ covering every write of the owner's
functions to a location not known unsealed, every exported function
included; Lean certifies each function within it and checks the side
conditions against it. External code changes a sealed location only by
calling the owner's functions ([trust](#trust)), so a callback's whole run,
a reentrant call of an exported writer included, is within $`\Sigma_O`$ on
sealed locations. A fact a walker holds about a sealed location survives a
callback exactly when every exported operation's writes keep it.

## The frame consequence

Every native step and every callback has an effect bounded on
$`\mathrm{dom}\,\Sigma_O`$ by $`\Sigma_O`$, by the admissibility clause, and
$`\Sigma_O`$ is rigid. By Reliance (proved: Paper I, Proposition
"Reliance", `rely_chain`), a fact whose support on sealed locations is
respected by their entries, and whose other support the call's effect
respects, holds after the call.

In the example the front infers $`\Gamma=\mathsf{keep}`$ on every path. That
inference rests on the writes before the seal, the two `fill`s and the
record's construction, being checked as writes to $`\mathsf{unsealed}`$
fresh locations; after `prepare`'s seal no function writes a sealed
location. `walk`'s parameter is at an entry's signature, so `h` is a sealed
root and $`\Sigma(r.\mathit{widths}.\mathsf{spine})=\Sigma(r.\mathit{flags}.\mathsf{spine})=\mathsf{keep}`$;
the facts $`i<|r.\mathit{widths}|`$ and $`|r.\mathit{flags}|=|r.\mathit{widths}|`$
cross `visit` with no annotation at the call and no change to `visit`'s
type (conjectured, the design's claim).

Reentrancy, two variants of the example:

- An exported `truncate(h)` pops `r.widths` and then `r.flags`. The first
  pop breaks $`I`$ until the second, so the declaration is refused
  (*Tolerant*). A walker reading `r.flags[i]` before `visit` is safe with
  it under Node: the refusal is the restriction's, a restriction control.
- With no invariant, an exported `truncate(h)` pops `r.widths`, and a walker
  reads `r.widths[i]` for `i` below the length it read before the loop.
  $`\Gamma(\mathtt{Handle}.\mathit{widths}.\mathsf{spine})=\mathsf{any}`$, so
  $`i<|r.\mathit{widths}|`$ does not survive `visit` and the read is
  refused; under Node a visitor calling `truncate` makes it read
  `undefined`.

An invariant $`|r.\mathit{flags}|\ge|r.\mathit{widths}|`$ is refused with
$`\mathsf{any}`$ on `widths`' spine: $`\mathsf{any}`$ lets the spine grow, which
the support does not tolerate.

## Every place encapsulation can leak

- **A cast out, outside the owner.** In analysed code: refused, including
  through `unknown`, an intersection or a generic. In external code:
  excluded by the [trust](#trust) assumptions.
- **An outward transfer of the representation or a part of it at a writable
  type.** Refused at the transfer: a tagged writable type is no subtype of
  an untagged type (`invalid-abstract-return-rep`). A fresh copy is
  admitted.
- **`PreparedTextWithSegments`'s `readonly widths: ArrayLike<number>`**
  (cited: upstream `layout.ts:53–57`). An intersected handle's member is a
  view: checked to be a read-only supertype, at every depth, of its own
  representation's field. A writable declared member is refused
  (`invalid-abstract-writable-view`); a representation part given out at a
  read-only type no intersected handle declares is refused
  (`invalid-abstract-undeclared-view`).
- **Spreading a handle.** In the owner: the result is a fresh record whose
  fields hold already-sealed locations; sealing it is an introduction,
  admitted where the shared paths have the same protocol entries. In
  external code: excluded by assumption (i).
- **Reentrant calls of exported writers.** Within $`\Sigma_O`$ by
  construction (above).
- **Typed arrays.** No path reads a typed array's elements, and its length
  never changes, so no fact the design keeps depends on which views share
  its bytes.
- **An untagged alias made before sealing.** Excluded by typing: the
  representation's locations are allocated at tagged contracts and no
  tagged writable value has an untagged writable type.
- **An owner alias writing after sealing.** The write rule: beyond the
  target's entry only where $`\mathsf{unsealed}`$ holds, and an
  unattributed write charged to every admitting path.
- **A callback of the owner's own code capturing the representation**
  (pretext's lambdas in `layoutWithLines`, `walkRichInlineLineRanges`).
  Analysed code: its writes are certified within $`\Gamma_O`$ or on
  unsealed locations, wherever it is called from.
- **A forged handle.** `{…} as unknown as A` of no representation is
  refused (`invalid-sealed-handle-forged`); an external value passed at
  $`A`$ is by assumption (i) one the owner sealed.
- **Prototype or host tampering.** $`I_A`$ reads own data fields of records
  the owner allocated, array spines and typed-array lengths: the caller
  contract, the ordinary-array assumption and fixed-length typed arrays
  (cited: [trust surface](../DESIGN.md#trust-surface), existing rows). Any
  other step on a handle is excluded by assumption (ii).

## Trust

Honouring the exported types does not give this design what it needs.
TypeScript gives a spread `{ ...h }`, `Object.assign({}, h)` and
`structuredClone(h)` the type of `h` with no cast, and `Object.freeze(h)`
and `Object.defineProperty(h, …)` are type-correct; Paper I's `readonly`
makes no location immutable. The design therefore rests on two **new
assumptions** about external code, which the owner approves on the
condition that each abstract type states them in its exported declaration,
by `@opaque`. A type without `@opaque` gets neither.

The new row of the [trust surface](../DESIGN.md#trust-surface):

> For each type an entry of the analysed sources exports with `@opaque`
> (an abstract type), external code (i) passes, at every position whose
> type names the abstract type, only a value identical to one it received
> from the analysed sources at a type naming it, and (ii) every step it
> takes on the properties, attributes or prototype of a value it holds at
> a type naming the abstract type, or of one reached from such a value, is
> a read of a member its type states. A type without `@opaque` is read
> under neither assumption.

Assumption (ii) restricts only steps on the properties, attributes and
prototype of values reached from an abstract type: holding such a value,
comparing it and using it as a key are no such steps. A read-only view
the owner gives out otherwise has no assumption behind it, and its
transfer is refused ([undeclared views](#the-definition)).

Where it is stated: the `@opaque` annotation of each such type, whose text
is the assumption in the words a user of the package reads; `@opaque` in
the declaration reader.

Two existing rows change with it:

- The row of sealed handles' callers ("passes … a value of `R` meeting the
  handle's invariant") applies to sealed handles without `@opaque`; for an
  abstract type (i) replaces it, and the invariant follows from (W6).
- The row of exported preconditions keeps "a sealed handle's included" for
  sealed handles without `@opaque`; an abstract type's invariant follows
  from (W6).

The assumptions state nothing about reentrant calls: external code may call
any exported function, with any arguments its types allow. For analysed
code each part is checked; for external code it is assumed.

**Scope lost.** Upstream pretext supports uses of a handle the assumptions
exclude; under them, acceptance says nothing of a program that makes one:

- A handle the application froze, or a copy kept by a store that freezes
  its state: upstream keeps the source lists of a frozen paragraph handle
  in a side table (cited: `rich-inline.ts:1141–1146`, `1173–1178`). The
  `Object.isFrozen` branch (`:1173`) stays checked code, not assumed dead.
- A JSON copy of a handle passed back: upstream reads `segmentFlags` by
  index so that such a copy lays out the same (cited:
  `line-break.ts:26–28`).
- A structural copy passed back: a spread, `Object.assign` or
  `structuredClone` of a handle, which TypeScript types as the handle.

## What Lean proves

1. **Preservation** (Paper I, Theorem "Preservation") for the extended
   state: (W5) from the seal's and the sealing store's obligations; the
   admissibility clause from each function's certified writes; (W6) from
   *Tolerant* over transitions meeting (W1) to (W5), as stated above. With
   reentrancy, the induction is over the length of the run, every owner
   function's certificate assuming the bound of the calls it makes.
2. **Sealing** extends the world and keeps (W1) to (W6), from its
   obligations collected over every root and path, every write that
   extends a path's locations included.
3. **Effect denotation**: the action on heap-and-world pairs; the
   class-entry reading is sound for every certified summary; world entries
   compose on normal and exceptional exits by `seq_eff`, rebasing and
   `fresh_eff`, whose statements gain the world component; respect gains
   the disjointness of $`\mathrm{dom}\,\Sigma_O`$ from the untagged
   classes; Independence of the world holds of every assertion without a
   world fact.
4. **The boundary conversion**: the external meaning of every admitted
   type, arrows included, is met by every value the owner gives out, from
   each function's certificate at its type's external meaning.
5. **Reliance**: $`\Sigma_O`$ is rigid and bounds every admissible
   transition; the class effects meet with it are rigid.
6. `SourceClaimJson.PassUnit.mode8Accepted_sound` keeps its statement;
   `PassUnitSafe`'s entry condition reads the extended well-formedness, and
   its premise and conclusion are reviewed again, as a change of the
   accepted plan type requires.

The note gains the tag, the sealed map and roots, (W5), (W6), the clause of
admissibility, the seal command and the two facts; the Lean states the same
definitions.

## Implementation

**What acceptance reads.** The fragment carries each abstract type's
declaration ($`R_A`$, $`I_A`$, its declared views, its `@opaque`), the
owner and its entries, the proposed $`\Gamma_O`$, the tags at allocations
and signatures, the seal points and each summary's $`\Sigma_O`$ entry.
`FunctionPlan.certify` checks each function at them; the module-interface
check (`--module-interface`) checks the side conditions, every outward
transfer's typing, and that every module of the owner reads the same
$`\Gamma_O`$. Every proposal is untrusted: a wrong tag, a missing seal, a
too-small $`\Gamma_O`$ fails a function's check.

**The annotation.** [ANNOTATIONS.md](../ANNOTATIONS.md) gains this entry:

> **`@opaque TEXT`**
>
> On an exported type alias or interface that states `@representation` and
> declares only a brand under a `unique symbol` key no module exports, or
> that is such a type intersected with a record of read-only members: the
> type is an abstract type of its owner, and external code is assumed to
> meet the two assumptions of the abstract-type row of the trust surface.
> `TEXT` must be the sentence below, up to white space, so that a user of
> the package reads the assumption where the type is declared; any other
> text is refused. A type without `@opaque` is a sealed handle and gets no
> abstract-type trust.
>
> "Pass back only a value this package gave you at this type, never a copy
> or a substitute. Of it and of anything reached from it, read only the
> members its type states; change nothing."

Upstream pretext's two handles, as they would be written (the
representation of `PreparedRichInline` named by an alias of its fields,
`RichInlineFlow`, so that `InternalPreparedRichInline` is
`PreparedRichInline & RichInlineFlow`; a type-only rewrite):

```ts
declare const preparedTextBrand: unique symbol

/** @opaque Pass back only a value this package gave you at this type, never a
 *  copy or a substitute. Of it and of anything reached from it, read only the
 *  members its type states; change nothing.
 *  @invariant this.segmentFlags.length === this.widths.length
 *  @representation PreparedLineBreakData */
export type PreparedText = {
  readonly [preparedTextBrand]: true
}

declare const preparedRichInlineBrand: unique symbol

/** @opaque Pass back only a value this package gave you at this type, never a
 *  copy or a substitute. Of it and of anything reached from it, read only the
 *  members its type states; change nothing.
 *  @representation RichInlineFlow */
export type PreparedRichInline = {
  readonly [preparedRichInlineBrand]: true
}
```

The invariant shown for `PreparedText` reads a typed-array length and an
array's spine, which $`\Gamma=\mathsf{keep}`$ on `widths` tolerates.

## Controls and Node-run negatives

Controls (forged fragment or forced proposal), each refused:
$`\Gamma_O`$ forced smaller than a writer needs; a tag dropped at an
allocation; a seal point removed; a summary's $`\Sigma_O`$ entry forced
empty on a sealing callee; a declared member forged writable; $`I_A`$
forged to read an untagged path or a typed array's element; an entry forged
as a non-entry; a path's agreement obligation forged to pass with two
entries for one location; `@opaque` forged onto a type whose declaration has no
`@opaque`.

Negative cases, each unsafe under Node (observed: the programs, as
JavaScript, in the session scratchpad, `node <file>` printing the reads):

- `invalid-abstract-return-rep`: an entry returns `widths`, the client
  pushes onto it, `walk` reads `flags` past its end: `[0, 0, undefined]`.
- `invalid-abstract-write-after-seal`: the builder keeps `widths` and an
  exported function pushes onto it after the return: `[0, 0, undefined]`.
- `invalid-abstract-callee-seals`: a callee passes the representation to
  external code, which keeps it; the caller pushes onto `widths`; `walk` of
  the kept handle reads `[0, 0, undefined]`.
- `invalid-abstract-reentrant-writer`: no invariant, an exported
  `truncate` pops `widths`, the walker reads below the length it read
  first, the visitor calls `truncate`: `[1, undefined, undefined]`.
- `invalid-abstract-writable-view`: a declared member `widths: number[]`;
  the visitor pushes through it: `[0, 0, undefined, undefined]`.
- `invalid-abstract-intolerant-invariant`: $`|flags|\ge|widths|`$ with an
  exported writer setting `widths.length`, called by the visitor:
  `[0, 0, undefined]`.
- `invalid-abstract-undeclared-view`: an entry returns `widths` at
  `readonly number[]`, a view declared on no abstract type's intersection,
  so no assumption covers it; the client pushes through it in the visitor:
  `[0, 0, undefined]`. It is also the control of the undeclared-view
  restriction.
- `invalid-abstract-seal-then-throw`: a callee seals its argument and
  throws; the caller's handler pushes onto `widths` and calls `walk`,
  refused at the push, the handler holding no $`\mathsf{unsealed}`$ fact:
  `[0, 0, undefined]`.
- Existing: `invalid-sealed-handle-forged`, `-builder`, `-resize`,
  `-invariant-cast`.

Restriction controls, safe under Node and refused by a stated restriction:
`abstract-open-invariant-refused`, an exported `truncate` popping `widths`
then `flags` under $`|flags|=|widths|`$, with a walker reading `flags[i]`
before `visit` (Node: `[0, 0]`); `abstract-view-element-refused`, an
invariant reading a typed array's element; `abstract-type-form-refused`,
a mapped type over an abstract type in an entry's signature.

Positive: the example above; `bounds-pattern-unreachable-handle-refused`
with its handle stating `@opaque`; `blocker-pretext-opaque-handle-cast`
once it states `@representation` and `@opaque`.

## Pretext

### Writes to a handle after its preparation

**Pretext writes handle fields after preparation, at one function**
(cited, a search of upstream `src/` for writes to the fields of
`PreparedLineBreakData`, `PreparedSegments` and
`InternalPreparedRichInline`, and for element and spine writes in
`line-break.ts`, `line-text.ts` and `layout.ts`):

- `materializeRichInlineLineRange` (`rich-inline.ts:1192`, exported) calls
  `findSegmentSources` (`:1199`) where the field `sourceStarts` it read at
  `:1198` is `null`, which writes `flow.sourceStarts`, `flow.sourceEnds` and
  `flow.sourceUnits` of an unfrozen paragraph handle (`:1176–1178`), each
  to a fresh array. The stores are sealing stores.
- No other function writes a handle's field, array or typed array once the
  handle is returned: `line-break.ts` writes only the cursor's and
  `stats`' fields (`:268–280`, `:312–315`, `:403–404`, `:583–584`,
  `:1064–1065`, `:1081–1082`, `:1127`, `:1155–1163`); `line-text.ts`
  writes its `WeakMap` side table and fresh `Int32Array`s (`:14–28`);
  `layout.ts` writes `prepared.kinds` before `prepareWithSegments` returns
  (`:150`).

The protocol for pretext (conjectured): $`\mathsf{keep}`$ on every path of
`PreparedText`; on `PreparedRichInline`, $`\mathsf{init}`$ on
`sourceStarts`, from the checked precondition
`flow.sourceStarts === null` of `findSegmentSources`, which `:1198–1199`
establishes with no write between; $`\mathsf{any}`$ on `sourceEnds` and
`sourceUnits`, whose being `null` no test there establishes;
$`\mathsf{scalar}`$ on `wholeWidth`, `wholeStart`, `wholeEnd`, written by
`findWholeLine`'s lambda after the seal below (`:819–823`);
$`\mathsf{keep}`$ on every other path. No walker reads the six fields, so
the protocol keeps every fact the walkers hold.

### Writes by preparation helpers into arrays they receive

**Yes** (cited):

- `measureAnalysis` (`prepare.ts:352`) fills a rich-inline paragraph's
  lists, which it receives: `widths`, `segmentFlags` and
  `breakableFitAdvances` are `paragraph`'s (`:379`, `:382`, `:383`), written
  by index (`:577–579`, `:588`, `:610`); `prepareRichInline` allocates them
  (`rich-inline.ts:287–290`) and passes them at `:479`.
- `addKanaKerning` writes cells of the `widths` it receives
  (`prepare.ts:668`, `:670`, `:672`).
- After its first cast to a branded type, preparation writes:
  `measureAnalysis` casts at `prepare.ts:638` and writes `prepared.segments`
  at `:639`; `prepareWithSegments` writes `prepared.kinds`
  (`layout.ts:150`); `prepareRichInline` writes `data.segments` (`:639`,
  after the cast to `PreparedSegments` at `:638`), `segmentData.hangEnds`
  (`:646`), and through `setEmptyObjectFacts` (called at `:640`)
  `emptyObjectSpaces` and `emptyObjectReturns` (`:794–795`);
  `findWholeLine` writes `wholeWidth`, `wholeStart`, `wholeEnd`
  (`:819–823`) after the casts at `:221` and `:664`.
- `measureAnalysis`'s result is both a text handle and a paragraph handle's
  `data` (`rich-inline.ts:214–221`); a multi-item paragraph's `data` is
  cast only to `PreparedSegments` (`:638`), no abstract type.
- The walkers take a structural type: `walkPreparedLinesRaw(prepared:
  PreparedLineData, …)` (`line-break.ts:287–288`).

These fix four parts of the definition: the tag is the owner, not the
abstract type (one allocation under two types); sealing is a command at the
owner's boundary, not the cast (every write above precedes the return to
the application); a helper's write into a received list is admitted by
$`\mathsf{unsealed}`$ as its inferred precondition, which `prepareRichInline`
establishes at allocation and keeps across calls whose $`\Sigma_O`$ entry is
empty; and the walkers' facts are stated on locations, not on an abstract
type.

### What each site gets

The sites and their results are the dossier's (cited:
[dossier](callback-frames-dossier.md), "Form (b)" and "Other patterns of
Paper II with shared structure"); what each gets is conjectured.

- **`walkPreparedLinesRaw`, after `onLine`**, and **`walkPreparedComplexLines`,
  after `onLine`**: the walker's precondition states
  $`\Sigma(\mathit{prepared}.p)=\mathsf{keep}`$ for the paths it reads
  (`widths`, its spine, `segmentFlags`), and the handle's facts
  (`segmentCount === prepared.widths.length` both ways, the relation of
  `segmentFlags`' and `widths`' lengths) survive the visitor's stated
  effect. Its callers establish it: `walkLineRanges` from its sealed
  `PreparedText`, `prepareRichInline` by sealing the paragraph handle before
  `findWholeLine`, which seals `flow.data`'s paths; every write to `data`
  precedes it. The cursor's facts stay lost (form (a), a later part), so
  these walkers verify with their reads restored only with that part too.
- **`walkLineRanges`**: holds no fact; its parameter at the entry's
  `PreparedText` gives the walker its precondition.
- **`walkRichInlineLineRanges`**: `flow`'s fields read by its lambda after
  each step survive the user's `onLine` ($`\mathsf{keep}`$ on every path
  they read).
- **`layoutWithLines`**: its lambda is analysed code; the handle's facts,
  `prepared.segments` included as a path of the intersected handle
  `PreparedTextWithSegments`, survive by their entries, `lines` by the
  lambda's inferred effect.
- **P18**: at pretext's sites `Prepared` is an abstract type, so its
  invariant holds after `step(c)` by (W6) and elimination, and its fields
  are $`\mathsf{keep}`$. Paper II's own program, with `Prepared` an exported
  structural type, is outside: external code may build and write one; it
  needs Paper I's rule for rigid paths.
- **P20**: with `ClassTable` an abstract type, a value read from a
  `Map<string, ClassTable>` is a sealed root and meets $`I_A`$ by (W6);
  the reviewed `Map` contract that a read returns a stored value is
  needed.
- **P15, P16**: a separate design, conjectured, at stage 4: a sealed root
  whose location is a module binding's, its paths those of the binding's
  type, sealed where the module's initialisation ends, its invariant a
  stated `@invariant` on the binding. Under it P15's array is
  $`\mathsf{keep}`$; P16's cell is $`\mathsf{init}`$, and its invariant
  `bmp === null || bmp.length === 65536` is no tolerant support of
  $`\mathsf{init}`$, so it needs single-write paths (stage 3).

## Stages and cost

1. The definition in the note and in Lean with every change, tolerant
   invariants only, view spines no paths: tags, roots, the sealed map,
   (W5), (W6), admissibility, effect denotation, Reliance. Front: `@opaque`,
   abstract types, owners and entries, casts, declared views, seal points,
   $`\Gamma_O`$ and the $`\Sigma_O`$ entries. The cases and controls above.
   Covers the example.
2. Owner-side spread, intersected handles (`PreparedTextWithSegments`,
   stating `@opaque` and `@representation PreparedSegments & { kinds }`);
   upstream's brands restored in the pretext fork with `@opaque`; the five
   handle sites measured.
3. Paths whose single write restores the invariant (P16).
4. Module bindings as sealed roots (P15, P16); the `Map` contract (P20).

Each stage states the whole definition; what a stage leaves out is an
explicit restriction, documented in SOURCE-FRAGMENT.md and enforced.

Cost (conjectured):

- Lean: the world components and (W5), (W6) touch Preservation's statement;
  3 to 5 weeks, most in item 1 and the effect denotation.
- Front: tag and seal-point inference, $`\Gamma_O`$ as a fixed point over
  the owner's functions, computed once per owner and keyed by its sources
  in the [stage store](../STAGE-STORE.md).
- The pass: one tag comparison per write and one meet per class entry on
  sealed locations; no work per call site beyond respect. Handle-taking
  functions lose their boundary invariant obligations.
- Trust: one row, two rows narrowed to types without `@opaque`.
- Sources: pretext's brands restored with `@opaque`; comments and one
  type alias.

## Decisions

Owner decisions, to be discussed again once the design is implemented:

1. **The owner's boundary is the package's `exports`.** An entry is a
   module `package.json`'s `exports` names, and the owner is the package's
   modules; for pretext the owner is every module of `src/`, with entries
   `layout.ts` and `rich-inline.ts` (cited: dossier, "What the API
   exposes"). A package without `exports` has every module as an entry, so
   its abstract types cannot span modules. What it trusts beyond the
   annotations: `package.json`'s `exports`; the mapping from each target
   (`./dist/layout.js`) to its source (`src/layout.ts`), read from the
   project's `tsconfig.json` (`rootDir` to `outDir`); and that consumers
   resolve the package through `exports`: a bundler that ignores it, or an
   import by file path, reaches `prepare.ts`'s exported `measureAnalysis`.
   These are trusted inputs, stated with the parser's.
2. **Invariants open across several writes are refused**, the *Tolerant*
   restriction, with single-write paths at stage 3. Pretext's post-return
   writes are to fields no invariant reads. Admitting an invariant the
   owner restores before it yields control needs invariants open between
   states in the step-indexed model and a closure check at every outward
   transfer.

## Later parts

- **The cursor**, P22's form (a), a `private` local the walker allocates
  and passes only to its helpers: outside this design. $`\Gamma_O`$ is per
  owner, and the stepper writes cursors, so a cursor type would get
  $`\mathsf{any}`$. The design gives that part the partition it refines:
  class entries no longer range over sealed locations.
- **Typed-array elements**: a byte class in each view spine's contract,
  fixed at allocation, which `subarray` and construction over a buffer
  join; `%ByteSet%` changing only view spines of the written view's class,
  a change to the typed-array trust row for the owner's approval; sealing
  applied to a class, a view created in a sealed class sealed at creation.
  Then view spines are paths, and facts about a sealed typed array's
  elements cross callbacks.
