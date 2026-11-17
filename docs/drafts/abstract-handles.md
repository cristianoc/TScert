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
  (`invariant-requires`, `-ensures`, `-returns`). Kept: the annotations,
  `handle-meaning` inside the owner, the identity cast. Added: the owner
  tag in the representation's contracts, the sealed set, the protocol
  $`\Gamma_O`$, and the invariant as a property of every state, (W5).
- **Contracts fixed at allocation** (cited: Paper I, Definition "World";
  [density belongs to a contract](../DESIGN.md#lasting-decisions)). A
  location's kind and contract are chosen where it is allocated and never
  change; the owner tag is one more component, as an array's presence mode
  is.
- **Support, respect and Reliance** (proved: Paper I, Definitions "Support"
  and "Respect", Proposition "Reliance"; Lean `respect_sound`,
  `rely_chain`). The frame consequence at a callback is Reliance with the
  callback's effect, under an admissibility that bounds sealed locations
  by $`\Gamma_O`$.
- **Inferred effects certified per function** (cited:
  [inferred call effects](../SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification)).
  The front proposes $`\Gamma_O`$, the tags and the seal points; Lean
  certifies each function at them.

No new judgment form and no new modality: one contract component, one
world component, one clause of well-formedness, one clause of
admissibility, one ghost command.

## The example

```ts
declare const brand: unique symbol
/** @invariant this.flags.length === this.widths.length @representation Rep */
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
analysed sources, its boundary as [open choice 1](#open-choices) fixes it.
An abstract type $`A`$ of $`O`$ is a type declared in $`O`$ stating
`@representation R_A`, with invariant $`I_A`$ (`true` where none is
stated). A path $`p`$ of $`R_A`$ is a field, the spine or the cells of an
array-typed field, or the view spine of a typed-array field, recursively
through record-typed fields.

**Owner tags.** A contract may carry an owner $`O`$:
$`W(l)=(\kappa,T,O)`$, fixed by world extension as $`\kappa`$ and $`T`$
are. A writable type tagged $`O`$ is a subtype of its untagged read-only
views (`readonly T[]`, `ArrayLike<T>`, a `readonly` field) and of no
untagged writable type, in either direction, as presence modes are. A
typed array created over the bytes of a typed array tagged $`O`$ carries
$`O`$. The front proposes each allocation's tag from the flow of its value
into a representation; Lean checks the function at it.

**The sealed set.** The world carries, for each owner $`O`$, a set
$`\Sigma_O`$ of locations, and for each abstract type $`A`$ of $`O`$ a set
$`\mathit{Sealed}_A`$ of identity locations, its sealed handles. Extension
only enlarges both. For a sealed handle $`o`$ of $`A`$ and a path $`p`$,
$`o.p(h)`$ is the set of locations path $`p`$ reaches from $`o`$ in $`h`$,
and the region $`A.p`$ is their union over $`\mathit{Sealed}_A`$; every
such location is in $`\Sigma_O`$.

**The protocol.** Each owner has an effect
$`\Gamma_O=\{A.p:\delta_{A.p}\}`$ over the paths of its abstract types. For
$`l\in\Sigma_O`$, $`\delta_l`$ is the meet of $`\delta_{A.p}`$ over the
regions $`A.p`$ holding $`l`$ in $`h`$, and $`\mathsf{keep}`$ where none
does. The changes form a chain, so the meet is the least.

**Well-formed state** gains:

- **(W5) invariants.** For every abstract type $`A`$ and every
  $`o\in\mathit{Sealed}_A`$: $`I_A(o,h)`$.

**Admissible transition** gains: every $`l\in\Sigma_O`$ with
$`l<|h|`$ satisfies $`(\delta_l)_{|h|}(h(l),h'(l))`$. A write through a
typed array changes the view spine of every typed array over the same
bytes (cited: Paper I, §"What exists: variables, locations, spines", typed arrays); the clause bounds each sealed
view spine whichever view the write went through.

**Meaning of an abstract type.** Inside its owner, `handle-meaning` holds: $`⟦A⟧=⟦R_A^O⟧`$, the representation at contracts tagged $`O`$.
At a type of a signature of an entry (a function an entry module exports,
[open choice 1](#open-choices)) and of any external function, $`A`$ means
its sealed handles:

```math
v\in⟦A⟧^{\mathrm{ext}}_W \iff v\in⟦R_A^O⟧_W \land \mathrm{id}(v)\in\mathit{Sealed}_A
```

so every value of $`A`$ that crosses the owner's boundary meets
$`I_A`$, by (W5).

**Declaration side conditions** (refused otherwise):

- *Closed.* $`\mathrm{supp}(I_A)`$ names only regions $`\mathtt{this}.p`$
  for paths $`p`$ of $`R_A`$.
- *Tolerant.* $`\Gamma_O\triangleleft\mathrm{supp}(I_A)`$ at every path:
  each change the protocol allows on a path the invariant reads is one its
  support tolerates. By Paper I's Tolerant frame theorem every admissible
  transition then keeps (W5), with no obligation at a write. **This is an
  explicit restriction**: an invariant that a write breaks and a later
  write restores (two parallel arrays shortened one after the other) is
  refused, as Paper I's limit "Broken and restored invariants" states for
  assertions; [open choice 2](#open-choices) states the alternatives. It is
  documented in SOURCE-FRAGMENT.md and enforced at the declaration.

**Sealing**, $`\mathsf{seal}_A(e)`$: a ghost command with empty effect, its
place proposed by the front at or before the first point where the value
reaches code outside the owner. Obligations: $`e`$ meets $`R_A^O`$;
$`I_A(e,h)`$; each location at a path of $`e`$ is unsealed, or already in
$`\Sigma_O`$ at a path with the same protocol entry. It adds
$`\mathrm{id}(e)`$ to $`\mathit{Sealed}_A`$ and the locations at $`e`$'s
paths to $`\Sigma_O`$, which extends the world. A write storing a value
into a sealed location at a path of $`A`$ seals that value's locations at
the continuing paths, under the same obligations.

**Sealed and unsealed facts.** $`\mathsf{sealed}_A(x)`$ is monotone: its
support is empty. $`\mathsf{unsealed}(x.p)`$ holds of a fresh allocation and
is supported by $`\{\Sigma_O:\mathsf{keep}\}`$: a call keeps it when its
summary's Boolean $`\mathsf{seals}_O`$ is false, which every call into code
that runs no seal command of $`O`$ states. Both are ordinary preconditions
and postconditions, inferred.

**Elimination**, `h as R_A` or `h as A & R_A`, only in the owner: the
identity, as `handle-meaning` gives it. Where $`\mathsf{sealed}_A(h)`$ is
known it gives $`I_A(h,h)`$, by (W5). A cast out written outside the owner
is refused.

**Writes.** A write whose target location is tagged $`O`$ is checked as one
of: the target is $`\mathsf{unsealed}`$, and the write is an ordinary one;
or the write is within $`\delta_l`$ for the target. A write through a typed
array tagged $`O`$ is checked at every view spine it changes.

**Effects.** A class entry $`(c:\delta)`$ of any effect, stated or inferred,
bounds a location of class $`c`$ outside every $`\Sigma_O`$ by $`\delta`$
and a location $`l\in\Sigma_O`$ by $`\delta\sqcap\delta_l`$. This is a
consequence of the admissibility clause, which every transition already
meets; it is no new reading of `Modifies`. So
`{ values: "any"; spines: "grow" }` bounds a sealed location by
$`\Gamma_O`$, and `{}` keeps it.

**The protocol is inferred, and closed under the owner's operations.** The
front proposes the least $`\Gamma_O`$ covering every write of the owner's
functions to a location not known unsealed, every exported function
included; Lean certifies each function within it and checks the side
conditions against it. External code changes a sealed location only by
calling the owner's functions ([trust](#trust)), so a callback's whole run,
a reentrant call of an exported writer included, is within $`\Gamma_O`$ on
sealed locations. A fact a walker holds about a sealed handle survives a
callback exactly when every exported operation's writes keep it.

## The frame consequence

Every native step and every callback has an effect bounded on
$`\Sigma_O`$ by the rigid $`\Gamma_O`$, by the admissibility clause. By
Reliance (proved: Paper I, Proposition "Reliance", `rely_chain`), a fact
whose support on sealed regions is respected by $`\Gamma_O`$, and whose
other support the call's effect respects, holds after the call.

In the example the front infers $`\Gamma=\mathsf{keep}`$ on every path:
after `prepare`'s seal no function writes a sealed location. `walk`'s
parameter is at an entry signature, so $`\mathsf{sealed}(h)`$ holds; the
facts $`i<|r.\mathit{widths}|`$ and $`|r.\mathit{flags}|=|r.\mathit{widths}|`$
cross `visit` with no annotation at the call and no change to `visit`'s
type (conjectured, the design's claim).

Reentrancy: let the module also export `truncate(h)`, popping
`r.widths` then `r.flags`. Its first pop breaks $`I`$ until its second, so
the declaration is refused (*Tolerant*). Let it instead pop only
`r.widths` with $`I`$ reading $`|r.\mathit{flags}|\ge|r.\mathit{widths}|`$:
it is admitted with $`\Gamma(\mathtt{Handle}.\mathit{widths}.\mathsf{spine})=\mathsf{any}`$,
$`I`$ survives, and $`i<|r.\mathit{widths}|`$ does not, so `walk`'s read is
refused, as Node shows it must be once `visit` calls `truncate`.

## Every place encapsulation can leak

- **A cast out, outside the owner.** In analysed code: refused, including
  through `unknown`, an intersection or a generic. In external code:
  excluded by the [trust](#trust) clause.
- **An entry returning the representation or a part of it at a writable
  type.** Refused at the return: a tagged writable type is no subtype of
  the untagged type an entry's signature states
  (`invalid-abstract-return-rep`). A fresh copy is admitted. The same
  holds of every transfer out: an argument to external code, a store into
  a location external code reaches, a throw.
- **`PreparedTextWithSegments`'s `readonly widths: ArrayLike<number>`**
  (cited: upstream `layout.ts:53–57`). A member an abstract type declares
  beside its brand is a view: checked to be a read-only supertype of the
  representation's field at its tag. External code reads the walkers' own
  array and writes it through no route. A writable declared member is
  refused (`invalid-abstract-writable-view`).
- **Spreading a handle.** In the owner: the result is a fresh record whose
  fields hold already-sealed locations; sealing it is an introduction,
  admitted where the shared paths have the same protocol entries. In
  external code: a copy, outside what the trust clause lets external code
  pass back at $`A`$.
- **Reentrant calls of exported writers.** Within $`\Gamma_O`$ by
  construction (above).
- **Typed arrays sharing bytes.** Every typed array over a tagged view's
  bytes carries the tag, so a write through any of them is checked against
  $`\Gamma_O`$; distinct view identities are no evidence of separation.
- **An untagged alias made before sealing.** Excluded by typing: the
  representation's locations are allocated at tagged contracts and no
  tagged writable value has an untagged writable type.
- **An owner alias writing after sealing.** The write rule: beyond
  $`\delta_l`$ only where $`\mathsf{unsealed}`$ holds.
- **A callback of the owner's own code capturing the representation**
  (pretext's lambdas in `layoutWithLines`, `walkRichInlineLineRanges`).
  Analysed code: its writes are certified within $`\Gamma_O`$ or on
  unsealed locations, wherever it is called from.
- **A forged handle.** `{…} as unknown as A` of no representation is
  refused (`invalid-sealed-handle-forged`); an external value
  passed at $`A`$ is by the trust clause one the owner sealed.
- **Prototype or host tampering.** $`I_A`$ reads own data fields of records
  the owner allocated, array spines and typed-array lengths: the caller
  contract, the ordinary-array assumption and fixed-length typed arrays
  (cited: [trust surface](../DESIGN.md#trust-surface), existing rows).
  A property definition, deletion, freeze or prototype change on a handle
  is a use beyond its exported type, excluded by the trust clause.

## Trust

The assumption is the existing row "Every value the initial environment
binds, native or imported, … meets its declared signature over kinded
worlds" (cited: [trust surface](../DESIGN.md#trust-surface),
owner-approved 2026-11-13): an external function's steps are admissible
and its results meet their types. Under this design "admissible" and "its
types" are the ones above, so external code honours the exported types,
the abstract and read-only ones included. The row gains one clause that
says so in words, for the owner's approval:

> … and, for each owner of the analysed sources, a step of external code
> changes a location of the owner's sealed set only by running a function
> of the owner that external code calls: external code passes at a type
> naming an abstract type only a value the owner sealed at that type, and
> through a value it holds at an abstract type or at a read-only view an
> entry's signature states, or anything reached from one, it performs no
> write, property definition or deletion, freeze, seal or
> extension prevention, and prototype change.

Two rows change with it:

- The row of sealed handles' callers reads: "A caller outside the analyzed
  sources passes, for a parameter whose type names an abstract type, a
  value its owner sealed at that type." The invariant follows from (W5).
- The row of exported preconditions loses "a sealed handle's included":
  (W5) gives a sealed handle's invariant.

The clause states no assumption that callbacks make no reentrant calls.
For analysed code each of its parts is checked; for external code it is
assumed, as every part of the row is.

**What the clause leaves out**, stated limits, each of upstream pretext:

- A handle the application froze. Upstream keeps the source lists of a
  frozen paragraph handle in a side table and writes them into an unfrozen
  one (cited: `rich-inline.ts:1141–1146`, `1173–1178`). A freeze is
  outside the clause, since the model's field write does not throw on a
  frozen target (conjectured: no model step reads frozenness).
- A JSON copy of a handle passed back. Upstream reads `segmentFlags` by
  index so that such a copy lays out the same (cited:
  `line-break.ts:26–28`). A copy is no value the owner sealed, and its
  `segmentFlags` is a plain object, no value of $`R_A`$.

## What Lean proves

1. **Preservation** (Paper I, Theorem "Preservation") for the extended
   state: (W5) and the admissibility clause, from each function's certified
   writes and the side conditions; the tolerant paths by Paper I's
   Tolerant frame theorem. With reentrancy, the induction is over the
   length of the run, every owner function's certificate assuming the
   bound of the calls it makes.
2. **Sealing** extends the world and keeps well-formedness, from its
   obligations; a typed array created over tagged bytes is tagged.
3. **Effect denotation**: the class-entry reading is sound for every
   certified summary; respect gains the disjointness of $`\Sigma_O`$ from
   the untagged classes and $`o.p\subseteq A.p`$ under
   $`\mathsf{sealed}_A(o)`$; rebasing, `seq_eff` and `fresh_eff` keep their
   statements.
4. **Reliance**: the union of the protocols is rigid and bounds every
   admissible transition.
5. `SourceClaimJson.PassUnit.mode8Accepted_sound` keeps its statement;
   `PassUnitSafe`'s entry condition reads the extended well-formedness, and
   its premise and conclusion are reviewed again, as a change of the
   accepted plan type requires.

The note gains the tag, the sealed set, (W5), the clause of admissibility,
the seal command and the two facts; the Lean states the same definitions.

## What acceptance reads

The fragment carries each abstract type's declaration ($`R_A`$, $`I_A`$,
its declared views), the owner and its entries, the proposed
$`\Gamma_O`$, the tags at allocations and signatures, the seal points and
each summary's $`\mathsf{seals}_O`$. `FunctionPlan.certify` checks each
function at them; the module-interface check (`--module-interface`)
checks the side conditions and that every module of the owner reads the
same $`\Gamma_O`$. Every proposal is untrusted: a wrong tag, a missing
seal, a too-small $`\Gamma_O`$ fails a function's check.

## Controls and Node-run negatives

Controls (forged fragment or forced proposal), each refused:
$`\Gamma_O`$ forced smaller than a writer needs; a tag dropped at an
allocation; a seal point removed; $`\mathsf{seals}_O`$ forced false on a
sealing callee; a declared member forged writable; $`I_A`$ forged to read
an untagged path; an entry forged as a non-entry.

Negative cases, each run under Node to a read of `undefined` or a
`TypeError`:

- `invalid-abstract-return-rep`: an entry returns `widths`, the caller pops
  it, `walk` reads past `flags`.
- `invalid-abstract-write-after-seal`: the builder keeps `widths` and
  pushes after the seal.
- `invalid-abstract-callee-seals`: a callee seals and stores; the caller
  pushes.
- `invalid-abstract-reentrant-writer`: the visitor calls an exported
  `truncate`; refused at `walk`'s read.
- `invalid-abstract-open-invariant`: a writer breaks $`I_A`$ and restores
  it at a second write; refused at the declaration.
- `invalid-abstract-view-alias`: the owner keeps a `subarray` of a sealed
  view and an exported function writes through it.
- `invalid-abstract-writable-view`: a declared member `widths: number[]`.
- Existing: `invalid-sealed-handle-forged`, `-builder`, `-resize`,
  `-invariant-cast`.

Positive: the example above; `bounds-pattern-unreachable-handle-refused`
with its handle sealed; `blocker-pretext-opaque-handle-cast` once it states
`@representation`.

## Pretext

### Writes to a handle after its preparation

**Pretext writes handle fields after preparation, at one function**
(cited, a search of upstream `src/` for writes to the fields of
`PreparedLineBreakData`, `PreparedSegments` and
`InternalPreparedRichInline`, and for element and spine writes in
`line-break.ts`, `line-text.ts` and `layout.ts`):

- `materializeRichInlineLineRange` (`rich-inline.ts:1192`, exported) calls
  `findSegmentSources` (`:1199`) where `sourceStarts` is `null`, which writes
  `flow.sourceStarts`, `flow.sourceEnds` and `flow.sourceUnits` of an
  unfrozen paragraph handle (`:1176–1178`), each from `null` (one-text
  paragraphs, `:220–221`) to a fresh array.
- No other function writes a handle's field, array or typed array once the
  handle is returned: `line-break.ts` writes only the cursor's and
  `stats`' fields (`:268–280`, `:312–315`, `:403–404`, `:583–584`, `:1064–1065`, `:1081–1082`, `:1127`, `:1155–1163`);
  `line-text.ts` writes its `WeakMap` side table and fresh `Int32Array`s
  (`:14–28`); `layout.ts` writes `prepared.kinds` before
  `prepareWithSegments` returns (`:150`).

So $`\Gamma`$ is $`\mathsf{keep}`$ on every path of `PreparedText` and
`PreparedTextWithSegments`, and on every path of `PreparedRichInline` but
those three fields, where it is $`\mathsf{init}`$ (conjectured: $`\mathsf{init}`$
needs the fact that the three are `null` together, `:1199`; without it the
front proposes $`\mathsf{any}`$ on them). No walker reads those fields, so
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
  `measureAnalysis` casts at `prepare.ts:637` and writes `prepared.segments`
  at `:638`; `prepareWithSegments` writes `prepared.kinds`
  (`layout.ts:150`); `findWholeLine` writes the paragraph handle's
  `wholeWidth`, `wholeStart`, `wholeEnd` (`rich-inline.ts:819–823`) after
  its cast (`:218–221`, `:663`).
- The paragraph handle's `segmentFlags` is `flags.subarray(0, segmentCount)`
  (`rich-inline.ts:581`), a view over the bytes of the list
  `measureAnalysis` filled, written again at `:587`.
- `measureAnalysis`'s result is both a text handle and a paragraph
  handle's `data` (`rich-inline.ts:214–221`), so one allocation lies under
  two abstract types of one owner.

These fix three parts of the definition: the tag is the owner, not the
abstract type (one allocation, two types); sealing is a command at the
owner's boundary, not the cast (every write above precedes the return to
the application, none follows a seal placed there); and a helper's write
into a received list is admitted by $`\mathsf{unsealed}`$ as its inferred
precondition, which `prepareRichInline` establishes at allocation and
keeps across calls whose $`\mathsf{seals}`$ is false.

### What each site gets

The sites and their results are the dossier's (cited:
[dossier](callback-frames-dossier.md), "Form (b)" and "Other patterns of
Paper II with shared structure"); what each gets is conjectured.

- **`walkPreparedLinesRaw`, after `onLine`**, and **`walkPreparedComplexLines`,
  after `onLine`**: the handle's facts (`segmentCount === prepared.widths.length`
  both ways, the relation of `segmentFlags`' and `widths`' lengths) survive
  the visitor's stated effect, under $`\Gamma=\mathsf{keep}`$, where the
  walker's precondition states $`\mathsf{sealed}(\mathit{prepared})`$.
  `findWholeLine` seals `flow.data` before its call, every write to `data`
  preceding it. The cursor's facts stay lost (form (a), a later part), so
  these walkers verify with their reads restored only with that part too.
- **`walkLineRanges`**: holds no fact; its parameter at the entry's
  `PreparedText` gives the walker $`\mathsf{sealed}`$.
- **`walkRichInlineLineRanges`**: `flow`'s fields read by its lambda after
  each step survive the user's `onLine` (keep on every path they read).
- **`layoutWithLines`**: its lambda is analysed code; the handle's facts
  survive by $`\Gamma`$, `lines` by the lambda's inferred effect.
- **P18**: at pretext's sites `Prepared` is an abstract type, so its
  invariant holds after `step(c)` by (W5) and elimination, and its fields
  are $`\mathsf{keep}`$. Paper II's own program, with `Prepared` an exported
  structural type, is outside: external code may build and write one; it
  needs Paper I's rule for rigid paths.
- **P20**: with `ClassTable` an abstract type, a value read from a
  `Map<string, ClassTable>` is a sealed handle and meets $`I_A`$ by (W5);
  the reviewed `Map` contract that a read returns a stored value is
  needed.
- **P15, P16**: the same definition with a module binding as the owner's
  state: a binding no entry exposes at a writable type, tagged with its
  owner, sealed when initialisation ends, its invariant a stated
  `@invariant` on the binding. P15's array is $`\mathsf{keep}`$; P16's cell
  is $`\mathsf{init}`$ and its invariant `bmp === null || bmp.length === 65536`
  is no tolerant support of $`\mathsf{init}`$, so it waits for the stage of
  single-write paths.

## Stages and cost

1. The definition in the note and in Lean with every change, tolerant
   invariants only: tags, sealing, (W5), admissibility, effect denotation,
   Reliance. Front: abstract types, owners and entries, casts, declared
   views, seal points, $`\Gamma_O`$ and $`\mathsf{seals}_O`$. The cases and
   controls above. Covers the example.
2. Owner-side spread, intersected handles (`PreparedTextWithSegments`),
   typed arrays over shared bytes; upstream's brands restored in the
   pretext fork; the five handle sites measured.
3. Paths whose single write restores the invariant (P16).
4. Module state as owner state (P15, P16); the `Map` contract (P20).

Each stage states the whole definition; what a stage leaves out is an
explicit restriction, documented in SOURCE-FRAGMENT.md and enforced.

Cost (conjectured):

- Lean: the world component and (W5) touch Preservation's statement; 3 to
  5 weeks, most in item 1 and the effect denotation.
- Front: tag and seal-point inference, $`\Gamma_O`$ as a fixed point over
  the owner's functions, computed once per owner and keyed by its sources
  in the [stage store](../STAGE-STORE.md).
- The pass: one tag comparison per write and one meet per class entry on
  sealed regions; no work per call site beyond respect. Handle-taking
  functions lose their boundary invariant obligations.
- Trust: one clause, one row reworded, one phrase deleted.
- Sources: pretext's brands restored; comments only.

## Open choices

1. **The owner's boundary.** (a) The package's `exports`: an entry is a
   module `package.json`'s `exports` names, every module where it names
   none, and the owner is the package's modules. (b) A declared group of
   modules, a new annotation. **Recommendation: (a).** It is the boundary
   the package already states, and Node resolves imports of the package's
   name through it; it needs no annotation, and for pretext it gives the
   owner every module of `src/` with entries `layout.ts` and
   `rich-inline.ts` (cited: dossier, "What the API exposes"). It makes
   `package.json` an input acceptance reads, stated as a trusted input with
   the parser's.
2. **Invariants open across several writes.** (a) Refused, the *Tolerant*
   restriction above, with single-write paths at stage 3. (b) Admitted when
   the owner restores every broken invariant before it yields control:
   before a return, a throw out of the owner, and any call of code that can
   observe or reenter it. **Recommendation: (a).** Pretext needs none of
   it: its post-preparation writes are $`\mathsf{init}`$ on fields no
   invariant needs to read. (b) needs an invariant that is open between
   states in the step-indexed model and a closure check at every outward
   transfer; it is designed when a program needs it.

## Later parts

- **The cursor**, P22's form (a), a `private` local the walker allocates
  and passes only to its helpers: outside this design. $`\Gamma_O`$ is per
  owner, and the stepper writes cursors, so a cursor type would get
  $`\mathsf{any}`$. The design gives that part the partition it refines:
  class entries no longer range over sealed locations.
