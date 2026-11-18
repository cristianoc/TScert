# Draft: read-only handles

A design for pattern P22 of
[Tolerant frames II](tolerant-frames-2-note/note.tex) in which pretext's
handles stay upstream's plain records behind their opaque types. In place
of private fields it rests on one trust row, stated in the API: code
outside the analyzed sources changes nothing reachable from a value that
crosses the API at a read-only type. A fact an analyzed function holds about
such storage, or about storage no outside code can reach, survives a call of
code of unknown effect, a user's callback included, bounded by what the
analyzed sources' exported functions may change. It answers P22 at its
handle sites (form (b) of the [dossier](callback-frames-dossier.md)) and at
its cursor sites (form (a)), and states what it gives P15, P16, P18 and
P20. It is a variant of [private representation](private-representation.md),
whose rule, protocol and checks it restates for another region; the
[comparison](#against-private-representation) states what each costs.

Base: TScert `single-pass` at `b60eca2f`; upstream pretext is
chenglou/pretext at `0d102a5c`, its files under `src/`; "Paper I" is
[Tolerant frames](tolerant-frames-note/note.tex). Claims are labelled
**proved** (with the Lean name), **cited** (a document with its scope, or a
source file and line at the stated commit), **observed** (a program run
under Node 26.13.0), **measured** (with the setup stated) or
**conjectured**. Everything this draft defines is conjectured until the
Lean of [what must be proved](#what-must-be-proved) exists.

## The existing mechanism this extends

[The general mechanisms](../DESIGN.md#general-mechanisms) give a fact a
construct relies on while other code runs to
[footprints](../FOOTPRINTS.md) (cited): the fact, its stable operations
stated as closed footprints, Lean certifying the code within them, and the
construct's rule. This design is that mechanism, its four parts read at the
analyzed sources $`A`$:

1. **The fact**: a handle type's invariant, and any fact whose support lies
   in the region $`R_A`$ below: storage outside code reaches only at a
   read-only type, or not at all.
2. **The stable operations**: the code of $`A`$ that outside code can call,
   its *members*; their joint footprint on $`R_A`$ is the protocol
   $`\Psi_A`$, a closed footprint.
3. **The checked contract**: Lean certifies each member within
   $`\Psi_A`$, as it certifies every function at its inferred effect
   (cited:
   [inferred call effects](../SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification)).
4. **The construct's rule**: Read-only frame, below, Private frame of
   private representation at another region. With it, Paper I's Theorem
   "Tolerant frame" and Proposition "Reliance" carry a fact across every run
   of code that is not $`A`$'s (proved: Paper I, Lean `frame_box`,
   `rely_chain`).

It reads four existing pieces:

- **The boundary of the trust surface** (cited:
  [trust surface](../DESIGN.md#trust-surface), the rows on exported
  preconditions and on a callback's stated effect). Both rows state what
  "a caller outside the analyzed sources" does; this design states one more
  such row, at the same boundary. No `package.json` exports and no owner
  tags take part.
- **Sealed handles** (cited:
  [type invariants](../ARITHMETIC.md#type-invariants), "Sealed handles";
  [a handle means its representation](../PROGRAM-TYPING.md#a-handle-means-its-representation)).
  An opaque type stating `@invariant` and `@representation T` means `T`, so
  a cast to its representation inside $`A`$ holds of every value of the
  type, and its invariant is a contract of function boundaries
  (`invariant-requires`, `-ensures`, `-returns`).
- **Exported preconditions** (cited: the trust row on exported
  preconditions). A caller outside $`A`$ passes a value meeting the
  invariant of each type the parameter's type names, a sealed handle's
  included.
- **Private representation's checks** (cited:
  [private representation](private-representation.md), "The class shape
  the rule requires"): reference-preserving protocol, tolerant invariant,
  incoming values, owning marks, confined collections, the exposed ghost
  set, throw edges, read-only types and views. Each is restated below for
  $`R_A`$.

New machinery: one region, one protocol for the analyzed sources, one
rule, one mark per allocation site, one confinement check and one trust row.
No new judgment form, no new modality, and no world component but the
ghost set $`E_A`$ of the roots that crossed the boundary.

## The example

```ts
declare const brand: unique symbol
/** Callers must not change anything reachable from a Handle.
 *  @invariant this.flags.length === this.widths.length
 *  @representation Rep */
export type Handle = { readonly [brand]: true }
type Rep = { widths: number[]; flags: Uint8Array }

export function prepare(n: number): Handle {
  return { widths: new Array<number>(n).fill(1), flags: new Uint8Array(n) } satisfies Rep as unknown as Handle
}

export function walk(h: Handle, visit: () => void): number[] {
  const r = h as unknown as Rep
  const w = r.widths, n = w.length, out: number[] = []
  for (let i = 0; i < n; i++) { visit(); out.push(w[i]!) }
  return out
}
```

`visit` is external code and may hold `h`, call `prepare` and `walk`. The
read `w[i]!` needs $`i<|w|`$ after `visit`. Under Node (observed), a visitor
calling both leaves the walker reading `[1, 1, 1]`.

## The rule

Paper I's notation throughout: a heap $`h`$, an environment $`\rho`$, the
action $`h\xrightarrow{\Phi}_\rho h'`$ of an effect, changes
$`\mathsf{keep}\sqsubseteq\mathsf{init}\sqsubseteq\mathsf{scalar}\sqsubseteq\mathsf{grow}\sqsubseteq\mathsf{any}`$
(Paper I, §3, the changes' definition), regions read at the entry heap,
$`\Phi\triangleleft_K S`$ for respect and $`\Box_\Phi F`$ for the modality.

### Definitions

**Code that is not $`A`$'s.** A step runs code that is not $`A`$'s when it
is a call whose callee is neither a function of $`A`$ nor an audited
native, an `await`, or a `yield`.

**Members.** The members $`M_A`$ are the functions of $`A`$ that code that
is not $`A`$'s can reach: every function a module of $`A`$ exports, every
method of a class a module exports, and every function of $`A`$ used as a
value given to such code (a result, an argument of a call of code that is
not $`A`$'s, a value thrown or yielded, the content of storage such code
reaches). Outside code may import any module of $`A`$, so every export of
every module counts, an export between modules of $`A`$ included.

**Read-only types and crossings.** A type is *read-only* as private
representation defines it ("Read-only types and views"): after expanding
every alias, every position of storage it reaches is read-only, no typed
array, no `any`, no type parameter; an opaque type
`{ readonly [brand]: true }` is read-only, since it states no member but its
brand. A value *crosses* the boundary when it passes between $`A`$ and code
that is not $`A`$'s, in either direction: a member's result, argument or
receiver, an argument or result of a call of code that is not $`A`$'s, a
value thrown, caught or yielded, the content of storage both sides reach. A
crossing is at the type of its position; a position of a crossing type is
*read-only* or *writable*.

**Exposure, a mark per allocation site.** Each allocation site of $`A`$
carries one of three marks, a component of the allocated location's
contract fixed at allocation, as private representation's owning mark is:

- *hidden*: its storage crosses at no position;
- *exposed*: its storage may cross at read-only positions only;
- *released*: its storage may cross at a writable position.

The front proposes each site's mark, and the pass checks every crossing:
storage reachable from a crossing value through a read-only position is
from an exposed site, or was allocated outside $`A`$; through a writable
position, from a released site, or allocated outside $`A`$. A forged mark
fails a crossing's check (conjectured).

**The exposed roots.** $`E_A`$ is a ghost component of the state: the set
of locations of storage that has crossed at a read-only position,
whoever allocated it. It only grows.

**The region.** $`R_A(\rho,h)`$ is the storage of $`h`$ allocated by $`A`$
at a hidden or exposed site, together with the storage reachable in $`h`$
from $`E_A`$ through fields, spines and element cells, stopping at
collections, whose entries the model holds in no location (cited:
[native footprints](../SOURCE-CONTRACTS.md#native-footprints), the row of
`Set` and `Map`). Storage from a released site, and storage outside code
allocated and never passed at a read-only position, is outside $`R_A`$.
Its parts are one per allocation site of $`A`$ and kind, and one per kind
for storage outside code allocated: $`R_s.\mathsf{spines}`$,
$`R_s.\mathsf{cells}`$, $`R_s.\mathsf{fields}`$ for a site $`s`$, and
$`R_{\mathrm{in}}.\mathsf{spines}`$, $`R_{\mathrm{in}}.\mathsf{cells}`$,
$`R_{\mathrm{in}}.\mathsf{fields}`$.

**Possible sites.** The body's flow propagates, for each reference, the set
of sites it may come from. A value received in a crossing may come from
every exposed site and from $`\mathrm{in}`$, whatever its type: TypeScript
admits a read-only view where a writable type is expected (cited: private
representation, "Incoming values", observed under `tsc` 7.0.2). A value
from a confined collection may come from the sites inserted into it.

**The protocol.** $`\Psi_A`$ has one entry per part of $`R_A`$. It is the
least such effect for which every member $`m\in M_A`$, checked with each of
its steps that run code that is not $`A`$'s bounded on $`R_A`$ by
$`\Psi_A`$, has normal and exceptional effects that, after `fresh_eff`
drops the locations it allocated, bound every location of $`R_A`$ of its
entry heap by $`\Psi_A`$. A write a member makes is charged to the parts of
every site the written object may come from. A member that writes only what
it allocated contributes $`\mathsf{keep}`$; a hidden site no member reaches
gets $`\mathsf{keep}`$.

**The bound on $`R_A`$.** $`\Phi\oplus_A\Psi_A`$ bounds the locations of
$`R_A`$ by $`\Psi_A`$ and every other location by $`\Phi`$:

```math
h\xrightarrow{\Phi\oplus_A\Psi_A}_\rho h'\iff h\xrightarrow{}_\rho h'\ \wedge\ \forall l<|h|.\ h'(l)=h(l)\ \vee\ \exists (r:\delta)\in(\text{if } l\in R_A(\rho,h) \text{ then } \Psi_A \text{ else } \Phi).\ l\in r(\rho,h)\wedge\delta_{|h|}(h(l),h'(l))
```

**A handle's invariant.** $`I_H(o,h)`$ is the `@invariant` of a sealed
handle type $`H`$, with `this` read as $`o`$ through its representation;
$`\mathrm{supp}(I_H)`$ is its support.

### Read-only frame

```math
\frac{c:\Phi\mid\Phi^{e}\qquad c\ \text{runs code that is not}\ A\text{'s}}
     {c:\ \Phi\oplus_A\Psi_A\ \mid\ \Phi^{e}\oplus_A\Psi_A}\ \textsf{(Read-only frame)}
```

An unknown callback, of effect $`\top`$, has by the rule the effect
$`\Psi_A`$ on $`R_A`$. A call naming a function of $`A`$ is checked at that
function's certified effect; an audited native keeps its audited effect,
and each call of a callback it makes is bounded by the rule.

**At a callback.** Let a walker hold $`F`$ with a support $`S`$ inside
$`R_A`$ and $`\Psi_A\triangleleft_K S`$. Tolerant frame gives
$`K\wedge F\vdash\Box_{\Phi\oplus_A\Psi_A}F`$, and Reliance carries $`F`$
across every step that runs code that is not $`A`$'s, given rigidity
((L3)). In the example `prepare` writes only what it allocates and `walk`
nothing, so every entry of $`\Psi`$ is $`\mathsf{keep}`$, and $`i<|w|`$
crosses `visit` (conjectured, the design's claim).

**At a handle's entry.** A parameter of a sealed handle type meets its
invariant: from an analyzed caller by `invariant-ensures` at the call's
source, from an outside caller by the row on exported preconditions. A cast
to the representation gives the representation's fields (handle-meaning).
The handle's storage is in $`R_A`$ from entry: it crossed at the read-only
handle type, so its root is in $`E_A`$, or it was allocated by $`A`$ at an
exposed site.

### What must be proved

The rule rests on two invariants of states and four lemmas. Each is
conjectured until its Lean exists.

- **(P2) Confinement.** Every path from a frame of code that is not $`A`$'s
  to a location of $`R_A`$ allocated by $`A`$ enters $`R_A`$ at a location
  reachable from $`E_A`$ through read-only positions. Paths run through
  fields, cells, spines and element cells; a closure's environment is not
  reachable from a holder of the closure. Conjectured, from the
  [confinement check](#the-checks-the-rule-requires) and the crossing
  checks of the marks.
- **(M) Marks.** Every location's mark is the mark of its allocation site,
  fixed at allocation; a location of a hidden site is reachable from no frame
  of code that is not $`A`$'s.
- **(L1) Outside step.** From a state meeting (P2) and (M), a step of code
  that is not $`A`$'s leaves every location of $`R_A`$ unchanged and keeps
  (P2) and (M). A location of a hidden site is out of its reach; a location
  reachable from $`E_A`$ it reaches only through a read-only crossing, and
  the [trust row](#trust) states it changes none. (L1) is conjectured from
  that row, which is trust: it holds of outside code that meets the row, and
  of no other.
- **(L2) Outside run.** A run of code that is not $`A`$'s from $`h`$ changes
  each location of $`R_A(h)`$ within $`\Psi_A`$. By induction on the budget
  $`k`$: the run changes $`R_A`$ only inside calls of members, each bounded
  by its certificate at $`\Psi_A`$, whose own steps that run code that is
  not $`A`$'s are bounded by the rule at a smaller budget.
- **(L3) Rigidity.** For every pair
  $`h\xrightarrow{\Phi\oplus_A\Psi_A}_\rho h'`$ of the action,
  $`R_A(h)\subseteq R_A(h')`$: the part by marks is fixed at allocation;
  the part reachable from $`E_A`$ is kept because $`E_A`$ only grows and
  $`\Psi_A`$ preserves the references (*Reference-preserving protocol*),
  every reference held in $`R_A(h)`$ held in $`R_A(h')`$ and every listed
  cell listed, by induction on the length of the path. Then
  $`\Phi\oplus_A\Psi_A`$ is rigid when $`\Phi`$ and $`\Psi_A`$ are rigid and
  $`\Psi_A\sqsubseteq\Phi`$, as for $`\Phi=\top`$ and for
  `{ values: "any"; spines: "grow" }`.
- **(L4) The handle invariant across a run.** A fact $`I_H(o)`$ that holds
  at a member's entry is kept by every member write to $`\mathrm{supp}(I_H)`$
  (*Tolerant invariant*) and by every outside step (L1); so it holds after
  every step that runs code that is not $`A`$'s, of the handles the walker
  holds. It holds at entry by the row on exported preconditions, which is
  trust, for a handle an outside caller passes.

`SourceClaimJson.PassUnit.mode8Accepted_sound` keeps its statement; the
premise and conclusion of `PassUnitSafe` are reviewed again, as a change of
the accepted plan type requires.

## The checks the rule requires

Each is chosen by the behaviour it excludes, documented in
SOURCE-FRAGMENT.md, enforced at the source boundary, and has a control
([negatives and controls](#negatives-and-controls)). Each is private
representation's check, restated at $`R_A`$.

- **Reference-preserving protocol.** Every entry of $`\Psi_A`$ preserves
  the references: in each pair of its action, every reference to storage
  held at a location of $`R_A`$ of the entry heap is held at a location of
  $`R_A`$ of the exit heap, and every cell a spine or view spine of $`R_A`$
  lists stays listed. The entries that meet it are those private
  representation names: $`\mathsf{keep}`$; $`\mathsf{scalar}`$ on a cell or
  a field; an extension on a spine. Its reason is (L3); a `pop` of storage
  in $`R_A`$ by a member is refused (WORK, "Shrinking owned arrays").
- **Tolerant invariant.** Every change a member makes to a location of
  $`\mathrm{supp}(I_H)`$ of a handle it did not allocate in the call, and
  every entry of $`\Psi_A`$ on such a location, is one $`\mathrm{supp}(I_H)`$
  tolerates, or one write checked to keep $`I_H`$. An invariant that one
  write breaks and a later write restores is refused.
- **Confinement.** No storage of a hidden or exposed site, and no storage
  reachable from $`E_A`$, crosses at a writable position: a return, an
  argument of a call of code that is not $`A`$'s, a `throw`, a `yield` or
  an `await`, a store into storage outside code reaches, each at a type
  whose position for that storage is writable, is refused. A copy is
  storage of a fresh site; a copy (`slice`, `Array.from`, a typed array
  built from it) separates only when its element type holds no storage.
- **Incoming values.** Every write $`A`$ makes to a value received in a
  crossing, or to anything reached from it, is charged to every exposed
  site and to $`R_{\mathrm{in}}`$, whatever the value's type, and meets
  *Reference-preserving protocol* and *Tolerant invariant*.
- **Confined collections.** A collection held only by a binding of $`A`$
  that no module exports, and never crossing, is *confined*; one that is not
  confined holds no storage of $`R_A`$. Insertion into a confined
  collection is a write of $`A`$, checked as a store into $`R_A`$, and
  preserves each value's possible sites; a lookup yields the sites inserted.
  The argument needs no location for a collection's entries: no outside code
  reaches a confined collection, and every write $`A`$ makes to storage from
  it is charged.
- **Writes to possibly frozen storage.** The row admits freezing, sealing
  and preventing extension. A write by $`A`$ to a location of $`R_A`$ that
  outside code may have frozen throws in strict code, which safety admits;
  every such write, a spine extension included, has a throw edge leaving the
  heap unchanged, its handler checked from that heap, and the native audit
  checks that freezing changes no location of the model (conjectured).
- **Views in analyzed code.** Analyzed code outside the exported functions'
  callers is checked, not trusted: a value read at a read-only type is read
  at a readonly view, and the pass refuses a write through it, a write
  through a writable type it was widened to included (cited: private
  representation, "Views in analyzed code").

## Trust

One new row of the [trust surface](../DESIGN.md#trust-surface), an
assumption about code outside the analyzed sources, of the kind of the rows
on exported preconditions and on a callback's stated effect (a stand-in
until applications are analyzed too):

> Code outside the analyzed sources, a function it passes in included,
> changes by its own steps, by any operation, a native's included, no
> element, field or length of storage reachable from a value that crosses
> the API at a read-only type, whoever allocated it, the hidden fields of a
> handle's representation included. A change made inside a call of an
> exported function of the analyzed sources is that function's, bounded by
> its certificate. Freezing, sealing and preventing extension change no
> element, field or length, and are admitted.

Where it is stated: in the API, in the doc comment of each read-only type
the analyzed sources export (each handle type and each read-only member a
handle shows), as "Callers must not change anything reachable from it".
TypeScript does not establish it: its `readonly` constrains only the written
type, a read-only view is admitted where `{ length: number }` is expected
and a cast removes it (cited: private representation, "Trust", observed
under `tsc` 7.0.2).

Rows used unchanged: exported preconditions, for a handle's invariant at an
entry; a callback's stated effect; ordinary arrays; fixed-length typed
arrays.

**Copies passed back.** A structural copy of a handle is a value outside
code allocated, passed at the handle's type:

- A `structuredClone()` or `postMessage()` copy, and a handle kept in
  IndexedDB, which stores structured clones, keep the representation's
  types: arrays stay arrays and a `Uint8Array` a `Uint8Array` (observed).
  The row on exported preconditions gives its invariant, and the row above
  covers it once it crosses at the handle's type. Covered.
- A JSON copy turns each typed array into a record of numeric keys with no
  `length` (observed). It is no value of the representation type, so the
  row on exported preconditions excludes it, and acceptance says nothing of
  a program passing it. Upstream lays such a copy out as the handle, by
  reading `segmentFlags` by index (cited: `line-break.ts:26–28`; upstream
  `RESEARCH.md`, Decisions Log, 2026-09-24, line 5553). To be checked: a
  representation type a JSON copy meets, or a check at entry.
- A `Proxy` of a handle runs its traps at the walker's reads (observed:
  one trap call per field read), code that is not $`A`$'s inside a step the
  model reads as a field read. The model has no proxy. To be checked: the
  row on exported preconditions read as excluding proxies, or a model of
  them.

A frozen handle, or one a store froze deep, lays out as before, and a write
to it throws in strict code (observed); upstream's side table for frozen
paragraph handles (`rich-inline.ts:1141–1178`) stays, analyzed as written.

## Pretext

### What changes in upstream's source

Checked against upstream `0d102a5c`; each item is cited or observed, what
it gives is conjectured.

- **The opaque types** stay: `PreparedText` and `PreparedRichInline` are
  `{ readonly [brand]: true }` (`layout.ts:44–46`, `rich-inline.ts:81–83`),
  and `PreparedTextWithSegments` is `PreparedText & { readonly segments;
  readonly kinds; readonly widths: ArrayLike<number> }` (`layout.ts:53–57`),
  each read-only. Their doc comments gain the row's sentence and the
  sealed-handle annotations `@invariant` and `@representation`, naming
  `InternalPreparedText`, `InternalPreparedTextWithSegments` and
  `InternalPreparedRichInline` (`layout.ts:63–64`, `rich-inline.ts:136`).
  Comments only.
- **The internal casts** stay: `getInternalPrepared` (`layout.ts:154–156`),
  `getInternalPreparedRichInline` (`rich-inline.ts:182–184`), and the casts
  at `layout.ts:140`, `:146`, `:185`, `:316`, `rich-inline.ts:215`, `:221`,
  `:664`. Each is a cast between a sealed handle and its representation,
  read by `handle-meaning`; the cases standing for them today,
  `blocker-pretext-opaque-handle-cast`, are refused for want of the
  annotations (cited: WORK.md, the census row).
- **`measureAnalysis`'s result type** (`prepare.ts:366`) names `PreparedText`,
  and in paragraph mode its result shares the paragraph's lists while they
  are still being filled (`prepare.ts:379–383`, `rich-inline.ts:479`), so
  it does not meet the handle's invariant there (cited: private
  representation, "Preparation"). The change: its result type names the
  representation records alone, and the cast at `prepare.ts:638` is to the
  record; `prepare` and `prepareWithSegments` cast to the handle where they
  return (`layout.ts:140`, `:146`). Two annotations.
- **`layout.ts:150`**, `prepared.kinds = kinds`, writes the record
  `prepareWithSegments` allocated in the same call, before it returns: a
  write to fresh storage, which `fresh_eff` drops. No change. The same holds
  of `prepare.ts:639`, `rich-inline.ts:639` and `findWholeLine`'s writes
  (`:819–823`), called at `:221` and `:664` before the handle is returned.
- **Writes after a handle is given out**: only
  `materializeRichInlineLineRange`, an exported function, through
  `findSegmentSources`, which writes `flow.sourceStarts`, `sourceEnds` and
  `sourceUnits` of an unfrozen paragraph handle (`rich-inline.ts:1176–1178`)
  after testing `sourceStarts === null` (`:1198–1199`), each from `null` to
  a fresh array (observed: a search of the five modules for writes to the
  fields of a handle, its arrays and its typed arrays). Its invariant is
  `sourceStarts` `null`, or the three lists each as long as the segments.
  Written in upstream's order, the first write breaks it until the third,
  which *Tolerant invariant* refuses. The change: write `sourceStarts` last,
  so that each write keeps the invariant, the last as a checked single write.
  One line moved.
- **The frozen side table** (`rich-inline.ts:1141–1178`) stays: the
  `Object.isFrozen` test, a `WeakMap` no module exports (a confined
  collection) holding the fresh lists, and the writes in the other branch.
  `Object.isFrozen` needs an audited contract; nothing runs between the test
  and the writes. `line-text.ts:11`'s `WeakMap` of grapheme ends is a
  confined collection holding fresh `Int32Array`s.
- **The measurement caches**, under `measurement.ts`'s binding
  `measureState` (`:405`), no module exporting it, are confined collections
  as private representation states ("The measurement caches"): handles
  share the cached advances lists, preparation copies a list before changing
  it (`prepare.ts:533–541`), the insertions store fresh values, and
  `clearCache` (`layout.ts:360–363`) is $`\mathsf{keep}`$ on $`R_A`$. The
  exported `noExtraSpacings` (`measurement.ts:661`), at `number[]`, is
  storage of a released site; no handle holds it and no walker keeps a fact
  about it.
- **The cursor**: the walkers' `LayoutCursor` records stay. A cursor a
  walker allocates (`line-break.ts:293`, `:396`, and in `countSteppedLines`,
  `layoutNextLine` and `layoutNextLineRange`) is of a hidden site: it is
  passed only to functions of $`A`$ by name. The steppers and
  `normalizePreparedLineStart` are exported from `line-break.ts`, so
  members, and write the cursor they are given; called from outside, that
  cursor is an incoming value, charged to exposed sites and
  $`R_{\mathrm{in}}`$, never to the walker's hidden site. So the walker's
  cursor facts cross `onLine` (observed: a visitor that calls the exported
  stepper on cursors it holds leaves the walker reading `[1, 1, 1]`). The
  public `LayoutCursor` a caller passes is validated on entry as upstream
  does.

In all: comments and annotations on the three handle types, one result type
and one cast in `prepare.ts`, and one line moved in `rich-inline.ts`.

The protocol for pretext (conjectured): $`\mathsf{scalar}`$ on the fields of
the paragraph handle's site from `materializeRichInlineLineRange`, and on
the fields of exposed sites and $`R_{\mathrm{in}}`$ from the exported
steppers' writes to the cursors they are given; $`\mathsf{keep}`$ on every
spine and cell, and on every hidden site. It preserves the references.

### What each site gets

The sites are the dossier's (cited: [dossier](callback-frames-dossier.md),
§2, §4); what each gets is conjectured.

- **P22, form (b)**: `walkPreparedLinesRaw` and `walkPreparedComplexLines`
  after `onLine`: the handle's facts come from its invariant at entry and
  survive by Read-only frame, every spine and cell of the handle's sites at
  $`\mathsf{keep}`$. A fact about a scalar field of a handle read again
  after `onLine` does not survive, the fields of exposed sites being at
  $`\mathsf{scalar}`$; the walkers read those fields into locals before the
  loop (cited: `line-break.ts:472–483`). `walkLineRanges` holds no fact;
  `walkRichInlineLineRanges` and `layoutWithLines` as in private
  representation.
- **P22, form (a)**: the six cursor sites, by the hidden mark of the
  walker's cursor.
- **P18**: at pretext's sites, the handle's invariant at entry and its
  support kept by (L4). Paper II's own program, whose `Prepared` is a
  structural type external code may build and write, is outside: it is no
  read-only type.
- **P20**: a value of a sealed handle type read from a `Map` meets its
  invariant only where the `Map` holds what was stored; with the `Map` a
  confined collection, every insertion is checked, which gives it; a `Map`
  that is not confined gives nothing.
- **P15**: a module constant array that no module exports and that crosses
  at no writable position is of a hidden or exposed site, and
  $`\mathsf{keep}`$ on its spine keeps its length.
- **P16**: a module cell initialized at first use, its one write checked to
  keep `bmp === null || bmp.length === 65536`, as the lazy lists'.

### Performance

The source keeps upstream's code but for the changes above, none of which
runs at a walker's step, so no regression is expected (conjectured). The
measurement this needs: upstream against the changed source on the setup
of private representation's tables (corpus paragraphs, stand-in Canvas, the
rich-inline operations, 15 processes per variant, V8 and JavaScriptCore),
with retained heap per handle and a browser run; and the cost of the
`sourceStarts` reorder at materialization.

## Against private representation

What this design gives up:

- **Wider trust.** Private representation trusts outside code only about
  what a handle gives out at a read-only type (`segments`, `kinds`,
  `widths`); a handle itself is protected by the language. Here the row
  covers every handle and everything reachable from it, hidden fields
  included, and any storage outside code passes in at a read-only type. A
  caller that changes a hidden field through a cast leaves the walker
  reading `[1, undefined, undefined]` (observed); the design accepts that
  program, whose caller breaks the row.
- **The invariant at entry rests on caller trust.** There, a handle's
  invariant holds of every complete instance by (L4), proved from the
  class's own code. Here it holds at an exported function's entry by the row
  on exported preconditions, and a forged or JSON-copied handle that breaks
  it is excluded by trust, not refused.
- **Copies and proxies to be checked**, above, where private representation
  makes every copy and proxy throw at its first private read.
- **Coarser protocol.** $`\Psi_A`$ joins every exported function of the
  analyzed sources, internal helpers exported between modules included, so
  the exported steppers' writes put the fields of every exposed site at
  $`\mathsf{scalar}`$; private representation's members exclude functions
  the body calls by name.

What it gains:

- **Pretext's source stays upstream's** but for annotations, one result
  type and one moved line: no class, no static block, no staging field, no
  public-field copies, no `#segments !== null` test, no move of five modules
  into one class body.
- **No class shape**: no base-class, evaluated-once, construction, staging,
  lexical-dispatch or distinct-name restriction; no lifting of the
  refusal-index rows on classes; no native key-enumeration audit; no trust
  row of the language.
- **Scope kept**: `structuredClone` and `postMessage` copies and handles in
  IndexedDB lay out as before, and a frozen handle as upstream handles it.

What both share: the rule's shape, the protocol as a least fixed point over
members, reference preservation, tolerant invariants, incoming values
charged, per-site marks, confined collections, throw edges and views in
analyzed code. The per-site mark replaces private names as what tells the
pass which storage outside code cannot reach; it is fixed at allocation
and checked at each crossing, with no owner, no sealed map and no exports
boundary.

## Negatives and controls

**Negative cases**, each unsafe under Node (observed: each program, as
JavaScript, run with `node`, printing the reads), each refused:

- `invalid-readonly-escape-writable`: an exported function returns a
  handle's `widths` at `number[]`; the client truncates it during the
  visitor: `[1, undefined, undefined]`. Refused by *Confinement*.
- `invalid-readonly-reentrant-writer`: an exported `truncate` pops a
  handle's `widths`; the walker caches the length; the visitor calls it:
  `[1, undefined, undefined]`. Refused by *Reference-preserving protocol*.
- `invalid-readonly-incoming-view`: an exported `trim(xs: { length:
  number })` decrements what it is given; the visitor passes it the handle's
  `widths`, read at `readonly number[]`: `[1, undefined, undefined]`.
  Refused by *Incoming values*: the write is charged to exposed sites and
  breaks *Reference-preserving protocol*.

**Restriction control**, safe under Node and refused (observed):
`readonly-lazy-lists-order-refused`, the three lazy lists written
`sourceStarts` first, as upstream writes them: `2`. *Tolerant invariant*.

**Positive cases**: the example, its visitor calling every exported
function (`[1, 1, 1]`); `readonly-hidden-cursor`, a visitor calling the
exported stepper on cursors it holds (`[1, 1, 1]`); `readonly-frozen`, a
handle frozen deep by its client (`[1, 1]`, and a write to it throws a
`TypeError`); `readonly-structured-clone`, a `structuredClone` copy passed
back (`[1, 1, 1]`).

**Accepted programs that break the row** (observed), which no case can
refuse, the breaking code being outside the analyzed sources: a caller
popping a hidden field of a handle in the visitor
(`[1, undefined, undefined]`); a caller passing the handle's `widths` where
`{ length: number }` is expected and clearing it, with no cast
(`[undefined, undefined, undefined]`).

**Observations**: a JSON copy's `flags` is no `Uint8Array` and has no
`length`; a proxy's trap runs at a walker's field read.

**Controls** (forged fragment or forced proposal), each refused:
$`\Psi_A`$ forced smaller than a member's effect; an exported function
forged as no member; a site's mark forged hidden where its storage crosses,
or exposed where it crosses at a writable position; an incoming value forged
to a hidden site; a write to a value from a confined collection forged
uncharged; an exported collection forged confined; a write to possibly
frozen storage forged without its throw edge; a handle invariant forged to
read a path outside its representation.

## Stages and cost

1. **The rule in the note and in Lean**: the marks, $`E_A`$, $`R_A`$,
   $`\Psi_A`$, (P2), (M), (L1) to (L4), Reliance at $`\Phi\oplus_A\Psi_A`$.
   Front: members, the marks and possible sites, $`\Psi_A`$ as a least fixed
   point, the checks above. The trust row. The cases and controls above.
2. **Pretext**: the annotations and the two source changes on the fork; the
   five handle sites and six cursor sites checked; the measurement above.
3. **Copies**: a decision on JSON copies and proxies.
4. **P15 and P16**.

Cost (conjectured): Lean as private representation's, with (M) in place of
(P1) and no construction lemma, two to three weeks; front, the site marks
and the flow of possible sites, which private representation's owning marks
already need; sources, comments, two annotations and one moved line.
