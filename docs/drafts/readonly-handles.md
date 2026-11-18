# Draft: read-only handles

A design for pattern P22 of
[Tolerant frames II](tolerant-frames-2-note/note.tex) in which pretext's
handles stay upstream's plain records behind their opaque types. In place
of private fields it rests on one trust row, stated in the API: code
outside the package changes nothing reachable from a value that crosses the
package's entries at a read-only type. A fact an analyzed function holds
about storage a handle reaches, or about storage only its own frames hold,
survives a call of code of unknown effect, a user's callback included,
bounded by what the package's entry functions may change. It answers P22 at
its handle sites (form (b) of the [dossier](callback-frames-dossier.md))
and at its cursor sites (form (a)), and states what it gives P15, P16, P18
and P20. It is a variant of
[private representation](private-representation.md), whose rule, protocol
and checks it restates for another region; the
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
construct's rule. This design is that mechanism, its four parts read at a
package $`P`$ of the analyzed sources:

1. **The fact**: a handle type's invariant, and any fact whose support lies
   in the protected region $`R_P`$ below: storage a value crossing the
   package's entries reaches, and storage only the package's own frames
   hold.
2. **The stable operations**: the package's *members*, the functions its
   entry modules export and the functions it gives out; their joint
   footprint on $`R_P`$ is the protocol $`\Psi_P`$, a closed footprint.
3. **The checked contract**: Lean certifies each member within
   $`\Psi_P`$, as it certifies every function at its inferred effect
   (cited:
   [inferred call effects](../SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification)).
4. **The construct's rule**: Read-only frame, below, Private frame of
   private representation at another region. With it, Paper I's Theorem
   "Tolerant frame" and Proposition "Reliance" carry a fact across every run
   of code that is not the package's (proved: Paper I, Lean `frame_box`,
   `rely_chain`).

It reads five existing pieces:

- **The trust surface's outside callers** (cited:
  [trust surface](../DESIGN.md#trust-surface)): the rows on exported
  preconditions and on a callback's stated effect state what "a caller
  outside the analyzed sources" does; this design states one more such row.
- **Sealed handles** (cited:
  [type invariants](../ARITHMETIC.md#type-invariants), "Sealed handles";
  [a handle means its representation](../PROGRAM-TYPING.md#a-handle-means-its-representation)).
  An opaque type stating `@invariant` and `@representation T` means `T`;
  its invariant is a contract of function boundaries (`invariant-requires`,
  `-ensures`, `-returns`), and the row on handle parameters gives it at an
  outside caller's call: the caller passes "a value of `R` meeting the
  handle's invariant" (cited: [trust surface](../DESIGN.md#trust-surface),
  the row on `@representation`).
- **The caller contract and the proxy row** (cited: the same table, the
  caller contract and the row "No object a program holds … is a proxy"). A
  value conforming to a structural annotation is a plain data object whose
  stated fields are own data properties, not accessors or proxies, and no
  object a program holds is a proxy. So a handle at entry is an ordinary
  object whose representation's members are own data properties of the
  representation's types.
- **The package's entries** (cited: the superseded abstract-handles
  design's decision on the owner's boundary, recoverable at `72055046`,
  "Decisions"): the modules `package.json`'s `exports` names. Here they
  choose the members, and nothing else: no owner tags, no sealed map.
- **Private representation's checks** (cited:
  [private representation](private-representation.md), "The class shape
  the rule requires"): reference-preserving protocol, tolerant invariant,
  incoming values, marks per allocation site, confined collections, the
  exposed ghost set, read-only types and views. Each is restated below for
  $`R_P`$.

New machinery: one region, one protocol per package, one rule, one mark per
allocation site, one confinement check and one trust row. No new judgment
form, no new modality, and no world component but the ghost set $`E_P`$ of
the roots that crossed at read-only positions.

## The example

```ts
declare const brand: unique symbol
/** Callers must not change anything reachable from a Handle.
 *  @invariant this.flags.length === this.widths.length
 *  @representation Rep */
export type Handle = { readonly [brand]: true }
/** @invariant this.flags.length === this.widths.length */
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

The module is the package's one entry. `visit` is external code and may
hold `h`, call `prepare` and `walk`. The read `w[i]!` needs $`i<|w|`$
after `visit`. Under Node (observed), a visitor calling both leaves the
walker reading `[1, 1, 1]`.

## The rule

Paper I's notation throughout: a heap $`h`$, an environment $`\rho`$, the
action $`h\xrightarrow{\Phi}_\rho h'`$ of an effect, changes
$`\mathsf{keep}\sqsubseteq\mathsf{init}\sqsubseteq\mathsf{scalar}\sqsubseteq\mathsf{grow}\sqsubseteq\mathsf{any}`$
(Paper I, §3, the changes' definition), regions read at the entry heap,
regions at a field key as Paper I's $`x.f`$, $`\Phi\triangleleft_K S`$ for
respect and $`\Box_\Phi F`$ for the modality.

### Definitions

**The package and its entries.** A package $`P`$ is the analyzed modules
of one `package.json`; its *entry modules* are those its `exports` names
(for pretext `.` and `./rich-inline`, `layout.ts` and `rich-inline.ts`).
A function an entry module exports, directly or re-exported, is an *entry*.
An export between modules of $`P`$ that no entry module re-exports is a
function of $`P`$ called by name.

**Code that is not $`P`$'s.** A step runs code that is not $`P`$'s when it
is a call whose callee is neither a function of $`P`$ nor an audited native,
an `await`, or a `yield`. A callback that an entry calls is code that is
not $`P`$'s, and its steps are its own.

**Members.** The members $`M_P`$ are the entries, every method of a class
an entry module exports, every function of $`P`$ used as a value given to
code that is not $`P`$'s (a result, an argument of a call of such code, a
value thrown or yielded, the content of storage such code reaches), and
every resumption of a suspended function of $`P`$: an async function's or a
generator's body after an `await` or a `yield`, which the job queue or
outside code resumes.

**Read-only types and crossings.** A type is *read-only* as private
representation defines it ("Read-only types and views"); a sealed handle's
type is read at its representation, every position of it read-only. A value
*crosses* when it passes between $`P`$ and code that is not $`P`$'s, in
either direction, through any alias: an entry's argument, receiver or
result; an argument or result of a call of code that is not $`P`$'s, a
callback's included; a value thrown, caught or yielded; a function of
$`P`$ given out, and what it later receives and returns; the content of
storage both sides reach. This one definition is the rule's and the trust
row's. A storage location is reached by a crossing *at a read-only
position* when the path to it through the crossing type passes only
read-only positions, and *at a writable position* otherwise.

**Marks, one per allocation site.** Each allocation site of $`P`$ carries a
mark, a component of the allocated location's contract fixed at
allocation, as private representation's owning mark is:

- *local*: its storage is held only by frames of $`P`$ (locals, and
  arguments of calls by name), never stored into storage or a binding of a
  module or closure, and never reachable from a crossing value;
- *internal*: its storage may be held by bindings or storage of $`P`$, and
  is never reachable in the heap from a crossing value;
- *exposed*: its storage may be reachable from a crossing value, at
  read-only positions only;
- *released*: its storage may be reached by a crossing at a writable
  position.

Exposure is by heap reachability: every location reachable in the heap from
a crossing value, through any field a cast could name, is of an exposed or
released site, a handle's representation fields included. The front
proposes each site's mark and the pass checks every crossing and every
store against it; a forged mark fails a check (conjectured).

**The exposed roots.** $`E_P`$ is a ghost component of the state: the
locations reached by a crossing at a read-only position, whoever allocated
them, from the crossing on. It only grows. A root of an exposed site is
protected from the crossing on; a root of a released site or of storage
outside code allocated is protected while it is *held*: while a frame,
binding or storage of $`P`$ references it.

**The protected region.** $`R_P(\rho,h)`$ is the storage of local and
exposed sites, together with the storage reachable from the protected roots
of $`E_P`$ through
fields, spines and element cells, stopping at collections, whose entries
the model holds in no location (cited:
[native footprints](../SOURCE-CONTRACTS.md#native-footprints), the row of
`Set` and `Map`). Internal storage is outside it: no handle reaches it.
Released storage is in it only where a later crossing at a read-only
position reached it. Its parts are one per allocation site of $`P`$, kind
and field key, and one per kind and key for storage outside code allocated:
$`R_s.\mathsf{spines}`$, $`R_s.\mathsf{cells}`$, $`R_s.k`$ for a site
$`s`$ and a key $`k`$, and $`R_{\mathrm{in}}`$'s alike.

**Possible sites.** The flow propagates, for each reference, the sites it
may come from. A value entering $`P`$ in a crossing (a member's argument or
receiver, a result of code that is not $`P`$'s, a caught value) may come
from every exposed and released site and from $`\mathrm{in}`$, whatever its
type: TypeScript admits a read-only view where a writable type is expected
(cited: private representation, "Incoming values", observed under `tsc`
7.0.2). A value from a confined collection may come from the sites inserted
into it. A reference a suspended function holds across an `await` or a
`yield` keeps its possible sites at the resumption, and each object it
reaches that was published during the suspension may come, at the
resumption, from every site that crossed meanwhile.

**The protocol.** $`\Psi_P`$ has one entry per part. It is the least such
effect for which every member $`m\in M_P`$, entered from code that is not
$`P`$'s (its parameters at the possible sites of an entering value), and
checked with each of its steps that run code that is not $`P`$'s bounded on
$`R_P`$ by $`\Psi_P`$, has normal and exceptional effects that, after
`fresh_eff` drops the locations it allocated, bound every location of
$`R_P`$ of its entry heap by $`\Psi_P`$. A write at key $`k`$ is charged to
$`R_s.k`$ for each site $`s`$ the written object may come from whose records
have $`k`$, released sites included; a write to an internal site is not
charged. A member that writes only what it allocated contributes
$`\mathsf{keep}`$. A call by name is checked at the callee's effect on its
actual arguments, not through $`\Psi_P`$. A resumption is a member: each
segment of a suspended function, from a resumption to its next suspension
or its completion, is certified against its own entry heap, the heap at the
resumption, with the possible sites its captured references keep; storage
the function allocated before the suspension is old for the segment, and
both of the segment's exits are charged. So a write a suspended function of
$`P`$ makes after its caller returned is in $`\Psi_P`$.

**The bound on $`R_P`$.** $`\Phi\oplus_P\Psi_P`$ bounds the locations of
$`R_P`$ by $`\Psi_P`$ and every other location by $`\Phi`$:

```math
h\xrightarrow{\Phi\oplus_P\Psi_P}_\rho h'\iff h\xrightarrow{}_\rho h'\ \wedge\ \forall l<|h|.\ h'(l)=h(l)\ \vee\ \exists (r:\delta)\in(\text{if } l\in R_P(\rho,h) \text{ then } \Psi_P \text{ else } \Phi).\ l\in r(\rho,h)\wedge\delta_{|h|}(h(l),h'(l))
```

**A handle's invariant.** $`I_H(o,h)`$ is the `@invariant` of a sealed
handle type $`H`$ or of a record type, with `this` read as $`o`$;
$`\mathrm{supp}(I_H)`$ is its support.

### Read-only frame

```math
\frac{c:\Phi\mid\Phi^{e}\qquad c\ \text{runs code that is not}\ P\text{'s}}
     {c:\ \Phi\oplus_P\Psi_P\ \mid\ \Phi^{e}\oplus_P\Psi_P}\ \textsf{(Read-only frame)}
```

An unknown callback, of effect $`\top`$, has by the rule the effect
$`\Psi_P`$ on $`R_P`$. A call naming a function of $`P`$ is checked at
that function's certified effect; an audited native keeps its audited
effect, and each call of a callback it makes is bounded by the rule.

**At a callback.** Let a walker hold $`F`$ with a support $`S`$ and
$`\Psi_P\triangleleft_K S`$. The frame applies where the pass shows $`S`$
inside $`R_P`$: every possible origin of each object a path of $`S`$ reads
is a local or exposed site, or a root of $`E_P`$. A record $`P`$ received
at a writable type and passed on internally has no such origin, and its
facts do not cross. Tolerant frame then gives
$`K\wedge F\vdash\Box_{\Phi\oplus_P\Psi_P}F`$, and Reliance carries $`F`$
across every step that runs code that is not $`P`$'s, given rigidity
((L3)). In the example `prepare` writes only what it allocates and `walk`
nothing, so every entry of $`\Psi`$ is $`\mathsf{keep}`$, and $`i<|w|`$
crosses `visit` (conjectured, the design's claim).

**At a handle's entry.** A parameter of a sealed handle type meets its
invariant: from an analyzed caller by `invariant-requires`, checked at the
call from the caller's own facts, and from an outside caller by the row on
handle parameters. A cast to the representation gives its fields
(handle-meaning). The handle crossed at its read-only type, so its storage
is in $`R_P`$ from entry.

**The invariant at use.** A handle's invariant is a contract of function
boundaries, and is assumed only where a boundary gives it: at a parameter,
by `invariant-requires`, and at a result, by `invariant-ensures`. A value
retained in a confined collection or in storage, or passed on internally,
gets it again at the next boundary it passes, where the caller proves it
from its facts, or by a check at use. Retention is no boundary, so no
argument about the support's protection through retention is needed: the
existing mechanism is the boundary contract, and a value read back is
checked where it is used.

### What must be proved

The rule rests on two invariants of states and four lemmas. Each is
conjectured until its Lean exists.

- **(P2) Confinement.** Every path from a frame of code that is not $`P`$'s
  to a location of a local or exposed site enters $`R_P`$ at a location
  reached from $`E_P`$ through read-only positions. Paths run through
  fields, cells, spines and element cells; a closure's environment is not
  reachable from a holder of the closure. From the
  [confinement check](#the-checks-the-rule-requires) and the marks.
- **(M) Marks.** Every location's mark is its site's, fixed at allocation;
  a location of a local site is reachable from no binding, no storage and no
  frame but $`P`$'s; a location of an internal site is reachable from no
  crossing value.
- **(L1) Outside step.** From a state meeting (P2) and (M), a step of code
  that is not $`P`$'s leaves unchanged every location of $`R_P`$ that is of
  a local or exposed site or is held by $`P`$, and keeps (P2) and (M). A local location is out of its reach; a location reachable
  from $`E_P`$ it reaches only through a read-only crossing, and the
  [trust row](#trust) states it changes none. (L1) is conjectured from that
  row, which is trust: it holds of outside code that meets the row, and of
  no other.
- **(L2) Outside run.** A run of code that is not $`P`$'s from $`h`$
  changes each location of $`R_P(h)`$ within $`\Psi_P`$. By induction on
  the budget $`k`$: the run changes $`R_P`$ only inside members, entries
  called and resumptions resumed, each bounded by its certificate at
  $`\Psi_P`$, whose own steps that run code that is not $`P`$'s are bounded
  by the rule at a smaller budget.
- **(L3) Rigidity.** Persistence is needed only of the support of a fact
  a live frame of $`P`$ relies on. For every pair
  $`h\xrightarrow{\Phi\oplus_P\Psi_P}_\rho h'`$ of the action and every
  such support $`S`$, $`R_P(h)\cap S\subseteq R_P(h')`$: the part by marks
  is fixed at allocation; a root of $`E_P`$ the support reads stays held,
  since the frame relying on the fact references it through the paths of
  $`S`$; and $`\Psi_P`$ preserves the references (*Reference-preserving
  protocol*), every reference held in $`R_P(h)`$ held in $`R_P(h')`$ and
  every listed cell listed, by induction on the length of the path. Storage
  that leaves $`R_P`$ because $`P`$ drops its last reference supports no
  live fact. Then
  $`\Phi\oplus_P\Psi_P`$ is rigid when $`\Phi`$ and $`\Psi_P`$ are rigid and
  $`\Psi_P\sqsubseteq\Phi`$, as for $`\Phi=\top`$ and for
  `{ values: "any"; spines: "grow" }`.
- **(L4) The handle invariant across a run.** A fact $`I_H(o)`$ that holds
  where a walker relies on it is kept by every member write to
  $`\mathrm{supp}(I_H)`$ (*Tolerant invariant*) and by every outside step
  (L1). It holds at an entry by the row on handle parameters, which is
  trust, for a handle an outside caller passes.

`SourceClaimJson.PassUnit.mode8Accepted_sound` keeps its statement; the
premise and conclusion of `PassUnitSafe` are reviewed again, as a change of
the accepted plan type requires.

## The checks the rule requires

Each is chosen by the behaviour it excludes, documented in
SOURCE-FRAGMENT.md, enforced at the source boundary, and has a control
([negatives and controls](#negatives-and-controls)).

- **Reference-preserving protocol.** Every entry of $`\Psi_P`$, on every
  part, preserves the references: in each pair of its action, every
  reference to storage held at a location of the part is held at a location
  of $`R_P`$ of the exit heap, and every cell a spine or view spine lists
  stays listed. The entries that meet it are private representation's:
  $`\mathsf{keep}`$; $`\mathsf{scalar}`$ on a cell or at a key; an extension
  on a spine. The parts of released sites are bound too, since released
  storage enters $`R_P`$ when it crosses back at a read-only position: an
  entry that shortens an array it gave out at a writable type is refused. A
  `pop` charged to $`R_P`$ is refused (WORK, "Shrinking owned arrays").
- **Tolerant invariant.** Every change a member makes to a location of
  $`\mathrm{supp}(I_H)`$ of storage it did not allocate in the call, and
  every entry of $`\Psi_P`$ on such a location, is one $`\mathrm{supp}(I_H)`$
  tolerates, or one write checked to keep $`I_H`$. An invariant that one
  write breaks and a later write restores is refused.
- **Confinement.** No storage of a local or exposed site, and no storage
  reachable from $`E_P`$, crosses at a writable position: a return, an
  argument of a call of code that is not $`P`$'s, a `throw`, a `yield` or
  an `await`, a store into storage outside code reaches, each at a type
  whose position for that storage is writable, is refused. A copy is
  storage of a fresh site, and separates only where its element type holds
  no storage.
- **Incoming values.** Every write $`P`$ makes to a value entering in a
  crossing, or to anything reached from it, is charged at its key to every
  exposed and released site and to $`R_{\mathrm{in}}`$, whatever the value's
  type, and meets *Reference-preserving protocol* and *Tolerant invariant*.
  By (M) it is never charged to a local or internal site.
- **Confined collections.** A collection held only by bindings or storage
  of $`P`$, and never crossing, is *confined*; one that is not confined
  holds no storage of $`R_P`$. Insertion into a confined collection is a
  write of $`P`$, checked as a store, and preserves each value's possible
  sites; a lookup yields the sites inserted. No outside code reaches a
  confined collection, and every write $`P`$ makes to protected storage from
  it is charged.
- **Writes outside code may make fail.** The row admits freezing, sealing,
  preventing extension and making a data property non-writable or
  non-configurable. A write by $`P`$ to storage outside code may have made
  so throws in strict code, which safety admits. Only a store proved atomic
  (a data property's assignment or definition at one key) has a throw edge
  leaving the heap unchanged. An array's `length` assignment is not atomic:
  with index 1 non-configurable, `xs.length = 0` of `[1, 2, 3]` deletes
  index 2 and then throws, leaving length 2 (observed). A native that throws
  part way leaves the writes it completed, as `Object.seal([1, , 3]).fill(9)`
  leaves element 0 at `9` (observed). Each of these has a throw edge
  carrying its audited partial-write footprint, and each handler is checked
  from the heap its edge gives. On protected storage a shortening `length`
  assignment is refused by *Reference-preserving protocol* anyway.
- **Native writes charge every affected part.** A native's write is charged
  through its audited footprint to every part it may change: each typed
  array viewing a buffer it writes, overlapping views over the same buffer
  included, and each element and length of an array it changes.
- **Views in analyzed code.** Analyzed code outside the package, a client,
  is checked, not trusted: a value it reads at a read-only type is read at a
  readonly view, and the pass refuses a write through it, a write through a
  writable type it was widened to included (cited: private representation,
  "Views in analyzed code"). The package's own write to storage it gave out
  as a view is a *representation write*: through a cast of the handle to its
  representation, checked against the representation's type, its invariant
  (*Tolerant invariant*), the throw edge of *Writes outside code may make
  fail*, and charged at its key to every possible site of the written
  object.

## Trust

One new row of the [trust surface](../DESIGN.md#trust-surface), an
assumption about code outside the analyzed sources, of the kind of the rows
on exported preconditions and on a callback's stated effect (a stand-in
until applications are analyzed too):

> Code outside a package of the analyzed sources enters it only through the
> modules its `package.json` `exports` names; an import of another file of
> the package is outside this row. That code, a function it passes in
> included, changes by its own steps, by any operation, a native's
> included, no element, field, length, prototype or property kind (a data
> property redefined as an accessor) of storage reached, through read-only
> positions of the crossing's type, from a value that crosses between it and
> the package in either direction, through any alias (an entry's argument,
> receiver or result, a callback's argument or result, a value thrown,
> caught or yielded, a function the package gives out and what it receives
> and returns), a handle's representation fields included: storage the
> package allocated at an exposed site, from the crossing on; storage it
> allocated at a released site, and storage outside code allocated, while
> the package holds a reference to it. Each step is the code's that executes
> it: a change made inside a call of an entry, or of a function the package
> gave out, is that function's, bounded by its certificate, and a step of a
> callback an entry calls is the callback's. Freezing, sealing, preventing
> extension and making a data property non-writable or non-configurable are
> admitted.

Where it is stated: in the API, in the doc comment of each read-only type
the entry modules export (each handle type and each read-only member a
handle shows), as "Callers must not change anything reachable from it",
and in the package's documentation, which names the entry modules.
TypeScript does not establish it: its `readonly` constrains only the written
type, a read-only view is admitted where `{ length: number }` is expected
and a cast removes it (cited: private representation, "Trust", observed
under `tsc` 7.0.2). Node's resolution of `exports` refuses a deep import of
a file the field does not name; a bundler or a path import can reach one,
which the row excludes.

Rows used unchanged: the row on handle parameters, for a handle's
invariant and its representation at an entry; the caller contract and the
proxy row, which make that representation an ordinary object of own data
properties, no proxy and no accessor; a callback's stated effect; ordinary
arrays; fixed-length typed arrays.

**Copies passed back.**

- A `structuredClone()` or `postMessage()` copy, and a handle kept in
  IndexedDB, which stores structured clones, keep the representation's
  types: arrays stay arrays and a `Uint8Array` a `Uint8Array` (observed). The
  copy is an ordinary object of own data properties, so the existing rows
  give its representation and invariant, and the new row covers it while
  the package holds it. Covered.
- A proxy of a handle, or a copy whose fields are accessors, runs outside
  code at a field read (observed: an accessor copy gives the walker
  `[1, undefined, undefined]`); the caller contract and the proxy row
  exclude both.
- A JSON copy turns each typed array into a record of numeric keys with no
  `length` (observed). It is no value of the representation type, so the
  row on handle parameters excludes it, and acceptance says nothing of a
  program passing it. Upstream lays such a copy out as the handle, by
  reading `segmentFlags` by index (cited: `line-break.ts:26–28`; upstream
  `RESEARCH.md`, Decisions Log, 2026-09-24, line 5553). This is the open
  copy question: a representation type a JSON copy meets, or a check at
  entry.

A frozen handle, or one a store froze deep, lays out as before, and a write
to it throws in strict code (observed); upstream's side table for frozen
paragraph handles (`rich-inline.ts:1141–1178`) stays, analyzed as written.

## Pretext

### What changes in upstream's source

Checked against upstream `0d102a5c`; each item is cited or observed, what
it gives is conjectured.

- **The entries.** `package.json`'s `exports` names `.` and
  `./rich-inline` (`package.json:26–38`), `layout.ts` and `rich-inline.ts`.
  They export 12 and 5 functions (`layout.ts:139–369`,
  `rich-inline.ts:186–1258`) and re-export none (observed: no
  `export … from` in either). So `measureAnalysis`, `walkPreparedLinesRaw`,
  `normalizePreparedLineStart`, the steppers, `getFontMeasurement`,
  `getSegmentMetrics`, `getSegmentFit`, `getFontSpaceKerning` and
  `getGraphemeEnds` are functions called by name. A deep import that calls
  `walkPreparedLinesRaw` with its own record and truncates it during
  `onLine` makes the walker read `[1, undefined, undefined]` (observed); the
  row excludes it. No change.
- **The edits, applied and checked.** The edits below are applied to a
  scratch copy of upstream `0d102a5c` and type-check under its
  `tsconfig.build.json` with its pinned TypeScript, 7.0.2 (observed: no
  error; under `tsconfig.json` the copy reports the same 282 errors as
  upstream, each from the `bun` and `node` types the copy does not install).
  Together they add 45 lines and remove 31 in `layout.ts`, `line-break.ts`,
  `prepare.ts` and `rich-inline.ts`. `oxlint`, which upstream's `check` also
  runs, was not run.
- **Representation records free of brands.** `InternalPreparedText` and
  `InternalPreparedTextWithSegments` intersect the brand
  (`layout.ts:63–64`), as `InternalPreparedRichInline` does
  (`rich-inline.ts:136`). They become the brand-free records
  `PreparedLineData` (`line-break.ts:65`),
  `PreparedSegments & { kinds: SegmentBreakKind[] }` and the paragraph's
  fields, and each handle states `@representation` of its record. The casts
  between a handle and its record (`layout.ts:155`, `:185`, `:316`,
  `rich-inline.ts:183`) become casts through `unknown`, read by
  handle-meaning.
- **The introductions of a handle.** A record becomes a handle where an
  entry returns it: `prepare` (`layout.ts:140`), `prepareWithSegments`
  (`:151`) and `prepareRichInline`'s two returns (`rich-inline.ts:218`,
  `:666`), each a cast through `unknown` at a return whose type names the
  handle. Each is a checked introduction: the cast states no fact, and the
  return's `invariant-ensures` proves the handle's invariant from the
  record's facts (cited: [type invariants](../ARITHMETIC.md#type-invariants),
  "a cast into the handle states no fact, and a boundary requiring the
  invariant proves it").
- **The invariants.** The walkers and steppers take `PreparedLineData` and
  `PreparedSegments`, so `@invariant` is stated on `PreparedLineData`, on the
  paragraph record and on the three handle types, with the row's sentence on
  the handle types. Each walker's entry then gets it by
  `invariant-requires`, checked at each call by name, and each entry's cast
  by handle-meaning. Five annotation comments.
- **`measureAnalysis`'s three results.** Its result type names the handle
  and the records (`prepare.ts:366`), and it has three results: a text's
  record without segments, for `prepare`, which passes
  `includeSegments = false` (`layout.ts:140`; `prepare.ts:384`,
  `:639–640`); a text's record with segments, for `prepareWithSegments`; and
  a paragraph item's measures, whose lists are the paragraph's, still being
  filled (`prepare.ts:379–383`, `rich-inline.ts:479`), which do not meet the
  invariant (cited: private representation, "Preparation"). The change:
  three overload signatures, by `includeSegments` and `paragraph` at literal
  types, returning `PreparedLineData`, `PreparedSegments` and
  `PreparedLineBreakData`, which states no invariant; the literal at
  `prepare.ts:638` is typed by an annotation in place of a cast through
  `unknown`. `prepareInternal` (`layout.ts:108–121`) takes two overloads and
  calls `measureAnalysis` at each literal. The cast at `rich-inline.ts:215`
  is dropped: the overload gives `PreparedSegments`. Each overload is the
  implementation's code checked at that overload (cited:
  SOURCE-FRAGMENT.md, the row on overloads), so the text overloads'
  `invariant-ensures` is proved in text mode only.
- **The writes before a handle is returned.** `layout.ts:150`,
  `prepare.ts:639`, `rich-inline.ts:639` and `findWholeLine`'s writes
  (`:819–823`, called at `:221` and `:664`) write records allocated in the
  same call, before the handle is returned: `fresh_eff` drops them. No
  change.
- **The lazy source lists.** After a handle is given out, only
  `materializeRichInlineLineRange`, an entry, writes it: through
  `findSegmentSources`, the three fields `sourceStarts`, `sourceEnds` and
  `sourceUnits` of an unfrozen paragraph handle (`rich-inline.ts:1176–1178`),
  after testing `sourceStarts === null` (`:1198–1199`) (observed: a search
  of the five modules for writes to a handle's fields, arrays and typed
  arrays). Three writes break the invariant relating them until the last,
  and moving `sourceStarts` last can replace a list an incoming handle
  holds in `sourceEnds`, outside $`\mathsf{scalar}`$. The change: one
  nullable field `sources`, holding the `TextSources` record
  `findSegmentSources` already builds (`:1155`, its `sourceUnits` widened to
  admit `null`), written once from `null`. The write is a representation
  write (*Views in analyzed code*): through the handle's cast to its record,
  checked to keep the lazy-list invariant (a checked single write), with an
  atomic store's throw edge, and charged at the key `sources` to every
  possible site of the handle, the paragraph handle's site and
  $`R_{\mathrm{in}}`$, since a structured clone passed back is outside
  storage. The fields' declarations (`:170–172`), the two initializers
  (`:220`, `:663`), the write and the read (`:1198–1199`) change; a
  multi-item paragraph handle holds one record more (not measured).
- **The frozen side table** (`rich-inline.ts:1141–1178`) stays: the
  `Object.isFrozen` test, a `WeakMap` no module exports (a confined
  collection) holding the fresh record, and the write in the other branch.
  `Object.isFrozen` needs an audited contract; nothing runs between the test
  and the write. `line-text.ts:11`'s `WeakMap` of grapheme ends is a
  confined collection holding fresh `Int32Array`s.
- **The measurement caches.** Under the protected region, storage is
  protected where a handle reaches it. The caches' records (each font's
  measurement, segment metrics and the fit records `getSegmentFit` stores in
  `metrics.fit`, `measurement.ts:1207`, `:1262`) are of internal sites: no
  handle reaches them, so their writes are not charged, and `getSegmentFit`
  replacing a fit record changes nothing protected. The advances and
  `lineStartExtras` lists a fit record holds are of an exposed site, since
  handles hold them (`prepare.ts:525–529`): every write $`P`$ makes to them
  is charged, and preparation copies a cached list before changing it
  (`prepare.ts:533–541`), so none is. `clearCache` (`layout.ts:360–363`)
  clears confined collections and writes a number to the internal state
  record: $`\mathsf{keep}`$ on $`R_P`$. The exported `noExtraSpacings`
  (`measurement.ts:661`) is no entry's; no handle holds it. No change.
- **The cursors**, each fact attributed to what establishes it (the six
  sites of the dossier, §2, "Form (a)"):
  - `walkPreparedLinesRaw`'s cursor (`line-break.ts:293`) is of a local
    site: held by frames and passed by name to the steppers and
    `normalizePreparedLineStart`, no member. Its facts cross `onLine` by
    Read-only frame, $`\Psi`$ being $`\mathsf{keep}`$ on it. The same holds
    in `walkPreparedComplexLines`, whose cursor is its caller's local one
    where an `onLine` is given.
  - `countSteppedLines` (`:396`), `layoutNextRichInlineLineRange`
    (`rich-inline.ts:1120`) and `prepareRichInline`'s cursor and `own`
    (`:359–365`) call no code that is not $`P`$'s between their reads: their
    facts across the helpers come from the helpers' certified effects on
    their actual arguments, which write the cursor alone, and so keep
    `own.segmentFlags`.
  - `stepNextLine` writes the `start` and `end` records of the result
    `layoutNextLine` and `layoutNextLineRange` return at `LayoutCursor`, a
    writable type (`layout.ts:305–333`): released sites. Its facts come from
    the helpers' effects on those fresh records, with no callback before the
    return.

  The public `LayoutCursor` a caller passes is validated on entry as
  upstream does. No change.

In all, checked as above: five annotation comments; brand-free records,
casts through `unknown` and four checked introductions in `layout.ts` and
`rich-inline.ts`; three overloads and a typed literal in `prepare.ts` and
two overloads in `layout.ts`; and the lazy lists' one field.

The protocol for pretext (conjectured): $`\mathsf{scalar}`$ at the key
`sources` of the paragraph handle's site and of $`R_{\mathrm{in}}`$, from
`materializeRichInlineLineRange`; $`\mathsf{keep}`$ on every other part.
It preserves the references.

### What each site gets

The sites are the dossier's (cited: [dossier](callback-frames-dossier.md),
§2, §4); what each gets is conjectured.

- **P22, form (b)**: `walkPreparedLinesRaw` and `walkPreparedComplexLines`
  after `onLine`: the handle's facts come from its invariant at entry and
  survive by Read-only frame, every part of the handles' sites at
  $`\mathsf{keep}`$. `walkLineRanges` holds no fact;
  `walkRichInlineLineRanges` and `layoutWithLines` as in private
  representation.
- **P22, form (a)**: the six cursor sites, two by the local mark and four
  by the helpers' certified effects, as attributed above.
- **P18**: at pretext's sites, the handle's invariant at entry and its
  support kept by (L4). Paper II's own program, whose `Prepared` is a
  structural type external code may build and write, is outside: it is no
  read-only type.
- **P20**: a value of a sealed handle type read back from a `Map` gets its
  invariant at the next boundary it passes or by a check at use
  (*The invariant at use*); the `Map` gives none.
- **P15**: a module constant array no entry exposes writably is of a local,
  internal or exposed site; if it is exposed or reaches a handle,
  $`\mathsf{keep}`$ on its spine keeps its length. Internal storage is not
  protected, so a fact about an internal array is kept only by the effects
  of the calls themselves.
- **P16**: a module cell initialized at first use, its one write checked to
  keep `bmp === null || bmp.length === 65536`, as the lazy lists'.

### Performance

The source keeps upstream's code but for the changes above. Only the lazy
lists' record runs at a line function's step, at the first materialization
of a one-item paragraph, so no regression is expected (conjectured). The
measurement this needs: upstream against the changed source on the setup
of private representation's tables (corpus paragraphs, stand-in Canvas, the
rich-inline operations, 15 processes per variant, V8 and JavaScriptCore),
with retained heap per handle and a browser run, the materialization of
one-item and multi-item paragraphs included.

## Against private representation

What this design gives up:

- **Wider trust.** Private representation trusts outside code only about
  what a handle gives out at a read-only type (`segments`, `kinds`,
  `widths`); a handle's state is protected by the language. Here the row
  covers every handle and everything reachable from it, its
  representation's fields included, and any storage outside code passes in
  at a read-only position while the package holds it. A caller that pops a
  representation field through a cast leaves the walker reading
  `[1, undefined, undefined]` (observed); the design accepts that program,
  whose caller breaks the row.
- **A boundary of the package.** The members are the entry modules'
  exports, which rests on outside code importing only those modules; there,
  the boundary is the class body, a lexical fact.
- **The invariant at entry rests on caller trust.** There, a handle's
  invariant holds of every complete instance by (L4), proved from the
  class's own code, and is recovered at the first private read of any
  instance, one read back from a `Map` included. Here it holds only of a
  handle that enters as an entry's parameter, by the row on handle
  parameters, and a value read back from a `Map` or storage gets it only at
  the next boundary it passes or by a check at use (P20).
- **Exclusions by trust where there they fail at run time.** Proxies,
  accessor copies and prototype changes are excluded by the caller contract,
  the proxy row and the new row; there, a proxy or a copy throws at its
  first private read and outside code cannot reach the state.

What it gains:

- **Pretext's source stays upstream's** but for the checked edits counted
  above (45 lines added and 31 removed, annotations included): no class, no static block, no staging field, no
  `#segments !== null` test, no move of five modules into one class body.
- **No class shape**: no base-class, evaluated-once, construction, staging,
  lexical-dispatch or distinct-name restriction; no lifting of the
  refusal-index rows on classes; no native key-enumeration audit; no trust
  row of the language.
- **Copies kept**: `structuredClone` and `postMessage` copies and handles
  in IndexedDB lay out as before, and a frozen handle as upstream handles
  it.

What both share: the rule's shape, the protocol as a least fixed point over
members, reference preservation, tolerant invariants, incoming values
charged, per-site marks, confined collections, throw edges and views in
analyzed code. The marks replace private names as what tells the pass which
storage outside code cannot change: local storage it cannot reach, exposed
storage the row covers, internal storage no handle reaches.

## Negatives and controls

**Negative cases**, each unsafe under Node (observed: each program, as
JavaScript, run with `node`, printing the reads), each refused:

- `invalid-readonly-escape-writable`: an entry returns a handle's `widths`
  at `number[]`; the client truncates it during the visitor:
  `[1, undefined, undefined]`. Refused by *Confinement*.
- `invalid-readonly-reentrant-writer`: an entry `truncate` pops a handle's
  `widths`; the walker caches the length; the visitor calls it:
  `[1, undefined, undefined]`. Refused by *Reference-preserving protocol*.
- `invalid-readonly-incoming-view`: an entry `trim(xs: { length: number })`
  decrements what it is given; the visitor passes it the handle's `widths`,
  read at `readonly number[]`: `[1, undefined, undefined]`. Refused by
  *Incoming values*: the write is charged to exposed sites and breaks
  *Reference-preserving protocol*.
- `invalid-readonly-hidden-field-writer`: outside code reads a handle's
  `widths` through a cast and passes it to an entry `shrink(xs: number[])`
  during the visitor, changing nothing by its own steps:
  `[1, undefined, undefined]`. Refused by *Incoming values*: the handle's
  `widths` is of an exposed site, reachable from the crossing handle, so the
  write is charged to it.
- `invalid-readonly-released-truncator`: an entry `give(): number[]`
  returns an array the package keeps; outside code passes it back to
  `walk(xs: readonly number[], visit)`, whose visitor calls an entry that
  truncates the kept array: `[1, undefined, undefined]`. Refused by
  *Reference-preserving protocol*: the truncation is charged to the
  released site, whose storage entered $`R_P`$ at the read-only crossing.
- `invalid-readonly-partial-length`: a function of the package, given an
  array by outside code that made its index 1 non-configurable, assigns
  `length = 0` and, in its handler, reads the last index it read before:
  `undefined`, the length being 2 after the throw. Refused by *Writes
  outside code may make fail*: the assignment's throw edge carries its
  partial deletion, so the handler holds no fact of the old length.

**Restriction control**, safe under Node and refused (observed):
`readonly-lazy-lists-order-refused`, the three lazy lists written one field
at a time, as upstream writes them: `2`. *Tolerant invariant*.

**Positive cases**: the example, its visitor calling every entry
(`[1, 1, 1]`); `readonly-hidden-cursor`, a visitor calling a stepper on
cursors it holds (`[1, 1, 1]`); `readonly-internal-cache-record`, a cache
replacing its fit record while a handle holds the record's list
(`[1, 1, 1]`); `readonly-frozen`, a handle frozen deep by its client
(`[1, 1]`, and a write to it throws a `TypeError`);
`readonly-structured-clone`, a `structuredClone` copy passed back
(`[1, 1, 1]`).

**Accepted programs that break a row** (observed), which no case can
refuse, the breaking code being outside the analyzed sources: a caller
popping a representation field of a handle in the visitor
(`[1, undefined, undefined]`); a caller passing the handle's `widths` where
`{ length: number }` is expected and clearing it, with no cast
(`[undefined, undefined, undefined]`); a deep import of
`walkPreparedLinesRaw` given a record its caller truncates during `onLine`
(`[1, undefined, undefined]`), outside the entry modules; a copy whose
`widths` is an accessor, passed at the handle type
(`[1, undefined, undefined]`), against the caller contract; an entry that
makes a handle and passes it only to its visitor, at the handle type, whose
visitor truncates its `widths` through a cast (`[1, undefined, undefined]`),
a callback argument, so a crossing the row covers.

**Observations**: a JSON copy's `flags` is no `Uint8Array` and has no
`length`; a proxy's trap runs at a walker's field read.

**Controls** (forged fragment or forced proposal), each refused:
$`\Psi_P`$ forced smaller than a member's effect; an entry forged as no
member; a function given out forged as called by name; a resumption forged
as no member; a site's mark forged local, internal or exposed where its
storage crosses otherwise; an incoming value forged to a local or internal
site; a write forged to a key other than the one it writes; a write to a
value from a confined collection forged uncharged; an exported collection
forged confined; a write that may fail forged without its throw edge, or a
native's throw edge forged without its partial writes; a handle invariant
forged to read a path outside its representation; a fact forged as
supported in $`R_P`$ whose origin is a writable crossing; a resumption's
segment forged to start from its function's entry heap; a `length`
assignment forged atomic; a native write forged to charge one typed-array
view where its buffer has two; the `sources` write forged uncharged to
$`R_{\mathrm{in}}`$; a value read from a `Map` forged to meet its type's
invariant with no boundary or check.

## Stages and cost

1. **The rule in the note and in Lean**: the marks, $`E_P`$, $`R_P`$,
   $`\Psi_P`$ with parts at keys, (P2), (M), (L1) to (L4), Reliance at
   $`\Phi\oplus_P\Psi_P`$. Front: entries from `package.json`, members and
   resumptions, the marks and possible sites, $`\Psi_P`$ as a least fixed
   point, the checks above. The trust row. The cases and controls above.
2. **Pretext**: the annotations and source changes on the fork; the five
   handle sites and six cursor sites checked; the measurement above.
3. **Copies**: a decision on JSON copies.
4. **P15 and P16**.

Cost (conjectured): Lean as private representation's, with (M) in place of
(P1) and no construction lemma, two to three weeks; front, the site marks,
the flow of possible sites and the parts at keys, which private
representation's owning marks already need; sources, as counted above.
