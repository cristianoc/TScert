# Draft: read-only handles

A design for pattern P22 of
[Tolerant frames II](tolerant-frames-2-note/note.tex) in which pretext's
handles stay upstream's plain records behind their opaque types. It is
stated for any component $`C`$, a set of code with a complete interface,
in a family of components that are nested or disjoint; pretext's package
is one instance. In place of private fields it rests, for a component whose
API states it, on one trust row: code outside $`C`$ that TScert does not
analyze changes nothing reachable from a value that crosses $`C`$'s
interface at a read-only type. A fact $`C`$'s code holds about storage a
handle reaches, or about storage only its own frames hold, survives a call
of code outside $`C`$, a user's callback included, bounded by what $`C`$'s
members may change. It answers P22 at
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
construct's rule. This design is that mechanism, its four parts read at
each component $`C`$:

1. **The fact**: a handle type's invariant, and any fact whose support lies
   in the protected region $`R_C`$ below: $`C`$'s own storage, the storage
   of the components nested in it included, and what crossed into $`C`$ at
   a read-only type.
2. **The stable operations**: $`C`$'s *members*, its functions reachable
   from outside $`C`$; their joint footprint on $`R_C`$ is the protocol
   $`\Psi_C`$, the join of their checked effects, a closed footprint.
3. **The checked contract**: Lean certifies each member within
   $`\Psi_C`$, as it certifies every function at its inferred effect
   (cited:
   [inferred call effects](../SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification)).
4. **The construct's rule**: Read-only frame, below, Private frame of
   private representation at another region. With it, Paper I's Theorem
   "Tolerant frame" and Proposition "Reliance" carry a fact across every run
   of code that is not $`C`$'s (proved: Paper I, Lean `frame_box`,
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
- **A component's interface**: every way code outside $`C`$ can enter
  $`C`$. A class body's is enforced by the language, a module file's is read
  from its source, a package's is its `package.json` `exports`, as the
  superseded abstract-handles design's decision on the owner's boundary took
  it (cited: recoverable at `72055046`, "Decisions"), assumed by a trust row.
  Here the interface chooses the members, and nothing else: no owner tags,
  no sealed map.
- **Private representation's checks** (cited:
  [private representation](private-representation.md), "The class shape
  the rule requires"): reference-preserving protocol, tolerant invariant,
  incoming values, marks per allocation site, confined collections, the
  exposed ghost set, read-only types and views. Each is restated below for
  $`R_C`$.

New machinery, per component: one region, one protocol, one rule, one
mark per allocation site, one confinement check and one trust row, stated
in the component's API. No new judgment form and no new modality. The
calculus gains one ghost tag, approved by the owner: each frame carries the
name of its innermost component. The state gains, per component, two ghost
components: the set $`E_C`$ of the exposed-site locations that crossed
read-only, and the history $`A_C`$ (with $`B_C`$) of the released and
outside locations each active call has seen protected.

## The example

```ts
declare const brand: unique symbol
/** The obligation on its callers, in the caller-facing words of Trust (below).
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

Here $`C`$ is the module, its interface its exports. `visit` is external code and may
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

**Components.** A *component* $`C`$ is a set of code (functions, class
bodies, module files) with a complete *interface*: the set of every way
code outside $`C`$ can enter $`C`$. The components of a program form a
laminar family: any two are nested or disjoint. Five modules, the code that
uses them, and that code itself a component other code uses are three
levels of one family. A component is drawn in one of three ways, which
differ only in how its interface is known:
- *enforced by the language*: a class body, whose private names no code
  outside it spells;
- *read from the source*: a module file, entered only through its exports;
- *assumed by a trust row*: a package, entered through its `package.json`
  `exports` (for pretext `.` and `./rich-inline`, `layout.ts` and
  `rich-inline.ts`), or any named set of files, entered through the
  functions its API names. Code that imports another file of the component
  is outside the row.

An *entry* of $`C`$ is a function its interface names. An export between
parts of $`C`$ that the interface does not name is a function of $`C`$
called by name. The rule applies per component: everything outside $`C`$,
other components included, is outside for $`C`$; a component nested in
$`C`$ is inside.

**Frames and whose code runs.** Each frame of the calculus carries a ghost
tag, the name of its innermost component. A frame *runs the code of* $`C`$ when
its innermost component is $`C`$ or nested in $`C`$. A step runs code that
is not $`C`$'s when its frame does not run $`C`$'s code: a call whose
callee's innermost component is outside $`C`$, outside every component
included, and is no audited native. $`C`$'s code never suspends (*No
suspension*, below), so every run of such code is inside a call of $`C`$
that stays active until it returns. A callback that an entry calls is code
that is not $`C`$'s, and its steps are its own.

**Analyzed is a separate fact.** Whether code is inside $`C`$ and whether
TScert analyzes it are independent. Analyzed code outside $`C`$ is checked,
not trusted (*Views in analyzed code*); only code TScert never sees relies
on the trust row.

**Members.** The members $`M_C`$ are $`C`$'s functions reachable from
outside $`C`$: the entries, every method of a class the interface names,
every function of $`C`$ used as a value given to code that is not $`C`$'s
(a result, an argument of a call of such code, a value thrown, the content
of storage such code reaches).

**Several components.** A fact rests on one component's rule: across a
step that runs code outside $`C`$, the rule for $`C`$ bounds the locations
of $`R_C`$. A fact whose support needs two components' regions relies on
both rules, each bounding its part; for $`D`$ nested in $`C`$, a step
outside $`C`$ is outside $`D`$ too, so both bound it, and a step inside
$`C`$ and outside $`D`$ only $`D`$'s.

**Read-only types and crossings.** A type is *read-only* as private
representation defines it ("Read-only types and views"); a sealed handle's
type is read at its representation, every position of it read-only. A value
*crosses* when it passes between $`C`$ and code that is not $`C`$'s, in
either direction, through any alias: an entry's argument, receiver or
result; an argument or result of a call of code that is not $`C`$'s, a
callback's included; a value thrown, caught or yielded; a function of
$`C`$ given out, and what it later receives and returns; the content of
storage both sides reach. This one definition is the rule's and the trust
row's. A crossing *reaches* every location reachable in the heap from the
crossing value through every own field, those its type does not mention
included. The crossing value sits at the *root position*, the position of
the crossing (the parameter, the result, the callback's argument), whose
type is the crossing's type; each field, element or index position below
it has the type the crossing's type gives it there, and an own field the
type does not mention has type `unknown`, read-only. A location is reached
*read-only* when some path to it passes a position whose type is read-only
throughout (every storage position it reaches read-only); from that
position on, every position is read-only, so no read-only location reaches
a writable one. A location every path reaches without passing such a
position is reached *writable*.

**Protection, one predicate per location.** Protection is decided for each
location on each path, by the location's own origin (an exposed site, a
released site, outside storage) and the direction of the crossing that
reached it read-only:
- a location of an exposed site that any crossing reaches read-only is
  protected from that crossing on;
- a location of a released site or outside storage is protected only when
  a crossing *into* $`C`$ (an entry's argument or receiver, a
  callback's result, a caught value) reaches it read-only, and then while
  $`C`$ holds it, or holds a location it is reachable from, or while
  it is recorded in a set of $`A_C`$; a crossing *out of* $`C`$ (an
  entry's result, a callback's argument, a value thrown) protects none,
  whatever position it leaves at.

The decision is per location: an exposed handle that holds a
caller's array gives the array no lasting protection, and a released
wrapper given out read-only still protects an exposed child it holds. In
`{ readonly a: readonly number[]; b: number[] }` with one array under both
fields, the array is reached read-only through `a`, and the row
forbids changing it through `b` too, since the pass cannot see the alias in
an incoming value. This one predicate, read at the current state, gives
the region, the marks, confinement and the trust row.
Two examples:
- a `LayoutLineRange` given to `onLine`, `{ width: number; start:
  LayoutCursor; end: LayoutCursor }` with writable fields: its type is not
  read-only, so the record and its cursors are reached writable, storage of
  released sites, and it protects nothing;
- `{ readonly box: { xs: number[] } }`: the root position's type is not
  read-only, nor is `box`'s, `{ xs: number[] }`, so `box` and `xs` are
  reached writable and the crossing protects nothing. A walker that holds `xs`
  keeps no fact of it across the caller's code.

**Marks, one per allocation site and component.** Each allocation site of
$`C`$'s code, a nested component's sites included, carries a mark for
$`C`$, $`\mu_C`$, a component of the allocated location's contract fixed at
allocation, as private representation's owning mark is. A site of a
component $`D`$ nested in $`C`$ carries a mark for each: an array $`D`$
gives out to $`C`$'s code at a writable type is released for $`D`$ and may
be local or exposed for $`C`$:

- *local*: its storage is held only by frames of $`C`$ (locals, and
  arguments of calls by name), never stored into storage or a binding of a
  module or closure, and never reachable from a crossing value;
- *internal*: its storage may be held by bindings or storage of $`C`$, and
  is never reachable in the heap from a crossing value;
- *exposed*: its storage may be reachable from a crossing value, at
  read-only positions only;
- *released*: some path of a crossing may reach its storage without
  passing a read-only position.

Exposure is by that reachability: every location a crossing reaches, a
handle's representation fields included, is of an exposed or released
site. The front
proposes each site's mark and the pass checks every crossing and every
store against it; a forged mark fails a check (conjectured).

**The exposed locations.** $`E_C`$ is a ghost component of the state: the
locations of exposed sites that a crossing has reached read-only, from the
crossing on. It only grows. It records which exposed locations outside code
can reach, which (P2) and the row read, and decides nothing of the region,
which holds every exposed location, crossed or not. A released or outside
location is protected only through a live incoming read-only crossing: one
that reached it read-only, while $`C`$ holds it, or holds a location
it is reachable from, or the location is recorded in a set of $`A_C`$. A
writable argument $`C`$ holds is not protected. Storage protected at a run's
entry stays protected until that run ends. A key of a `WeakMap` is no hold:
the two confined `WeakMap`s pretext keys by handle (`line-text.ts:11`,
`rich-inline.ts:1156`) protect nothing, and no fact relies on them, since a
value read from a confined collection gets no invariant (*The invariant at
use*).

**The history.** $`A_C`$ is a ghost component of the state: the stack of
the active calls of $`C`$, each with the set of every released or outside
location protected at some state of that call, each location itself, not
one a path starts from, together with the record $`B_C`$ of the released
and outside locations an incoming read-only crossing reached that $`C`$ still holds while no call of it runs. Its transitions: a call's
entry pushes a set holding the locations protected at entry, those of
$`B_C`$ among them when the call is outermost; at an outermost call's exit
$`B_C`$ becomes the locations of its set that $`C`$ still holds, and
a location leaves $`B_C`$ when $`C`$ stops holding it; a step that makes a location
protected (an incoming read-only crossing, a hold of a location so reached
or of one it is reachable from) adds that location, and every location
then protected through it, to the set of every active call, so the sets of
overlapping calls grow together; a call's normal and exceptional exits pop
its own set, and nothing else removes a location from a set. A released or
outside location is protected at a state exactly when a live incoming
read-only crossing protects it, held or recorded in a set of $`A_C`$ or in
$`B_C`$. Two states with the same heap and the same holds differ in
$`A_C`$ where an active call overlapped an earlier hold, and in $`B_C`$
where one array $`C`$ holds came in read-only and another came in
writable; the protection, the region and the action read both.

**The protected region.** $`R_C(\rho,h,A)`$ is the storage of local and
exposed sites, crossed or not, and the released and outside locations a
live incoming read-only crossing protects at the state, held or recorded in
$`A`$. This is the one membership test, used alike in *At a callback*,
(P2), (L3), the region and the row.
Reachability runs through fields, spines and element cells, stopping at
collections, whose entries the model holds in no location (cited:
[native footprints](../SOURCE-CONTRACTS.md#native-footprints), the row of
`Set` and `Map`). Internal storage is outside it: no handle reaches it. Its parts are one per allocation site of $`C`$, kind
and field key, and one per kind and key for storage outside code allocated:
$`R_s.\mathsf{spines}`$, $`R_s.\mathsf{cells}`$, $`R_s.k`$ for a site
$`s`$ and a key $`k`$, and $`R_{\mathrm{in}}`$'s alike.

**Possible sites.** The flow propagates, for each reference, the sites it
may come from. A value entering $`C`$ in a crossing (a member's argument or
receiver, a result of code that is not $`C`$'s, a caught value) may come
from every exposed and released site and from $`\mathrm{in}`$, whatever its
type: TypeScript admits a read-only view where a writable type is expected
(cited: private representation, "Incoming values", observed under `tsc`
7.0.2). A value from a confined collection may come from the sites inserted
into it.

**The protocol.** $`\Psi_C`$ has one entry per part. It is the least such
effect for which every member $`m\in M_C`$, entered from code that is not
$`C`$'s (its parameters at the possible sites of an entering value), and
checked with each of its steps that run code that is not $`C`$'s bounded on
$`R_C`$ by $`\Psi_C`$, has normal and exceptional effects that, after
`fresh_eff` drops the locations it allocated, bound every location of
$`R_C`$ of its entry heap by $`\Psi_C`$. A write at key $`k`$ is charged to
$`R_s.k`$ for each site $`s`$ the written object may come from whose records
may have $`k`$. A site's keys are every key a record of it may have: those
its allocation gives it and every key a write of $`C`$ may add to a
record that may come from the site, by the flow of possible sites, so the
text handle's site has `segments` and `kinds`, stored after its allocation
(`prepare.ts:639`, `layout.ts:150`). A record of a released site, which
outside code may extend, and outside storage may have any key. A write to an internal site
is not charged. A member that writes only what it allocated contributes
$`\mathsf{keep}`$. A call by name is checked at the callee's effect on its
actual arguments, not through $`\Psi_C`$.

**The bound on $`R_C`$.** $`\Phi\oplus_C\Psi_C`$ bounds the locations of
$`R_C`$ by $`\Psi_C`$ and every other location by $`\Phi`$:

```math
h\xrightarrow{\Phi\oplus_C\Psi_C}_\rho h'\iff h\xrightarrow{}_\rho h'\ \wedge\ \forall l<|h|.\ h'(l)=h(l)\ \vee\ \exists (r:\delta)\in(\text{if } l\in R_C(\rho,h) \text{ then } \Psi_C \text{ else } \Phi).\ l\in r(\rho,h)\wedge\delta_{|h|}(h(l),h'(l))
```

**A handle's invariant.** $`I_H(o,h)`$ is the `@invariant` of a sealed
handle type $`H`$ or of a record type, with `this` read as $`o`$;
$`\mathrm{supp}(I_H)`$ is its support.

### Read-only frame

```math
\frac{c:\Phi\mid\Phi^{e}\qquad c\ \text{runs code that is not}\ C\text{'s}}
     {c:\ \Phi\oplus_C\Psi_C\ \mid\ \Phi^{e}\oplus_C\Psi_C}\ \textsf{(Read-only frame)}
```

An unknown callback, of effect $`\top`$, has by the rule the effect
$`\Psi_C`$ on $`R_C`$. A call naming a function of $`C`$ is checked at
that function's certified effect; an audited native keeps its audited
effect, and each call of a callback it makes is bounded by the rule.

**At a callback.** Let a walker hold $`F`$ with a support $`S`$ and
$`\Psi_C\triangleleft_K S`$. The frame applies where the pass shows $`S`$
inside $`R_C`$ by the one membership test: every possible origin of each
object a path of $`S`$ reads is a local or exposed site, or a released or
outside location a live incoming read-only crossing protects. A record $`C`$ received
at a writable type and passed on internally has no such origin, and its
facts do not cross. Tolerant frame then gives
$`K\wedge F\vdash\Box_{\Phi\oplus_C\Psi_C}F`$, and Reliance carries $`F`$
across every step that runs code that is not $`C`$'s, given rigidity
((L3)). In the example `prepare` writes only what it allocates and `walk`
nothing, so every entry of $`\Psi`$ is $`\mathsf{keep}`$, and $`i<|w|`$
crosses `visit` (conjectured, the design's claim).

**At a handle's entry.** A parameter of a sealed handle type meets its
invariant: from an analyzed caller by `invariant-requires`, checked at the
call from the caller's own facts, and from an outside caller by the row on
handle parameters. A cast to the representation gives its fields
(handle-meaning). The handle crossed at its read-only type, so its storage
is in $`R_C`$ from entry.

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

- **(P2) Confinement.** Every path from a frame of code that is not $`C`$'s
  to a location of a local or exposed site reaches it only through a
  location of $`E_C`$, through read-only positions: a local location, and an
  exposed one not yet in $`E_C`$, are reachable from no such frame. Paths run through
  fields, cells, spines and element cells; a closure's environment is not
  reachable from a holder of the closure. From the
  [confinement check](#the-checks-the-rule-requires) and the marks.
- **(M) Marks.** Every location's mark is its site's, fixed at allocation;
  a location of a local site is reachable from no binding, no storage and no
  frame but $`C`$'s; a location of an internal site is reachable from no
  crossing value.
- **(L1) Outside step.** From a state meeting (P2) and (M), a step of code
  that is not $`C`$'s leaves unchanged every location of $`R_C`$, local and
  exposed sites and the storage protected in the current run, and keeps
  (P2) and (M). A local location is out of its reach; a protected location
  it reaches only through a read-only crossing, and the
  [trust row](#trust) states it changes none. Outside code TScert
  analyzes meets this by its checks (*Views in analyzed code*); for the rest,
  (L1) is conjectured from the row, stated in $`C`$'s API, which is trust:
  it holds of outside code that meets the row, and of
  no other.
- **(L2) Outside run.** A run of code that is not $`C`$'s from a state
  $`(h,A)`$, inside a call $`c`$ of $`C`$ active in $`A`$, changes each
  location of $`R_C(h,A)`$ within $`\Psi_C`$. Every released or outside
  location protected at $`(h,A)`$ is in $`c`$'s set or one below it; the
  run's transitions push and pop only above $`c`$'s set and only add to the
  sets, so each such location stays in a set of every later state until
  $`c`$ returns,
  $`R_C(h,A)`$ stays inside the region of every later state of the run, and
  (L1) holds at each outside step. By
  induction on the budget $`k`$: the run changes $`R_C`$ only inside
  members and entries called, each bounded by its
  certificate at $`\Psi_C`$, whose own steps that run code that is not
  $`C`$'s are bounded by the rule at a smaller budget.
- **(L3) Rigidity.** The action relates states with their histories:
  $`(h,A)\xrightarrow{\Phi\oplus_C\Psi_C}_\rho(h',A')`$ when the heaps are
  so related, with regions read at $`(h,A)`$, and $`A'`$ has the calls of
  $`A`$ from the bottom to the current one, each set of $`A'`$ containing
  that of $`A`$. The relation on histories is transitive: a nested call's
  entry pushes above the current set, its steps only add to the sets, and
  its exit, normal or exceptional, pops only its own set, so the sets from
  the bottom to the current call only grow across it, and composition of a
  call's two exits with what follows carries the relation. For every pair of the
  action within a call of $`C`$, $`R_C(h,A)\subseteq R_C(h',A')`$: the part
  of local and exposed sites is fixed by marks at allocation; every released
  or outside location protected at $`(h,A)`$ stays in a set of $`A'`$; and $`\Psi_C`$ preserves
  the references (*Reference-preserving protocol*), every reference held in
  $`R_C(h)`$ held in $`R_C(h')`$ and every listed cell listed, by induction
  on the length of the path. So for $`h\to h'\to h''`$ within the call, a
  location of $`R_C(h)`$ is in $`R_C(h')`$ and both steps bound it by
  $`\Psi_C`$; a location outside $`R_C(h)`$ that enters $`R_C(h')`$ is
  bounded by $`\Phi`$ in the first step and by $`\Psi_C`$ in the second.
  Then
  $`\Phi\oplus_C\Psi_C`$ is rigid when $`\Phi`$ and $`\Psi_C`$ are rigid and
  $`\Psi_C\sqsubseteq\Phi`$, as for $`\Phi=\top`$ and for
  `{ values: "any"; spines: "grow" }`.
- **(L4) The handle invariant across a run.** The protocol carries, beside
  $`\Psi_C`$, a guarantee $`G_C`$: the invariants every member keeps, at
  every write to their support and on both of its exits, each write checked
  (*Tolerant invariant*). The change $`\mathsf{scalar}`$ alone does not give
  them: it lets `sourceStarts` go from `null` to a list of any length. A
  fact $`I_H(o)`$ that holds where a walker relies on it, with
  $`I_H\in G_C`$ and $`\mathrm{supp}(I_H)`$ inside $`R_C`$ there, holds
  after every step that runs code that is not
  $`C`$'s: by induction on the run as in (L2), each member's writes and
  exits keep it by $`G_C`$, its calls of code that is not $`C`$'s keep it by
  the induction, and every outside step changes no location of its support
  (L1). The write check of $`G_C`$ is *Tolerant invariant*'s, over complete
  handles as that check defines them: a list a member makes and stores in a
  handle that existed at its entry is checked at every later write, so the
  write that shortens it is refused. It holds at an entry by the
  row on handle parameters, which is trust, for a handle an outside caller
  passes.

`SourceClaimJson.PassUnit.mode8Accepted_sound` keeps its statement; the
premise and conclusion of `PassUnitSafe` are reviewed again, as a change of
the accepted plan type requires.

## The checks the rule requires

Each is chosen by the behaviour it excludes, documented in
SOURCE-FRAGMENT.md, enforced at the source boundary, and has a control
([negatives and controls](#negatives-and-controls)).

- **Reference-preserving protocol.** Every entry of $`\Psi_C`$, on every
  part, preserves the references: in each pair of its action, every
  reference to storage held at a location of the part is held at a location
  of $`R_C`$ of the exit heap, and every cell a spine or view spine lists
  stays listed. The entries that meet it are private representation's:
  $`\mathsf{keep}`$; $`\mathsf{scalar}`$ on a cell or at a key; an extension
  on a spine. The parts of released sites are bound too, since released
  storage enters $`R_C`$ when it crosses back at a read-only position: an
  entry that shortens an array it gave out at a writable type is refused. A
  `pop` charged to $`R_C`$ is refused (WORK, "Shrinking owned arrays").
- **Tolerant invariant.** A handle is *complete* when it existed at the
  member's entry or has crossed; a record the member is still building is
  free until its introduction's `invariant-ensures`. Every change a member
  makes to a location of $`\mathrm{supp}(I_H)`$ of a complete handle,
  storage the member allocated in the same call included once it is
  installed there, and every entry of $`\Psi_C`$ on such a location, is one
  $`\mathrm{supp}(I_H)`$ tolerates, or one write checked to keep $`I_H`$.
  This is the condition (L4) uses. An invariant that one write breaks and a
  later write restores is refused.
- **Confinement.** No location currently protected, by the predicate at
  the crossing's state, and no storage of a local site crosses at a
  writable position: a return, an
  argument of a call of code that is not $`C`$'s, a `throw`, a store into storage outside code reaches, each at a type
  whose position for that storage is writable, is refused. A copy is
  storage of a fresh site, and separates only where its element type holds
  no storage.
- **Incoming values.** Every write $`C`$ makes to a value entering in a
  crossing, or to anything reached from it, is charged at its key to every
  exposed and released site and to $`R_{\mathrm{in}}`$, whatever the value's
  type, and meets *Reference-preserving protocol* and *Tolerant invariant*.
  By (M) it is never charged to a local or internal site.
- **Confined collections.** A collection held only by bindings or storage
  of $`C`$, and never crossing, is *confined*; one that is not confined
  holds no storage of $`R_C`$. Insertion into a confined collection is a
  write of $`C`$, checked as a store, and preserves each value's possible
  sites; a lookup yields the sites inserted. No outside code reaches a
  confined collection, and every write $`C`$ makes to protected storage from
  it is charged.
- **Writes outside code may make fail.** The row admits freezing, sealing,
  preventing extension and making a data property non-writable or
  non-configurable. A write by $`C`$ to storage outside code may have made
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
- **Views in analyzed code.** Analyzed code outside $`C`$, a client,
  is checked, not trusted, for the row's obligation through every alias: a
  value it reads at a read-only type is read at a readonly view, and the
  pass refuses a write through it, a write through a writable type it was
  widened to included (cited: private representation, "Views in analyzed
  code"); and every write a client makes, and every callback effect it
  passes to $`C`$, stated or certified, is checked against all the
  storage currently protected that the client may reach, through every alias:
  storage it passed at a read-only position in an earlier call included, as
  in `remember(xs)` and then `walkSaved(visit)` with `visit` truncating
  `xs`. A client cannot know when $`C`$ drops a reference, so for it
  storage it passed at a read-only position stays protected from then on.
  Each such write, and each such callback effect, is checked within the
  component's client obligation $`\Theta`$ (*Other encapsulations*), as a
  callback's body is checked against its stated `Modifies` effect; for a
  read-only type, $`\Theta=\{\}`$ admits none. $`C`$'s own write to storage it gave out
  as a view is a *representation write*: through a cast of the handle to its
  representation, checked against the representation's type, its invariant
  (*Tolerant invariant*), the throw edge of *Writes outside code may make
  fail*, and charged at its key to every possible site of the written
  object.

- **Ownership of installed storage.** Private representation's
  *Ownership at construction*, restated for $`R_C`$: a write of $`C`$ that installs storage into a location of protected storage, or
  into a location the support of an invariant in $`G_C`$ or of a framed
  fact reads, stores storage protected for the rest of the run, and so
  does every location that support reads through the installed storage,
  not its outermost object alone. Admitted: storage of an exposed site, by
  its mark, which *Confinement* then refuses to let cross at a writable
  position, in either order, before the install or after it; an unconfined
  copy made in the call, itself of an exposed site; storage already
  protected. Fresh storage of a released site is not admitted: `install2`,
  which allocates `[7]`, installs it and returns it at `number[]`, and a
  member that gives a fresh `[7]` to a visitor at `number[]` and then
  installs it, are refused. A typed array over a buffer $`C`$ did not
  allocate is not fresh: its elements are the buffer's owner's. A caller's
  writable argument is none of these: an entry
  `install(xs: number[])` storing the visitor's own `[7]` in a handle whose
  invariant reads it is refused unless it copies. Pretext's entries meet it
  (by reading them): `prepareRichInline` stores of its items only their
  strings and numbers (`text`, `font`, `letterSpacing`, `break`,
  `extraWidth`, `rich-inline.ts:57–64`), and the options of `prepare`,
  `prepareWithSegments` and `prepareRichInline` are strings and numbers.
- **Reads through a possibly null value.** A read `e![k]` or `e!.f` whose
  operand's type admits `null` or `undefined` is the read of `e`: the `!`
  is erased, as TypeScript erases it, and the operand, held in a slot,
  reaches the existing lowering of a member of `null` or `undefined`,
  `nullishSplit` and `nullishGuard`, which throws a `TypeError` where it is
  nullish (cited: [members of primitives and nullish values](../PROGRAM-TYPING.md#members-of-primitives-and-nullish-values), "A member of `null` or `undefined`").
  No new step: the read throws as JavaScript's does, and a throw is an
  allowed outcome.
- **No suspension.** The rule applies to a component whose code never
  suspends: no `await`, no `yield`, no async function and no generator in
  the analyzed sources of a component whose handles it protects. Its reason:
  a suspension returns the call to its caller while its frame lives on, so
  no call stays active through the run that follows, and (L2) and (L3),
  which bound that run by an active call's history, do not cover it. An
  entry that reads `saved.widths`, awaits while the caller clears `saved`
  and truncates the list, and reads on, reads `[1, undefined, undefined]`
  (observed). In refusal-index terms: "An `await`, a `yield`, an async
  function or a generator in a component whose handles Read-only frame
  protects", its owner this draft, refused at the source boundary; its
  control `readonly-suspending-package-refused`. Pretext's `src` has none
  (observed: `git grep` at `0d102a5c` for `async`, `await`, `yield` and
  `function*` finds none outside the tests). Lifting it is open work
  ([WORK](../../WORK.md#status), "Read-only frame across a suspension").

## Trust

One new row of the [trust surface](../DESIGN.md#trust-surface), per
component, an assumption about code outside the component that the
analyzed sources do not include, of the kind of the rows
on exported preconditions and on a callback's stated effect (a stand-in
until applications are analyzed too). Its basis is the maintainer's
decision for the whole codebase (cited: upstream `RESEARCH.md`, Decisions
Log, "2026-10-06: the library is written for well-typed TypeScript, and
checks no argument's type at runtime", line 5886): a caller the types rule
out "gets whatever the code does with it". The row is that assumption made
exact where TypeScript leaks, at a read-only type widened to a writable
one, a cast and `any`; upstream already tells callers to copy a read-only
array before changing it (cited: `CHANGELOG.md:15`).

> Code outside a component $`C`$ whose API states this row enters $`C`$
> only through $`C`$'s interface; code that enters it otherwise is outside
> this row. That code, when TScert does not analyze it, a function it passes
> in included, changes by its own steps, by any operation, a native's
> included, beyond the client obligation $`\Theta`$ that $`C`$'s exported
> type states (`@clients`, read-only by default: no element, field or
> length changed, no field added or removed, and no prototype or property
> kind, a data property redefined as an accessor, changed) storage
> reachable in the heap from a value that crosses
> between it and $`C`$ in either direction, through any alias (an entry's
> argument, receiver or result, a callback's argument or result, a value
> thrown, caught or yielded, a function $`C`$ gives out and what it receives
> and returns), from the first position on the path whose type is read-only
> throughout (every field, element and index position it reaches
> read-only), an own field the type does not mention counting as read-only,
> decided per location: storage $`C`$'s code allocated at a site exposed for
> $`C`$, from the crossing on, whichever direction it crosses; storage of a
> site released for $`C`$, and storage code outside $`C`$ allocated, only
> where a crossing into $`C`$ reached it, and then while $`C`$ holds a
> reference to it or to storage it is reachable from and until every call
> of $`C`$ running while it did returns; a crossing out of $`C`$ protects no
> such storage. Each step is the code's that executes it, by its frame's
> innermost component: a change made inside a call of an entry of $`C`$, or
> of a function $`C`$ gave out, is that function's, bounded by its
> certificate, and a step of a callback an entry calls is the callback's.
> Freezing, sealing, preventing extension and making a data property
> non-writable or non-configurable are admitted unless $`\Theta`$ keeps the
> integrity attributes.

The row is stated per component, in that component's API, and applies only
to a component whose API states it. Its parameter $`\Theta`$, the *client
obligation*, is an effect in Paper I's change lattice bounding what code
outside $`C`$ that TScert does not analyze may do to $`C`$'s protected
storage. With it, the rule's bound on a callback on $`R_C`$ is
$`\Psi_C\sqcup\Theta`$, and a fact survives a call of code that is not
$`C`$'s when $`\Psi_C\sqcup\Theta`$ respects its support; an invariant in
$`G_C`$ is framed only where $`\Theta`$ respects its support too. For a
component whose API does not state the row, the rule holds only where all
code outside it is analyzed, which *Views in analyzed code* checks. For
pretext, $`C`$ is its package, its interface the modules `package.json`'s
`exports` names, `.` and `./rich-inline`; its API states the row with
$`\Theta=\{\}`$, read-only; the demo and any other analyzed code around
it is outside $`C`$ and checked.

### Other encapsulations

**The annotation.** $`\Theta`$ is written in TScert's existing effect
language: the protocol `P` of `Modifies<P, T>` (cited:
[`Modifies<P, T>`](../ANNOTATIONS.md#types-the-verifier-declares),
[stated effects](../SOURCE-ELABORATION.md#stated-effects)), a type literal
of class keys (`values`, `spines`) and path keys, each at a change. It is a
JSDoc tag on a type the component exports, `@clients P`, its path keys read
from `this`, the value at that type, and it bounds storage reached
read-only from a value crossing at that type. A read-only type is shorthand
for `@clients {}`, so pretext's instance is unchanged:

```ts
/** The obligation on its callers, in the caller-facing words of Trust.
 *  @clients {}
 *  @invariant this.segmentFlags.length === this.widths.length
 *  @representation InternalPreparedText */
export type PreparedText = { readonly [preparedTextBrand]: true }
```

with the same `@clients {}` on `PreparedTextWithSegments` and
`PreparedRichInline`.

**The restriction.** $`\Theta`$ must preserve references, the restriction
*Reference-preserving protocol* puts on $`\Psi_C`$, since (L3)'s rigidity
needs it of $`\Psi_C\sqcup\Theta`$: each entry is $`\mathsf{keep}`$,
$`\mathsf{scalar}`$ on a cell or at a key, or an extension on a spine. Paper
I's change lattice $`\mathsf{keep}\sqsubseteq\mathsf{init}\sqsubseteq\mathsf{scalar}\sqsubseteq\mathsf{grow}\sqsubseteq\mathsf{any}`$
names no extension-only change: $`\mathsf{grow}`$ may replace a listed cell
by a fresh one. The extension `push` gives exists only as its audited
contract (Lean `ReceiverAppends`, the kept prefix). So the lattice gains
one change, $`\mathsf{extend}`$, between $`\mathsf{keep}`$ and
$`\mathsf{grow}`$ on spines: the old spine is a prefix of the new. It is
added once, and serves $`\Psi_C`$ and $`\Theta`$ alike; in a protocol it is
spelled `"extend"`. The integrity attributes (extensible, writable,
configurable) are one more key, `integrity`, at `"keep"` or `"freeze"`
(changes toward frozen only, which preserve references); read-only's
shorthand admits `"freeze"`, as the row does.

**The checks.**
- Analyzed client code is checked against $`\Theta`$: each write it makes,
  through any alias, to storage it reached through a crossing at the
  component's type lies within $`\Theta`$, by the check a callback's body
  gets against its stated `Modifies` effect (*Views in analyzed code*).
- The bound on a callback is $`\Psi_C\sqcup\Theta`$ on $`R_C`$.
- A fact survives when $`\Psi_C\sqcup\Theta`$ respects its support.

**The instances.** Each is supported; each example and negative is
observed under Node:
- **Read-only**, `@clients {}`: pretext's instance.
- **Grow-only**, `@clients { "this.items[*]": "extend" }`: a client may
  append to a handle's `items`, as `push` does. A walker that caches
  `items.length` keeps $`i<|\mathit{items}|`$ across a visitor that
  appends: it reads `[1, 1, 1]`. Negative: a client that pops, outside
  $`\Theta`$, makes it read `[1, undefined, undefined]`; refused at the
  client's write where the client is analyzed, and a client breaking the
  row where it is not.
- **Freezing kept**, `@clients { integrity: "keep" }`: no client changes the
  handle's integrity attributes, so a write of the package to it cannot
  fail by a freeze and needs no throw edge for one. A package that writes a
  cache inside a `try` and reads it after relies on the write: it reads
  `5`. Negative: a client that freezes the handle, outside $`\Theta`$, makes
  the write throw, the `catch` go on and the read give `undefined` at type
  `number`; refused at the client's freeze where the client is analyzed.
- **Not read at all** is no instance of $`\Theta`$: a read changes no
  location and so bounds no fact's support; it concerns information hiding
  and representation independence, which are outside frames.

**An obligation of the implementation.** ANNOTATIONS.md will need an entry
`@clients P`: "On a type a component exports: code outside the component
that TScert does not analyze changes storage reached read-only from a value
at this type at most as `P` says, `P` a `Modifies` protocol with path keys
read from `this`, its changes preserving references; a read-only type is
`@clients {}`." The entry, the `"extend"` change and the `integrity` key
are added with their implementation, `tests/docs.mts` checking the
annotation list.

The row covers own fields the crossing's type does not mention: a value
crossing at `{ readonly n: number }` whose own field `extra` holds an array
protects that array. It uses the path predicate of the definitions: a
`LayoutLineRange` given to `onLine` protects nothing, and
`{ readonly box: { xs: number[] } }` protects neither `box` nor `xs`.

Where it is stated: in the API, in the doc comment of each handle type the
entry modules export, and in the package's documentation, for pretext the
README's section "Callers' obligation", naming `.` and `./rich-inline`.
The row is in the proof's terms, which a caller cannot read: it can tell
neither a site's mark nor what the package holds. The API states the
obligation in what a caller observes, at least as strong as the row:

> Code outside this package uses it only through `@chenglou/pretext` and
> `@chenglou/pretext/rich-inline`, the modules its package.json exports
> names, and the library is written for well-typed callers. Never change,
> through any alias, anything you reach in a value this package gives you
> only through a part its type shows read-only or a field its type does not
> show: a handle and everything in it, and the read-only members of a
> `prepareWithSegments()` handle (copy one before changing it). The cursors
> of a range, line or fragment this package gives you are yours to change,
> since it gives them out writable; anything you are already obliged not to
> change stays so, whatever alias you reach it through. Change nothing,
> through any alias, that you passed the package through a part of the
> parameter's type that is read-only or a field that type does not show, nor
> anything you return to it from a callback through such a part, while any
> call into the package is running, the one you passed it to or one that was
> already running then; no entry of this package keeps a value you pass it,
> so the obligation ends when all of them have returned. This holds in your
> code and in every function you pass in. No element, field or length of
> such storage changes, no field is added or removed, and no prototype or
> property kind (a data property redefined as an accessor) changes, by any
> operation. Freezing, sealing, preventing extension and making a data
> property non-writable or non-configurable do not break this obligation;
> for a handle, `Object.freeze()` of it or of its objects and arrays is
> supported, and a deep freeze throws at the typed array it holds.

It is at least as strong, by the per-location predicate in both
directions: what the package gives out protects only exposed storage, which
the text forbids changing for good, unmentioned fields and read-only parts
inside writable results and callback arguments included, while the cursors a range, line or fragment carries are
released, given out writable, and the caller's, and an obligation a
caller already has survives any other alias of the same storage; what a
caller passes is protected by the row while the package holds it or a call
that ran while it did runs, which the text covers by "while any call into
the package is running, the one you passed it to or one that was already
running then", so a structured clone passed to `layout()` inside a walk's
visitor stays protected until the walk returns; read-only parts inside writable arguments and unmentioned fields
included, and pretext holds a passed value after its call only as a
`WeakMap` key, which is no hold. "Through any alias" covers a change made
through a binding the caller kept from an earlier call. Freezing and the
other attribute changes are what the row admits and the proof tolerates;
the text says they do not break the obligation, not that pretext supports
them: its rule is "Don't deep-freeze a handle" (cited: `CHANGELOG.md:19`),
`Object.freeze()` of a handle, or of its objects and arrays, being
supported and a deep freeze throwing at its typed array (`CHANGELOG.md:63`;
Decisions Log, "2026-10-12: no line function writes to a frozen handle or
to anything it holds", line 6317). TypeScript does not establish it: its `readonly` constrains only the written
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

A handle frozen with `Object.freeze()`, or whose record and arrays are
frozen, lays out as before; a deep freeze of a `prepareWithSegments` handle
throws a `TypeError` at its `Uint8Array`, upstream and edited alike
(observed under Bun: "Attempting to store non-configurable property on a
typed array"), as upstream documents (`CHANGELOG.md:19`, `:63`); a write to
a frozen object throws in strict code (observed); upstream's side table for frozen
paragraph handles (`rich-inline.ts:1141–1178`) stays, analyzed as written.

## Pretext

Pretext is one instance of the rule. $`C`$ is pretext's package; its
interface is `package.json`'s `exports`, assumed by the trust row its API
states; its five modules are components nested in $`C`$, and its facts
rest on $`C`$'s rule alone. The demo and any application around it are
code outside $`C`$: where TScert analyzes them, they are checked (*Views in
analyzed code*); where it does not, they rely on the row. Below, "the
package" is $`C`$.

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
  row excludes it. Read by the path predicate, the 17 signatures and the
  types they name (by reading them): the three handle types are read at
  their representations, read-only throughout, so each handle's storage is
  reached read-only from the handle; the `PreparedTextWithSegments` members
  are `readonly` arrays and `ArrayLike<number>`, also read-only; every other
  value at a read-only position is a number or a string; the types that are
  not read-only (the items `prepareRichInline` takes, the `LayoutCursor` a
  stream takes, the results and callback arguments `LayoutLine`,
  `LayoutLineRange`, `RichInlineLine` and the rest) reach only storage of
  released sites or outside storage, and no protected storage of the
  package, as the `LayoutLineRange` example shows. One result carries
  more than its type states: the `RichInlineLine` that
  `materializeRichInlineLineRange` returns holds, in each fragment, the
  `start` and `end` cursors of the range it was given (`rich-inline.ts:1227–1228`),
  fields `RichInlineFragment` does not mention, by upstream's decision
  (Decisions Log, 2026-10-10, "the line to pass back is the range it was
  materialized from"). A range the walk or the stream gave holds cursors
  pretext allocated (`:934–935`, `:1007`, `:1039–1040`), given out in the
  range at `LayoutCursor`, a writable type: storage of released sites. Given
  out again in the fragments, at an unmentioned field, they are not
  protected, since a crossing out of the package protects only exposed storage.
  Passed back in a range at `RichInlineLineRange`, a writable type, they
  are reached writable and are not protected either, so *Confinement*, which
  binds protected storage, is not at stake, and every write the package
  makes to them is charged at its key to the released sites. Materializing
  one range repeatedly, in the walk's visitor and after it, is admitted and
  gives the same fragments (observed under Bun, upstream and edited alike),
  and the aliases are upstream's: passing `range.end` back gives the next
  line, and a change of a range's cursor shows in its fragment (observed).
  Copying them would change what a caller observes. No change.
- **The edits, applied and checked.** The edits below are applied to a
  scratch copy of upstream `0d102a5c` and type-check under its
  `tsconfig.build.json` with its pinned TypeScript, 7.0.2 (observed: no
  error). Upstream's own suite, `bun test src/layout.test.ts`, passes 191 of
  191 on the edited copy (observed, Bun 1.4.2). Together they add 113 lines
  and remove 24 in `README.md`, `layout.ts`, `line-break.ts`, `line-text.ts`,
  `prepare.ts` and `rich-inline.ts`, many of the added lines being the
  obligation in three doc comments and in the README. `oxlint`, which upstream's `check` also runs,
  was not run.
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
  (`:151`, after its write of `kinds` at `:150`, so the record is complete
  when it is cast; the result of `prepareInternal` is held at
  `PreparedSegments & { kinds?: SegmentBreakKind[] }` until then) and `prepareRichInline`'s two returns (`rich-inline.ts:218`,
  `:666`), each a cast through `unknown` at a return whose type names the
  handle. Each is a checked introduction: the cast states no fact, and the
  return's `invariant-ensures` proves the handle's invariant from the
  record's facts (cited: [type invariants](../ARITHMETIC.md#type-invariants),
  "a cast into the handle states no fact, and a boundary requiring the
  invariant proves it").
- **The invariants.** The walkers and steppers take `PreparedLineData` and
  `PreparedSegments`. `@invariant` is stated on:
  - `PreparedLineData`: `segmentFlags.length === widths.length`;
  - `PreparedSegments`, `segments.length === widths.length`. It is an
    intersection naming `PreparedLineData`, so it carries that type's
    invariant too (cited: [type invariants](../ARITHMETIC.md#type-invariants),
    "an intersection with a part naming it");
  - `PreparedTextWithSegments`: both clauses and `kinds.length ===
    widths.length`;
  - the paragraph record and `PreparedRichInline`, as five tags, each a
    clause the clause reader elaborates (observed: each run through the
    pipeline at `b60eca2f` in a probe with the same types, `verified`, and
    load-bearing, a probe without the `sourceEnds` tag being refused at the
    read it supports): `data`'s two clauses; one per lazy list,
    `this.sourceStarts === null || this.sourceStarts.length ===
    this.data.widths.length` and alike, a leading guard; and
    `forall i in this.itemSegments: safeInteger(this.itemSegments[i]) &&
    0 <= this.itemSegments[i] && this.itemSegments[i] <= this.data.widths.length`.
    The clause that `sourceStarts` `null` implies the other two `null` is
    part of the invariant the design states and the lazy write keeps, and
    the clause reader refuses it (observed: "the clause names null, which is
    no parameter"); a null test is a leading guard, not an atom, so it needs
    clause-language support for a cross-field null implication
    ([WORK](../../WORK.md#status), "Cross-field null implications in
    clauses"). Until then it is stated, not checked.

  Each walker's entry then gets them by `invariant-requires`, checked at each
  call by name, and each entry's cast by handle-meaning. The paragraph's
  walkers pass `flow.data` to the text walkers (`rich-inline.ts:1121–1124`,
  `:1252`, `:1266`), which the paragraph's invariant gives. The data clauses
  are proved at the paragraph's two introductions: at `:218` from
  `measureAnalysis`'s overload with segments, at `:666` from the paragraph's
  lists, filled one entry per segment (conjectured until checked). A handle
  from outside meets them by the row on handle parameters, which supplies
  `segments.length === widths.length` at the entry; the lazy writer checks
  only that each destination field is `null`. Six annotation comments, three of them with the obligation, and the
  row in the README's new section "Callers' obligation", which names the
  entry modules `.` (`@chenglou/pretext`) and `./rich-inline`, each in the
  caller-facing words of *Trust*.
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
  arrays). The edited code stays upstream's as far as the invariant allows:
  - *the invariant*, one clause per field: each of `sourceStarts`,
    `sourceEnds` and `sourceUnits` is `null` or as long as `data.widths`,
    `sourceUnits` in its upstream meaning, `null` where no segment has units
    of its own (`:163–172`); and where `sourceStarts` is `null`, so are
    `sourceEnds` and `sourceUnits`. Upstream writes `sourceStarts` first,
    so every state upstream produces, one a throw part way through its
    write leaves included, meets it;
  - *the writes*: upstream's three stores in upstream's order, each guarded
    by its field being `null`. Each writes a `null` field with a fresh list
    as long as `data.widths` ($`\mathsf{scalar}`$), so it keeps its own
    clause alone, and writing `sourceStarts` first keeps the last clause;
    no rollback is needed. On a handle that meets the invariant the guards
    always hold, so the stores are upstream's. Each is an
    atomic store with its throw edge, charged at its key to every possible
    receiver: the paragraph handle's site, $`R_{\mathrm{in}}`$, since a
    structured clone passed back is outside storage, and every released
    site, whose records a caller may extend. The clauses are
    in $`G_C`$;
  - *the side table*: taken for a frozen handle, upstream's condition;
  - *the readers*: the read is upstream's (`:1198–1199`); the two reads of
    `sourceEnds` that need a list (`:1215`, `:1219`) stay upstream's
    `sourceEnds![…]`, which throws upstream's own `TypeError`, with its
    message, where the field is `null` (observed under Bun, upstream and
    edited alike: "null is not an object (evaluating 'sourceEnds[endSegmentIndex - 1]')");
    a throw is an allowed outcome, read by *Reads through a possibly null
    value*. The outer `!`, that the element read gives a number, needs its
    index in range, and that stays a stated gap of the materializer, which is
    no P22 site. The index is `Math.min(first + fragment.end.segmentIndex,
    itemEnd) - 1`, from a range the caller passes at a writable type. The
    `itemSegments` clause bounds `itemEnd` and `first` by
    `data.widths.length`, but the fragment's own indices need a
    precondition, and the clause language states a comparison only of safe
    integers: an `@requires` with `safeInteger` atoms elaborates (observed)
    and excludes upstream's tested range ending at segment `Infinity`
    (`layout.test.ts:356–366`), which the `Math.min` clamp admits. No clause
    states "a safe integer, or `Infinity`", so no `@requires` is added; a
    caller that sets a writable fragment's indices to `-2` and `-1`, or an
    `itemSegments` entry past the widths on a clone, makes both versions
    return `sourceEnd` `undefined` at type `number` (cited: the reviews'
    reproductions), the second outside the invariant. The reads of a
    segment's grapheme ends at a fragment's grapheme index need a bound no
    clause states either (a segment's grapheme count is computed).

  With one of the three fields made non-writable by outside code, which the
  row admits, two materializations of the same line under Bun give the same
  outcomes and the same fields in upstream and the edited copy (observed):
  - `sourceStarts`: `TypeError` twice; all three fields `null`;
  - `sourceEnds`: `TypeError` twice; `sourceStarts` set;
  - `sourceUnits`: `TypeError`, then success; `sourceStarts` and
    `sourceEnds` set, `sourceUnits` `null`, a state the invariant admits.

  Also observed under Bun, against upstream and the edited copy: a
  structured clone of a two-item paragraph `["ab", "cd"]` gives the source
  ranges `[[0,2],[0,2]]` in both; a one-item paragraph handle passed back
  with one segment fewer than its widths makes both install 2 source starts
  for 3 widths; that value is outside the paragraph's invariant, so its
  behaviour rests on the row on handle parameters, and the edits check
  nothing at run time, by the decision of 2026-10-06.

  The difference with writable fields: a handle whose `sourceStarts` is
  `null` and whose `sourceEnds` is set. Upstream overwrites all three; the
  edited copy keeps the stored `sourceEnds`. On a clone of a one-item
  paragraph, two materializations give (observed under Bun):
  - `sourceEnds = []`: `[[0,7]], [[0,7]]` upstream, `[[0,7]], [[0,null]]`
    edited;
  - `sourceEnds` as long as the widths, filled with `42`: `[[0,7]],
    [[0,7]]` upstream, `[[0,7]], [[0,42]]` edited;
  - the same filled with `0`: `[[0,7]], [[0,7]]` upstream, `[[0,7]],
    [[0,0]]` edited.

  Each state is outside the invariant, by its last clause, whatever the
  list's length. Upstream never makes one: a one-item paragraph's three
  fields are `null` until its first materialization, which writes
  `sourceStarts` first, and a multi-item paragraph sets all three at
  preparation (`:663`). Only outside code makes it, so the edited copy's
  behaviour on it rests on the row on handle parameters.

  The changes: the three guards. The length of the lists the writer builds
  is that of `data.segments`, which equals `data.widths`' by the
  paragraph's invariant, supplied at entry by the row on handle parameters;
  the writer checks nothing.
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
  handles hold them (`prepare.ts:525–529`): every write $`C`$ makes to them
  is charged, and preparation copies a cached list before changing it
  (`prepare.ts:533–541`), so none is. `clearCache` (`layout.ts:360–363`)
  clears confined collections and writes a number to the internal state
  record: $`\mathsf{keep}`$ on $`R_C`$. The exported `noExtraSpacings`
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
    (`:359–365`) call no code that is not $`C`$'s between their reads: their
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

In all, checked as above: the README's section and six annotation
comments, three with the obligation; brand-free records, casts through `unknown` and four checked
introductions in `layout.ts` and `rich-inline.ts`; three overloads and a
typed literal in `prepare.ts` and two overloads in `layout.ts`; and the
lazy write's three guards.

The protocol for pretext (conjectured): $`\mathsf{scalar}`$ at the keys
`sourceStarts`, `sourceEnds` and `sourceUnits` of every possible receiver:
the paragraph handle's site, $`R_{\mathrm{in}}`$, and every released site,
whose records a caller may extend with a handle's fields and pass as the
handle (observed under Bun: a range record so extended gets `sourceStarts`
`[0,2,3,4,5]` from materialization, upstream and edited alike), from
`materializeRichInlineLineRange`;
$`\mathsf{keep}`$ on every other part.
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
- **An interface assumed, not enforced.** Pretext's component is its
  package, whose interface, the entry modules' exports, rests on outside
  code importing only those modules, a trust row; there, the component is a
  class body, whose interface the language enforces. Both are components of
  the one rule, drawn differently.
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
  above (113 lines added and 24 removed): no class, no static block, no staging field, no
  `#segments !== null` test, no move of five modules into one class body.
- **No class shape**: no base-class, evaluated-once, construction, staging,
  lexical-dispatch or distinct-name restriction; no lifting of the
  refusal-index rows on classes; no native key-enumeration audit; no trust
  row of the language.
- **Copies kept**: `structuredClone` and `postMessage` copies and handles
  in IndexedDB lay out as before, and a frozen handle as upstream supports
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
  released site, whose storage entered $`R_C`$ at the read-only crossing.
- `invalid-readonly-partial-length`: a function of the package, given an
  array by outside code that made its index 1 non-configurable, assigns
  `length = 0` and, in its handler, reads the last index it read before:
  `undefined`, the length being 2 after the throw. Refused by *Writes
  outside code may make fail*: the assignment's throw edge carries its
  partial deletion, so the handler holds no fact of the old length.
- `invalid-readonly-writable-reach`: an entry takes
  `{ readonly box: { xs: number[] } }`, holds `xs` and caches its length;
  the caller truncates `xs` during the visitor, which the row lets it do:
  `[1, undefined, undefined]`. Refused at the walker's read: by the path
  predicate the crossing protects nothing, `xs` is outside $`R_C`$, and the
  fact of its length does not cross the visitor.
- `invalid-readonly-key-added-later`: `make()` allocates a record with `a`
  alone and then adds `n`; a visitor passes the handle to an entry
  `reset(x: { n: number })`, whose write at `n` is the package's; the
  walker, relying on `n <= a.length`, reads `[undefined, undefined]`.
  Refused by *Tolerant invariant*: the site's keys include `n`, added by
  `make`'s write, so `reset`'s write is charged to it and does not keep the
  invariant.
- `invalid-readonly-install-caller-array`: an entry
  `install(xs: number[])` stores the visitor's own `[7]` in a handle whose
  invariant reads it; the visitor then pops its array, and the walker,
  relying on the invariant, reads `[7, undefined]`. Refused by *Ownership
  of installed storage*: the stored array is neither fresh, a copy, nor
  protected.
- `invalid-readonly-install2`: `install2(h)` allocates `[7]`, installs it
  in a handle whose invariant reads it and returns it at `number[]`; the
  visitor pops what it got: `[undefined, undefined]`. Refused by
  *Ownership of installed storage*: the array is of a released site.
- `invalid-readonly-give-then-install`: a member gives a fresh `[7]` to the
  visitor at `number[]`, then installs it; the visitor kept it and pops it
  later: `[7, undefined]`. Refused by *Ownership of installed storage*, in
  the other order.
- `invalid-readonly-installed-then-shortened`: a member installs a fresh
  list of the right length in an old handle, then shortens it before a
  callback; a walker relying on the invariant reads
  `[0, undefined, undefined]`. Refused at the shortening write by
  *Tolerant invariant*: the handle existed at the member's entry, so it is
  complete, and the write to the list installed in it is checked.
- `invalid-readonly-client-earlier-alias`: an analyzed client passes its
  array to `remember(xs)` at `readonly number[]`, then calls
  `walkSaved(visit)` and truncates the array through its own binding in
  `visit`: `[1, undefined, undefined]`. Refused at the client's callback:
  its effect is checked against storage it passed in an earlier call.
- `invalid-readonly-lazy-wrong-length`: a member's lazy write sets a list
  from `null` to one of the wrong length, within $`\mathsf{scalar}`$; a
  walker relying on the invariant after the visitor calls it reads
  `[0, undefined, undefined]`. Refused by *Tolerant invariant*: the checked
  single write does not keep the invariant, so it is not in $`G_C`$.
- `invalid-readonly-short-segments`: a one-item paragraph handle passed back
  with one segment fewer than its widths; materialization makes upstream
  install 2 source starts for 3 widths (observed under Bun on upstream's
  `src` and on the edited copy), against the lazy-list clause. Excluded at
  the handle's entry by the paragraph's invariant, which no such value
  meets, by the row on handle parameters.


**Positive cases**: the example, its visitor calling every entry
(`[1, 1, 1]`); `readonly-hidden-cursor`, a visitor calling a stepper on
cursors it holds (`[1, 1, 1]`); `readonly-internal-cache-record`, a cache
replacing its fit record while a handle holds the record's list
(`[1, 1, 1]`); `readonly-frozen`, a handle frozen deep by its client
(`[1, 1]`, and a write to it throws a `TypeError`);
`readonly-structured-clone`, a `structuredClone` copy passed back
(`[1, 1, 1]`).

**Positive control**: `readonly-released-back-writable`, a released record
passed in at a read-only type and, after that call returned, passed back at
a writable type and changed by the package (`{"start":2,"end":4}`),
admitted: at the second crossing the record is no longer protected, which
*Confinement* checks at the crossing's state.

**Restriction control**, refused (observed under Node):
`readonly-suspending-package-refused`, the async entry of *No suspension*,
`[1, undefined, undefined]`.

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
a callback argument, so a crossing the row covers; the package keeping an
outside array in a binding, a visitor calling an entry that clears the
binding, the package's last reference, and then truncating the array
(`[1, undefined, undefined]`), during the run of `walk`, a call of the
package running while the package held the array, which the run-scoped row
covers; the same with `walk` first calling an entry that holds nothing
(`[1, undefined, undefined]`), where $`A_C`$ records that `walk`'s call was
active while the array was held.

**Observations**: a JSON copy's `flags` is no `Uint8Array` and has no
`length`; a proxy's trap runs at a walker's field read.

**Controls** (forged fragment or forced proposal), each refused:
$`\Psi_C`$ forced smaller than a member's effect; an entry forged as no
member; a function given out forged as called by name; a site's mark forged local, internal or exposed where its
storage crosses otherwise; an incoming value forged to a local or internal
site; a write forged to a key other than the one it writes; a write to a
value from a confined collection forged uncharged; an exported collection
forged confined; a write that may fail forged without its throw edge, or a
native's throw edge forged without its partial writes; a handle invariant
forged to read a path outside its representation; a fact forged as
supported in $`R_C`$ whose origin is a writable crossing; a `length`
assignment forged atomic; a native write forged to charge one typed-array
view where its buffer has two; a site's keys forged to its allocation's alone; a caller's writable
argument forged as protected storage at an install; protection of
released storage forged from a crossing out of the package; the lazy write
forged uncharged to
$`R_{\mathrm{in}}`$, or forged to fill the three fields where one is not
`null`; a client's callback forged to keep storage it truncates, or checked
only against storage passed in the same call; a crossing forged to protect a
location at a position whose type is not read-only; a weak key forged as a
hold; a write to a freshly installed list forged unchecked; a nested
call's protected location forged into its own set only; a package containing
an `await` forged as one that never suspends; a record still being built forged complete, or a complete
handle's installed list forged free; a call's exit forged to keep its set of $`A_C`$, or a step forged
to remove a location from one; an invariant forged into $`G_C`$ that a write
does not keep; a value read from a `Map` forged to meet its type's
invariant with no boundary or check.

## What the Lean states

The definitions and statements below are the draft's, in Paper I's
notation, as Lean states them in
[ReadOnlyRegion.lean](../../lean/Verification/Paper/TolerantFrames/ReadOnlyRegion.lean)
and [ReadOnlyFrame.lean](../../lean/Verification/Paper/TolerantFrames/ReadOnlyFrame.lean)
(namespace `TolerantFrames.ReadOnly`). The components form a laminar
family (`Family`, in
[ReadOnlyComponents.lean](../../lean/Verification/Paper/TolerantFrames/ReadOnlyComponents.lean)):
"nested in" is reflexive and transitive, any two components are nested or
disjoint, each site has an innermost component and a mark for each
component. Each component $`C`$ is read as a package (`Family.at`): its
sites are those of $`C`$'s code, nested components' included, with their
marks for $`C`$, so every definition and lemma below holds at each $`C`$,
with its own $`E_C`$, $`A_C`$, $`B_C`$, $`\Psi_C`$, members and runs. A
frame runs $`C`$'s code when its tag (`ComponentTag`, the calculus's ghost
tag) names $`C`$ or a component nested in it (`Family.Runs`); a step
outside $`C`$ is outside every component nested in $`C`$ (proved,
`Family.outside_mono`), and two components' code is nested or disjoint
(`Family.runs_laminar`). A component's storage includes its nested
components': a location a nested component's site allocated is classified
by its mark for $`C`$, never as outside storage of $`C`$ (proved,
`Family.nested_origin`); with each site's mark for an enclosing component at
most its mark for a nested one (`MarksConsistent`, in the order
$`\mathsf{local}\sqsubseteq\mathsf{internal}\sqsubseteq\mathsf{exposed}\sqsubseteq\mathsf{released}`$,
checked by the pass), nested local storage is in $`R_C`$
(`Family.nested_local_inR`) and nested exposed storage is not released
for $`C`$ (`Family.nested_exposed`). Statements about runs take outside steps as
hypotheses; the calculus's steps meet an outside step's three step
properties at the roots of outside code (*The active frame and the roots
of outside code*, below).
The combination of two components' rules for a fact that relies on both is
not stated. A state is
$`s=(\rho,h,W,k,\mathit{site},\mathit{key},E,A,B,\mathit{roots})`$: Paper
I's environment, heap, world and budget; the site that allocated each
location and each field location's key, fixed at allocation; $`E`$ a set of
locations, $`A`$ a stack of sets of locations, one per active call of $`C`$, and $`B`$ a set of locations; and the values the frames of code
that is not $`C`$'s hold. Each statement is labelled **proved** with
its Lean name, or **hypothesis** where Lean assumes it.

**Marks**. $`C`$'s sites each carry a mark; a location's mark is its
site's,
$`\mu(l)\in\{\mathsf{local},\mathsf{internal},\mathsf{exposed},\mathsf{released}\}`$,
and $`\mu(l)=\mathsf{out}`$ for a location outside code allocated. A
transition *keeps the marks* (`Kept`) when it is admissible and fixes every
old location's site and key; the world fixes its kind (`kindAt_kept`), so a
location's part is fixed (`Kept.part`).

**Paths and read-only reach.** A path $`\pi`$ from a value $`v`$ is a
sequence of field keys (the spine key among them), view-spine steps,
element indices and code steps; $`h\vdash v\xrightarrow{\pi}l`$ (`Follows`)
when following $`\pi`$ from $`v`$ in $`h`$ reaches $`l`$, never through a
collection's entries. A code step (`Succ`, `codeVals`) goes from a value to
a value its code holds: from a bound function to its target, receiver and
bound arguments, and from a closure whose code is not $`C`$'s to the
values its node expressions and captures hold; no code step leaves a
closure of $`C`$. A path's other steps go through a location to its
contents, and its last step reaches a location. Which code is $`C`$'s is
the package's classifier of tags (`Package.ofC`, `F.ofC C` at a component). For a crossing type $`T`$ at the root position, each prefix of
$`\pi`$ has a type $`T|_{\pi'}`$ (`TypeView`), an own field $`T`$ does not
mention having type `unknown`:

```math
\mathrm{ro}_T(\pi)\iff\exists\,\pi'\preceq\pi.\ \mathrm{RO}(T|_{\pi'}),
\qquad
\mathrm{Reach}^{\mathrm{ro}}_T(v,h)=\{\,l\mid\exists\pi.\ h\vdash v\xrightarrow{\pi}l\wedge\mathrm{ro}_T(\pi)\,\}
```

with $`\mathrm{RO}(U)`$ the draft's read-only types, closed under the types
of children; so $`\mathrm{ro}_T(\pi)\iff\mathrm{RO}(T|_\pi)`$ (proved,
`TypeView.roPath_iff`).

**Crossings**. A crossing passes a value $`v`$ at type $`T`$ between $`C`$ and code that is not its, with a direction
$`d\in\{\mathsf{in},\mathsf{out}\}`$; a store of $`C`$ into storage
outside code reaches is a crossing of the stored value at the type of its
position. It updates the ghosts (`Ghost.cross`):

```math
E'=E\cup\{\,l\in\mathrm{Reach}^{\mathrm{ro}}_T(v,h)\mid\mu(l)=\mathsf{exposed}\,\},
\qquad
N=\begin{cases}\{\,l\in\mathrm{Reach}^{\mathrm{ro}}_T(v,h)\mid\mu(l)\in\{\mathsf{released},\mathsf{out}\}\,\}&d=\mathsf{in}\\ \emptyset&d=\mathsf{out}\end{cases}
```

and adds $`N`$ to every set of $`A`$.

**Holds**. $`\mathrm{Held}(l,s)`$ holds when a frame of $`C`$, a
binding of $`C`$ or a location of storage of $`C`$ references $`l`$
or a location from which $`l`$ is reachable by a path; a key of a
`WeakMap` is no reference. Lean takes it as the predicate an exit or a drop
reads.

**The history** (`HStep`). A call's entry pushes the protected set
$`\bigcup A\cup B`$; a crossing updates $`E`$ and $`A`$; a hold that makes
locations protected adds them to every set; each exit, normal or
exceptional, pops the top set, and when the stack becomes empty $`B'`$ is
the popped set's locations $`l`$ with $`\mathrm{Held}(l,s')`$; a step
outside every call removes from $`B`$ each location no longer held. Every
transition keeps each set of $`A`$ equal to $`\bigcup A\cup B`$ (proved,
`HStep.uniform`): the sets of overlapping calls grow together, so the stack
carries one set and its depth, and a location protected in any call stays
protected until the outermost active call returns (`exit_unprotects`
shows the outermost exit ending it).

**The membership test** (`Ghost.InR`).

```math
l\in R_C(s)\iff\mu(l)\in\{\mathsf{local},\mathsf{exposed}\}\ \vee\ \bigl(\mu(l)\in\{\mathsf{released},\mathsf{out}\}\wedge(l\in{\textstyle\bigcup}A\ \vee\ l\in B)\bigr)
```

It is the one test the region, the frame's premise, (P2), (L3) and the trust
row read.

**Parts and the protocol.** A part is $`(\sigma,\kappa,k)`$ (`Part`): a site
$`\sigma`$ or $`\mathsf{out}`$, a kind $`\kappa`$ of Paper I's world and,
for a field location, a key $`k`$. $`\mathrm{Keys}(\sigma)`$ is the set of
keys its allocation gives and every key a write of $`C`$ may add to
a record whose possible sites include $`\sigma`$; for $`\sigma`$ released
or $`\mathsf{out}`$ it is every key. $`\Psi_C`$ maps each part to a change
(`Protocol`). The action of $`\Phi\oplus_C\Psi_C`$ (`OAction`) keeps the
marks and bounds each old location $`l`$ by $`\Psi_C(\mathrm{part}(l))`$
when $`l\in R_C(s)`$ and by $`\Phi`$ otherwise, $`R_C`$ and $`\Phi`$'s
regions read at the entry state. A member's certificate (`Member`,
hypothesis) states what the pass's check of the member establishes: with
each run of code that is not $`C`$'s it makes bounded on $`R_C`$ by
$`\Psi_C`$ and keeping the invariants of states, one call deeper, its call
bounds every location of $`R_C`$ at its entry by $`\Psi_C`$ of its part,
keeps the invariants and keeps each $`I\in G_C`$; $`\Psi_C`$ is the least
map for which every member has one. $`G_C`$ is a set of invariants $`I`$
with: every write of a member to a location of $`\mathrm{supp}(I)`$ of a
complete handle, and every exit of a member, keeps $`I`$.

**Runs of code that is not $`C`$'s** (`RunAt`, `Run`). Inside a call
of $`C`$ at depth $`d`$, such a run is a sequence of outside steps
and member calls, each member call's own runs of code that is not $`C`$'s one call deeper, within a budget of nesting. An outside step
(`OutsideStep`) keeps the marks and the history, allocates outside storage
and meets three hypotheses: it changes only storage its frames reach and
afterwards reaches only storage it reached or allocated (properties of the
language's steps), and it meets the client obligation $`\Theta_C`$ read
by the membership test (`Row`): it changes each exposed location of $`E`$
and each released or outside location recorded in $`A`$ or $`B`$ within
$`\Theta_C`$ at its part. $`\Theta_C`$ is an effect of the same type as
$`\Psi_C`$ (`Protocol`); the read-only row is $`\Theta_C=\mathsf{keep}`$.
Both take their changes in Paper I's lattice with $`\mathsf{extend}`$
(`Footprints.Change`):
$`\mathsf{keep}\sqsubseteq\mathsf{init}\sqsubseteq\mathsf{scalar}\sqsubseteq\mathsf{extend}\sqsubseteq\mathsf{grow}\sqsubseteq\mathsf{any}`$,
$`\mathsf{extend}`$ appending fresh cells to an array spine's end, as
`push` does, so every listed cell stays listed at its index
(`Change.Holds.extend_entry`) and a view spine is kept; the lattice's
lemmas (`Holds.mono`, `.lower`, `.trans`, `.seq`) cover it, and so do
(L1)–(L4).

**Read-only frame.**

```math
\frac{c:\Phi\mid\Phi^{e}\qquad c\ \text{a call whose callee is neither a function of}\ P\ \text{nor an audited native}}
     {c:\ \Phi\oplus_C\Psi_C\ \mid\ \Phi^{e}\oplus_C\Psi_C}
```

under the side conditions of the checks: $`C`$'s code contains no
`await`, `yield`, async function or generator; $`\Psi_C`$ preserves the
references; *Ownership of installed storage* holds of every install.
Proved (`readOnly_rule`): a call of code that is not $`C`$'s inside a
call of it, whose run is bounded by $`\Phi`$ (by $`\Phi^{e}`$ at an
exceptional exit), is an action of $`\Phi\oplus_C\Psi_C`$ with the history
growing.

**The invariants of states** (`Ok`): at least one call of $`C`$
active, a uniform history, and

- (M) (`MarksOk`, `Kept`): every location's mark is its site's, fixed at
  allocation; a local location is reachable from no binding, no storage
  and no frame but $`C`$'s; an internal location is reachable from
  no value that has crossed. Lean states the clauses an outside step reads:
  no local or internal location is reachable from a frame of code that is
  not $`C`$'s (`MarksOk`), and storage that references local storage
  through a field, a spine or a cell is local (`LocalClosed`), kept by
  outside steps (proved, `outside_localClosed`) and by checked steps
  (`pkg_step_ok`, the check `localStores`). On a closure's bindings: no
  value that a closure of code that is not $`C`$'s, or a bound function,
  held in storage binds (a capture, a node expression's value, a saved
  target, receiver or argument) reaches local storage in its paths' first
  location step (`BindingsClosed`, `Leaves`), kept by outside steps
  (proved, `outside_bindingsClosed`) and by checked steps (`pkg_step_ok`,
  the check `localBindings`); with `LocalClosed`, no path from such a
  binding reaches local storage (proved, `binding_no_local`). A closure of
  $`C`$ binds what it captures, local storage among it.
- (P2) (`Confined`): every exposed location reachable from a frame of code
  that is not $`C`$'s is in $`E`$. Every path from such a frame to a
  local or exposed location then passes a location of $`E`$, from which on
  every position is read-only.

**The lemmas**. Each quantifies over states meeting the invariants and
over outside steps meeting their hypotheses.

- (L1) Outside step (proved, `outside_step`). For a step $`s\to s'`$ of
  code that is not $`C`$'s:
  $`\Theta_C(\mathrm{part}(l))_{|h|}(h(l),h'(l))`$ for every
  $`l\in R_C(s)`$, and $`s'`$ meets (M) and (P2).
- (L2) Outside run (proved, `Run.bound`). For a run $`s\to^{*}s'`$ of code
  that is not $`C`$'s inside an active call $`c`$ of $`C`$:
  every $`l\in R_C(s)`$ is in $`R_C(t)`$ for every state $`t`$ of the run,
  $`(\Psi_C\sqcup\Theta_C)(\mathrm{part}(l))_{|h|}(h(l),h'(l))`$ (the
  run's bound is any protocol above $`\Theta_C`$ that the members'
  certificates meet, `Protocol.join` giving $`\Psi_C\sqcup\Theta_C`$),
  and $`s'`$ meets the invariants. By induction on the budget, member
  calls by their certificates.
- (L3) Rigidity (proved, `HSteps.grows`, `InR.mono`, `Leads.trans`). The
  relation $`s\leadsto s'`$, holding when the heaps are related by the
  action of $`\Phi\oplus_C\Psi_C`$ at $`R_C(s)`$ and the history grows
  (at least the calls of $`A`$ up to the current one active, $`B`$ kept,
  every protected location protected, $`E`$ growing), is transitive, and
  $`R_C(s)\subseteq R_C(s')`$ for $`s\leadsto s'`$ within a call: the test
  reads the marks, fixed at allocation, and the history, which only grows
  inside a call, so no argument about references is needed. With $`\Phi`$
  rigid and $`\Psi_C\sqsubseteq\Phi`$ (a change within $`\Psi_C`$ at a
  location of $`R_C`$ is one $`\Phi`$ allows there),
  $`\Phi\oplus_C\Psi_C`$ is rigid on such states; $`\Psi_C`$ composes at
  each part by itself (`Change.Holds.trans`). The same holds of
  $`\Psi_C\sqcup\Theta_C`$: what (L3) asks of $`\Psi_C`$ it asks of
  $`\Theta_C`$, rigidity at each part, which every change has, and
  $`\Psi_C\sqcup\Theta_C\sqsubseteq\Phi`$. $`\top`$ meets both premises
  for every protocol (`Leads.trans_top`).
- (L4) Invariants (proved, `Run.keeps`). For $`I\in G_C`$ with
  $`\mathrm{supp}(I)\subseteq R_C`$ tolerating $`\Theta_C`$ (`SupportInR`) and $`I`$ true at
  $`s`$, a run as in (L2) ends in a state where $`I`$ holds.
- (O) Ownership (proved, `ownership`). A write of $`C`$ that stores
  a value $`v`$ into a location of $`R_C(s)`$, or of
  $`\mathrm{supp}(I)`$ for $`I\in G_C`$, is admitted (`Admitted`) only when
  every location the support reads through $`v`$ is of an exposed site, an
  unconfined copy made in the call among them, or in $`R_C(s)`$; those
  locations are then in $`R_C(t)`$ for every later state $`t`$ of the call.

**The consequence** (proved, `readOnly_frame`, `readOnly_rely`). For a fact
$`F`$ with a support $`S`$ (Paper I's Definition "Support", over the
states keeping the marks) every location of which is in $`R_C`$ with
$`\Psi_C(\mathrm{part}(l))`$ within its change (`Inside`, $`\Psi_C\triangleleft S`$
on $`R_C`$), $`F`$ holds after every action of $`\Phi\oplus_C\Psi_C`$, and
after every run of code that is not $`C`$'s inside a call of $`C`$. `SourceClaimJson.PassUnit.mode8Accepted_sound` keeps its
statement; `PassUnitSafe`'s entry condition gains the invariants and the
ghost components, and its premise and conclusion are reviewed again.

**The checks of a step** (`PkgStep`, in
[ReadOnlyChecks.lean](../../lean/Verification/Paper/TolerantFrames/ReadOnlyChecks.lean)).
A step of $`C`$'s code inside a call at depth $`d`$ allocates, fixing
every old location's site and key; its history transitions never pop below
$`d`$; its crossings, read at the heap after it, update $`E`$ and meet the
marks (`CrossOk`: no local or internal location reachable from the
crossing value, an exposed one only through a read-only path, which is
*Confinement* and the marks' definition). Every value it gives to code that
is not $`C`$'s crosses, and so does every value it leaves, changed
or allocated, in storage such code reaches after the step. The frames of
code that is not $`C`$'s hold every value such code can reach without
calling $`C`$: the captures of its own closures among them, a
closure of $`C`$ being reached only by a call, which is a member's
call.

- The step lemma (proved, `pkg_step_ok`): a checked step keeps the
  invariants of states and the marks, and grows the history. A path the
  frames have after the step either is one they had (`follows_split`), or
  runs from the new contents of a location the step changed or allocated,
  which crossed; a path of a well-formed heap from a valid value ends at an
  allocated location (`follows_lt`).
- *Incoming values* (proved, `incoming_site`, `incoming_charged`): a
  location reachable from a value outside frames hold is exposed, released
  or outside storage, so a write charged to every such part is charged to
  its own.
- A member from its checks (proved, `memberOfChecks`): its call is a
  sequence of checked steps and runs of code that is not $`C`$'s one
  call deeper (`MemberRun`); with its certified effect within $`\Psi_C`$
  part by part (the protocol a fixed point over the members) it meets
  `Member.bound`, and with every step keeping each invariant of complete
  handles (`TolerantStep`, *Tolerant invariant*) it meets `Member.keeps`.

**The active frame and the roots of outside code** (in
[ReadOnlySteps.lean](../../lean/Verification/Paper/TolerantFrames/ReadOnlySteps.lean)
and [ReadOnlyOutside.lean](../../lean/Verification/Paper/TolerantFrames/ReadOnlyOutside.lean)).

- Every old location a step of the paper model's reduction changes is a
  slot of an object or an element cell of a spine that the stepped term
  references (proved, `step_changes`).
- The evaluation path of a term (`path`) lists the frames on it, innermost
  first, each with its tag and its term with the nested frame on the path
  cut out, then the top segment, tagged with the code that runs it; it
  follows the congruence rules of `Step`, a `goto` being a frame not yet
  entered. A step is a step inside the innermost frame on the path
  (proved, `step_path`, `PathStep`): that frame's term changes and the
  frames outside it stay, or the frame is popped, by a return or a throw
  out of a node without a handler, and its parent's term changes; the
  frames on the path of the term the step produces are pushed, a call's
  run among them. The step's active tag (`activeTag`) is the innermost
  frame's, or the top segment's when no frame is on the path.
- The roots of outside code at a term (`vals`, in
  [ReadOnlyRegion.lean](../../lean/Verification/Paper/TolerantFrames/ReadOnlyRegion.lean))
  are the values at the positions of the frames whose tags do not run
  $`C`$'s code: objects, spines and view spines, each with the values its
  code holds, which are the values a code step reaches. A closure whose
  code runs $`C`$'s contributes itself, so its own slots and identity, and
  none of its code, which outside code reaches only by calling it. An
  allocation of a typed array contributes its view spine, as the object it
  allocates names it. The roots' references other than identities are
  valid where the term's are (`RefsOkN`, `RootsValid`, proved,
  `rootsValid_of_term`).
- A step whose active frame runs no code of $`C`$ changes only locations
  one path step from these roots (proved, `step_reach`), which is
  `OutsideStep.reach` with these roots as the state's (`outsideStep_reach`);
  every value it leaves in a location it changes or allocates, and from
  which a path step leaves, is one of these roots (proved, `step_writes`),
  which gives `OutsideStep.writes`: the first location of every path from
  such a value is reached by the roots or fresh (`outsideStep_writes`).
- After such a step the roots reach only locations the roots reached
  before or the step allocated (proved, `step_noForge`, at a heap holding
  values), which is `OutsideStep.noForge` with the roots before and after
  as the states' (`outsideStep_noForge`). A path after the step runs
  through good values: one whose location steps, and those of the values
  its code holds, reach locations the roots reached or fresh ones (`GV`).
  The roots after the step are good (`step_cover`): each is a root before
  the step; the contents of a location a root reaches (a read, a spread's
  elements, a copy's values, `mergeParts_cover`, `readElems_cover`); a
  value a root's code holds (a call's run, a bound function's call); a
  substitution or an instantiation of good terms by good values
  (`subst_cover`, `instantiate_cover`); or an allocation, whose slots and
  cells are fresh. The new contents of a location a good path passes are
  the step's roots (`step_writes`) or its old contents. A capture of a
  closure read from a field is reached before the read through the
  closure's code (`capture_reached`).
- The active frame before a step classifies it. The entry of a member's
  call, a call of a closure of $`C`$ from a frame of outside code, has an
  outside active frame; it changes and stores nothing, so `step_reach` and
  `step_writes` hold of it, and `RunAt` counts it in the member's call,
  whose entry pushes the history while an outside step keeps $`A`$. A
  return from $`C`$'s code into outside code has an active frame of
  $`C`$ and ends the member's call.

**Integrity is not in the model.** The paper model's objects carry no
integrity state (frozen, sealed, non-extensible), and its field write
(`writeField`) never throws for one. The protocol's `integrity` key is
unsupported in Lean, and nothing is built on it.

**What Lean assumes.** The client obligation (`OutsideStep.row`); three
properties of the language's steps, which the calculus's steps meet at the
roots of outside code (`OutsideStep.reach`, `outsideStep_reach`;
`OutsideStep.writes`, `outsideStep_writes`; `OutsideStep.noForge`,
`outsideStep_noForge`), a state's roots being those of its term, the top
segment's values among them exactly when the top segment's code is not
$`C`$'s; these three hold whatever the top segment's code, so a client's
top level outside $`C`$ and a module of $`C`$ whose top level calls outside
code are both covered; the validity of the frames' values, identities
aside (`RootsValid`, which the roots of a valid term meet,
`rootsValid_of_term`); for each member, the soundness of
its certified effect on $`R_C`$ (`memberOfChecks`'s `certified`, what the
pass's check of its body establishes) and its steps' checks; and, for the
frame's premise, the flow of possible sites and the protection a region
is read with.

**The frame's premise, checked** (proved, `insideCheck_sound`). The check
`insideCheck` reads, for each region of $`S`$, the parts its locations may
have: each part's change in $`\Psi_C`$ is within the region's, and the part
is of a local or an exposed site, or released or outside storage of a
region a live incoming read-only crossing protects. Where the flow of
possible sites covers each location's part, and each region read as
protected has its released and outside locations recorded in the history,
the check gives `Inside`.

## Stages and cost

1. **The rule in the note and in Lean**: the marks, $`E_C`$, the history
   $`A_C`$, $`R_C`$, $`\Psi_C`$ with parts at keys and its guarantee $`G_C`$, (P2), (M), (L1) to (L4), Reliance at
   $`\Phi\oplus_C\Psi_C`$, per component of the laminar family, with the
   frames' ghost tags. Front: each component's interface (for pretext's
   package, `package.json`'s `exports`), members, the
   restriction *No suspension*, the marks and possible sites, $`\Psi_C`$ as a least fixed
   point, the checks above. The trust row. The cases and controls above.
2. **Pretext**: the annotations and source changes on the fork; the five
   handle sites and six cursor sites checked; the measurement above.
3. **Copies**: a decision on JSON copies.
4. **P15 and P16**.

Cost (conjectured): Lean as private representation's, with (M) in place of
(P1) and no construction lemma, two to three weeks; front, the site marks,
the flow of possible sites and the parts at keys, which private
representation's owning marks already need; sources, as counted above.
