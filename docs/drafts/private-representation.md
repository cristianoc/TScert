# Draft: private representation

A design for handles whose representation is in ECMAScript private fields:
a class whose instances hold their state under private names, which code
outside the class body cannot spell, read, write or enumerate. A fact a
function of the class holds about that state survives a call of code of
unknown effect, a user's callback included, bounded by what the class's own
callable code may change. It answers pattern P22 of
[Tolerant frames II](tolerant-frames-2-note/note.tex) at its handle sites
(form (b) of the [dossier](callback-frames-dossier.md)) and at its cursor
sites (form (a)), and states what it gives P15, P16, P18 and P20.

Base: TScert `single-pass` at `72055046`; upstream pretext is
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
class $`C`$ with private state:

1. **The fact**: the class invariant $`I_C`$, and any fact whose support
   lies in the class's private state.
2. **The stable operations**: the code of $`C`$ that other code can call,
   its *members*; their joint footprint on the private state is the
   protocol $`\Psi_C`$, a closed footprint.
3. **The checked contract**: Lean certifies each member within
   $`\Psi_C`$, as it certifies every function at its inferred effect
   (cited:
   [inferred call effects](../SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification)).
4. **The construct's rule**: Private frame, below. With it, Paper I's
   Theorem "Tolerant frame" and Proposition "Reliance" carry a fact across
   every run of code that is not the class's (proved: Paper I, Lean
   `frame_box`, `rely_chain`).

It reads three existing pieces:

- **Private names** (cited:
  [classes](../SOURCE-CONTRACTS.md#classes), "Private names"). A private
  name `#x` is a key $`\sigma_{C.\#x}`$ identified by its declaring member;
  `o.#x` and `o.#x = e` are the named read and write at it; a copy takes no
  private slot.
- **Rigid paths** (cited: Paper I, "Invariant assertions and rigid paths";
  [records](../POSITIVE-TYPES.md#records), `@stable`). A path through fields
  that keep the object they hold reads the same object in every heap. A
  private field that holds an object keeps it under every change the
  protocol admits ($`\mathsf{scalar}`$ keeps an object), so `o.#f` is
  rigid where the field's contract admits only objects.
- **Type invariants** (cited:
  [type invariants](../ARITHMETIC.md#type-invariants),
  [`@invariant`](../ANNOTATIONS.md#invariant-c-on-a-type)). The clause
  language states $`I_C`$ over the paths `this.#f`.

New machinery: the regions of a class body's private state, one protocol
per body, one rule, one confinement check and two trust rows, one a
property of the language, one a caller's use of a value given out at a
read-only type. No new judgment form, no new modality, no world component
but the ghost set $`E_C`$ of exposed locations, which (P2) reads.

## The example

```ts
let prepare: (n: number) => Handle
let walk: (h: Handle, visit: (w: number) => void) => number[]

/** @invariant this.#flags.length === this.#widths.length */
class Handle {
  static #staged: Parts | null = null
  readonly #widths: number[] = Handle.#check().widths
  readonly #flags: number[] = Handle.#staged!.flags
  constructor() { Handle.#staged = null }

  static #check(): Parts {
    const p = Handle.#staged
    if (p === null || p.flags.length !== p.widths.length) { Handle.#staged = null; throw new TypeError("made by prepare()") }
    return p
  }

  static {
    prepare = (n: number): Handle => {
      Handle.#staged = { widths: new Array<number>(n).fill(1), flags: new Array<number>(n).fill(0) }
      return new Handle()
    }
    walk = (h: Handle, visit: (w: number) => void): number[] => {
      const widths = h.#widths, flags = h.#flags, out: number[] = []
      for (let i = 0; i < widths.length; i++) { visit(widths[i]!); out.push(flags[i]!) }
      return out
    }
  }
}
type Parts = { widths: number[]; flags: number[] }
```

`visit` is external code and may hold `h`, call `prepare`, `walk` and
`new h.constructor()`. The read `flags[i]!` needs
$`i<|h.\#\mathit{flags}|`$ after `visit`. Under Node (observed), a visitor
that calls every one of them leaves the walker reading `[0, 0, 0]`.

## The rule

Paper I's notation throughout: a heap $`h`$, an environment $`\rho`$, the
action $`h\xrightarrow{\Phi}_\rho h'`$ of an effect, changes
$`\mathsf{keep}\sqsubseteq\mathsf{init}\sqsubseteq\mathsf{scalar}\sqsubseteq\mathsf{grow}\sqsubseteq\mathsf{any}`$
(Paper I, §3, the changes' definition: $`\mathsf{scalar}`$ keeps a location
that holds an object; $`\mathsf{grow}`$ keeps a spine's length and density,
and may replace a listed cell by a fresh one, `[1]` to `[10]` at a heap of 10
locations), regions read at the entry heap, $`\Phi\triangleleft_K S`$ for respect and
$`\Box_\Phi F`$ for the modality.

### Definitions

**Bodies.** A class declares private names $`\sigma_{D.\#f}`$ for its
instance fields, static fields and methods. A private name is spelled only
inside its class's declaration, the declarations of classes nested in it
included. Below, $`C`$ is a top-level class with private state, and its
*body* is the code lexically inside its declaration; the classes declared
in that body are $`C`$'s *classes*, $`C`$ among them, and they declare
distinct private names (a nested `#x` would shadow an outer one). One body,
one protocol: a nested class's code reads the private state of the classes
around it, so they share it.

**The regions.** For a top-level class $`C`$:

- $`\mathsf{priv}_{D.\#f}(\rho,h)`$, for a private field $`\#f`$ of one of
  $`C`$'s classes $`D`$, is the set of field locations $`o.\sigma_{D.\#f}`$
  of every object $`o`$ of $`h`$, or, for a static field, its cell; the
  staging fields ([the class shape](#the-class-shape-the-rule-requires))
  are in none. $`\mathsf{priv}_C`$ is their union.
- $`\mathsf{own}_C(\rho,h)`$ is every location reachable in $`h`$ from a
  location of $`\mathsf{priv}_C`$ through fields, spines and element cells,
  stopping at instances of classes with private state, whose state is
  $`\mathsf{priv}`$ of their own body, and at collections (`Map`, `Set`,
  `WeakMap`), whose entries the model holds in no location of the heap
  (cited: [native footprints](../SOURCE-CONTRACTS.md#native-footprints), the row of `Set` and `Map`: they write only the receiver's internal slots, which no location of the model holds).
  A collection is never owned storage (*Confined collections*, below). It has one
  part per kind of Paper I's world: $`\mathsf{own}_C.\mathsf{spines}`$
  (array and view spines), $`\mathsf{own}_C.\mathsf{cells}`$ (element
  cells) and $`\mathsf{own}_C.\mathsf{fields}`$ (field and cell locations).
- $`R_C=\mathsf{priv}_C\cup\mathsf{own}_C`$.

**Code that is not the body's.** A step runs code that is not the body's
when it is a call whose callee is neither a function of the body nor an
audited native, an `await`, or a `yield`. A call *names* its callee when the
callee is a function of the body, a binding of the body written once with
one, or a private method.

**Read-only types and views.** A type is *read-only* when, read after
expanding every alias (`Readonly<T>` and mapped types included), every
storage it reaches is read-only in it: every array, tuple and index
signature position readonly, every field `readonly`, no typed array, no
`any`, no type parameter, and no function type but the members of
`ReadonlyArray`; recursively through element, field and index types. A
union or an intersection is read-only when each of its members is.
`unknown`, `object` and `{}` are read-only: they grant no write, and the
read-only views row covers what a caller does after narrowing. A reference the body gives
to code that is not the body's at a read-only type (a member's result, an
argument of a call it does not name, a value thrown or yielded, or the
content of a public field) is a *view*; a location of
$`\mathsf{own}_C`$ reachable from a view is *exposed*.

**Members.** The members $`M_C`$ are the functions of the body that code
that is not the body's can reach: the constructors of $`C`$'s classes,
which `new h.constructor()` reaches; every public method, accessor and
static; and every function of the body used as a value other than as the
content of a binding that names it (returned, thrown, stored in storage, or
passed as an argument). A function the body only calls by name is no
member.

**The protocol.** $`\Psi_C`$ has one entry per private field and one per
part of $`\mathsf{own}_C`$:

```math
\Psi_C=\{\ \mathsf{priv}_{D.\#f}:\psi_{D.\#f}\ \}_{D,\#f}\ \cup\ \{\ \mathsf{own}_C.\mathsf{spines}:\psi_{s},\ \ \mathsf{own}_C.\mathsf{cells}:\psi_{c},\ \ \mathsf{own}_C.\mathsf{fields}:\psi_{f}\ \}
```

It is the least such effect for which every member $`m\in M_C`$, checked
with each of its steps that run code that is not the body's bounded on
$`R_C`$ by $`\Psi_C`$, has normal and exceptional effects that, after
`fresh_eff` drops the locations it allocated, bound every location of
$`R_C`$ of its entry heap by $`\Psi_C`$. A member that writes only what it
allocated contributes $`\mathsf{keep}`$.

**The bound on $`R_C`$.** For an effect $`\Phi`$, $`\Phi\oplus_C\Psi_C`$
bounds the locations of $`R_C`$ by $`\Psi_C`$ and every other location by
$`\Phi`$:

```math
h\xrightarrow{\Phi\oplus_C\Psi_C}_\rho h'\iff h\xrightarrow{}_\rho h'\ \wedge\ \forall l<|h|.\ h'(l)=h(l)\ \vee\ \exists (r:\delta)\in(\text{if } l\in R_C(\rho,h) \text{ then } \Psi_C \text{ else } \Phi).\ l\in r(\rho,h)\wedge\delta_{|h|}(h(l),h'(l))
```

**The class invariant.** $`I_C(o,h)`$ is the clause of `@invariant` on a
class of the body, with `this` read as $`o`$; its paths are `this.#f` and
the lengths and elements they reach; $`\mathrm{supp}(I_C)`$ is its support,
inside $`R_C`$. A class without `@invariant` has $`I_C=\mathsf{true}`$. An
instance is *complete* once its construction has returned.

### Private frame

A step that runs code that is not the body's runs code outside the body,
which enters it only by calling members, or a member itself:

```math
\frac{c:\Phi\mid\Phi^{e}\qquad c\ \text{runs code that is not the body's}}
     {c:\ \Phi\oplus_C\Psi_C\ \mid\ \Phi^{e}\oplus_C\Psi_C}\ \textsf{(Private frame)}
```

An unknown callback, of effect $`\top`$, has by the rule the effect
$`\Psi_C`$ on $`R_C`$. An `await` or a `yield` has the effect $`\top`$
outside $`R_C`$ and $`\Psi_C`$ on it. A call that names a function of the
body is checked at that function's certified effect; an audited native,
owned storage among its arguments, keeps its audited effect, and each call
of a callback it makes is bounded by the rule.

**At a callback.** Let a walker hold $`F`$ with a support $`S`$ inside
$`R_C`$ and $`\Psi_C\triangleleft_K S`$. Tolerant frame gives
$`K\wedge F\vdash\Box_{\Phi\oplus_C\Psi_C}F`$, and Reliance carries $`F`$
across every step that runs code that is not the body's, given rigidity
([what must be proved](#what-must-be-proved), (L3)). In the example every
entry of $`\Psi`$ is $`\mathsf{keep}`$: `prepare` and `new Handle()` write
only what they allocate and the staging field, `walk` writes nothing. So
$`i<|\mathit{widths}|`$ and $`|\mathit{flags}|=|\mathit{widths}|`$ cross
`visit` (conjectured, the design's claim).

**At a private read.** `o.#f` either throws, as JavaScript does where `o`
holds no slot, or reads a location of $`\mathsf{priv}_C`$. Of a complete
instance it gives $`I_C(o)`$ ((L4) below). A value of type $`C`$ is any
object; the private read is the elimination that gives $`I_C`$.

**Reentrancy.** A callback may call any member on any instance. A member
`truncate(h)` that pops `h.#widths` gives $`\psi_s=\mathsf{any}`$, beyond
the *Reference-preserving protocol* the class shape states, so the class is
refused; under Node a
visitor calling it makes a walker that cached the length read
`[1, undefined, undefined]` (observed). A member that pushes onto `#widths`
and then onto `#flags` preserves the references, and breaks $`I_C`$ until its
second push; the class is refused by *Tolerant invariant*.

### What must be proved

The rule rests on two invariants of states and four lemmas. Each is
conjectured until its Lean exists; the statement each cites is labelled.

- **(P1) No private key is a value.** No value of $`\rho`$ or $`h`$ is a
  $`\sigma_{D.\#f}`$, and no step yields one to code outside the body. For
  JavaScript, cited: [ECMA-262](../REFERENCES.md#ecma-262), Private Names
  and the operations PrivateFieldFind, PrivateGet, PrivateSet and
  PrivateFieldAdd: a private name is reachable only through the lexical
  environment of its class body, no reflection operation lists private
  elements, and a copy or a proxy holds none. For the model, conjectured
  until the audit of [the natives that enumerate keys](#what-tscert-must-change).
- **(P2) Confinement.** Every path from a frame of code outside the body to
  a location of $`\mathsf{own}_C`$ passes through a location of
  $`\mathsf{priv}_C`$ or enters $`\mathsf{own}_C`$ at an exposed
  location. Which locations are exposed is a ghost component of the state,
  $`E_C`$, set by how a reference left the body and only growing; it is the
  one exception to "no world component". Paths run through fields, cells,
  spines and element cells; a closure's environment is not reachable from a
  holder of the closure. Contents are (P2)'s: a member may return a number
  read from a private field. Conjectured, from the
  [confinement check](#the-class-shape-the-rule-requires).
- **(L1) Outside step.** From a state meeting (P1) and (P2), a step of code
  outside the body leaves every location of $`R_C`$ unchanged and keeps
  (P1) and (P2). A write at $`o.\sigma`$ needs $`\sigma`$ as a static key,
  which the code lacks, or as a value, which (P1) excludes; a change of
  owned storage needs a reference, which (P2) gives only as a view, through
  which the [read-only views row](#trust) states code outside changes
  nothing. (L1) is conjectured from that row, which is trust: it holds of
  external code that meets the row, and of no other.
- **(L2) Outside run.** A run of code that is not the body's from $`h`$
  changes each location of $`R_C(h)`$ within $`\Psi_C`$. By induction on
  the budget $`k`$: the run changes $`R_C`$ only inside calls of members,
  each bounded by its certificate at $`\Psi_C`$, whose own steps that run
  code that is not the body's are bounded by the rule at a smaller budget.
- **(L3) Rigidity.** For every pair
  $`h\xrightarrow{\Phi\oplus_C\Psi_C}_\rho h'`$ of the action, not only the
  transitions of checked runs,
  $`\mathsf{own}_C(h)\subseteq\mathsf{own}_C(h')`$: a location of
  $`R_C(h)`$ changes within $`\Psi_C`$, which preserves the references
  ([*Reference-preserving protocol*](#the-class-shape-the-rule-requires)),
  so every reference to storage held in $`R_C(h)`$ is held in $`R_C(h')`$
  and every cell a spine or view spine of $`R_C(h)`$ lists is listed in
  $`h'`$; reachability from $`\mathsf{priv}_C`$ is then kept by induction
  on the length of the path. Hence a location's region is the same in
  $`h'`$ as in $`h`$ for every location of $`h`$ in $`R_C(h)`$, and
  $`\Phi\oplus_C\Psi_C`$ is rigid when $`\Phi`$ and $`\Psi_C`$ are rigid
  and $`\Psi_C\sqsubseteq\Phi`$: a location outside $`R_C(h)`$ that enters
  $`R_C(h')`$ changes in the second step within $`\Psi_C`$, hence within
  $`\Phi`$. Both hold for $`\Phi=\top`$ and for
  `{ values: "any"; spines: "grow" }`.
- **(L4) The class invariant.** In every state of every run, $`I_C(o,h)`$
  holds of every complete instance $`o`$. Its construction establishes it
  for every caller; every change the body makes to a location of $`R_C`$ of
  a complete instance is tolerated by $`\mathrm{supp}(I_C)`$, or is one
  write checked to keep $`I_C`$ (*Tolerant invariant*); outside code changes
  none (L1). No step of the argument assumes $`I_C`$ of the state it
  concludes it of.

`SourceClaimJson.PassUnit.mode8Accepted_sound` keeps its statement; the
premise and conclusion of `PassUnitSafe` are reviewed again, as a change of
the accepted plan type requires.

## The class shape the rule requires

Each restriction is chosen by the behaviour it excludes, documented in
SOURCE-FRAGMENT.md, enforced at the source boundary, and has a control
([negatives and controls](#negatives-and-controls)).

- **No base class.** A class with private state extends nothing. A base
  constructor runs during construction, before the private fields exist,
  and chooses the object that receives them: a base returning another
  object installs the derived class's private fields on an object other code
  already holds, and the construction runs code the body does not check.
  The model's derived form builds a base part as a copy, which holds no
  private slot (cited: SOURCE-FRAGMENT.md, "A private name in
  inheritance"). Construction therefore allocates a fresh instance by the
  body's code alone.
- **Lexical dispatch.** Wherever a certificate assumes which function a
  call runs, the call names it: by a function of the body, a binding
  written once, or a private method. A call of a public method, accessor or
  static of a class with private state is a call whose callee is not
  named; nothing of the class's method is assumed at it. Freezing the class
  and its prototype does not name the callee: an instance's own property
  shadows a frozen prototype's method (observed).
- **Evaluated once.** Each evaluation of a class declaration makes new
  private names, and the model identifies a name by its declaring member. A
  class with private state is declared at the top level of its module, or in
  a static block of such a class, which runs once.
- **Reference-preserving protocol.** Every entry of $`\Psi_C`$ preserves
  the references: in each pair of its action, every reference to storage
  held at a location of $`R_C`$ of the entry heap is held at a location of
  $`R_C`$ of the exit heap, and every cell a spine or view spine of $`R_C`$
  lists stays listed. The entries that meet it: $`\mathsf{keep}`$; on a
  private field, a cell or a field, $`\mathsf{scalar}`$ (a location holding
  an object keeps it); on a spine, an extension, the old spine a prefix of
  the new, as `push` gives by its audited postcondition. Paper I's
  $`\mathsf{grow}`$ does not meet it, since a growth may replace a listed
  cell. A class whose protocol exceeds it is refused. Its reason: (L3),
  storage leaving $`\mathsf{own}_C`$ while other code may still reach it.
  It is wider than that reason: a `pop` of an owned array of numbers drops a
  cell no other code reaches, and is refused all the same, a restriction of
  the language ([WORK](../../WORK.md#status), "Shrinking owned arrays").
  Since every incoming value is charged (*Incoming values*), it also
  refuses a member that shrinks, or overwrites a reference in, storage
  its caller passed, which the same row covers.
- **Construction.** An instance field's initializer reads `this` only as
  `this.#f` of an earlier field, gives `this` to nothing, and runs no code
  that is not the body's. The instance is complete, and meets $`I_C`$, only
  once construction has returned; a private read of an incomplete instance
  is checked without $`I_C`$. A field that holds storage from construction
  is written by its initializer, from a *staging field*: a private static
  that the body sets to parts it allocated and holds nowhere else,
  immediately before `new`. The first initializer checks the staged parts
  (`#check`), the others read the staging field, whose value no code changes
  between initializers, and the constructor's body sets it to `null`; no
  field keeps the parts. The staging field holds `null` or such parts in
  every state, and is `null` again before every return and every throw of
  the construction (`#check` clears it before it throws). Its
  reasons: the constructor is a member, reached by `new h.constructor()`,
  so it takes no storage from its caller; an initializer cannot read the
  constructor's arguments; and a field declared and then assigned in the
  constructor costs the walkers 15–19% on V8 ([performance](#performance)).
  A field that holds no storage may be written anywhere within the
  protocol; a field holding `null` or `undefined` may take storage after
  construction by the checked write of *Ownership at construction*.
- **Confinement.** A value is *confined* when it is read from a private
  field or from confined storage, or stored into either; confined storage is
  that of $`\mathsf{own}_C`$, and storage the body keeps in its own bindings
  and gives to no code outside. A write the body makes through such a
  binding to storage that may also be owned counts on the entries of
  $`\mathsf{own}_C`$ in $`\Psi_C`$. A confined value that may be
  storage flows only to: a binding of the body; the object of an element or
  field read or write, or of a `length` read; an initializer of a private
  field, or a write into confined storage; an argument of a call naming a
  function of the body, whose parameter is then confined; and a native whose
  audited contract calls no code but the body's and keeps no reference to
  it. A copy (`slice`, `Array.from`, a typed array built from it) is
  unconfined only when its element type holds no storage: a shallow copy of
  an array of arrays shares the inner arrays (observed). A return out of a
  member, a `throw`, a `yield` or an `await` of a confined value, a store
  into storage not confined, and an argument of a call that does not name a
  function of the body are refused. A closure of the body may capture a
  confined value; a closure given out is a member, and its own flows are
  checked the same. A confined value may also leave the body as a view: a
  return out of a member, an argument of a call that does not name a
  function of the body, a `throw`, a `yield`, or a store into a public field
  of an instance of the body's classes, each at a read-only type. A value
  given as a view stays confined for the body, which may still write it
  within $`\Psi_C`$; the body never takes a view back as owned storage, by
  *Ownership at construction*.
- **Ownership at construction.** Storage enters private state, or confined
  storage, only where a location holding no object is written, and only
  storage allocated during the current call of the body, an unconfined copy
  made there, or storage already confined. During construction that write
  is an initializer. After it, it is a checked $`\mathsf{scalar}`$ write of
  a location of a complete instance holding `null` or `undefined`, of fresh
  storage complete before the write, which keeps every instance invariant
  that reads the location (*Tolerant invariant*'s checked single write).
- **Confined collections.** A collection held only by a binding of the
  body that no module exports, and never passed to, stored where, or
  returned to code that is not the body's, is a *confined collection*.
  A collection held in private state is refused, and one that is not
  confined holds nothing private state takes uncopied. Every value the body
  obtains from a confined collection, and everything reached from it, is
  possibly owned storage, except an object *Owning allocation sites*,
  below, proves disjoint from $`\mathsf{own}_C`$; a type gives no such proof, since storage of one
  object type is a value of every type it is assignable to: every write the
  body makes to such a value, or to anything reached from it, is charged to
  the entries of $`\mathsf{own}_C`$ in $`\Psi_C`$, and meets
  *Reference-preserving protocol* and *Tolerant invariant* as a write to
  owned storage does. An insertion into a confined collection is a write of
  the body, checked as a store into owned storage: what it stores is owned,
  fresh, or already confined. Storage from a confined collection may enter
  private state uncopied. The argument needs no location for a collection's
  entries: (P2) holds since no code outside the body reaches the collection,
  so no path from such code runs through it; and (L2) holds since every
  write the body makes to storage it may share with private state is
  charged.
- **Incoming values.** A value the body receives from code that is not
  the body's may be a view passed back, at a writable type TypeScript
  admits (observed: a member `change(x: { n: number })` given
  `{ readonly n: number }` type-checks, and its write changes the private
  record). Private storage of type `{ n: number; extra: number }`, given out
  at a read-only type, enters `change(x: { n: number })` the same way
  (observed by Astra under `tsc` 7.0.2 `--strict` and Node). So every value
  the body receives from such code (a member's argument or receiver, the
  result of a call it does not name, a callback's result, a native's result
  or callback argument, a caught exception, a read of storage that is not
  confined) is possibly owned storage, whatever its type, as a value from a
  confined collection is: every write the body makes to it, or to anything
  reached from it, is charged to the entries of $`\mathsf{own}_C`$ in
  $`\Psi_C`$ and meets *Reference-preserving protocol* and *Tolerant
  invariant*. Member certificates carry the charge, so (L2) covers a
  member's write to a view passed back.
- **Owning allocation sites.** An allocation site of the body is *owning*
  when storage it allocates may become reachable from $`\mathsf{priv}_C`$:
  stored into private state or into owned storage, directly or through a
  binding, a confined collection or a call naming a function of the body.
  The test applies to the object each write changes: a write is uncharged
  only when every allocation site the written object may come from,
  propagated by the body's flow through the reads that reached it, is not
  owning. A record's disjointness says nothing of what it references: a
  record from a site that is not owning may hold an array from an owning
  one, as pretext's cached measurement holds `fit.advances`
  (`measurement.ts:1262`), which handles share (`prepare.ts:525–529`,
  `:579`, `:628`). A value received from code that is not the body's has no
  such proof. *Owning* is a component of a location's contract, fixed at
  allocation: the front proposes it per allocation site, and the pass
  checks every store into private state or into owned storage to store a
  value marked owning, or fresh storage from a site marked owning. A
  confined collection holds values of either mark, which insertion and
  lookup preserve, so a cached record unmarked stays unmarked while the
  owning lists it holds stay marked. A write is uncharged only through a reference
  whose possible contracts are all unmarked. Disjointness is then a typing
  fact, and a forged mark fails a store's check (conjectured).
- **Tolerant invariant.** Every change the body makes to a location of
  $`R_C`$ of a complete instance, and every entry of $`\Psi_C`$, is one
  $`\mathrm{supp}(I_C)`$ tolerates, or is one write checked to keep
  $`I_C`$ of its instance. An invariant that one write breaks and a later
  write restores is refused, as Paper I's limit "Broken and restored
  invariants" states for assertions.

## Trust

Two new rows of the [trust surface](../DESIGN.md#trust-surface).

**Private names**, a property of the language:

> ECMAScript private names behave as the specification states
> ([ECMA-262](../REFERENCES.md#ecma-262), Private Names): code outside a class
> body reads, writes and enumerates no private element of the class or of
> its instances, no operation yields a private name as a value, and a
> private field is installed only by its class's own construction. Code
> running outside the language's semantics (a debugger, an inspector
> protocol) is outside the model.

**Read-only views**, an assumption about code outside the analyzed
sources, of the kind of the rows on exported preconditions and on a
callback's stated effect (a stand-in until applications are analyzed too):

> Code outside the analyzed sources, a function it passes in included,
> changes by its own steps no element, field or length of storage it
> reaches through a view (a reference a class with private state gives out
> at a read-only type, or any copy of that reference), by any operation, a
> native's included. A change made inside a call of a member of the class
> is the member's, bounded by its certificate. Freezing, sealing and
> preventing extension change no element, field or length, and are
> admitted.

Analyzed code outside the body is checked, not trusted: the pass reads a
view at its read-only type and refuses a write through it, a write through
a widening to a writable type included (an obligation of
[what TScert must change](#what-tscert-must-change)). A body write to an
exposed location that code outside froze throws, since modules are strict,
which safety admits. The model has one outcome for a write, so the
obligation is that every body write to a possibly exposed location, a
spine extension included, has a throw edge leaving the heap unchanged, its
handler checked from that heap; that freezing changes no location of the
model is checked by the native audit (conjectured). Pretext makes no such
write after construction.

The row is stated in the API: the declaration of each value given out as a
view states, in its doc comment, that callers must not change it. The
type check of a caller does not establish it. TypeScript's `readonly`
constrains only the written type, and TypeScript admits a `readonly string[]`
where `{ length: number }` is expected, and an `ArrayLike<number>` where
`{ [i: number]: number; length: number }` is, whose writes then
type-check (observed: `tsc` 7.0.2 under `strict` accepts both, and Node
truncates both arrays); a cast or `any` removes it too.

What they replace:

- **No assumption about external code's use of a handle itself.** A copy, a
  JSON copy, a `structuredClone` copy, a proxy and an object inheriting from
  a handle throw a `TypeError` at the first private read (observed), which
  safety admits. Only what a handle gives out at a read-only type rests on
  the read-only views row.
- **The invariant of a class with private state needs no caller trust
  but the read-only views row.** The row on exported preconditions ("the
  type invariant … of each type its parameters' types name, a sealed
  handle's included") does not apply to such a class: its invariant holds
  of every complete instance by (L4), which rests on the read-only views
  row wherever $`\mathrm{supp}(I_C)`$ reaches exposed storage.
- **No owner boundary.** The boundary is the class body, a lexical fact.

Rows used unchanged: ordinary arrays, fixed-length typed arrays, the public
fields of objects external code holds at their types.

## Scope lost

A handle with private state keeps nothing across a structural copy.
Upstream pretext supports these uses; under this design each throws a
`TypeError` at the first line function:

- **A JSON copy of a handle passed back** (cited: upstream `RESEARCH.md`,
  Decisions Log, "2026-09-24: a JSON copy of a prepared handle lays out as
  the handle does", line 5553, the maintainer's decision, which
  records that no such use had turned up; `line-break.ts:26–28`, which reads
  `segmentFlags` by index so that such a copy lays out the same).
- **A `structuredClone()` or `postMessage()` copy** (cited: the same entry,
  "copies worked throughout"): a handle prepared in a worker and laid out on
  the page.
- **A handle kept in IndexedDB** (cited: upstream `CHANGELOG.md:63`, a
  handle "kept in IndexedDB or sent by a worker").
- **A proxy of a handle**, as a store wrapping its state in a `Proxy` makes
  (observed).

Kept: **a frozen handle** (cited: Decisions Log, "2026-10-12: no line
function writes to a frozen handle or to anything it holds", line
6317). `Object.freeze` leaves private fields as they are (observed). A
store's deep freeze reaches the exposed arrays through the public fields
and freezes them (observed), which the read-only views row admits: no
member writes them after construction, and a write to a frozen one
throws. Upstream's side table for
frozen paragraph handles (`rich-inline.ts:1141–1178`) is not needed.

A worker that prepares and a page that lays out need an explicit pair of
functions, one writing a handle's parts to a plain value, one checking
$`I_C`$ of such a value and constructing from a copy of it; neither is part
of this design.

## What TScert must change

**Refusal index rows to lift** (cited: SOURCE-FRAGMENT.md, the table
"Classes"):

- "A constructor's rest parameter or parameter pattern; a default or
  statement reading `this` before the instance is complete; …"
  (`class-constructor-reads-this`): an instance field's initializer may read
  `this.#f` of an earlier field, as *Construction* states; the construction
  lowering binds each field's value in order and reads an earlier one as its
  binding.
- "A class declared in a `case` clause, or one with a static member, a
  private name, …": admitted for a class declared in a static block of a
  top-level class, which runs once.
- "Reads of a class's statics before the class value exists (an instance
  member reading a private static, …); … a mutable or optional static
  field": a private static field written by the body is a module cell no
  source outside the body spells, read by instance initializers, which run
  only once the class value exists.
- A static block's closure writing a module `let` cell, and the module's
  exports read from it once at module evaluation: admitted where the lowering
  of [module cells](../SOURCE-ELABORATION.md#module-cells) refuses them today
  (conjectured).

Kept refused: "A private name in inheritance; `#x in o`" is the restriction
*No base class*; `#x in o` is not needed.

**The audit of the natives that enumerate keys.** Every native entry that
reads an object's own keys or values is checked to yield no private name and
no value under one, and to copy none: `Object.keys`, `Object.values`,
`Object.entries`, `Object.assign`, an object spread and an object pattern's
rest, `%ForIn%` and `%Iterate:ForIn%`, `JSON.stringify`, `structuredClone`,
`Reflect.ownKeys`, `Object.getOwnPropertyNames`,
`Object.getOwnPropertySymbols`, `Object.getOwnPropertyDescriptors`,
`Object.freeze` and `%Freeze:K%`. The model's private slots are own keys of
the instance that every such entry excludes, which is (P1) in the model.

**The trust rows** above, in [the trust surface](../DESIGN.md#trust-surface).

**Views in analyzed code.** A value whose type is read-only is read at a
readonly view ([records](../POSITIVE-TYPES.md#records), the views
$`\psi`$), and the pass refuses a write through it in analyzed code outside
the body, a write through a writable type it was widened to included: the
subtyping from a readonly view to a writable field or element is checked
to give no write capability (conjectured until checked against
[subtyping](../POSITIVE-TYPES.md#subtyping)).

**`@invariant` on a class.** [ANNOTATIONS.md](../ANNOTATIONS.md) gains the
reading on a class with private state: the clause holds of every complete
instance in every state, by (L4), and its paths are private fields.

**What acceptance reads.** The fragment carries each body's private state,
its members, the proposed $`\Psi_C`$ and $`I_C`$. `FunctionPlan.certify`
checks each member at $`\Psi_C`$ and each step that runs code that is not
the body's at $`\Phi\oplus_C\Psi_C`$; the module-interface check checks the
shape restrictions, that $`\Psi_C`$ preserves the references, the confinement and ownership
of every flow, *Tolerant invariant*, and that every function of the body
reads the same $`\Psi_C`$. Every proposal is untrusted: a $`\Psi_C`$ too
small fails a member's check.

## Pretext

### The handles

The three handles and the internal cursor are classes of one body, since a
private name is spelled only inside its class and the classes nested in it.
The top-level class is `PreparedText`. Its static block declares the cursor
class `LineCursor` and `PreparedRichInline`, and holds the code of
`line-break.ts`, `line-text.ts`, `layout.ts`, `measurement.ts` and
`rich-inline.ts`, and of `measureAnalysis` with its helpers, that reads or
builds a handle's state. Each function lies in the innermost of these
classes whose names it spells: the text walkers and steppers, which read the
cursor and the text handle, in `LineCursor`'s static block; the paragraph's
walkers and materialization in `PreparedRichInline`'s. Each nested static
block assigns its functions to bindings of the outer static block, written
once, which call them by name. The outer block assigns the package's
functions to one module binding, from which `layout.ts` and
`rich-inline.ts` export them.

```ts
let api: Api | null = null

/** @invariant this.#segmentFlags.length === this.#widths.length && … */
export class PreparedText {
  static #staged: TextParts | null = null
  readonly #widths: number[] = PreparedText.#check().widths // checks I, clearing the staging field before it throws
  readonly #segmentFlags: Uint8Array = PreparedText.#staged!.segmentFlags
  readonly #segments: string[] | null = PreparedText.#staged!.segments
  readonly #kinds: SegmentBreakKind[] | null = PreparedText.#staged!.kinds
  // … every field of PreparedLineBreakData, each by its initializer
  /** Each segment's text. Callers must not change it. */
  readonly segments: readonly string[] | null = this.#segments
  /** What each segment is. Callers must not change it. */
  readonly kinds: readonly SegmentBreakKind[] | null = this.#kinds
  /** Each segment's width in px. Callers must not change it. */
  readonly widths: ArrayLike<number> | null = this.#kinds === null ? null : this.#widths

  constructor() { PreparedText.#staged = null }
  static #check(): TextParts { /* as in the example */ }

  static {
    let walkPreparedLinesRaw: (prepared: PreparedText, maxWidth: number, onLine?: InternalLineVisitor) => number
    class LineCursor {
      #segment = 0
      #grapheme = 0
      static {
        walkPreparedLinesRaw = (prepared, maxWidth, onLine) => { /* reads prepared.#widths, cursor.#segment, … */ }
        // … the steppers and the other walkers
      }
    }
    /** @invariant this.#sources === null || (this.#sources.starts.length === … && …) */
    class PreparedRichInline {
      // the fields of InternalPreparedRichInline, and #sources: TextSources | null = null
      static { /* the paragraph's walkers and materialization */ }
    }
    // … preparation, the measurement caches and the package's functions, which call the walkers by name
    api = { prepare, prepareWithSegments, layout, walkLineRanges, /* … */ prepareRichInline, walkRichInlineLineRanges /* … */ }
  }
}

export type PreparedTextWithSegments = PreparedText & {
  readonly segments: readonly string[]
  readonly kinds: readonly SegmentBreakKind[]
  readonly widths: ArrayLike<number>
}
```

- **`PreparedText` and `PreparedTextWithSegments`** are one class.
  `prepareWithSegments` computes the segments and their kinds before it
  constructs, so `#segments` and `#kinds` are written by their
  initializers; its result narrows to `PreparedTextWithSegments` by a
  user-defined guard on the three public fields, checked by TScert's guard
  rules. The public `segments`, `kinds` and `widths` hold the private
  fields' own arrays as views, at upstream's read-only types (cited:
  upstream `layout.ts:53–57`, `readonly string[]`,
  `readonly SegmentBreakKind[]`, `ArrayLike<number>`), with no copy; their
  doc comments state the read-only views row, and $`\psi`$ is
  $`\mathsf{keep}`$ on every array they hold. The public fields are ordinary
  fields: external code may store an array in `segments` of a handle
  `prepare()` made, which then meets `PreparedTextWithSegments` while its
  `#segments` is `null`. So the guard gives no fact about the private
  fields, and each function taking `PreparedTextWithSegments` tests
  `#segments !== null` and throws a `TypeError` where it fails, a test
  upstream does not have. Upstream's `layout.ts:150`
  write of `prepared.kinds` after preparation becomes a part computed before
  construction.
- **`PreparedRichInline`** holds `#data: PreparedText`, an instance whose
  state is its own class's, and the paragraph's fields. The three lists of
  where its segments are in the item's text, which upstream finds at a
  line's first materialization from one test of `sourceStarts`
  (`rich-inline.ts:1198–1199`, writing the three at `:1176–1178`), are one
  record `TextSources` held by one field, `#sources`, `null` until a line is
  first materialized and then written once, by a $`\mathsf{scalar}`$ write
  of a record whose three lists `findSegmentSources` fills in one loop over
  the segments (`:1160–1181`). Its invariant, the lazy-list invariant, is
  `#sources` `null`, or holding three lists each as long as
  `#data.#widths`. It is discharged by *Tolerant invariant*'s checked single write:
  the record is complete before the write, and nothing writes its lists
  after. The whole-line fields, written by `findWholeLine`'s lambda
  (`:817–825`), are computed before construction.
- **Preparation** happens before construction. `measureAnalysis` and its
  helpers move into the body. In paragraph mode, where upstream returns a
  handle sharing the paragraph's lists while they are still being filled,
  with a `segmentFlags` of the paragraph's length and `widths` of the item's
  (`prepare.ts:379–383`; `rich-inline.ts:479–573`), it returns a plain record
  of the item's results, which no class's invariant reads.
- **The measurement caches** of `measurement.ts` are confined collections:
  the module binding `measureState` (cited: `:405`), which no module
  exports, holds the record whose `Map`s of fonts (`:1379`, `:1447–1448`)
  hold each font's measurement, its `Map`s of segment metrics and the
  advances and `lineStartExtras` lists `getSegmentFit` caches (`:1262`); the code that reads them
  moves into the body with the rest of preparation. `breakableFitAdvances`
  shares the cached lists as upstream does. The body's writes to values
  from the caches are charged: preparation copies a cached list before
  changing it (cited: `prepare.ts:533–541`, a `slice()` before each
  adjustment, the cached lists being shared by every occurrence of a text),
  so no owned spine or cell is written; the insertions (`:697`, `:729`,
  `:800`, `:1304`, `:1380`) store fresh values; the fields set lazily on a
  font's measurement, its segment metrics and the state record (`:595`,
  `:731`, `:780`, `:818`, `:824`, `:844`, `:847`, `:879–914`, `:1055`,
  `:1072`, `:1189`, `:1207`, `:1262`, `:1374`, `:1457`) are fields of
  records allocated at sites that are not owning, since a handle holds the
  advances and `lineStartExtras` lists (`prepare.ts:526`, `:529`) and its
  own arrays and no such record (conjectured until the flow runs), so not
  owned. `clearCache` (`layout.ts:360–363`)
  calls `clearMeasurementCaches` (`measurement.ts:1453–1458`): two `clear`s
  of confined collections, which hold no location of $`\mathsf{own}_C`$,
  and a number written to the state record, which is not owned; its entry
  in $`\Psi`$ is $`\mathsf{keep}`$ on every part of $`\mathsf{own}_C`$.
- **The internal cursor** is a `LineCursor`, whose two private number
  fields `#segment` and `#grapheme` the steppers write. The walker allocates
  it and passes it only to functions of the body that it calls by name.
  Every member writes only cursors it allocates, so
  $`\psi_{\mathtt{LineCursor}.\#\mathit{segment}}=\psi_{\mathtt{LineCursor}.\#\mathit{grapheme}}=\mathsf{keep}`$,
  and the walker's cursor facts cross `onLine`. The public `LayoutCursor`
  stays a record that applications build, read and keep as JSON (cited:
  Decisions Log, 2026-09-24, "cursors and ranges are plain JSON"); it is
  validated by `normalizePreparedLineStart` on entry and copied into a
  `LineCursor`.

The protocol for pretext (conjectured): $`\mathsf{scalar}`$ on
`PreparedRichInline.#sources`, from `materializeRichInlineLineRange`, and
$`\mathsf{keep}`$ on every other private field and on every part of
$`\mathsf{own}`$. It preserves the references: `#sources` changes only
from `null` to a fresh record, and no member writes an owned spine, cell or
field after construction. No walker reads `#sources`.

### What each site gets

The sites are the dossier's (cited: [dossier](callback-frames-dossier.md),
§2 "Form (a)" and "Form (b)", §4); what each gets is conjectured.

- **P22, form (b)**: `walkPreparedLinesRaw` and `walkPreparedComplexLines`
  after `onLine`. The handle's facts (`segmentCount === widths.length`, the
  relation of the lengths of `segmentFlags` and `widths`) come from $`I_C`$
  at the private reads and survive `onLine` by Private frame, with
  $`\psi_s=\psi_c=\mathsf{keep}`$. `walkLineRanges` holds no fact.
  `walkRichInlineLineRanges`: the paragraph's fields its lambda reads after
  each step survive the user's `onLine`. `layoutWithLines`: its lambda is a
  function of the body used as a value, so a member; it pushes onto
  `lines`, which is fresh and not owned, and writes no owned location.
- **P22, form (a)**: the six cursor sites. The cursor's two indices survive
  `onLine` and every step that runs code that is not the body's; the
  steppers' writes are the walker's own steps, checked as written.
- **P18**: at pretext's sites the prepared handle is a class with private
  state, so its invariant holds after `step(c)` by (L4), and its fields keep
  the arrays they hold. Paper II's own program, with `Prepared` a structural
  type external code may build, is outside.
- **P20**: a value of a class with private state read back from a
  `Map<string, ClassTable>` meets $`I_C`$ at its first private read, by
  (L4); no contract of `Map` beyond its read returning a stored value is
  needed.
- **P15**: a module constant array moved into a private static field of the
  body is owned, and $`\psi_s=\mathsf{keep}`$ keeps its length.
- **P16**: a cell initialized at first use, moved into a private field
  holding `null` until its one write, changes by $`\mathsf{scalar}`$; its
  invariant `bmp === null || bmp.length === 65536` is kept by *Tolerant
  invariant*'s checked single write, as the lazy lists' is.

### Performance

The criterion is upstream (`plain`): no operation slower.

**Measured** on mechanical variants of upstream `src/` at `0d102a5c`,
bundled to one ESM file, all with equal checksums of results:

- `plain`: upstream as is.
- `plainw`: the same code in a class's static block.
- `designscalar`: this design's shape. `PreparedText` with the staging
  field, `#parts`, 17 private fields and the three public copies, each
  written once by its initializer, `#take` checking the staged parts;
  `segments` and `kinds` computed before construction; `LineCursor` with
  `#segment` and `#grapheme` around `line-break.ts`, the streams copying the
  public cursor in and out; `PreparedRichInline` a class with staging, its
  whole line computed before construction, `#sources` owned; nested blocks
  handing their functions to bindings of the outer block; exports assigned
  in the static block.
- `design`: `designscalar` with the cursor's indices in an owned two-cell
  array behind one private field.

Setup: 563 corpus paragraphs, 72,144 UTF-16 units from eight of pretext's
corpus files; a stand-in Canvas (7.25 px per unit below U+2E80, 16 px
above); five rich-inline operations on paragraph handles (every third
paragraph one item, the others cut into items of about 40 units in two
fonts). One process per variant with 5 warm-up and 15 timed passes, the
median per operation; 15 processes per variant in shuffled order; the
figure is the median of the process medians. Apple M2 Max, load average
4.1–5.0; Node 26.13.0 (V8 14.6) and Bun 1.4.2 (JavaScriptCore).

| Operation | V8, `designscalar` / `plain` | JSC, `designscalar` / `plain` | V8, `design` / `plain` | JSC, `design` / `plain` |
| --- | --- | --- | --- | --- |
| `prepare`, cache cleared | 0.938 | 0.986 | 0.939 | 0.984 |
| `prepare`, text seen | 0.932 | 0.978 | 0.934 | 0.983 |
| `prepareWithSegments`, text seen | 0.945 | 1.011 | 0.948 | 1.027 |
| `layout` | 0.931 | 0.996 | 0.931 | 0.997 |
| `walkLineRanges` | 0.956 | 0.940 | 1.073 | 1.073 |
| `measureLineStats` | 0.936 | 0.929 | 1.035 | 1.091 |
| `layoutWithLines` | 0.912 | 0.885 | 0.937 | 0.907 |
| `layoutNextLineRange` | 0.953 | 0.909 | 1.208 | 1.283 |
| `layout`, full walker | 0.611 | 0.981 | 0.624 | 0.995 |
| `walkLineRanges`, full walker | 0.647 | 0.976 | 0.661 | 1.001 |
| rich: prepare, text seen | 0.937 | 1.010 | 0.947 | 0.995 |
| rich: prepare, walk, materialize | 0.956 | 1.007 | 0.958 | 1.016 |
| rich: walk, materialize | 0.904 | 0.946 | 0.928 | 0.942 |
| rich: stats | 0.756 | 0.929 | 0.795 | 1.011 |
| rich: stream | 0.870 | 0.953 | 0.918 | 1.106 |

- **No regression of `designscalar` against upstream is detected within
  the measured spread**: its largest ratio, 1.011 (JSC,
  `prepareWithSegments`), is inside the spread of `plain`'s own processes,
  and the ranges of the two variants overlap on several operations.
- **The cursor behind an owned array regresses**: `design` is slower than
  upstream wherever a cursor is read or made, up to +21% (V8) and +28%
  (JSC) on `layoutNextLineRange`. The cursor's indices are private number
  fields for this reason.
- **Against the same code in a static block** (`plainw`), `designscalar`
  is between 10% faster and 3% slower, but JSC's `layoutNextLineRange`,
  +11% (10.86 against 9.77 ms): the stream allocates one `LineCursor` per
  line, where upstream writes the result's own records. JSC's `plain` is
  slower there than both (11.96 ms).
- The three public copies of `designscalar` cost `prepareWithSegments`
  1–2% on V8 and 3–4% on JSC against `plainw`; the specified shape gives
  the private arrays out as views and makes no copy.
- A field declared and then assigned in the constructor, in place of
  written by its initializer, cost the full walker 15–19% on V8 against
  `plainw` in an earlier run on the same setup without rich-inline
  operations, and nothing on JSC; which V8 mechanism causes it is not
  established.
- On V8, `plain`'s full walker takes 49.6 and 53.8 ms in these processes,
  against 30.6 and 34.8 ms in that earlier run, which laid out no paragraph
  handle; the variants in a static block do not show it. Its cause is not
  established, and it makes those two ratios no evidence of a gain.

**Limits.** No browser ran, and Firefox (SpiderMonkey) was not measured;
upstream records differences of this size from V8's inlining budget alone
(cited: `measurement.ts:983–988`, one field more in a function V8 then no
longer inlined, 11–18% slower). The stand-in Canvas leaves out real
measurement, so the handle's share of preparation is overstated. The
variants are a mechanical transform of upstream's functions, not a
hand-written rewrite; the table's variants differ from this design in
two points, `measureAnalysis` in paragraph mode constructing an instance
and `#sources` holding the three lists in three fields, which `views`
below does not.

**The specified shape and retained memory.** Measured on `views`, the
shape this draft specifies: `measureAnalysis` in paragraph mode returning a
plain record, `#sources` one field, the staged parts kept by no field, the
cache's lists shared as upstream shares them, and the public `segments`,
`kinds` and `widths` holding the private arrays. Setup above, against
`plain`, 15 processes each, load average 5.5–6.0, with four more
operations: `layout` and `walkLineRanges` on `prepareWithSegments`
handles, `walkLineRanges` at 12 and 30 px, and a visitor reading
`h.segments` and `h.widths` of the handle for every line.

- **Time**: no operation of the 19 is slower than `plain` outside the
  spread of `plain`'s own processes, in either engine. On V8 every ratio
  to `plain` is between 0.60 and 0.96. On JSC the ratios are between 0.89
  and 1.013; the two above 1 (`prepare` of seen text, 1.001; rich prepare,
  walk and materialize, 1.013) are below `plain`'s slowest process. The
  visitor reading `h.segments` per line: 0.959 (V8), 0.934 (JSC).
- **Retained heap** per handle, bytes after a full collection holding 20
  handles of each text, `views` against `plain`: `prepare` 2020 against
  1972 on V8 (×1.02) and 1929 against 1867 on JSC (×1.03);
  `prepareWithSegments` 3592 against 3586 (×1.00) and 4839 against 4778
  (×1.01), the same after every public array is read;
  `prepareRichInline` 4335 against 4297 (×1.01) and 5717 against 5676
  (×1.01). The difference on a `prepare` handle is six fields upstream's
  record lacks there (`#items`, `#segments`, `#kinds` and the three
  public fields).
- **The alternatives measured** on the same setup: the public arrays copied
  at construction (`shared`) retain 29–33% more per `prepareWithSegments`
  handle; copied by getters at first read (`sharedlazy`) they cost JSC
  17.6% for the visitor reading `h.segments` per line; every cached
  advances list copied (`exactcopy`) costs JSC 4–6% on preparation and
  49–98% of retained heap; frozen arrays (`frozen`) cost `layout` ×4.2 on
  V8 and ×6.8 on JSC; a store's deep freeze freezes the same public arrays
  of a handle, at a cost not measured.

## Negatives and controls

**Negative cases**, each unsafe under Node (observed: each program, as
JavaScript, run with `node`, printing the reads), each refused:

- `invalid-private-escape-return`: a member returns `#widths` at
  `number[]`; the client pushes onto it; the walker reads `#flags` past its
  end: `[0, 0, undefined]`. Refused by *Confinement* at the return: the type
  is not read-only.
- `invalid-private-escape-argument`: the walker passes `#widths` at
  `number[]` to the user's callback, which pushes onto it:
  `[0, 0, undefined, undefined]`. Refused by *Confinement* at the argument.
- `invalid-private-shallow-copy`: a member returns `#fits.slice()` of an
  array of arrays; the client truncates an inner array; the walker reads
  `[undefined, undefined, 3, 4]`. Refused by *Confinement*: the copy's
  elements hold storage.
- `invalid-private-received-array`: the factory stages an array it received
  without copying it; the caller pushes onto its alias after construction:
  `[0, 0, undefined]`. Refused by *Ownership at construction*.
- `invalid-private-reentrant-member`: a member pops `#widths`; the walker
  caches the length; the visitor calls the member:
  `[1, undefined, undefined]`. Refused by *Reference-preserving protocol*:
  a `pop` drops a listed cell.
- `invalid-private-rewritten-field`: a member writes another array to
  `#widths`; the walker reads through the field after the visitor calls it:
  `[undefined, undefined, undefined]`. Refused by *Reference-preserving protocol*:
  the field's old array leaves $`R_C`$.
- `invalid-private-await-between`: a body function tests
  `#pos < #widths.length`, awaits, and reads `#widths[#pos]`; a member
  setting `#pos` to the length, within a reference-preserving protocol, runs while it is
  suspended: `undefined`. Refused at the read: the `await` runs code that is
  not the body's, and $`\psi_{\#\mathit{pos}}=\mathsf{scalar}`$ does not
  keep the test.
- `invalid-private-escaping-collection`: a handle holds, uncopied, an
  array from a cache `Map` the module exports; external code pops the cached
  array during the visitor: `[1, undefined, undefined]`. Refused by
  *Confined collections*: the `Map` is not confined.
- `invalid-private-replaceable-method`: the walker bounds its loop by a
  public prototype method; external code replaces it:
  `[1, 1, undefined, undefined]`. Refused by *Lexical dispatch*: the bound
  states no fact about `#widths`.
- `invalid-private-shadowed-method`: the same with the class and its
  prototype frozen and an own property of the instance shadowing the
  method: `[1, 1, undefined, undefined]`. Refused by *Lexical dispatch*.

- `invalid-private-view-widened`: analyzed code outside the body passes a
  view at `readonly number[]` where `{ length: number }` is expected and
  sets its length to 0 during the visitor; the walker reads
  `[undefined, undefined]`. Refused at the write: a write through a view
  widened to a writable type (*Views in analyzed code*).
- `invalid-private-incoming-record`: private storage
  `{ n: number; extra: number }` given out at a read-only type; the visitor
  passes it to a member `change(x: { n: number })`, which sets `n` to 0;
  the walker, which tested `#rec.n <= #items.length` and reads
  `#items[#rec.n - 1]` after each visitor, reads `[undefined, undefined]`
  (both type-check under `tsc` 7.0.2 `--strict`). Refused by *Incoming
  values*: the write is charged, whatever the parameter's type.
- `invalid-private-incoming-view`: a member `trim(xs: { length: number })`
  decrements the length of what it is given; the visitor passes it a view
  of `#widths`, with no cast (both type-check under `tsc` 7.0.2
  `--strict`); the walker, which cached the length, reads
  `[1, undefined, undefined]`. Refused by *Incoming values*: the write is
  charged to $`\mathsf{own}_C`$ and breaks *Reference-preserving
  protocol*.

**Restriction controls**, each safe under Node and refused by its stated
restriction (observed):

- `private-base-class-refused`: a base constructor returns a plain object,
  which receives the derived class's private fields; the walker reads
  `[1, 1]` from it. *No base class*.
- `private-two-evaluations-refused`: a class evaluated twice in a function;
  one evaluation's static method given the other's instance throws a
  `TypeError`. *Evaluated once*.
- `private-open-invariant-refused`: a member pushes onto `#widths` and then
  onto `#flags` under $`|\mathit{flags}|=|\mathit{widths}|`$, with a walker
  reading `#flags[i]` before `visit`: `[0, 0, 0, 0]`. *Tolerant
  invariant*.

**Positive cases**: the example, its visitor calling every member
(`[0, 0, 0]`); `private-confined-collection`, a handle holding, uncopied, an
array from a cache `Map` only the body reaches, its visitor preparing again
(`[1, 1]`); `private-escape-copy`, a member giving out a copy of a
number array that the client pushes onto (`[0, 0]`); `private-view`, a
member returning `#widths` at `readonly number[]` and the walker's visitor
reading it, the walker reading `#widths[i]` after each call (`[1, 1]`);
`private-frozen-view`, the same with the view frozen by the client before
the walk (`[1, 1]`);
`bounds-pattern-unreachable-field-refused` and
`bounds-pattern-unreachable-handle-refused` rewritten with a class with
private state.

**Observation**: on an instance, `Reflect.ownKeys`,
`Object.getOwnPropertySymbols`, `Object.values`, `Object.assign({}, h)` and
`JSON.stringify` yield no private key or value; a spread, a JSON copy, a
`structuredClone` copy, a `Proxy` and `Object.create(h)` throw a
`TypeError` at a private read; a frozen instance reads as before;
`h.constructor` is the class.

**The read-only views row is load-bearing** (observed): a client that
passes `private-view`'s result where `{ length: number }` is expected and
sets its length to 0 type-checks under `tsc` 7.0.2 `--strict` and leaves
the walker reading `[undefined, undefined]`. The design accepts that program, whose
client breaks the row; no case can refuse it, since the client is outside
the analyzed sources.

**Controls** (forged fragment or forced proposal), each refused:
$`\Psi_C`$ forced smaller than a member's effect; a member forged as a
non-member; a function used as a value forged as called by name only; an
`await` forged as body code; a confined flow forged to an outside argument; a view forged at a type
that is not read-only; a type forged read-only; an incoming value forged as
fresh; an owning allocation site forged not owning; `cache.get(k).array.pop()`
forged uncharged, where only `array` enters private state and the
record from the cache comes from a site that is not owning; a body write to a possibly exposed location forged without its throw
edge;
a copy of an array of arrays forged unconfined; a write to a value from a confined collection forged
uncharged; an exported collection forged confined; an owned store forged as
fresh; a staging field forged left set on a throw; an initializer forged to
pass `this` to a call; $`I_C`$ forged to read a path outside $`R_C`$.

## Stages and cost

1. **The rule in the note and in Lean**: the regions, $`\Psi_C`$ and its
   bound, $`\Phi\oplus_C\Psi_C`$, (P1) and (P2) as invariants of states,
   (L1) to (L4), Reliance at $`\Phi\oplus_C\Psi_C`$. Front: bodies with
   private state, members, $`\Psi_C`$ as a least fixed point over the
   members, computed once per body and keyed by its sources in the
   [stage store](../STAGE-STORE.md); the shape restrictions and the
   confinement check; `@invariant` on a class. The native audit. The cases
   and controls above. Covers the example.
2. **The fragment rows**: initializers reading earlier fields, classes in a
   static block, the staging field, a static block's writes of a module cell
   and the exports read from it.
3. **Pretext**: the rewrite above on the fork; the five handle sites and six
   cursor sites checked; the rewritten source benchmarked against upstream
   on the setup above, with retained memory, and in a browser.
4. **P15 and P16**: module tables and lazily initialized cells as private
   fields.

Each stage states the whole definition; what a stage leaves out is an
explicit restriction, documented in SOURCE-FRAGMENT.md and enforced.

Cost (conjectured):

- Lean: (L2) and (L4) by one induction over runs with member certificates
  at $`\Psi_C`$; (L3) from reference preservation; (P1) in the model by the native audit;
  the effect $`\Phi\oplus_C\Psi_C`$ joins the effect language as a bound per
  region. Two to four weeks.
- Front: the fixed point over members and the confinement check, a flow
  over the body's code.
- The pass: one region test per entry of an effect at a step that runs code
  that is not the body's; no work per call site beyond respect.
- Trust: two rows, one of the language and one of callers' use of views,
  stated in the API. No row about external code's use of a
  handle.
- Sources: pretext's handle code moves into one class body; its public
  handle types become a class; the scope above is lost.
