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
   every call of unknown code (proved: Paper I, Lean `frame_box`,
   `rely_chain`).

It reads three existing pieces:

- **Private names** (cited:
  [classes](../SOURCE-CONTRACTS.md#classes), "Private names"). A private
  name `#x` is a key $`\sigma_{C.\#x}`$ identified by its declaring member;
  `o.#x` and `o.#x = e` are the named read and write at it; a copy takes no
  private slot.
- **Stable keys** (cited: [records](../POSITIVE-TYPES.md#records), `@stable`).
  A location allocated at a contract admitting one value keeps it in every
  heap; a path through such fields is rigid (Paper I, "Invariant assertions
  and rigid paths"). A private field written once, by its initializer, is
  such a location.
- **Type invariants** (cited:
  [type invariants](../ARITHMETIC.md#type-invariants),
  [`@invariant`](../ANNOTATIONS.md#invariant-c-on-a-type)). The clause
  language states $`I_C`$ over the paths `this.#f`.

New machinery: four regions, one protocol per class, one rule, one
confinement check and one trust row, a property of the language. No new
judgment form, no new modality, no world component.

## The example

```ts
let prepare: (n: number) => Handle
let walk: (h: Handle, visit: (w: number) => void) => number

/** @invariant this.#flags.length === this.#widths.length */
class Handle {
  static #staged: Parts | null = null
  readonly #parts: Parts = Handle.#take()
  readonly #widths: number[] = this.#parts.widths
  readonly #flags: number[] = this.#parts.flags

  static #take(): Parts {
    const p = Handle.#staged
    if (p === null || p.flags.length !== p.widths.length) throw new TypeError("made by prepare()")
    Handle.#staged = null
    return p
  }

  static {
    prepare = (n: number): Handle => {
      Handle.#staged = { widths: new Array<number>(n).fill(1), flags: new Array<number>(n).fill(0) }
      return new Handle()
    }
    walk = (h: Handle, visit: (w: number) => void): number => {
      const widths = h.#widths, flags = h.#flags
      let s = 0
      for (let i = 0; i < widths.length; i++) { visit(widths[i]!); s += flags[i]! }
      return s
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
$`\mathsf{keep}\sqsubseteq\mathsf{init}\sqsubseteq\mathsf{scalar}\sqsubseteq\mathsf{grow}\sqsubseteq\mathsf{any}`$,
regions read at the entry heap, $`\Phi\triangleleft_K S`$ for respect and
$`\Box_\Phi F`$ for the modality.

### Definitions

**Classes with private state.** A class declares private names
$`\sigma_{D.\#f}`$ for its instance fields, static fields and methods. A
private name is spelled only inside its class's declaration, the
declarations of classes nested in it included. Below, $`C`$ is a top-level
class with private state, and its *body* is the code lexically inside its
declaration; the classes declared in that body are $`C`$'s *classes*, $`C`$
among them. One body, one protocol: a nested class's code reads the private
state of the classes around it, so they share it.

**Storage** is the locations of arrays, typed arrays and records: their
spines, view spines, element cells and field locations.

**The regions.** For a top-level class $`C`$:

- $`\mathsf{priv}_C(\rho,h)`$ is the set of field locations
  $`o.\sigma_{D.\#f}`$, for every object $`o`$ of $`h`$ and private field
  $`\#f`$ of one of $`C`$'s classes $`D`$, and the cells of their private
  static fields but their staging fields ([fields written once](#the-class-shape-the-rule-requires)).
- $`\mathsf{own}_C(\rho,h)`$ is the storage reachable in $`h`$ from a
  location of $`\mathsf{priv}_C`$ through element cells and record fields,
  stopping at instances of classes with private state, whose state is
  $`\mathsf{priv}`$ of their own body. Its three parts are
  $`\mathsf{own}_C.\mathsf{spines}`$ (array spines and view spines),
  $`\mathsf{own}_C.\mathsf{cells}`$ and $`\mathsf{own}_C.\mathsf{fields}`$.
- $`R_C=\mathsf{priv}_C\cup\mathsf{own}_C`$.

**Calls through a value.** A call names its callee when its callee is a
function of the body, or a binding of the body written once with one; every
other call is a call through a value.

**Members.** The members $`M_C`$ are the functions of the body that a call
through a value can reach: the constructors of $`C`$'s classes, which
`new h.constructor()` reaches; every public method, accessor and static; and
every function of the body used as a value other than as such a binding's
content (returned, thrown, stored in storage, or passed as an argument). A
function the body only calls by name is no member.

**The protocol.** $`\Psi_C`$ is an effect with one entry on each part of
$`R_C`$:

```math
\Psi_C=\{\ \mathsf{priv}_C:\psi_{p},\ \ \mathsf{own}_C.\mathsf{spines}:\psi_{s},\ \ \mathsf{own}_C.\mathsf{cells}:\psi_{c},\ \ \mathsf{own}_C.\mathsf{fields}:\psi_{f}\ \}
```

It is the least such effect for which every member $`m\in M_C`$, checked
with each of its calls through a value bounded on $`R_C`$ by
$`\Psi_C`$, has normal and exceptional effects that, after `fresh_eff`
drops the locations it allocated, bound every location of $`R_C`$ of its
entry heap by $`\Psi_C`$. A member that writes only storage it allocated
contributes $`\mathsf{keep}`$.

**The bound on $`R_C`$.** For an effect $`\Phi`$, $`\Phi\oplus_C\Psi_C`$
bounds the locations of $`R_C`$ by $`\Psi_C`$ and every other location by
$`\Phi`$:

```math
h\xrightarrow{\Phi\oplus_C\Psi_C}_\rho h'\iff h\xrightarrow{}_\rho h'\ \wedge\ \forall l<|h|.\ h'(l)=h(l)\ \vee\ \exists (r:\delta)\in(\text{if } l\in R_C(\rho,h) \text{ then } \Psi_C \text{ else } \Phi).\ l\in r(\rho,h)\wedge\delta_{|h|}(h(l),h'(l))
```

**The class invariant.** $`I_C(o,h)`$ is the clause of `@invariant` on
$`C`$, with `this` read as $`o`$; its paths are `this.#f` and the lengths
and elements they reach; $`\mathrm{supp}(I_C)`$ is its support, inside
$`R_C`$. A class without `@invariant` has $`I_C=\mathsf{true}`$.

### Private frame

A call through a value runs either code outside the body, which enters it
only by calling members, or a member itself. Either way:

```math
\frac{c:\Phi\mid\Phi^{e}\qquad c\ \text{a call through a value}}
     {c:\ \Phi\oplus_C\Psi_C\ \mid\ \Phi^{e}\oplus_C\Psi_C}\ \textsf{(Private frame)}
```

An unknown callback, of effect $`\top`$, has by the rule the effect
$`\Psi_C`$ on $`R_C`$. A native step on storage outside $`R_C`$ meets the
rule trivially; a native step on owned storage is a step of the body's code,
checked as written.

**At a callback.** Let a walker hold $`F`$ with a support $`S`$ inside
$`R_C`$ and $`\Psi_C\triangleleft_K S`$. Tolerant frame gives
$`K\wedge F\vdash\Box_{\Phi\oplus_C\Psi_C}F`$, and Reliance carries $`F`$
across every call through a value the walker makes, given rigidity
([what must be proved](#what-must-be-proved), (L3)). In the example
$`\Psi=\{\mathsf{priv}:\mathsf{keep},\ \mathsf{spines}:\mathsf{keep},\ \mathsf{cells}:\mathsf{keep},\ \mathsf{fields}:\mathsf{keep}\}`$:
`prepare` and `new Handle()` write only what they allocate and the staging
field, `walk` writes nothing. So $`i<|\mathit{widths}|`$ and
$`|\mathit{flags}|=|\mathit{widths}|`$ cross `visit` (conjectured, the
design's claim).

**At a private read.** `o.#f` either throws, as JavaScript does where `o`
holds no slot, or reads a location of $`\mathsf{priv}_C`$ of an instance,
which meets $`I_C`$ ((L4) below). A value of type $`C`$ is any object; the
private read is the elimination that gives $`I_C`$. A field written once is
a stable key, so `o.#f` is a rigid path.

**Reentrancy.** A callback may call any member on any instance. Two
variants of the example:

- A member `truncate(h)` pops `h.#widths`. $`\psi_s=\mathsf{any}`$, so
  $`i<|\mathit{widths}|`$ does not survive `visit`, and a walker that
  cached the length is refused at its read; under Node a visitor calling
  `truncate` makes it read `[1, undefined, undefined]` (observed).
- A member pops `#widths` and then `#flags`. The first pop breaks
  $`I_C`$ until the second; the class is refused by *Tolerant*, below.

### What must be proved

The rule rests on two invariants of states and four lemmas. Each is
conjectured until its Lean exists; the statement each cites is labelled.

- **(P1) No private key is a value.** No value of $`\rho`$ or $`h`$ is a
  $`\sigma_{C.\#f}`$, and no step yields one or the content of a location
  of $`\mathsf{priv}_C`$ to code outside $`C`$'s body. For JavaScript,
  cited: [ECMA-262](../REFERENCES.md#ecma-262), Private Names and the
  operations PrivateFieldFind, PrivateGet, PrivateSet and PrivateFieldAdd:
  a private name is reachable only through the lexical environment of its
  class body, no reflection operation lists private elements, and a copy or
  a proxy holds none. For the model, conjectured until the audit of
  [the natives that enumerate keys](#what-tscert-must-change).
- **(P2) Confinement.** Every path from a frame of code outside $`C`$'s body
  to a location of $`\mathsf{own}_C`$ passes through a location of
  $`\mathsf{priv}_C`$. Paths run through fields, element cells and
  collection contents; a closure's environment is not reachable from a
  holder of the closure. Conjectured, from the
  [confinement check](#the-class-shape-the-rule-requires).
- **(L1) Outside step.** From a state meeting (P1) and (P2), a step of code
  outside $`C`$'s body leaves every location of $`R_C`$ unchanged and keeps
  (P1) and (P2). A write at $`o.\sigma`$ needs $`\sigma`$ as a static key,
  which the code lacks, or as a value, which (P1) excludes; a write to owned
  storage needs a reference, which (P2) excludes.
- **(L2) Outside run.** A run of code outside $`C`$'s body from $`h`$ changes
  each location of $`R_C(h)`$ within $`\Psi_C`$. By induction on the budget
  $`k`$: the run changes $`R_C`$ only inside calls of members, each bounded
  by its certificate at $`\Psi_C`$, whose own calls through a value are
  bounded by the rule at a smaller budget.
- **(L3) Rigidity.** For every transition of such a run,
  $`\mathsf{own}_C(h)\subseteq\mathsf{own}_C(h')`$: private fields are
  written once and an owned reference is written only by an
  $`\mathsf{init}`$ (the shape below). Then $`\Phi\oplus_C\Psi_C`$ is rigid
  when $`\Phi`$ and $`\Psi_C`$ are rigid and $`\Psi_C\sqsubseteq\Phi`$, as
  for $`\Phi=\top`$ and for `{ values: "any"; spines: "grow" }` with
  pretext's $`\Psi`$.
- **(L4) The class invariant.** In every state of every run,
  $`I_C(o,h)`$ holds of every instance $`o`$. The constructor establishes it
  for every caller; every change the body makes to a location of $`R_C`$ of
  an existing instance is within a change $`\mathrm{supp}(I_C)`$ tolerates
  (*Tolerant*); outside code changes none (L1). No step of the argument
  assumes $`I_C`$ of the state it concludes it of.

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
- **No replaceable code.** No call of analysed code reaches code of the
  class through a property other code can replace: the class has no public
  prototype method, accessor or static method, or the class and its
  prototype are frozen when its evaluation ends. The body calls its own code
  by name and through private names, and the module's exports are bindings
  fixed when the module is evaluated. A public data field is an ordinary
  field.
- **Evaluated once.** Each evaluation of a class declaration makes new
  private names, and the model identifies a name by its declaring member. A
  class with private state is declared at the top level of its module, or in
  a static block of such a class, which runs once.
- **Fields written once.** Every private instance field is written once, by
  its initializer, and every private static field is written once by its
  initializer, but one: a class may have one *staging* field, a private
  static that holds the values of the instance being constructed. The body
  writes it, constructs, and the first initializer takes and clears it, with
  no call through a value in between, so it holds nothing at any state where
  code outside the body runs. Its reason: an initializer cannot read the
  constructor's arguments, and a field declared and then assigned in the
  constructor costs the walkers 15–19% on V8
  ([performance](#performance)). The instance's changing state lives in
  owned storage.
- **Confinement.** A value is *confined* when it is read from a private
  field or from confined storage, or stored into either. A confined value
  that may be storage flows only to: a binding of the body; the object of an
  element or field read or write, or of a `length` read; an initializer of a
  private field, or a write into confined storage; an argument of a call
  naming a function of the body, whose parameter is then confined; and a native whose audited
  contract calls no code but the body's and keeps no reference to it, a
  copy (`slice`, `Array.from`, a typed array built from it) among them. A
  return out of a member, a `throw`, a `yield` or an `await` of it, a store
  into storage not confined, and an argument of a function outside the body
  are refused. A closure of the body may capture a confined value; a closure
  given out is a member, and its own flows are checked the same. A copy is
  not confined, and may go anywhere.
- **Ownership at construction.** Storage enters private state, or confined
  storage, only at a location's first write (an initializer, or an
  $`\mathsf{init}`$ of a location holding `null` or `undefined`), and only
  storage allocated during the current call of the body, a copy made there,
  or storage already confined (a cache the body keeps).
- **Tolerant invariant.** Every change the body makes to a location of
  $`R_C`$ of an existing instance, and every entry of $`\Psi_C`$, is one
  $`\mathrm{supp}(I_C)`$ tolerates. An invariant that one write breaks and a
  later write restores is refused, as Paper I's limit "Broken and restored
  invariants" states for assertions.

## Trust

The new row of the [trust surface](../DESIGN.md#trust-surface), a property
of the language:

> ECMAScript private names behave as the specification states
> ([ECMA-262](../REFERENCES.md#ecma-262), Private Names): code outside a class
> body reads, writes and enumerates no private element of the class or of
> its instances, no operation yields a private name as a value, and a
> private field is installed only by its class's own construction. Code
> running outside the language's semantics (a debugger, an inspector
> protocol) is outside the model.

What it replaces:

- **No assumption about external code's use of a handle.** A copy, a JSON
  copy, a `structuredClone` copy, a proxy and an object inheriting from a
  handle throw a `TypeError` at the first private read (observed), which
  safety admits.
- **The invariant of a class with private state needs no caller trust.**
  The row on exported preconditions ("the type invariant … of each type its
  parameters' types name, a sealed handle's included") does not apply to
  such a class: its invariant holds of every instance by (L4).
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
6317). `Object.freeze` leaves private fields as they are, and a store's
deep freeze reaches no owned storage (observed). Upstream's side table for
frozen paragraph handles (`rich-inline.ts:1141–1178`) is not needed.

A worker that prepares and a page that lays out need an explicit pair of
functions, one writing a handle's parts to a plain value, one checking
$`I_C`$ of such a value and constructing from a copy of it; neither is part
of this design.

## What TScert must change

**Refusal index rows to lift** (cited: SOURCE-FRAGMENT.md, the table
"Classes"):

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

**The trust row** above, in [the trust surface](../DESIGN.md#trust-surface).

**`@invariant` on a class.** [ANNOTATIONS.md](../ANNOTATIONS.md) gains the
reading on a class with private state: the clause holds of every instance
in every state, by (L4), and its paths are private fields.

**What acceptance reads.** The fragment carries each class's private state,
its members, the proposed $`\Psi_C`$ and $`I_C`$. `FunctionPlan.certify`
checks each member at $`\Psi_C`$ and each call through a value at
$`\Phi\oplus_C\Psi_C`$; the module-interface check checks the shape
restrictions, the confinement and ownership of every flow, *Tolerant*, and
that every function of the body reads the same $`\Psi_C`$. Every proposal
is untrusted: a $`\Psi_C`$ too small fails a member's check.

## Pretext

### The handles

The three handles and the internal cursor are classes of one body, since a
private name is spelled only inside its class and the classes nested in it.
The top-level class is `PreparedText`. Its static block declares the cursor
class `LineCursor` and `PreparedRichInline`, and holds the code of
`line-break.ts`, `line-text.ts`, `layout.ts` and `rich-inline.ts`, and of
`measureAnalysis` with its helpers, that reads or builds a handle's state.
Each function lies in the innermost of these classes whose names it spells:
the text walkers and steppers, which read the cursor and the text handle, in
`LineCursor`'s static block; the paragraph's walkers and materialization in
`PreparedRichInline`'s. Each nested static block assigns its functions to
bindings of the outer static block, written once, which call them by name.
The outer block assigns the package's functions to one module binding, from
which `layout.ts` and `rich-inline.ts` export them.

```ts
let api: Api | null = null

/** @invariant this.#segmentFlags.length === this.#widths.length && … */
export class PreparedText {
  static #staged: TextParts | null = null
  readonly #parts: TextParts = PreparedText.#take() // checks I and clears the staging field
  readonly #widths: number[] = this.#parts.widths
  readonly #segmentFlags: Uint8Array = this.#parts.segmentFlags
  // … every field of PreparedLineBreakData and PreparedSegments, each by its initializer
  readonly segments: readonly string[] | null = this.#parts.segmentsCopy
  readonly kinds: readonly SegmentBreakKind[] | null = this.#parts.kindsCopy
  readonly widths: ArrayLike<number> | null = this.#parts.widthsCopy

  static #take(): TextParts { /* as in the example */ }

  static {
    let walkPreparedLinesRaw: (prepared: PreparedText, maxWidth: number, onLine?: InternalLineVisitor) => number
    class LineCursor {
      readonly #at: number[] = [0, 0]
      static {
        walkPreparedLinesRaw = (prepared, maxWidth, onLine) => { /* reads prepared.#widths, cursor.#at, … */ }
        // … the steppers and the other walkers
      }
    }
    /** @invariant … */
    class PreparedRichInline {
      // the fields of InternalPreparedRichInline, and #sources
      static { /* the paragraph's walkers and materialization */ }
    }
    // … preparation and the package's functions, which call the walkers by name
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
  constructs, so `#segments` and `#kinds` are written once; its result
  narrows to `PreparedTextWithSegments` by a user-defined guard on the three
  public fields, checked by TScert's guard rules. The public `segments`,
  `kinds` and `widths` are copies, made at construction and written once:
  the walkers' own arrays are confined. Upstream's
  `layout.ts:150` write of `prepared.kinds` after preparation becomes a
  part computed before construction.
- **`PreparedRichInline`** holds `#data: PreparedText`, an instance whose
  state is its own class's, and the paragraph's fields. The three lists of
  where its segments are in the item's text, which upstream finds at a
  line's first materialization (`rich-inline.ts:1160–1181`), are fields of
  an owned record, `#sources = { starts: null, ends: null, units: null }`,
  each written once by an $`\mathsf{init}`$ of a fresh array. The
  whole-line fields, written by `findWholeLine`'s lambda (`:817–825`), are
  computed before construction.
- **Preparation's arrays** are allocated by `measureAnalysis` and its
  helpers, which move into the body; `breakableFitAdvances`' entries come
  from the measurement cache, storage the body keeps and confines.
- **The internal cursor** is a `LineCursor`, whose one field `#at` holds a
  fresh two-cell array, segment and grapheme index, written by the steppers.
  The walker allocates it and passes it only to functions of the body that
  it calls by name. Every member writes only cursors it allocates, so
  $`\psi_c=\mathsf{keep}`$ on the cursors that exist when a callback runs,
  and the walker's cursor facts cross `onLine`. The public `LayoutCursor`
  stays a record that applications build, read and keep as JSON (cited:
  Decisions Log, 2026-09-24, "cursors and ranges are plain JSON"); it is
  validated by `normalizePreparedLineStart` on entry and copied into a
  `LineCursor`.

The protocol for pretext (conjectured):
$`\Psi=\{\mathsf{priv}:\mathsf{keep},\ \mathsf{spines}:\mathsf{keep},\ \mathsf{cells}:\mathsf{keep},\ \mathsf{fields}:\mathsf{init}\}`$,
the last from `#sources`. The staging fields hold nothing at a member's
entry or exit. No walker reads `#sources`.

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
  `onLine` and every call through a value, by $`\psi_c=\mathsf{keep}`$; the
  steppers' writes are the walker's own steps, checked as written.
- **P18**: at pretext's sites the prepared handle is a class with private
  state, so its invariant holds after `step(c)` by (L4) and its fields are
  stable keys. Paper II's own program, with `Prepared` a structural type
  external code may build, is outside.
- **P20**: a value of a class with private state read back from a
  `Map<string, ClassTable>` meets $`I_C`$ at its first private read, by
  (L4); no contract of `Map` beyond its read returning a stored value is
  needed.
- **P15**: a module constant array moved into a private static field
  written once by its initializer is owned, and $`\psi_s=\mathsf{keep}`$
  keeps its length.
- **P16**: a cell initialized at first use, moved into an owned record
  field, changes by $`\mathsf{init}`$. Its invariant
  `bmp === null || bmp.length === 65536` is no support that tolerates
  $`\mathsf{init}`$, so it needs a write checked to establish the invariant,
  which *Tolerant* refuses: a later part.

### Performance

**Measured** on mechanical variants of upstream `src/` at `0d102a5c`,
bundled to one ESM file: `plainw`, the bundle's code inside a class's
static block, the control; `priv`, every field of `PreparedLineBreakData`
and `items`, `segments` and `kinds` (17) a private field of one class whose
constructor assigns them; `priv2`, the same with 15 of them written once by
initializers reading module cells the factory sets; `privcopy`, `priv` with
the constructor copying its eight arrays. Rich-inline's own handle stays a
record whose `data` is the class instance. Texts: 563 paragraphs, 72,144
UTF-16 units from eight of pretext's corpus files; a stand-in Canvas
(7.25 px per unit below U+2E80, 16 px above). Per process, 5 warm-up and 15
timed passes, the median per operation; 15 processes per variant in shuffled
order; the figure is the median of the process medians. Apple M2 Max, load
average 3.5–4.7; Node 26.13.0 (V8 14.6) and Bun 1.4.2 (JavaScriptCore).

| Operation | V8, `priv2` / `plainw` | V8, `priv` / `plainw` | JSC, `priv2` / `plainw` |
| --- | --- | --- | --- |
| `prepare`, cache cleared | 1.004 | 0.988 | 1.006 |
| `prepare`, text seen | 0.990 | 0.979 | 1.019 |
| `layout` | 1.001 | 1.016 | 0.998 |
| `walkLineRanges` | 1.015 | 1.023 | 1.003 |
| `measureLineStats` | 0.983 | 0.993 | 0.997 |
| `layoutWithLines` | 0.971 | 0.979 | 0.957 |
| `layoutNextLineRange` | 0.997 | 1.007 | 0.992 |
| `layout`, full walker (`pre-wrap`, letter spacing) | 0.997 | 1.185 | 0.998 |
| `walkLineRanges`, full walker | 0.999 | 1.153 | 0.988 |

- With fields written once by their initializers, every operation is within
  ±2% of the control in both engines, but `layoutWithLines`, 3–4% faster.
- Declared fields assigned in the constructor cost 15–19% on V8 in the full
  walker, and nothing elsewhere or on JavaScriptCore. A class with the same
  shape and public fields measures as `priv`, and one without field
  declarations, each field assigned once in the constructor, as the control;
  so the cost is that of a field declared and then assigned, not of private
  access. Which V8 mechanism causes it is not established.
- Copying the eight arrays at construction changes preparation by +1.6% on
  V8 and +1.1% on JavaScriptCore, within the spread between processes.

**Limits.** No browser ran, and Firefox (SpiderMonkey) was not measured;
upstream records differences of this size from V8's inlining budget alone
(cited: `measurement.ts:983–988`, one field more in a function V8 then no
longer inlined, 11–18% slower). The stand-in Canvas leaves out real
measurement, so the handle's share of preparation is overstated. The
variants differ from this design's shape: their staging is module cells,
where this design has one private static and a `#parts` field read by the
other initializers; `#segments` and `#kinds` are assigned after
construction; the cursor and the rich-inline handle keep their records; the
public copies of `segments`, `kinds` and `widths` are not made. None of
these differences was measured, and a hand-written rewrite of the source was
not measured.

## Negatives and controls

**Negative cases**, each unsafe under Node (observed: each program, as
JavaScript, run with `node`, printing the reads), each refused:

- `invalid-private-escape-return`: a member returns `#widths`; the client
  pushes onto it; the walker reads `#flags` past its end:
  `[0, 0, undefined]`. Refused by *Confinement* at the return.
- `invalid-private-escape-argument`: the walker passes `#widths` to the
  user's callback, which pushes onto it: `[0, 0, undefined, undefined]`.
  Refused by *Confinement* at the argument.
- `invalid-private-received-array`: the factory stages an array it received
  without copying it; the caller pushes onto its alias after construction:
  `[0, 0, undefined]`. Refused by *Ownership at construction*.
- `invalid-private-reentrant-member`: a member pops `#widths`; the walker
  caches the length; the visitor calls the member:
  `[1, undefined, undefined]`. Refused at the walker's read, the fact not
  surviving $`\psi_s=\mathsf{any}`$.
- `invalid-private-rewritten-field`: a member writes `#widths` again; the
  walker reads through the field after the visitor calls it:
  `[undefined, undefined, undefined]`. Refused by *Fields written once* at
  the write.
- `invalid-private-replaceable-method`: the walker bounds its loop by a
  public prototype method; external code replaces it:
  `[1, 1, undefined, undefined]`. Refused by *No replaceable code* at the
  class.

**Restriction controls**, each safe under Node and refused by its stated
restriction (observed):

- `private-base-class-refused`: a base constructor returns a plain object,
  which receives the derived class's private fields; the walker reads
  `[1, 1]` from it. *No base class*.
- `private-two-evaluations-refused`: a class evaluated twice in a function;
  one evaluation's static method given the other's instance throws a
  `TypeError`. *Evaluated once*.
- `private-open-invariant-refused`: a member pops `#widths` then `#flags`
  under $`|\mathit{flags}|=|\mathit{widths}|`$, with a walker reading
  `#flags[i]` before `visit`: `[0, 0]`. *Tolerant invariant*.

**Positive cases**: the example, its visitor calling every member
(`[0, 0, 0]`); `private-escape-copy`, a member giving out a copy that the
client pushes onto (`[0, 0]`); `bounds-pattern-unreachable-field-refused`
and `bounds-pattern-unreachable-handle-refused` rewritten with a class with
private state.

**Observation**: on an instance, `Reflect.ownKeys`,
`Object.getOwnPropertySymbols`, `Object.values`, `Object.assign({}, h)` and
`JSON.stringify` yield no private key or value; a spread, a JSON copy, a
`structuredClone` copy, a `Proxy` and `Object.create(h)` throw a
`TypeError` at a private read; a frozen instance reads as before;
`h.constructor` is the class.

**Controls** (forged fragment or forced proposal), each refused:
$`\Psi_C`$ forced smaller than a member's effect; a member forged as a
non-member; a function used as a value forged as called by name only; a
confined flow forged to an outside argument; an owned store forged as fresh;
a staging write forged across a call through a value; a private field's
second write forged away; $`I_C`$ forged to read a path outside $`R_C`$.

## Stages and cost

1. **The rule in the note and in Lean**: the regions, $`\Psi_C`$,
   $`\Phi\oplus_C\Psi_C`$, (P1) and (P2) as invariants of states, (L1) to
   (L4), Reliance at $`\Phi\oplus_C\Psi_C`$. Front: classes with private
   state, members, $`\Psi_C`$ as a least fixed point over the members,
   computed once per class body and keyed by its sources in the
   [stage store](../STAGE-STORE.md); the shape restrictions and the
   confinement check; `@invariant` on a class. The native audit. The cases
   and controls above. Covers the example.
2. **The fragment rows**: classes in a static block, the staging field, a
   static block's writes of a module cell and the exports read from it.
3. **Pretext**: the rewrite above on the fork; the five handle sites and six
   cursor sites checked; the rewritten source benchmarked against upstream
   on the setup above and in a browser.
4. **P16 and P15**: a write checked to establish an invariant; module tables
   as private statics.

Each stage states the whole definition; what a stage leaves out is an
explicit restriction, documented in SOURCE-FRAGMENT.md and enforced.

Cost (conjectured):

- Lean: (L2) and (L4) by one induction over runs with member certificates
  at $`\Psi_C`$; (P1) in the model by the native audit; the effect
  $`\Phi\oplus_C\Psi_C`$ joins the effect language as a bound per region.
  Two to four weeks.
- Front: the fixed point over members and the confinement check, a flow
  over the body's code.
- The pass: one region test per entry of a call's effect; no work per call
  site beyond respect.
- Trust: one row, of the language. No row about external code's use of a
  handle.
- Sources: pretext's handle code moves into one class body; its public
  handle types become a class; the scope above is lost.
