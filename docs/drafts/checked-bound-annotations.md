# Draft: checked bound annotations

The design of written contracts for the integer facts that cross function
and record boundaries (parameter ranges, result lengths, parallel arrays,
cursors), with TScert checking every contract and inferring the local
linear facts inside a unit. It is the RFC for
[TScert #104](../REFERENCES.md#tscert-104)'s decision P, the
interprocedural preconditions. Base: TScert main at `07146495`. Claims are
labelled **proved** (with the Lean name), **cited** (with the document and
its scope), **measured** (with what ran and when) or **conjectured**;
every Lean name this draft gives without a location is a proposal.

## The existing mechanism this extends

**Cited.** [General mechanisms](../DESIGN.md#general-mechanisms) assigns
each concern one mechanism. The design is first of all a generalization of
one implemented mechanism, the callable precondition and promise of
[the elements fact](../FOOTPRINTS.md#the-elements-fact), owned by
FOOTPRINTS:

- **Proved, implemented.** A call signature's effect states
  `requires R`, a precondition $`\mathrm{elems}(r,R)`$ on its receiver in
  the heap the call starts in, and `elements R`, a promise about the heap a
  normal return of `true` leaves (`CallEffects.Effect.requires`,
  `Effect.elements`). A call at a signature with a precondition is
  accepted where its receiver's knowledge holds the atom (`call-requires`,
  `requiresTree_sound`). One signature covers another where its
  precondition is weaker and its promise stronger (`Effect.covers`,
  `covers_sound`); an ordinary arrow erases only a signature without a
  precondition (`Effect.plain`, `PromiseWith.erase`); `bind` keeps neither
  part (`Effect.keeps`); graph code stating either part is refused
  (`effectChecked`).

This design generalizes `requires` from one elements predicate on the
receiver to a conjunction of atoms over the receiver and the arguments
(the generalization #104 §5 proposes), generalizes `elements` to an
`ensures` over the result, the receiver and the arguments at every normal
return, and lifts `effectChecked`'s refusal for both: graph code with a
written `requires` is certified from it as entry knowledge, and graph
code with a written `ensures` is certified to establish it (§2). `covers`,
`plain` and `keeps` are the rules for function values, unchanged in shape
(§2.5).

The other concerns the design meets, by the state of their mechanism:

| Concern | Mechanism | State | What this design adds |
| --- | --- | --- | --- |
| What holds at a program point | [Heap state assertions](../PROGRAM-TYPING.md#heap-state-and-assertions), checked on every incoming edge; [supplied point claims](../PROGRAM-TYPING.md#supplied-point-claims-and-incoming-edges) at cuts; conditional atoms made unconditional by an observed answer ([a membership test](../PROGRAM-TYPING.md#a-membership-test)) | implemented | Linear integer atoms, guarded by nullness, with checked steps (§4) |
| A fact kept while other code runs | [Footprints](../FOOTPRINTS.md#the-fact): a fact kind, its support, the footprints keeping it | implemented | Length and read links move by their supports, as every heap fact does |
| What a call may change | [Effect-qualified signatures](../SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification), [stated effects](../SOURCE-ELABORATION.md#stated-effects), [exceptional footprints](../SOURCE-ELABORATION.md#exceptional-footprints) | implemented | The clauses ride on the effect (§2.5) |
| Code of another module | [Certified imports](../SOURCE-CONTRACTS.md#certified-imports) | implemented | A contracted declaration is read only at a certified import (§2.5) |
| A test that establishes a fact | [Guards](../SOURCE-ELABORATION.md#guards) and [user-defined guards](../SOURCE-ELABORATION.md#user-defined-guards) | implemented | Validation at public entry points (§2.7) |
| A function's contract with old values, its plan and its goal | The knowledge contract, `Goal.ensures`, `CertifiedPlan.spec` of [correctness specifications](correctness-specs.md#3-the-knowledge-contract) | approved by the owner (2026-10-28); its row in [WORK](../../WORK.md#status) | One plan constructor for both (§2.4); old values of numbers (§1.5) |
| Bounds inside a unit, numbers as integers | [TScert #104](../REFERENCES.md#tscert-104): integer, safe-integer, difference, length, extent, density and presence facts, and decision N's `Float.Model` lemmas; with [correctness specifications §4](correctness-specs.md#4-the-atoms)'s order and integer atoms | a design comment against `4ffa514e` (2026-11-05) | The linear atom and its steps replace #104's difference fact and its checker (§4); one bridge (§5) |

**Cited.** #104's decision P lists three routes for a bound that comes
from a caller: keep a checked boundary, which #104 recommends; "expose
relational preconditions through a declaration-bound source contract,
then certify every caller"; or validate a structure once and encapsulate
its invariant. **This design proposes the second route**, on the
evidence of §8: a `@requires` is P's precondition, a `@ensures` its
postcondition, a record `@invariant` a pair of them attached by type. The
first and third routes establish the same atoms by runtime checks, and
public entry points use them (§2.7).

**Cited.** The [written-boundary rule](../../AGENTS.md#conventions)
states that a unit's boundary is written and what lies inside a unit is
inferred. Annotations extend the written boundary from types to the
integer facts of the boundary: a declaration's clauses are part of its
signature, carried in the Fragment from the source. Inside a unit nothing
is written: loop invariants, local closures' contracts and every local
bound are inferred (§3); a clause written inside a unit is a hint.

**Conjectured.** What the design adds to these mechanisms, each with its
obligation in §2:

1. a written precondition on graph code, conditioning the unit's safety;
2. old values of number-valued paths, a restricted extension of
   correctness specifications' stated limit 11, which refuses old values;
3. record invariants as clauses attached by a declared type;
4. contracts over the captures of a local closure that does not escape;
5. the linear inequality under a nullness guard, one atom form for the
   integer facts.

It amends two recommendations of correctness specifications that the
owner approved, for bound clauses: the unconditional safety plan
(its decision 7, a contract's plan beside the unit's ordinary plan) and
the statement form (its decision 1).

## 1. The annotation language

### 1.1 Where clauses are written

**Conjectured.** Clauses are JSDoc tags on the declaration they bind:

| Tag | Written on | Binds |
| --- | --- | --- |
| `@requires C` | a signature with a body: a function declaration, a method, a `const` bound to an arrow or function expression; and a function type or a method signature of an interface or type literal | its parameters and `this` |
| `@ensures C` | a signature with a body | its parameters, `this`, `result` and `old(…)` |
| `@opens x` | a signature with a body | removes the invariant requirement of parameter `x` (§1.7) |
| `@invariant C` | a type alias, an interface or a class declaring a record type | `this`, the record |
| `@invariant C` | a loop statement (a hint, §3.3) | the bindings in scope |
| `@predicate name(x: T, …) C` | any declaration of the module | a named clause of the module, expanded where it is used |

A declaration with several tags of one kind holds their conjunction. An
ensures is written only where Lean certifies the code that meets it; a
signature without a body (a function type, an interface method, a
`declare function`, an overload signature, an abstract method) states a
requires at most, which every value at that type must accept (§2.5).

Refused, each at the declaration with its location: a clause on a
signature with a parameter default or a destructuring parameter (the
entry heap is then the heap of the call); on an async function or a
generator; a requires on a member an implicit call can reach, whose
implicit callers establish nothing. No single document lists those
members, so the design fixes a closed list of **hook keys**, the union of
the admitted mechanisms that call one: conversion hooks (`toString`,
`valueOf`, `join`, `Symbol.toPrimitive`,
[prototype contracts](../SOURCE-CONTRACTS.md#prototype-contracts)); the
members of [the iterator protocol](../SOURCE-ELABORATION.md#the-iterator-protocol)
(`Symbol.iterator`, `Symbol.asyncIterator`, `next`, `return`, `throw`);
`then` ([objects owning `then`](../SOURCE-CONTRACTS.md#objects-owning-then));
`toJSON` ([`JSON` and `Error`](../SOURCE-CONTRACTS.md#json-and-error));
`Symbol.hasInstance` ([imported classes and `instanceof`](../SOURCE-CONTRACTS.md#imported-classes-and-instanceof));
and `constructor` and `Symbol.species` as the properties a species lookup
reads (a class's own constructor is no hook: `new` sites establish its
requires). Lean refuses, from the Fragment, a requires on every function
type at a hook key in the Fragment's types: a member with a body, an
interface method signature, and a record field holding a contracted
function value (`{ toString: f }`), so this refusal rests on no front-end
code. Accessors are
outside the fragment ([the refusal index](../SOURCE-FRAGMENT.md): no
`get` or `set` in a literal or a class). A mechanism admitting a new
implicit call adds its key to the list. The JSDoc text is a
comment: pretext's emitted code is the same with and without it.

### 1.2 Reading a clause

**Conjectured.** TypeScript's parser parses the clause text as an
expression. The front end resolves its names to the declaration's
parameters, `this`, `result`, the module's `@predicate` names and, for a
local closure, the bindings it captures (§2.6), and types each property
path by asking TypeScript's checker for the property's declared type:
`P.f` a property the declared type of `P` names, `P.length` the length of
an array or a string (a typed array's length waits on #104's decision H,
which owns its host model). TypeScript checks the clause no further. A
`@predicate` is a macro of its module, substituted hygienically before
anything else reads the clause; a cycle of predicates is refused. Another
module sees a predicate only through the clauses it is expanded into.
Correctness specifications' helper atoms are reified functions; a bound
clause needs none. Every form outside §1.3 is refused with its location.

### 1.3 The grammar

**Conjectured.**

```text
C ::= A | G => A | C && C                    a conjunction of guarded atoms
G ::= P !== null | P !== undefined           a guard on a path's presence
    | result                                 a Boolean result's truth (ensures only)
A ::= E rel E   rel ∈ { <, <=, >, >=, === }
    | safeInteger(E)
    | name(E, …)                             a @predicate, expanded
E ::= n | E + E | E - E | n * E | -E         n an integer literal
    | P | old(P)
P ::= x | this | result | P.f | P.length
```

A guarded atom is written in the source as a disjunction of one shape:
`P === null || A` where the declared type of `P` admits `null` and not
`undefined`, `P === undefined || A` where it admits `undefined` and not
`null`, and `result === false || A` in the ensures of a signature whose
result is `boolean`. Any other `||`, `!` and `!==` between numbers are
refused: each is a disjunction of linear atoms, which the knowledge of §4
holds only through a guard. A guarded atom has one guard; compound guards
are outside this language. A path whose declared type admits `null` or
`undefined` is admitted only behind a guard on it; the reader decides
this from the declared types, so every path of a clause is defined
wherever its atom is read.

### 1.4 Meaning

**Conjectured.** A clause denotes a predicate
$`⟦C⟧(\rho_0,h_0,\rho,h)`$ of the entry environment and heap and the
current ones:

- a path reads the environment and the heap through data properties,
  `old(P)` in the entry environment and heap; a guarded atom $`G\Rightarrow A`$
  holds where the guard fails or $`A`$ holds;
- `safeInteger(E)` holds where $`E`$'s value is a **safe integer**, finite and
  integral with $`\lvert E\rvert\le 2^{53}-1`$, JavaScript's
  `Number.isSafeInteger`;
- `+`, `-` and `n *` are mathematical integer operations on the decoded
  values of their operands; an atom is false where an operand **or an
  intermediate result** of its arithmetic is no safe integer;
- a comparison with no arithmetic compares two numbers in IEEE order,
  false where either is NaN: correctness specifications' order atom.

So `0 <= from` holds of `0.5`, `from + 1 <= to` is false of `0.5`, and a
clause that needs `from` integral says `safeInteger(from)`. This integer
reading is the contract. A JavaScript evaluation of the clause's text
agrees with it where every term under arithmetic and every intermediate
result is a safe integer (conjectured, `clause_js_agree`); a runtime test
written in JavaScript establishes the contract only through the bridge's
exactness at each of its nodes (§5). An ensures holds at every normal
return: nothing runs the clause, so it is a strong postcondition, where
correctness specifications' source postconditions are weak.

### 1.5 `result` and `old`

**Conjectured.** `result` is the value the function returns. A parameter
in any clause denotes the actual passed, its entry value, also where the
body reassigns the parameter. `old(P)`, with `P` number-valued, is
$`⟦P⟧(\rho_0,h_0)`$, the path read in the call's entry heap. A number is
immutable, so `old(P)` names one number for the whole call and needs no
snapshot of the heap; `old` of an object, whose meaning needs the entry
heap's contents, is refused, correctness specifications' limit 11. An
`old(P)` is admitted only where the whole requires entails that every
prefix of `P` is present at entry; a guarded requires such as
`x === null || safeInteger(x.n)` admits `x` null, so it admits no `old(x.n)`. Two occurrences
of one path name one ghost.

### 1.6 Integrality

**Conjectured.** Integrality comes from `safeInteger(E)` in a clause and from
the bridge's facts (§5): a length, an integer literal, a bitwise result,
a sum of safe integers shown in range. A requirement such as
`0 <= from && from <= to && to <= xs.length` without
`safeInteger(from) && safeInteger(to)` admits `from = 0.5`, at which `xs[from]`
reads `undefined`; the read then stays an obligation the clause does not
discharge.

### 1.7 Record invariants

**Conjectured.** `@invariant C` on a declared record type `T` defines
$`\mathrm{inv}_T(x)=C[x/\mathtt{this}]`$. A declared type **names** `T`
when it is `T`, an alias resolving to `T`, `Readonly<T>`, an intersection
with a member naming `T`, an interface extending `T` or a class
implementing `T`, each resolved by declaration identity through
re-exports. For each signature of the checked program:

- a parameter `x` whose declared type names `T` has $`\mathrm{inv}_T(x)`$
  in its requires, and, on a signature with a body, in its ensures
  (preservation);
- `this` of a member at a hook key (§1.1) carries neither the requirement
  nor the ensures of $`\mathrm{inv}_T(\mathtt{this})`$, so a class with an
  invariant may have conversion hooks; an explicit call of such a member
  keeps the invariant's atom by the member's certified footprint (§2.3),
  and a call by a native (a conversion, an iteration) by that native's
  callback effects, the footprint its row states for the callbacks it
  runs; a constructor is under `@opens this`, ensuring the invariant
  without requiring it;
- `this` of any other method of a class or interface naming `T` is such a
  parameter;
- a result whose declared type names `T`, on a signature with a body, has
  $`\mathrm{inv}_T(\mathtt{result})`$ in its ensures;
- `@opens x` removes the requirement for `x` and keeps its ensures: an
  appending builder receives a record whose invariant may not hold, and
  establishes it before every normal return; a result keeps its ensures;
- a type that only contains `T` (`T | null`, `T[]`, a field of another
  record) adds no clause, so a record reached through another structure
  has no invariant atom (§7);
- a callback written as an argument is a local closure: its contract is
  the one its contextual type states, met by the flow rule of §2.5.

A record invariant is a pair of boundary clauses: a `T` value has the
invariant's atom exactly where a clause of the current signature names
it, or the code since established it.

## 2. Obligations

Write $`f:\{K_p\}\,\vec A\to B\,\{K_q\}`$ for a contracted signature of
$`f`$: $`K_p`$ the elaborated requires over the receiver and the
parameters, $`K_q`$ the elaborated ensures over those, the result and the
ghost slots $`\vec g`$ of its `old` terms. In `CallEffects.Effect` terms,
$`K_p`$ is the generalized `requires` and $`K_q`$ the generalized
promise.

### 2.1 Elaboration and the written clause

**Conjectured.** The Fragment carries each declaration's written clauses,
read from the source by the front end (§4.1). A clause elaborates to
stored knowledge (§4.2) whose atoms are over **path terms**: a slot, or a
path term followed by a field read or `.length`, evaluated in the heap
the knowledge is read in. Each atom of the clause elaborates by its form:

- a comparison with no arithmetic, `P < Q`, to correctness
  specifications' **order atom** over the two terms, IEEE order and
  neither NaN: `0 <= x` holds of `0.5` and of `Infinity`, of no NaN;
- `safeInteger(E)` to $`\mathsf{int}(E)`$ with the definedness atoms of
  $`E`$'s arithmetic, as below;
- a comparison with arithmetic to a **linear atom**, together with its
  definedness atoms, each under the same guard as the atom:
  $`\mathsf{int}`$ of every operand and every intermediate result, and
  each intermediate's range
  $`\lvert e\rvert\le 2^{53}-1`$ as an atom of its own, so that a normal
  form of the sum keeps them.

One recursive elaborator of arithmetic serves every atom, `safeInteger(E)`
included: for each arithmetic subterm of $`E`$ it emits the definedness
atoms above before any normal form is taken, so
`safeInteger((x + 1) - 1)` elaborates to atoms that are false at
$`x=2^{53}-1`$, where $`x+1`$ is no safe integer, never to
$`\mathsf{int}(x)`$ alone. An order atom becomes a linear atom by a step (§4.2) once both terms are
$`\mathsf{int}`$; `0 <= from` with `safeInteger(from)` gives the linear
$`-from\le 0`$. A guard elaborates to
the conditional form of the atom, conditional on an answer about the
guarded term, as the atoms of [the elements fact](../FOOTPRINTS.md#the-elements-fact)
are conditional on a slot's truthiness: a presence answer for
`P !== null`, the truth of the result for `result`. An observation of that
answer on a branch's edge makes the atom unconditional
(`HeapKnowledge.observe`). Each `old(P)` elaborates to a ghost slot.

The trims example's clause `xs === null || xs.length === n`, with `xs` the
path `r.widthTrims` and `n` a slot, elaborates to an order atom under the
guard; with $`\mathsf{int}(n)`$, which the expansion of `trimLengths` at
`n := to - from` gives through its definedness atoms, a step turns it
into

```math
\bigl[\,r.\mathtt{widthTrims}\ne\mathsf{null}\,\bigr]\ \Rightarrow\ \bigl(\mathrm{len}(r.\mathtt{widthTrims})-n\le 0\ \land\ n-\mathrm{len}(r.\mathtt{widthTrims})\le 0\bigr)
```

whose support is the field location of `widthTrims` in `r` and the store
location of the array it holds. $`\mathrm{Holds}`$ of a guarded atom is
true where the guarded term reads `null`; where it reads an array, the two
inequalities hold of its store's length. $`\mathrm{Holds}`$ of an atom whose path term reads through
a value other than an object is false, a definition of Lean's, so a
reader that admitted such a path would make a clause unestablishable,
never assumed. A test of a slot $`s`$ that a read link ties to the path
$`P`$ observes the guard on $`P`$: the true edge of `s !== null` makes the
atoms guarded by $`P\ne\mathsf{null}`$ unconditional.

Lean computes $`\mathrm{elab}`$ from the Fragment's clauses itself, so for
every unit with a body the $`K_p`$ and $`K_q`$ it certifies are exactly
the written clauses, and empty where none is written; a producer's claim
of other knowledge for a written signature is refused. The producer
proposes a $`K_p`$ and a $`K_q`$ only for a local closure that does not
escape (§2.6). `elab_sound` (new) states

```math
\mathrm{Holds}(\mathrm{elab}(C),\rho\cdot\vec g,h)\iff ⟦C⟧(\rho_0,h_0,\rho,h)
\quad\text{where}\quad g_i=⟦P_i⟧(\rho_0,h_0)
```

Callers establish $`\mathrm{elab}(K_p)`$ and the body assumes it, so both
directions are used. A program read `const n = xs.length` gives the slot
`n` and the atom $`n=\mathrm{len}(xs)`$ (#104's length observation), so
path terms and slots meet through equalities.

### 2.2 At the definition

**Conjectured.** The unit is certified from entry knowledge $`K_p`$ and
the ghost bindings, at a goal whose return check maps $`K_q`$ into each
return node: correctness specifications' `Goal.ensures`
([§3](correctness-specs.md#3-the-knowledge-contract)). The request's entry
environment has one more slot per ghost, bound by entry read links to
$`⟦P_i⟧(\rho_0,h_0)`$; no node of the program reads a ghost slot, and
every edge keeps it, a number. With $`\vec g(\rho,h_0)`$ the ghost
values, the obligation is

```math
\models_B\{K_p\}\,f\,\{K_q\}\iff
\forall n\,W\,h_0\,\rho.\ \mathrm{EnvOk}(\Gamma,\rho,n,W)\land\mathrm{WorldAdm}(W)\land\mathrm{HeapOk}(n,W,h_0)\land\mathrm{Holds}(K_p,\rho,h_0)
\Longrightarrow\mathrm{SafePostExc}_P\bigl(⟦R⟧,\ \lambda h\,v.\ \mathrm{Holds}(K_q,[v,\rho,\vec g(\rho,h_0)],h)\land\mathrm{Post}(⟦\Phi⟧_{\vec a,h_0},h_0,h),\ R_{\mathrm{exc}},\ n,W,h_0,\mathsf{goto}(s,\rho\cdot\vec g(\rho,h_0))\bigr)
```

with $`\Phi`$ the unit's certified footprint and $`R_{\mathrm{exc}}`$ its
exceptional footprint where it has `onThrow`, `True` otherwise
([exceptional footprints](../SOURCE-ELABORATION.md#exceptional-footprints)):
the knowledge contract of correctness specifications verbatim, with
$`\mathrm{Holds}(K_p,\rho,h_0)`$ among its premises. Callers' frames and
handlers read the footprint from it as they read it from today's plan.

### 2.3 At a call

**Conjectured.** A call `f(a⃗)` at a contracted signature, in caller
knowledge $`K`$ after the arguments are evaluated, generalizes
`call-requires` ([the elements fact](../FOOTPRINTS.md#the-elements-fact)):

```math
\frac{K\vdash K_p[\vec a/\vec x]\qquad
      K\vdash P_i[\vec a/\vec x]\mapsto s_i\ \ (i\in I)}
     {K\ \vdash\ r\leftarrow f(\vec a)\ \dashv\ \mathrm{frame}_\epsilon(K)\cup K_q|_I[r/\mathtt{result},\ \vec a/\vec x,\ \vec s/\vec g]}\ \textsf{call-contract}
```

Both premises are checked in the state after the arguments are
evaluated: $`K_p`$ of the actuals, and for each ghost $`g_i`$ with
$`i\in I`$ a caller slot $`s_i`$ linked to the path $`P_i`$ at the
actuals. $`K_q|_I`$ keeps the atoms of $`K_q`$ whose ghosts are all in
$`I`$. $`\mathrm{frame}_\epsilon(K)`$ keeps the atoms of $`K`$ whose
supports the callee's certified footprint $`\epsilon`$ keeps, by the
stability check of the atoms' fact kinds
([changes and footprints](../FOOTPRINTS.md#changes-and-footprints)). A
call that cannot establish $`K_p`$ is refused at the call.

**Exceptional edges.** An ensures is a normal-return guarantee, as a
promise is ([what stays on normal edges](../SOURCE-ELABORATION.md#what-stays-on-normal-edges)),
so a handler never receives $`K_q`$. A handler receives no current-content
fact, even below an `onThrow` footprint
([handler facts](../SOURCE-ELABORATION.md#handler-facts)), and this design
keeps that rule: a handler receives the environment-only atoms of $`K`$
(integer and linear atoms over slots, which no heap change affects) and
no heap atom. Heap atoms on handler edges are a separate extension.

### 2.4 The plan and the verdict

**Conjectured.** One plan constructor serves this design and correctness
specifications: correctness specifications' `CertifiedPlan.spec`, with a
field stating whether $`K_p`$ conditions the unit's safety. Conditioning,
it holds the unit's request at entry knowledge $`K_p`$ and the return
goal of $`K_q`$, in place of the unit's ordinary plan; otherwise it is
correctness specifications' plan, beside the ordinary one. The
exhaustive `FunctionPlan` conversion covers both
([acceptance/soundness invariant](../../AGENTS.md#acceptancesoundness-invariant)).
`SourceClaimJson.checkUnitJson_safe` then states, for each function of an
accepted unit, safety from the entry knowledge of its written requires,
empty where none is written, so today's statement is the instance without
clauses. Its conclusion changes once, for both designs: a review
obligation of the theorem.

**Program safety.** `program_safe` (new, conjectured) composes the
units' verdicts: for a set of accepted units, a correct public inventory
and a correct list of public modules, every run of the program entered
through the public modules is safe. Its argument: every call inside the
checked program establishes the written requires (§2.3); a value with a
requires reaches only callers that establish it, by the flow rules of
§2.5 and the escape inventory of §2.6; no member at a hook key has a
requires, so no implicit call meets one (§1.1, checked by Lean); a
signature external code can
call has no requires (below). So every run of a contracted unit starts in
a state meeting its requires. A requires that no state meets makes its
unit vacuously certified and every call of it refused, so no run reaches
the unit. The two premises about the boundary, the inventory and the
module list, are front-end facts, trusted (§4.3).

**Public entry points.** The code outside the checked program establishes
nothing, so a signature it can call has no requires and no invariant
requirement. The **public modules** are those `package.json` names in
`exports` or `main`, or the modules the run names where the package states
none (pretext's `src/layout.ts` and `src/rich-inline.ts`, for example). The
assumption of the verdict is that external code enters only through
them; a deep import of another module breaks it. The **public
inventory** is every signature external code can call through them:

- the declarations those modules export;
- every signature in the declared types of those exports, transitively
  through every type constructor: records, classes, functions, arrays,
  tuples, `Map`, `Set`, `Promise`, union and intersection members, index
  signatures and generic arguments, in every position: returned
  functions, callable fields, methods (`private` and `protected` ones
  included, which JavaScript calls like any other; `#` members excluded),
  and the callbacks external code passes in or receives;
- a function value handed to a native (a callback passed to
  `Array.prototype.map`, a listener), met by the flow rule of §2.5 at the
  native's parameter type, which states no requires.

A value can carry more members than its declared type shows (an object
returned at an interface that omits one of its methods). The flow rule of
§2.5 closes that gap: a value with a member that has a requires is
refused wherever it flows to a type that omits or erases that member. So
the inventory over declared types covers every signature that reaches
external code. The front end computes the inventory and refuses a
requires on any signature in it; the verdict names the public modules.

An entry point's body validates what its callees require, by a runtime
check (§2.7), and its verdict is unconditional. An entry point may state
an ensures, which Lean checks. A contracted declaration exported from any
other module is internal: checked modules import it through certified
imports.

### 2.5 Function values and imports

**Conjectured.** The contract is part of the signature's effect, so the
existing rules for effects carry it:

- **Coverage.** A value at $`\{K_p\}\to\{K_q\}`$ is accepted at an
  expected $`\{K'_p\}\to\{K'_q\}`$ when $`K'_p\vdash K_p`$ and
  $`K_q\vdash K'_q`$, each by a certificate: `Effect.covers`, a weaker
  precondition and a stronger promise, with its `requiresCovers` an
  entailment.
- **Erasure.** An ordinary arrow erases only a signature without a
  requires (`Effect.plain`): a function with a requires passed, stored or
  returned at a function type without one is refused with its location; a
  function with only an ensures may be, losing the promise. A written
  function type with a requires carries it, so a callback parameter may
  state a requires that its caller then establishes.
- **Erasing targets.** A value with a requires, or an object with a member
  that has one, is refused where it flows to `unknown`, `object`, `{}`,
  `Function`, a type parameter whose bound does not state the requires, or
  a record type that omits the member; a member read of such a function
  value other than its call (`f.apply`, `f.call`, `f.bind`, passing it to
  `Reflect.apply`) is refused.
- **Binding.** `bind` keeps neither the requires nor the promise
  (`Effect.keeps`).
- **Methods and records.** An object reaches a type by structural
  subtyping of its record or class type, member by member; each method
  member is compared by coverage, so an object with a method that has a
  requires is refused at a supertype whose method states none.
- **Every carrier of a signature** carries the contract as it carries the
  effect: overload combination, weakening by an annotation, construct
  signatures. A contracted value instantiates a type parameter only by
  coverage at its bound; a contracted signature is never itself generic,
  and an overloaded declaration has no contract, as correctness
  specifications refuses both ([§2](correctness-specs.md#2-the-source-form)).
- **Imports.** A contracted declaration is read at its contract by every
  reader of its signature, through one function as `statedResult` reads a
  stated effect ([stated effects](../SOURCE-ELABORATION.md#stated-effects)),
  and only at a certified import. Where certified imports read an import
  at its ordinary signature (a read that would close a cycle of the
  qualified-dependency graph, an ineligible import), a contracted
  declaration is refused with the import's location.
- **Recursion.** A recursive call, or a cycle of contracted functions of
  one module, uses the knowledge contract one budget level lower, the
  argument recursive closures' types rest on; correctness specifications
  states the same argument (conjectured there and here).

### 2.6 Local closures and captures

**Conjectured.** A captured binding reaches a closure's body as graph
code binds captures ([closures are graph code](../DESIGN.md#closures-are-graph-code)):
a `const` capture as a value, a mutable one as a cell. A local closure's
contract is inferred (§3.2), and may name its captures only when the
closure does not escape and the captures it names are `const` bindings
or parameters nothing assigns ([a `let` nothing assigns](../SOURCE-ELABORATION.md#a-let-nothing-assigns)).
A closure does not escape when it is bound by `const` and every use of
its binding is a direct call inside the unit; Lean checks this inventory
from the unit's graph. Its contract is then indexed by its capture
environment: the producer proposes $`K_p`$ and $`K_q`$ over its
parameters and captures (and its result, for $`K_q`$), Lean certifies its
body from $`K_p`$ at the return goal of $`K_q`$, and each call
establishes $`K_p`$ in the caller's current knowledge, where the captured
bindings are the caller's own slots, and receives $`K_q`$ on its normal
return by `call-contract`. A requirement over a capture is checked in the
state of each invocation. A closure that escapes has a contract over its
parameters only, and no atom about its captures enters its body.

### 2.7 Runtime checks establish the same atoms

**Conjectured.** A test the code runs establishes the atoms of its true
edge ([guards](../SOURCE-ELABORATION.md#guards)):
`if (!(i >>> 0 === i && i < xs.length)) throw …` gives `xs[i]` its
bound, by the calculus's own `>>>` and comparison (§5): `i >>> 0 === i`
holds exactly of the integers in $`[0,2^{32}-1]`$. Arithmetic in such a
test reaches the linear atoms through the bridge's exactness at each of
its nodes. A validation function returning `boolean` states its facts in
an ensures guarded by its result, `result === false || C`: its body is
certified to hold $`C`$ at every return of `true`, and a caller receives
$`C`$ conditional on the result, unconditional on the true edge of a test
of it, as `Effect.elements` promises a fact at a return of `true`. A
return of `false` gives the caller nothing. These are #104's first and
third routes.

### 2.8 At a record write

**Conjectured.** A write creates no obligation of its own. It drops every
heap atom whose support **may** hold a location the write changes, by
the support of the atom's fact kind and the stability check of
[footprints](../FOOTPRINTS.md#changes-and-footprints): the field's location
for a field write; the store location for `push`, a length cut, an
append and a write that fills a hole; the element's location for a write
over a present element, which keeps the store. A write that fills a hole
below the length changes the store and keeps its length, a fact its rule
states again (§3.4). A path's support is every location its
read links read, field locations and store locations along the path.
Linear and integer atoms name only slots and are kept. Between two
appends of a builder the invariant's atom is absent from the knowledge.
It is demanded only at the **observation points**:

- a normal return of a function whose ensures holds it;
- a call whose requires holds it, a callback's call included;
- a loop head whose hint holds it.

A callback invoked while the atom is absent relies on its own contract.
If its signature names `T` for the argument, the invoking code
establishes the invariant at the call. If it reaches the record by
capture, its contract names it only under §2.6, and then each call
establishes it. A builder that throws between two appends leaves its
caller's handler with no heap atom of the record (§2.3).

## 3. The automatic part

### 3.1 Domain

**Conjectured.** At each program point the producer proposes a
conjunction of:

- $`\mathsf{int}(x)`$, a safe integer (§5), and correctness
  specifications' order atoms between terms not shown integral;
- linear inequalities $`\sum_i c_i x_i\le d`$ with integer coefficients
  over $`\mathsf{int}`$ terms, equalities as two inequalities, each
  possibly under a guard on a path term (§2.1);
- #104's heap facts: length links $`\mathrm{len}(a)=n`$, extent, density
  and presence, and the field read links of stored knowledge, each with
  its support.

The domain covers intervals (`0 <= i < n`), differences (`i + 1 < count`,
equal lengths) and affine equalities in any number of variables (the
paired counters of `measureAnalysis`, `at = base + mi - from`). The
producer may find them by any method (intervals, difference bounds,
affine equalities with widening); only the certificates of §4 reach Lean.

### 3.2 What it infers

**Conjectured.**

- Counters: initialization, update and guard give `int(i)`, `from <= i`,
  and on the guard's true edge `i < to`.
- Successors and predecessors under a guard: `i + 1 < count` bounds
  `i + 1` on the true edge; `i > 0` gives `i - 1 >= 0`; the false edge of
  `i + 1 === count` gives the disequality that, with `i + 1 <= count`,
  bounds `i + 1 < count`.
- Affine cursors: an equality every edge of the loop keeps.
- Appends: a one-argument `push` on an ordinary array with
  $`\mathrm{len}(a)=n`$ gives $`\mathrm{len}(a)=n+1`$ on its normal return,
  by the strengthened `push` row of §4.3.
- Local closures' contracts (§2.6), proposed from their call sites and
  their bodies' obligations.

### 3.3 Hints

**Conjectured.** `/** @invariant C */` before a loop, and clauses written
on a local closure, are hints: the producer reads them as proposals, and
Lean checks them on every incoming edge
([supplied point claims](../PROGRAM-TYPING.md#supplied-point-claims-and-incoming-edges)).
A wrong hint fails verification and strengthens nothing, correctness
specifications' decision 9.

### 3.4 Accesses

**Conjectured.** A read `xs[i]` of a readable array is in bounds where the
knowledge entails $`\mathsf{int}(i)\land 0\le i\land i<n`$ with
$`\mathrm{len}(xs)=n`$; its result has the element contract (#104 §5,
conjectured there): `number` for a readable `number[]`, and `null` or
`undefined` stay possible where the element contract admits them, and
`undefined` at a hole where the element contract admits one. A non-null
assertion `e!` is an obligation that `e` is neither `null` nor
`undefined`. The readable presence mode admits a hole only where the
element contract admits `undefined`
([arrays](../POSITIVE-TYPES.md#arrays): a hole is permitted by
`(number | undefined)[]`, not by `number[]`), so an in-bounds read of a
value whose contract is readable `number[]` discharges it. The mode is
that of the value's contract, not of its spelling: an unrestricted `map`
result may be sparse, and is at readable `number[]` only where its
signature says so; for an element contract admitting `undefined`,
#104's density or presence fact at the index is needed besides the bound.
Presence removes only the hole alternative: an element contract admitting
`undefined` or `null` still needs a value refinement of the read before
`!`.

A write `xs[k] = v` on a writable homogeneous array of element contract
$`A`$ is typed by the bounded write rule (conjectured; designed for
pretext's 57 write sites in a draft outside the repository, and stated
here):

```math
\frac{\Gamma\vdash x:L\qquad \mathit{store}(L)\equiv\mathsf{list}(\tau)\ \text{homogeneous, writable, element}\ A\qquad
      K\vdash\mathsf{int}(k)\land 0\le k\le 2^{32}-2\land k\le\mathrm{len}(x)\qquad \Gamma\vdash v:A}
     {K\vdash x[k]=v}\ \textsf{setElem-bounded}
```

its premises read in the state after `v` is evaluated, with
$`n=\mathrm{len}(x)`$ before the write. Three cases follow the calculus's
steps (`Semantics/Calculus.lean`), and the knowledge after the write is
that of the case the premises select:

- **present** (density or presence at $`k`$, or $`k<n`$ on an array whose
  presence mode admits no hole, such as `number[]`): `setPresent` writes the
  element's location and leaves the store, so every store-supported atom
  stays;
- **in bounds** ($`k<n`$): a present element or a hole; at a hole
  `setGrow` gives the store a fresh location, so store-supported atoms are
  dropped, and in both cases the rule states $`\mathrm{len}(x)=n`$
  (`placeAt` keeps the length below it, `placeAt_length` in
  `Types/Types.lean`);
- **append** ($`k=n`$): `setGrow` appends; store-supported atoms are
  dropped and the rule states $`\mathrm{len}(x)=n+1`$, with a dense prefix
  extended by one;
- with only $`k\le n`$ known, the join: store-supported atoms dropped and
  $`n\le\mathrm{len}(x)\le n+1`$.

No case makes a hole. A string's `charCodeAt` and `codePointAt` take
#104's refined contracts.

## 4. How the producer proposes and Lean checks

### 4.1 The wire

**Conjectured.** Three documents carry the design, each typed against its
one declaration as every wire format is:

- **the Fragment** ([its format](../FRAGMENT-FORMAT.md)): each
  signature's clauses, `requires`, `ensures` and `opens`, after the front
  end has expanded `@predicate`s and attached the record invariants of
  §1.7 (front-end work, a trust row of §4.3), as terms of §1.3 with paths
  named by binding and field; every signature has the fields, empty lists
  included; and the public modules and the public inventory of §2.4;
- **the source claims** ([SourceClaims](../SOURCE-CLAIMS.md)): the
  producer's proposals, a non-escaping local closure's $`K_p`$ and
  $`K_q`$ over its parameters, captures and result, and a loop head's
  hint atoms, in #104 §6's tagged shape with a
  `linear` atom (integer coefficients and bound as canonical decimal
  strings, slots as bounded naturals) in place of `difference`;
- **the request and the evidence** ([request protocol](../REQUEST-PROTOCOL.md)):
  the elaborated knowledge at entry and return, the ghost slots with the
  paths binding them, and each node's and edge's linear steps.

Lean elaborates the Fragment's clauses itself (§2.1); a request whose
entry or return knowledge differs from that elaboration is refused.

### 4.2 Atoms and steps

**Conjectured.** The atoms join stored knowledge
([stored knowledge](../PROGRAM-TYPING.md#stored-knowledge-and-how-it-is-read)):
$`\mathsf{int}`$ and linear atoms whose terms are all slots name only the
environment and survive every write and call, as
[separation facts](../PROGRAM-TYPING.md#separation-facts) do; an atom with
a path term reads the heap, and moves by the support of its paths, the
locations their reads read; a guarded atom is conditional on an answer
about its guarded term, and an observation of that answer on a branch's
edge makes it unconditional, as `HeapKnowledge.observe` does for the
elements fact. Correctness specifications' order atom (IEEE
order between two non-NaN numbers) stays for values not shown integral;
on two $`\mathsf{int}`$ slots an order atom and a linear atom state the
same thing, and a step converts one to the other.

Each entailment step concludes one atom $`c\cdot x\le d`$ from atoms
already held, by natural multipliers $`\lambda_j`$ over premises
$`a_j\cdot x\le b_j`$ and a divisor $`g\ge 1`$, accepted where

```math
\sum_j\lambda_j a_j=g\,c\qquad\Bigl\lfloor\frac{\sum_j\lambda_j b_j}{g}\Bigr\rfloor\le d .
```

With $`g=1`$ it is a nonnegative combination; with $`g>1`$ one rounding,
valid because $`c\cdot x`$ is an integer where every term is
$`\mathsf{int}`$. A
strict comparison of integers enters as $`x-y\le -1`$. A second step form
uses a disequality: from $`c\cdot x\le d`$ and $`c\cdot x\ne d`$ it
concludes $`c\cdot x\le d-1`$. Steps chain, each conclusion a premise of
later steps, so a derivation may round more than once, one step at a
time. The checker is executable and runs compiled; `Linear.check_sound`
(new) states that an accepted step's conclusion holds of every integer
valuation meeting its premises. The producer finds multipliers by
elimination or a simplex run. The steps are incomplete for integer
arithmetic: an implication true over the integers that no chain of such
steps derives is refused (a stated limit).

This checker replaces #104's `IndexFacts.Certificate` difference steps;
#104's other step forms (equality transport, extent weakening, length
substitution) stay, over the linear atom. The steps are part of the node
and edge evidence: `HeapExpressionRules.StepEvidence` and the edge checks
of `ControlFlow` take a linear step that consumes atoms of the sequent it
reads. Transport under slot maps, drops, joins and canonical forms
([canonical heap knowledge](heap-knowledge-canonical.md)) extends
`HeapKnowledge.shift_holds` and `KnowledgeExpand.checkIn_sound`: renaming
the variables of a linear atom is a substitution.

### 4.3 Trust

**Conjectured.** Each part of a verdict is proved, or rests on a trusted
component or an audited row:

- **To be proved:** the steps (`Linear.check_sound`), the arithmetic laws
  over `Float.Model` (§5), `elab_sound`, `program_safe`, the plan and
  call rules, the capture inventory of §2.6. An array's and a string's
  `length` are the calculus's own steps (`lenV`, `lenStr`: the store's
  length, the count of UTF-16 code units, as `bitsOfNat`), and validation
  by `>>>` is the calculus's own operator. A length read is exact where
  the length is at most $`2^{53}`$ (`bitsOfNat_exact` of #104); its range
  is the admissibility invariant below.
- **Length admissibility.** Every built-in array store lists at most
  $`2^{32}-1`$ positions. The bound is one more length conjunct of
  `listT` (`Types/Types.lean`; POSITIVE-TYPES' $`\mathsf{Bounds}_\tau`$),
  whose conjuncts state the required and optional lengths today. Every
  view of one store is a conjunction of `listT`s, readonly weakening only
  element slots, so every view carries the same bound. The existing heap
  premise `HeapOk` (`Semantics/Heaps.lean`), every location meeting its
  contract, then carries it, assumed wherever `HeapOk` is: of the input
  heap and of every heap an external, declared call returns, a
  strengthened premise of every safety theorem, justified by ECMAScript's
  array length limit (cited: [ECMA-262](../REFERENCES.md#ecma-262),
  ArrayCreate and ArraySetLength). Its preservation is the typing lemmas
  that build or change a store:
  - `listT_grow`, given $`k<2^{32}-1`$ from `indexOfBits`, so a store
    grown at $`k`$ has length at most $`\max(n,k+1)\le 2^{32}-1`$, and
    `write_sound` applies to `setGrow`;
  - `listT_alloc` (`Types/Types.lean`) and `arr_alloc_rule`
    (`Semantics/Rules.lean`), with
    `arrAlloc` gaining the premise $`\lvert vs\rvert\le 2^{32}-1`$: today
    `arrSpread` and `arrAlloc` (`Semantics/Calculus.lean`) build a
    literal's store of any length, so `[...a, ...a]` with
    $`\mathrm{len}(a)>2^{31}`$ makes a longer one; a new step raises a
    `RangeError` there, as engines throw, allocating its error as
    `arithThrow` does; `arr_alloc_rule` then gains an `ErrorsIn Ξ` premise
    and a throwing case, as `arith_throw_safe` has, and the length premise
    keeps the new step disjoint from `arrAlloc` for the determinism lemmas;
  - the rest-entry lemmas (`Programs/RestCalls.lean`,
    `Programs/VariadicTyping.lean`, `Purity.CollectingRun`), whose pack
    (`graphEntry`'s `.arrLit`) gains the same throw and an exceptional
    case whose postcondition holds of the unchanged heap and the error.

  Every native row that returns or grows a built-in array store assumes
  the bound of its result, as it assumes `HeapOk` of it: a class of rows
  (`push`, `unshift`, `splice`, `concat`, `Array.from`, `flat`,
  `flatMap`, `map`, `filter`, `slice`, a string's `split`, `Object.keys`,
  match results, and any other). This trust does not end: a throw at
  $`2^{32}-1`$ in the specification-step model (`Arr.push` in
  `Semantics/FootprintNatives.lean` appends with no limit) moves it into
  the step-correspondence premise of native footprints from their steps.
  With the bound, `length_number_exact` states: a length read `lenV` of a
  built-in array store at a world location under `HeapOk` gives
  $`\mathsf{int}(n)\land 0\le n\le 2^{32}-1`$. Typed-array and host stores
  are not under `listT` (#104's decision H). Strings get no such bound:
  the calculus's concatenation builds a string of any length, where
  JavaScript throws past its limit, so a string's length is
  $`\mathsf{int}`$ only through #104's string boundary (its source-model
  length limit), which this design does not change.
- **New front-end code in the trusted front end** (a trust row): the
  JSDoc reader, its name resolution and path typing, `@predicate`
  expansion, invariant attachment, the list of public modules (from
  `package.json` or named by the run) and the public inventory of §2.4.
  The verdict assumes external code enters only through the public
  modules. A
  misread or misattached clause cannot make a call inside the checked
  program unsafe: Lean certifies the body from the clause the Fragment
  carries and checks every call against the same clause, so a misreading
  changes which programs verify. The refusal of requires at hook keys,
  which implicit calls rely on, is Lean's, from the Fragment (§1.1). A
  public-inventory error can make a call unsafe: a
  signature the inventory misses may carry a requires that external code
  never establishes. That is why the inventory belongs to this row.
- **Existing trusted components, newly load-bearing:** the value
  faithfulness of the lowering bears on safety where a runtime check
  stood: the bound of `xs[i - from]` rests on `i - from` lowered as that
  subtraction, the reliance correctness specifications
  [§8](correctness-specs.md#8-trust) states. Compiled `Float` operations
  correspond to `Float.Model` by `extern`, a trusted step of every
  compiled check.
- **One strengthened native row:** `push`'s exact length. The row of
  [native footprints](../SOURCE-CONTRACTS.md#native-footprints) for
  `push` states its footprint, `{value: any, store: grow}`, trusted input
  whose argument is proved of the specification steps (`Arr.push_grow`).
  The exact length on a normal return of a one-argument `push`,
  $`\mathrm{len}=n+1`$, is a stronger statement about the same native,
  its argument proved of the same steps (`Arr.push_length`, new) and
  tested under Node. The row applies only at a call whose knowledge
  entails $`\mathrm{len}(x)<2^{32}-1`$, a premise checked before the call:
  at length $`2^{32}-1`$ the call writes the property `"4294967295"`, then
  throws a `RangeError`, and that write can break a declared contract
  another alias holds. With `xs` at `(number | undefined)[]` of length
  $`2^{32}-1`$ and an alias `pinned` at `{ "4294967295": 1 }` (admitted by
  `numericOwn`, its singleton within the element contract), `xs.push(2)`
  throws and leaves `pinned["4294967295"]` at `2` (observed under Node
  v26.13.0, 2026-11-06). Dropping heap atoms on the exceptional edge does
  not repair a location contract. Under the premise the call never
  reaches that write, so the row's normal and exceptional outcomes keep
  every location contract. The same write-before-throw exists for `push`,
  `unshift` and `splice` at the length limit under main's footprint rows,
  which trust these natives to keep every location's contract; whether
  they do at the limit is a question of those rows, outside this design,
  with the witness above as its negative case. The existing footprint does not imply
  the exact length: a native appending two elements meets `store: grow`
  too. So every route through `push` strengthens an assumption about the
  host: this row, or
  [native footprints from their specification steps](native-footprints-from-steps.md),
  whose premise that the native runs the steps its row names is stronger
  than main's footprint row, though under it `Arr.push_length` adds
  nothing further. The route that adds no assumption is in the source: an
  index append, `out[i] = 0` for `out.push(0)`, which the append case of
  §3.4 types from the calculus alone; otherwise lengths built by `push`
  stay unknown and their reads checked (decision 7).

## 5. The arithmetic bridge

**Cited.** #104 §2 and [correctness specifications §4](correctness-specs.md#4-the-atoms)
state one foundation: number operations are `Float` operations over
`Float.Model` in the pinned Lean 4.33.1, so the laws are theorems to
prove. #104 separates the integral fact from the safe-integer fact; this
design's atom is the second, and the first enters only through a range
proof.

**Conjectured.** The lemmas, #104's list (decision N) with three added,
marked:

| Fact | Statement |
| --- | --- |
| decoding | $`\mathsf{int}(x)`$: $`x`$ finite, integral, $`\lvert x\rvert\le 2^{53}-1`$, `-0` decoding to 0 (`decodeIntegerBits_sound`) |
| promotion (added) | an integral $`x`$ with a certified $`\lvert x\rvert\le 2^{53}-1`$ is $`\mathsf{int}(x)`$ |
| exact operation | at each arithmetic node, $`\mathsf{int}(x),\mathsf{int}(y)`$ and a certificate of $`\lvert x\pm y\rvert\le 2^{53}-1`$ give $`\mathsf{int}(r)`$ and $`r=x\pm y`$ (`add_integer_exact`, `sub_integer_exact`) |
| constant multiple (added) | $`\mathsf{int}(x)`$ and a certificate of $`\lvert nx\rvert\le 2^{53}-1`$ give $`\mathsf{int}(nx)`$, exactly |
| comparison | on $`\mathsf{int}`$ operands a true `<` gives $`x-y\le-1`$, a false one $`y\le x`$, a false `===` the disequality (`compare_integer_sound`, `compare_integer_false_sound`); without $`\mathsf{int}`$ a false edge gives nothing, NaN included |
| lengths | under length admissibility (§4.3), the result of `lenV` is an integer in $`[0,2^{32}-1]`$ (`length_number_exact`, `bitsOfNat_exact`); a string's length by #104's string boundary; a typed array's waits on #104's decision H |
| index | an integer in $`[0,2^{32}-2]`$ is an array index (`arrayIndex_decode`) |
| bitwise (added) | `x \| 0`, `x >>> 0` and `x & y` give integers in the 32-bit ranges of JavaScript's conversions |

Exactness is established **at every arithmetic node**, before its result
joins any linear atom, so every atom states a sum the doubles computed.
With `x = 2 ** 53 - 1`, `(x + 2) - x` evaluates to `1`, since `x + 2`
rounds to $`2^{53}`$ (observed under Node v26.13.0, 2026-11-06); the node
computing `x + 2` has no certificate of its range, so no atom says it
equals $`x+2`$, and nothing concludes the difference is 2. In the worked
example of §9 the array-index arithmetic the clauses justify sits below
$`2^{32}`$, where lengths give the range certificates; the character
offsets read from `starts`, which the clauses do not bound, stay outside
that claim.

## 6. A wrong annotation

**Conjectured.** Every failure is a located
[obligation diagnostic](../OBLIGATION-DIAGNOSTICS.md) naming the clause:

| Failure | Located at | Names |
| --- | --- | --- |
| a requires not established | the call | the callee, the clause, the actuals |
| an ensures not established | the return | the clause, the returned expression |
| an invariant absent at an observation point | that point | the clause, and the last step whose effect dropped its atom (information, not a premise) |
| a hint not kept | the loop entry or the back edge | the clause, the edge |
| a function value at a weaker contract, a contracted import read at an ordinary signature, an escaping closure with a capture contract | the flow, the import, the closure | the signatures |
| a clause outside §1.3; a clause on a signature with a default or a pattern, on an async function or a generator; an ensures on a signature without a body; a requires on a member an implicit call reaches or on a public entry point | the declaration | the form refused |
| a request whose entry or return knowledge differs from the Fragment's clauses | the unit | the clause and the claimed knowledge |

A failure says that no certificate was found, never that the clause is
false. The producer may attach a candidate counterexample from its solver
(an integer assignment to the clause's terms), marked unchecked; only a
run under Node shows a violation, as for every negative case.

## 7. Out of scope

Stated limits, each refused where it is written:

- **Facts about stored values.** "Every `segmentItems[j]` is a valid index
  of `hyphenWidths`" quantifies over an array's contents. Correctness
  specifications' `forAll` range atoms and lemmas are the mechanism for it
  ([§4](correctness-specs.md#4-the-atoms)); the grammar of §1.3 does not
  state it.
- **Encoded tables and products.** Table dimensions, decoded states and
  products of two variables are nonlinear or content facts.
- **Regular expressions.** What a match implies about a string.
- **Nullability correlations.** "`frameEnd` is set exactly when
  `frameStarts` is" relates two fields' nullness; a guard's conclusion is
  a linear atom, never a nullness fact, so the grammar does not state it.
- **Records reached through other structures**, whose invariant would be
  a fact about stored values (§1.7).
- **`old` of objects**, parameter defaults and patterns in contracted
  signatures, async functions and generators, generic and overloaded
  contracted signatures, requires on members implicit calls reach, typed
  arrays' lengths (until #104's decision H), heap atoms on handler edges.

## 8. Motivation and estimates

**Measured** (the census reported in [TScert #94](../REFERENCES.md#tscert-94)
against TScert `e4598052`, `TSCERT_STEP_LIMIT=300`, by unit, 2026-11-06):
pretext `0d102a5c` verifies 108 of its 209 functions; its rewrite
`f715061c` verifies 211 of 211 (the 209 and the two helpers `defined` and
`present` of `src/checked.ts`), after 481
checked reads (448 `defined`, 33 `present`) and 57 rewritten writes (56
`splice`, one length cut). With the 57 writes turned back into index
writes (`18360b74`), 199 of 211 verify, each of the 12 refused functions
refused at a write with "a numeric array key needs a proved array-index
singleton" (`TSCERT_STEP_LIMIT=300`, 2026-11-06, the write-site design's
census).

**Measured** (pretext's `bun harness bench`, 3 sessions per engine,
2026-11-06; Chrome 156, Firefox 157.0.1, webkit-host): the variant
measurements are a cost study of the rewrites, with the variants'
commits `d055b142` (checked reads reverted), `18360b74` (splices
reverted) and `592b2627` (checks inline) on pretext's local branch
`minimal`, its logs and census records to be attached to the RFC issue; #94
holds the runs of `f715061c` itself. Over the benchmark rows slower in both runs of `f715061c` against
`0d102a5c` (35, 43 and 20 of 68 rows per engine), the mean of those rows'
time ratios is +19.9 %, +40.3 % and +23.0 %; the means are of that
selection; the remaining rows include single-run slowdowns, results
within noise, and speedups. A variant reverting only the checked reads,
and one reverting only the splices, attribute it; a kind's share is how
much of the summed log ratio reverting it removes, assuming the two costs
add (no variant reverts both):

| Engine | Checked reads' share | Splices' share |
| --- | ---: | ---: |
| Chrome 156 | 29 % | 64 % |
| Firefox 157.0.1 | 68 % | 31 % |
| webkit-host | −1 % | 102 % |

Preparation rows lose their slowdown when the splices are reverted
(prepare rows: Chrome's 13 +25.1 % → +1.1 %, Firefox's 13 +30.7 % →
+3.2 %, webkit-host's 10 +29.0 % → −1.6 %); layout, resize and lines
rows lose theirs when the checked reads are (Firefox's 6 resize rows:
+129.9 % → −0.5 %). A third variant writes each checked read inline, as
`const v = e; if (v === undefined) throw …` where the read is a `const`
initializer (71 sites) and `e ?? missing()` elsewhere (410 sites): it
recovers 107 % of the checked reads' cost in Chrome and 86 % in Firefox,
and verifies 208 of 210 functions (the 209 and its helper `missing`,
same census settings, 2026-11-06); in webkit-host it also loses 8 rows
that the checked reads made faster.

**Conjectured, from the measurements.** The writes are the stronger
reason: the splices cost the preparation rows in all three engines, and no
verified form of an index write at a computed key exists today. For the
reads, the inline form recovers most of the cost already; annotations
remove the residue (Firefox's `long-breakable-runs layout` stays +52.2 %
inline against +0.2 % reverted) and the throw paths themselves.

**Conjectured estimates** (a case study's classification of 40 of the 481
read sites, chosen to cover differing mechanisms, and of all 57 writes,
by reading the sources; percentages describe the sample, not the
population):

- reads: 6 of 40 need no annotation, 22 need clauses of §1.3, 12 need
  facts §7 leaves out (stored indices, tables, regex, nullability);
- writes: 46 of 57 are candidates (5 local, 41 from boundary or
  cross-structure facts); 10 rely on a checked read's presence, and the
  length cut needs a pairing invariant of the bracket stack;
- burden: 40–60 annotated functions, 140–240 clauses after expanding
  predicates, 220–380 annotation lines;
- removal: 300–370 of the 481 checked reads; 40–50 of the 57 writes, the
  range above 46 counting presence sites that the write-site design's
  presence route discharges without a clause.

These ranges are planning estimates, not confidence intervals: the
sample is selected, and stored-offset facts and unproved call effects can
move sites out of the scalar class.

## 9. A fully annotated example

`zeros` and `getHanKerningTrims` of pretext `0d102a5c`
(`src/measurement.ts`, `src/han-kerning.ts`), with clauses added and the
code otherwise unchanged (its comments left out). In `f715061c`,
`getHanKerningTrims` holds six checked reads and four `splice` writes.

```ts
/** @requires safeInteger(count) && 0 <= count && count <= 4294967295
 *  @ensures result.length === count
 */
export function zeros(count: number): number[] {
  const out: number[] = []
  for (let i = 0; i < count; i++) out.push(0)
  return out
}

/** @predicate trimLengths(r: HanKerningTrims, n: number)
 *    (r.widthTrims === null || r.widthTrims.length === n) &&
 *    (r.lineStartExtras === null || r.lineStartExtras.length === n) &&
 *    (r.lineEndTrims === null || r.lineEndTrims.length === n) &&
 *    (r.overflowLineEndTrims === null || r.overflowLineEndTrims.length === n)
 */
export type HanKerningTrims = {
  widthTrims: number[] | null
  lineStartExtras: number[] | null
  lineEndTrims: number[] | null
  overflowLineEndTrims: number[] | null
}

/** @requires safeInteger(from) && safeInteger(to)
 *  @requires 0 <= from && from <= to && to <= analysis.flags.length
 *  @requires analysis.starts.length === analysis.flags.length
 *  @ensures trimLengths(result, to - from)
 */
export function getHanKerningTrims(measurement: FontMeasurement, analysis: TextAnalysis, from: number, to: number): HanKerningTrims {
  const out: HanKerningTrims = { widthTrims: null, lineStartExtras: null, lineEndTrims: null, overflowLineEndTrims: null }
  const data = getFontData(measurement)
  if (data === null) return out
  const { flags, starts, normalized } = analysis
  const count = flags.length
  const addWidthTrim = (i: number, trim: number): void => {
    out.widthTrims ??= zeros(to - from)
    out.widthTrims[i - from] = out.widthTrims[i - from]! + trim
  }
  for (let i = from; i < to; i++) {
    if ((flags[i]! & KIND_BITS) !== TEXT) continue
    const start = starts[i]!
    const end = i + 1 < count ? starts[i + 1]! : normalized.length
    const first = normalized.charCodeAt(start)
    if (i > 0 && maybeHanKerns(first) && haltedSide(getCharType(data, normalized, start - 1), getCharType(data, normalized, start)) === 1) {
      const trim = getTrim(data, first, measurement)
      out.lineStartExtras ??= zeros(to - from)
      out.lineStartExtras[i - from] = trim
      addWidthTrim(i, trim)
    }
    for (let k = start + 1; k < end; k++) {
      const earlier = normalized.charCodeAt(k - 1)
      const later = normalized.charCodeAt(k)
      if (!(maybeHanKerns(earlier) || maybeHanKerns(later)) || isCanvasCjkSymbol(earlier) === isCanvasCjkSymbol(later)) continue
      const side = haltedSide(getCharType(data, normalized, k - 1), getCharType(data, normalized, k))
      if (side !== 0) addWidthTrim(i, getTrim(data, side === 1 ? later : earlier, measurement))
    }
    const last = normalized.charCodeAt(end - 1)
    if (!maybeHanKerns(last)) continue
    const atEnd = i + 1 === count
    if (!atEnd && haltedSide(getCharType(data, normalized, end - 1), getCharType(data, normalized, end)) === -1) {
      addWidthTrim(i, getTrim(data, last, measurement))
      continue
    }
    const lastType = getStaticCharType(normalized, end - 1)
    if ((lastType !== CLOSE && lastType !== CLOSE_QUOTE) || getCharType(data, normalized, end - 1) !== CLOSE) continue
    if (atEnd || ((flags[i + 1]! & KIND_BITS) === TEXT && (flags[i + 1]! & UNBROKEN) === 0)) {
      out.lineEndTrims ??= zeros(to - from)
      out.lineEndTrims[i - from] = getTrim(data, last, measurement)
    } else {
      out.overflowLineEndTrims ??= zeros(to - from)
      out.overflowLineEndTrims[i - from] = getTrim(data, last, measurement)
    }
  }
  return out
}
```

**Conjectured.** What discharges each obligation, and what each needs; the
example verifies only once the footprints below exist:

| Obligation | Discharged by |
| --- | --- |
| `zeros`' ensures | automatic once each iteration's length is known: the loop keeps $`\mathrm{len}(out)=i`$ and $`i\le count`$, and the false edge of `i < count` with both $`\mathsf{int}`$ gives $`i=count`$; the length after `out.push(0)` needs a `push` route of decision 7, and the index append `out[i] = 0` gives it with no added trust (§3.4) |
| `zeros(to - from)`'s requires | `to - from` is exact (§5) and in $`[0,\mathrm{len}(flags)]\subseteq[0,2^{32}-1]`$ by the requires |
| `flags[i]`, `starts[i]` | automatic: `i` from `from` by one, $`from\le i<to\le count`$, `count` the length read of `flags`; `starts` by the equal-length requires |
| `starts[i + 1]` | the true edge of `i + 1 < count` |
| both `flags[i + 1]` | `atEnd` false: the disequality $`i+1\ne count`$ with $`i+1\le count`$ (§4.2) |
| `out.f[i - from]` writes | $`0\le i-from<to-from`$, and `trimLengths(out, to - from)` after `out.f ??= zeros(to - from)`: either the field was already of that length or `zeros` just gave one; `getTrim`, evaluated after the receiver and key, must keep the array's store |
| `addWidthTrim`'s contract | a non-escaping local closure (§2.6): the producer proposes $`K_p`$ = `safeInteger(from) && safeInteger(to) && 0 <= from && from <= to && to <= 4294967295 && safeInteger(i) && from <= i && i < to && trimLengths(out, to - from)`, which carries the outer requires' facts about the captures `from` and `to` (without them `from = 0.5`, `to = 2`, `i = 1` meets the rest, and `zeros(1.5)` makes an array of length 2 read at `0.5`), and $`K_q`$ = `trimLengths(out, to - from)` over its captures `out`, `from`, `to`; Lean certifies its body (the `??=` either keeps a field of that length or installs `zeros(to - from)`), and each of its three calls establishes $`K_p`$ and receives $`K_q`$, re-established on return although the call may change the field |
| facts kept across calls | the length atoms of `flags` and `starts` and the atoms about `out` must survive the calls of `getFontData`, `getCharType`, `getStaticCharType`, `getTrim`, `maybeHanKerns`, `haltedSide`, `isCanvasCjkSymbol` and `zeros`, by their certified footprints; `addWidthTrim`'s atoms about `out` come from its $`K_q`$ instead |
| the ensures | `trimLengths(out, to - from)` at both returns, the early one with four `null` fields |
| the caller | `measureAnalysis` (`src/prepare.ts`) calls it with its own `analysis`, `from`, `to`; with the same three requires, it establishes them where the calls before (measurement, `zeros`, the segment loop) keep `analysis`'s field links and the stores of `flags` and `starts` by their footprints, the same kind of obligation as the row above |

The example is a conditional target: its footprint obligations are
open. `getTrim` writes the cache `data.trims` (a `Map`) and measures text
through the canvas, its own caches included. A footprint keeping array
stores (`store: "keep"`) would keep the length atoms of `flags`,
`starts` and `out`'s arrays; one changing every value location drops the
read links of `out`'s fields, and the `trimLengths(out, …)` atom with
them. The needed footprint leaves `out`'s fields out of `getTrim`'s
changes. Correctness specifications' region frames
([§1](correctness-specs.md#1-the-contract)) name a parameter's own
fields and elements, not `data.trims`'s `Map` contents nor the
measurement caches reached through `measurement`; the extension, nested
or reachability-based frames, is decision 9. Freshness of `out` alone
does not give it.

The clauses do not say that the character offsets in `starts` lie inside
`normalized`: `charCodeAt` answers `NaN` out of range, a value its number
contract admits, so array safety does not need it.

A record invariant on the prepared handle has the form

```ts
/** @invariant this.lineEndTrims === null || this.lineEndTrims.length === this.widths.length
 *  @invariant this.lineStartExtras === null || this.lineStartExtras.length === this.widths.length
 */
export type PreparedLineBreakData = { widths: number[]; lineEndTrims: number[] | null; lineStartExtras: number[] | null; /* … */ }
```

and attaches to every signature naming `PreparedLineBreakData`, the
intersection `PreparedLineData` included (§1.7). The public functions
taking a handle validate it once (§2.4), a few length comparisons per
call; the line walkers behind them then read without checks. It cannot
state `segmentFlags.length === widths.length`: pretext's comment on the
type says a JSON copy of the handle turns `segmentFlags` into an object
with no length, so that read stays checked.

## 10. Cases and controls

**Conjectured.** Positive pipeline cases: `zeros` and a caller reading
`zeros(n)[n - 1]` under `n > 0`; parameter ranges with a forward and a
reverse loop; the paired counters `at = base + mi - from`; an append
contract `widths.length === old(widths.length) + to - from`; a record
invariant kept by a walker and established by a builder with `@opens`; a
public entry point validating a handle (§2.4); a non-escaping closure
with a capture contract.

Negative cases, each run under Node with a concrete wrong value:
`from = 0.5` without `safeInteger(from)`, reading `undefined` at `number`;
a validator returning `false` whose caller reads on that branch as
though it had returned `true`;
an inclusive end `to <= xs.length + 1`; a missing equal-length requires,
reading the shorter array past its end; a callback truncating an array
between the bound and the read; a builder throwing between two appends,
its caller catching and reading the shorter array; an escaping closure
called after its captured record shrank.

Controls (`pipeline/test.mts`), bypassing the producer: a forged
$`K_p`$ at a call; a ghost slot bound to another path, or to the path
after a mutation; an ensures checked at another result slot; a linear
step with a wrong multiplier, and one rounding a non-integer slot; an
exactness claim at `2 ** 53 - 1 + 2`; a length or read link kept across
a write of its support through an alias, across a receiver replacement,
and across a callback changing a nested array; a heap atom carried onto a
handler edge; a request claiming entry knowledge other than an exported
unit's written requires, and claiming a requires where none is written;
an ensures on a signature without a body; a contracted function value
passed at a plain arrow; an object with a contracted method passed at a
supertype whose method states no requires; a contracted import read at
its ordinary signature; a non-escaping closure's capture contract with
its binding passed as a value; a store-supported atom kept across a
write filling a hole of a sparse receiver; an $`\mathsf{int}`$ atom
claimed from `Number.isInteger` alone at $`2^{53}`$; an elaboration of
`safeInteger((x + 1) - 1)` to $`\mathsf{int}(x)`$; a spread of two arrays
whose lengths sum past $`2^{32}-1`$; a requires attached to a member at
a hook key in a forged Fragment, bypassing the front end; the strengthened `push` row used
at a call whose knowledge does not entail $`\mathrm{len}(x)<2^{32}-1`$; a validator's guarded
atom used on its `false` branch; a requires on a callable field of a
public module's exported type; an object with a method that has a
requires returned at an interface that lacks the method; a function with
a requires passed at `unknown` and called after a `typeof` test; a clause attached to another declaration.

## 11. Order of work

**Conjectured.** Each step lands with its cases and the suites green:

1. Correctness specifications' steps 1–4 (the knowledge contract, its
   plan, calls through it) and #104's steps 1–4 (the numeric foundation,
   fact transport, loops, strings and readable arrays); the `RangeError`
   step of the calculus's array allocations and rest packs, the length
   bound as a length conjunct of `listT`, and the typing lemmas
   `listT_grow`, `listT_alloc`, `arr_alloc_rule` and the rest-entry
   lemmas with their exceptional case.
2. Linear and guarded atoms, the certificate steps and
   `Linear.check_sound`; the producer's affine inference.
3. The precondition in the unit's safety: the conditioning field of
   `CertifiedPlan.spec`, the changed statement of `checkUnitJson_safe`,
   public entry points, the generalized `requires` with `covers`,
   `plain` and `keeps` at flows and imports.
4. Ghost slots for `old`, capture contracts of local closures, the exact
   `push` row and the bounded write rule.
5. The JSDoc reader, elaboration and `elab_sound`, `@predicate`
   expansion, record invariants and `@opens`.
6. Pretext: annotate the 12 write-holding functions and the line walkers,
   turn the corresponding rewrites back, and measure the census and the
   benchmark on the result.

## Decisions for the owner

1. **The written form.** JSDoc tags parsed by TypeScript's parser and
   resolved by the front end (recommended: shipped code unchanged, clauses
   at the declaration); correctness specifications' `spec(f, {…})`
   statements, whose closures TypeScript checks whole but which add calls
   to the shipped module; or a sidecar `.spec.ts` module. JSDoc reverses,
   for bound clauses, correctness specifications' decision 1, which the
   owner approved: its form table records that TypeScript does not check
   JSDoc clauses.
2. **A precondition conditions safety** (§2.4), changing the statement of
   `checkUnitJson_safe` for contracted units and amending correctness
   specifications' unconditional safety plan for them. Recommended: yes;
   it is #104's decision P, second route, in place of #104's
   recommendation of the first.
3. **Public entry points** carry no requires and validate (§2.4).
   Recommended: yes; the verdict then assumes only that external code
   enters through the public modules (decision 7).
4. **Record invariants by type**, with `@opens` keeping the ensures
   (recommended), or named predicates written on each signature only.
5. **The arithmetic foundation**: #104's decision N as recommended there,
   shared with correctness specifications' decision 6.
6. **Linear steps** with one rounding or one disequality per step,
   chained (recommended), in place of #104's difference-only fact.
7. **The trust of §4.3.** Each part is a property JavaScript
   guarantees; each strengthens what the verdict assumes about the host or
   the program's boundary, so each needs the owner's choice:
   - the JSDoc reader, attachment and public inventory, new code of the
     trusted front end;
   - the public modules, the verdict's one assumption about external
     code, derived from `package.json` where it states `exports` or
     `main` (recommended);
   - length admissibility in the store contract, assumed of input heaps
     and of heaps external calls return, as `HeapOk` is; preserved by the
     calculus once its allocations gain the `RangeError` step, and by
     natives through the bound every store-returning row assumes,
     trusted on every route (a throw in the step model moves it into the
     step-correspondence premise); without it no array
     length is a known integer and no annotation discharges an array
     bound;
   - `push`'s exact length: a strengthened native row, or the
     specification-step interface of native footprints from their steps,
     both stronger than main; or, adding nothing, index appends in the
     source in place of `push`, or reads of `push`-built arrays kept
     checked (recommended under the goal of adding no trust).
8. **Order.** This design after correctness specifications' steps 1–4 and
   #104's steps 1–4 (recommended), or a first landing of parameter ranges
   and result lengths alone.
9. **Frames for pretext's helpers** (§9): a footprint that keeps a fresh
   record's fields across a call that writes a cache, by nested region
   frames or by frames of what is reachable from the call's arguments; an
   extension of correctness specifications' region frames, needed by the
   worked example and to be designed before step 6 of §11.
