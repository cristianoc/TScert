# Source contracts

Source verification requires a faithful interpretation of annotations, module
bindings and library contracts. This document specifies how the type reader
translates them into graph types: modules and their imports, declarations and
their equations, written and computed types, classes, and the reviewed
contracts of library types, globals, modules, regular expressions and
promises. The lowering of statements, guards and iteration that consumes
these contracts is in [Source elaboration](SOURCE-ELABORATION.md).

The prerequisites are the judgments and state rules in
[Program typing](PROGRAM-TYPING.md), declaration equations and binders in
[Recursive equations](RECURSIVE-EQUATIONS.md), and graph types in
[Positive types](POSITIVE-TYPES.md). Types are finite unions of graph labels;
$`\Gamma`$ assigns types to variables, and $`\Gamma\vdash_G t:A`$ is the core
term judgment. Runtime values and worlds are specified in
[Semantics](SEMANTICS.md). The trusted source model and refusal boundaries are
specified in [Source model](SOURCE-MODEL.md) and
[Source fragment](SOURCE-FRAGMENT.md).

Throughout, $`⟦T⟧`$ is the graph type a
declared or written term lowers to, and $`T[\vec p:=\vec U]`$ the term with its
binders fixed to ground types.

## Modeling a library

A library contract describes the operations real project code uses. Choose
representative calls, callbacks and returned values from that code, and state
the supported use in the contract. Complete coverage of the library's API is
not a prerequisite. The compiler-API instance is specified in
[Compiler API](COMPILER-API.md).

Use the existing mechanisms: declaration overlays for native contracts,
[host families](HOST-FAMILIES.md) for objects with shared invariants, and
[footprints](FOOTPRINTS.md) for facts preserved across calls. A native
operation receives a stronger effect only where its audit establishes it;
other operations retain their declared effects. An operation's name or its
membership in a library supplies no preservation guarantee.

Audit the supported operation's execution: callbacks it retains or invokes,
serialization and coercion, aliases, result construction, and both normal and
exceptional exits. A runtime declaration describes types; it does not prove
these effects. A project wrapper can require stronger invariants, with its
body checked against them. Using a guarantee whose body or dependencies are
uncertified requires an explicitly approved external contract; without that
contract the stronger use is refused.

A restriction is a boundary of admitted behavior. State it in the source
fragment and the external contract, enforce it, and retain a control showing
that excluded behavior cannot enter silently. An excluded behavior requires
no general modeling machinery. Every contract the admitted use relies on is
represented completely or refused; a restriction cannot erase a callback,
field or execution that the admitted use still permits.

Measure a simplification against the real project. Keep pipeline examples
and independent boundary controls, run the project suites, and compare the
census before and after. Coverage losses are part of the result. A smaller
example alone does not establish that a simplification preserves project
support. General mechanisms remain reusable; library-specific work follows
the project's useful calls rather than hypothetical uses of every export.

## Modules and code units

A module is the unit of verification. Its function declarations are hoisted;
its other top-level code (constants, classes, enums, expression statements)
is the initialization unit $`I`$, run once, in order. With $`F`$ the module's
functions and $`\Gamma_M`$ the module's scope:

```math
\frac{\forall f\in F.\;\Gamma_M\vdash f\quad
      (I\neq[\,]\Rightarrow\Gamma_M\vdash I:\mathsf{undefined})\quad
      F\neq\emptyset\lor I\neq[\,]}
     {\vdash M}\ \textsf{module}
```

where $`\Gamma_M\vdash I:\mathsf{undefined}`$ checks the initialization unit as
a body with no parameters that completes with `undefined`. A module with
neither runs nothing and states no claim; it is refused, so an acceptance
always checked some code. A class's methods are closures its initialization
allocates, so they are checked in that unit. A module function's slot is its
annotated signature $`(R;\vec A\to B)`$, a generic one's read as a value its
[scheme](#generic-function-and-constructor-types), and, for a function that is not
generic and has no rest parameter, also that signature extended by a rest of
`unknown` elements (`moduleArrow`):

```math
\frac{f\ \text{a module function at}\ (R;\vec A\to B),\ \text{no rest parameter, no binders}}
     {\Gamma_M(f)=⟦(R;\vec A\to B)\land(R;\vec A,\ldots\top\to B)⟧}\ \textsf{module-function}
```

Its code collects no rest and is checked by its own unit at
$`(R;\vec A\to B)`$, which is the extension's fixed row, so it offers the
extension too (`CodeOffers`, then `offers_sem`): a call writing
further actuals runs it from the same frame, the actuals past its parameters
discarded. By [function coverage](POSITIVE-TYPES.md#function-and-class-coverage)
(`rest`, and the variadic rule) the slot then meets every signature
$`(R';\vec A'\vec C\to B')`$ and $`(R';\vec A'\vec C,\ldots E\to B')`$ with
$`R'\sqsubseteq R`$, $`\vec A'\sqsubseteq\vec A`$ and $`B\sqsubseteq B'`$,
whatever $`\vec C`$ and $`E`$: a module function is a value of a signature
binding more parameters, as JavaScript calls it. A guard's slot holds its
promise signature beside its plain one, and that one extended by the same
rest, which the same code offers, so the guard meets a promise signature
binding more parameters (`native-guard-filter`). A function with a rest
parameter collects further actuals, so its slot is its signature alone. A
value known only by its type, a parameter or an import, has no such
extension: a function type's meaning is a promise about calls writing at most
its positions (`callsT`), which a function reading further positions keeps,
one with further optional parameters or one with a rest parameter (`rest`).
TypeScript admits `(x: T, y?: S) => U` as a `(x: T) => U`, so a call through
that type writing a second actual of another type is not safe.

A module constant is read at its annotation or at the
initialization unit's claim for its initializer
([module constants](SOURCE-ELABORATION.md#mutable-bindings-and-module-constants)).
An unannotated constant whose initializer is a closure without a rest
parameter, binders, defaults or a guard, with a written result, is claimed
where it is created at its signature and at that signature extended by a
rest of `unknown` elements, the closure's body checked at each, as a module
function's slot holds both:

```math
\frac{c = \lambda(\vec x{:}\vec A).\,b\ \text{no rest, binders, defaults or guard}\quad
       \Gamma_c\vdash b:B\ \text{at}\ (R;\vec A\to B)\ \text{and at}\ (R;\vec A,\ldots\top\to B)}
     {\Gamma_I\vdash c:⟦(R;\vec A\to B)\land(R;\vec A,\ldots\top\to B)⟧}\ \textsf{constant-closure}
```

The closure code collects no rest, so a call writing further actuals binds
its parameters and discards the rest; the second signature is a claim its
body is checked at (`arrow-constant-callback`), never a widening of the
first. The
initialization unit refuses a call, direct or through module functions, that
can read a constant not yet initialized (`checkInitializationOrder`). Walking
the steps in order, with $`\mathrm{ready}_k`$ the constants the steps before
step $`k`$ declare, $`\mathrm{code}`$ the module functions and the constants
the source names holding a closure, $`\mathrm{names}(c)`$ the names code $`c`$ mentions, and
$`\mathrm{step}(k)`$ the names step $`k`$ mentions outside the closure a constant's
declaration holds:

```math
\frac{R_k=\mathrm{reach}(\mathrm{step}(k)\cap\mathrm{code})\qquad
       \forall c\in R_k.\ \mathrm{names}(c)\cap\mathrm{constants}\subseteq\mathrm{ready}_k}
     {\text{step}\ k\ \text{is admitted}}\ \textsf{initialization-order}
```

where $`\mathrm{reach}`$ closes a set of code under the code its names mention.
Creating a closure runs none of its code, and every call of it follows a
mention of its name, so its code is reached there.

**Claims against annotations.** A claimed type $`C`$ is within the
annotation's $`A`$ (`within`) when

```math
\frac{\mathrm{canon}_G(C)\subseteq\mathrm{canon}_G(A)}{C\sqsubseteq_G A}
\qquad
\frac{\mathrm{check}(G,C,A,p)=\mathsf{true}}{C\sqsubseteq_G A},
```

and $`C\sqsubseteq_G A`$ implies $`⟦C⟧_G\subseteq⟦A⟧_G`$ at every
assignment of the parameter rows (proved:
`CertificateProducer.comparisonUsing_sound`, the comparison `within`
accepts; the first rule compares rows with identical clauses). A
top-level function's claimed parameter and result types are the
annotation's (`sameMeaning`):

```math
\frac{C\sqsubseteq_G A\quad A\sqsubseteq_G C}{A\simeq_G C},
```

so the claim may replace the annotation. A closure's claimed signatures, a
method's among them, and a class's claimed construct signatures need only be
within the source's, parameter by parameter
([source closures](SOURCE-ELABORATION.md#source-closures-and-their-annotations)). The body is
checked at each claimed signature, so this comparison is not what makes a
claim sound; it keeps a producer from advertising a signature the source does
not state.

## Imported, ambient and global values

A value the module does not define joins its scope at the type its
declaration states. These rules are assumptions a result is relative to:

```math
\frac{x\ \text{imported, declared at}\ T\ \text{with no binders}}
     {\Gamma(x)=⟦T⟧}\ \textsf{import}
\qquad
\frac{\begin{array}{c}
x\ \text{declared at}\ \forall\vec p\le\vec B.\,T\quad
\text{(certified by its own unit, or imported)}\\
\forall k.\;\vec U_k\ \text{ground},\ |\vec U_k|=|\vec p|,\quad
\forall i.\;G\vdash⟦U_{k,i}⟧\le⟦B_i[\vec p:=\vec U_k]⟧
\end{array}}
{\Gamma(x)=\bigwedge_k⟦T[\vec p:=\vec U_k]⟧}\ \textsf{instances}
```

where $`\vec U_1,\ldots,\vec U_m`$ are the type arguments the unit's calls of
$`x`$ name and the conjunction is one callable carrying every instance's
signatures (`Scheme.moduleInstances`); the second rule is sound because each
instance holds of the value. An intersection in the signature whose operands
are ground once the binders are fixed is the graph's meet of those operands
(`meetRow`); one still over a binder at a non-record operand is refused. A
class is read at its construct signature, which `new` meets.

A constant declared `unique symbol` whose symbol is known
([symbol keys](#library-globals), $`\mathrm{sym}(k)`$) holds that symbol, the
value of `typeof` it ([unique-symbol](#computed-types)); one whose symbol is
not known is a symbol:

```math
\frac{x\ \text{imported, declared}\ \mathtt{const}\ x\colon\mathtt{unique\ symbol}\quad \mathrm{sym}(x)\ \text{known}}
     {\Gamma(x)=\mathsf{symbolLit}(\mathrm{sym}(x))}\ \textsf{import-unique}
```

A function declared with overloads $`S_1,\ldots,S_n`$ ($`n>1`$) is callable at
exactly those; an implementation's own signature is not callable from outside.
Generic overloads stating the same type parameters $`\vec p`$, each with the
same bound, are one generic declaration ($`\vec p`$ empty where none is
generic):

```math
\frac{x\ \text{declared with overloads}\ \forall\vec p.\,S_1,\ldots,\forall\vec p.\,S_n\ (n>1)}
     {\Gamma(x)=⟦\forall\vec p.\ S_1\wedge\cdots\wedge S_n⟧}\ \textsf{overloads}
\qquad
\textstyle\bigcap_i⟦\forall\vec p.\,S_i⟧=⟦\forall\vec p.\ \bigwedge_i S_i⟧ .
```

The equation holds because each $`S_i`$ names only the shared binders, so an
instance of the conjunction is the conjunction of the instances. Each call
is checked at the instance its claim names, against any overload whose
parameters admit its actuals (`ambient-generic-overloads`; at a marker the
second overload of `valFromOption`, whose instance the bound admits). Generic
overloads stating different type parameters are refused
(`ambient-generic-overloads-renamed`).

An ambient declaration the module writes (`declare function`, `declare
const`, `declare class`, `declare enum`) runs nothing and is in scope everywhere, read as an
import is. With $`D`$ the declarations TypeScript binds $`x`$ to:

```math
\frac{x\ \text{bound by ambient declarations}\ D\ \text{of the module}}
     {\Gamma(x)=⟦\mathsf{type}(D)⟧}\ \textsf{ambient}
```

where $`\mathsf{type}(D)`$ is what `import` and `overloads` read. `declare const
k: unique symbol` names a symbol and binds no value. A name that is also an
interface or alias denotes the value in a value position and the other
declaration in a type position.

A value name the module neither imports nor binds is a **global** when
TypeScript binds it to a global variable. A namespace of the same name
declaring only types (interfaces, aliases and such namespaces) makes no
value, so the name's value is the variable's (`node-console`: Node declares
`console` as both). A global is read only at the
members and call signatures the module's references select (`selectGlobal`):
every reference reads a member by name, is called, or is read as a value; a
method's reference must be called; a `this` result is the selection itself; a
generic, optional or modified method, and a member of a generic base
interface, are refused. With $`I`$ the annotated interface, $`M`$ the names
read, $`O_m`$ the overloads TypeScript resolves the calls of method $`m`$ to,
and $`C`$ the call signatures it resolves the calls $`x(\ldots)`$ to, joined
by all of $`\mathsf{calls}_I`$ where a reference reads $`x`$ as a value, which
whoever receives it may call at any of them:

```math
\frac{x\ \text{a global variable annotated}\ I\qquad
      M=\{m\mid x.m\ \text{occurs}\}\qquad
      \text{every occurrence of}\ x\ \text{is some}\ x.m,\ \text{a callee or a value}\qquad
      O_m\subseteq\mathsf{overloads}_I(m)\qquad
      C\subseteq\mathsf{calls}_I\qquad
      (x\ \text{read as a value}\Rightarrow C=\mathsf{calls}_I\neq\emptyset)}
     {\Gamma(x)=⟦\mathsf{sel}_{M,O,C}(I)⟧}\ \textsf{global}
\qquad
⟦I⟧\subseteq⟦\mathsf{sel}_{M,O,C}(I)⟧ .
```

The inclusion is why the rule assumes no more than the declaration: a record
says nothing of keys it does not name, a method's receiver is its host, and a
`this` result is the host. A declaration's `any` is read as `unknown`.

The overloads $`O_m`$ a method's calls select, generic ones among them, are
one callee (`overloadTerm`): with $`\forall\vec p_i.\,S_i`$ the $`i`$-th
(its binders $`\vec p_i`$ empty for a plain one), the scheme over every
binder holding every signature,

```math
\frac{O_m=\{\forall\vec p_1.\,S_1,\ldots,\forall\vec p_n.\,S_n\}\qquad
      \vec p_1,\ldots,\vec p_n\ \text{pairwise disjoint}\qquad
      \mathrm{fv}(S_i)\cap\vec p_j=\emptyset\ (i\neq j)}
     {⟦\mathsf{sel}(m)⟧=⟦\forall\vec p_1\cdots\vec p_n.\ S_1\wedge\cdots\wedge S_n⟧}\ \textsf{global-overloads}
\qquad
\textstyle\bigcap_i⟦\forall\vec p_i.\,S_i⟧\subseteq⟦\forall\vec p_1\cdots\vec p_n.\ \bigwedge_i S_i⟧ .
```

The inclusion holds because a reassignment of every binder within its bound
reassigns each $`S_i`$ only at its own binders, so a value meeting each
overload meets every signature there. Each call is checked at the instance
its claim names, at any signature of it whose parameters admit its actuals
(`object-entries-mixed-overloads`). A binding of the
[library modules](#library-modules) reads the overloads its calls select
the same way, their binders its type parameters. Two generic overloads
binding the same name are refused. A
global both called and read through members is a callable object holding
those members, its call signatures and each member's contract
(`number-call-and-members`). A global both constructed and read through
members or called has no clause and is refused, unless the overlay reads its
construction or those members as intrinsics (`new Promise`,
`Promise.resolve`). A global both read as a value and constructed is
refused too. A global declared as a function, its overloads without
bodies (`declare function parseInt(…)`), is only called, at the overloads
TypeScript resolves its calls to:

```math
\frac{x\ \text{a global function of overloads}\ F\qquad
      \text{every occurrence of}\ x\ \text{is a callee}\qquad
      C\subseteq F}
     {\Gamma(x)=⟦\mathsf{calls}(C)⟧}\ \textsf{global-function}
```

Every global variable is read through the reviewed overlay
([Library globals](#library-globals)), wherever it is declared (the standard
library, an installed package such as Node's `process`, a declaration file of
the project): each member, call, construct or value reading it selects is one
an entry lists with its exact text and its origin, or it is refused. An
origin is the standard library or an installed package, the directory under
`node_modules` whose `package.json` names it; every declaration of the
variable comes from an origin its entries admit, so an identically spelled
declaration of the project is refused (`invalid-fake-process-argv`); a mixed declaration
(`console` of the DOM's library and of `@types/node`) is no exception
([Node's `process`](#nodes-process); `invalid-host-global-variable`,
`invalid-node-console-unreviewed`). So is every global function: its implementation is outside what is verified,
wherever its declaration lies (the standard library, an installed package,
a declaration file of the project), so each overload a call resolves to is
one an entry lists with its exact text, an augmentation's included, or the
call is refused (`node-clear-timeout`; `invalid-parse-int-overload`, run
under Node; `invalid-node-global-unreviewed`, `invalid-host-global-unreviewed`,
`invalid-host-global-changed`). The checked file's own ambient declarations
are the [ambient assumption](DESIGN.md#trust-surface). A
a function of Node's modules an overlay entry lists, through the overlay of
library modules ([Library modules](#library-modules)).

### Imported classes and `instanceof`

`x instanceof C` runs ECMA-262's InstanceofOperator: it looks up
`C[Symbol.hasInstance]` along the class value's prototype chain, every
object on it and an accessor's getter included, and calls the method where
one other than `Function.prototype`'s is found; otherwise it reads
`C.prototype` and looks for that object along `x`'s prototype chain. A class
declaration's `prototype` is the object its class statement creates, held by
a property no code can write or redefine; the object `new C` allocates
inherits it, and a constructor returning another object makes `new C` that
object, a value of `C`'s type like any other to the test's refinement. For a class another module declares, the test reads the
import binding and looks for the key $`\kappa_C`$ the import's name gives
the class's prototype, as the test of a class of the file does
([`instanceof`](SOURCE-ELABORATION.md#instanceof)):

```math
\frac{\begin{array}{c}
C\ \text{a named or default import TypeScript binds to a class declaration}\ D\quad
\mathsf{checked}(D)\\
\mathsf{type}(C)\ \text{states no}\ \texttt{[Symbol.hasInstance]}\qquad
\Gamma\vdash e:A\qquad \Gamma(C)=⟦\mathsf{type}(D)⟧
\end{array}}
{e\ \mathtt{instanceof}\ C\;\equiv\;\mathsf{let}\ x=e\ \mathsf{in}\ \mathsf{let}\ p=C\ \mathsf{in}\ \mathsf{hasKey}(\kappa_C)(x)\ :\ \mathsf{boolean}}\ \textsf{import-instanceof}
```

with $`\kappa_C = \texttt{[[}C\texttt{.prototype]]}`$, $`C`$ the import's
local name, which no class of the file shares, and

```math
\mathsf{checked}(D)\iff
\begin{cases}
D\ \text{is at the top level of a module}\ M\ \text{other than the file, not}\ \mathtt{declare}\text{d},\\
M\ \text{is a source file of the program, not a declaration file, which TypeScript accepts without an error},\\
M\ \text{holds no comment}\ \texttt{@ts-ignore},\ \texttt{@ts-expect-error}\ \text{or}\ \texttt{@ts-nocheck},\\
M\ \text{reads}\ D\text{'s binding only as}\ \mathtt{new}\text{'s callee,}\ \mathtt{instanceof}\text{'s right operand, a base class's or}\ \mathtt{export\ default}\text{'s expression, or a member read's receiver (no}\ \mathtt{\_\_proto\_\_}\text{, no write), or names it in a type or an export},\\
D\ \text{extends nothing, the standard}\ \mathtt{Error},\ \text{or a class declaration}\ E\ \text{with}\ \mathsf{checked}(E).
\end{cases}
```

A re-export is passed through to the declaration TypeScript resolves the
import to. Because $`M`$ has no TypeScript error and suppresses none, no
code of $`M`$ writes the class's binding (TS2629);
`invalid-instanceof-rebound-value-import` and
`invalid-instanceof-suppressed-value-import`, run under Node, show the test
of a module that does. The uses of the binding $`M`$ may make, searched in
every expression that runs (heritage clauses, `export default` and
decorators included), leave it no alias, pass it to no function and write
none of its members, so no code of $`M`$ reaches the class value by its name
to change its prototype chain (`invalid-instanceof-default-hook-value-import`,
`invalid-instanceof-heritage-hook-value-import`, run under Node: `true` of a
string). A module replacing that
chain's prototype by an object holding a `[Symbol.hasInstance]` method makes
that method answer the test (`invalid-instanceof-hooked-value-import`, run
under Node: `true` of a string); one defining a getter for it through an
alias runs the getter at every test (`invalid-instanceof-getter-value-import`,
run under Node: the getter shrinks the array a `map` visits, leaving a
hole). The test refines a tested immutable
variable as every tag test does: no value the file makes owns
$`\kappa_C`$, and a passed test drops the primitive arms; a failed one keeps
the class's arm, which a record meeting the class's type belongs to
(`invalid-instanceof-class-else-value-import`, run under Node).

**What it assumes.** The import meets its declaration, as `import` assumes
of every imported value ([trust surface](DESIGN.md#trust-surface)): the
binding holds the class $`D`$'s statement creates, and, throughout
execution, the lookup of `Symbol.hasInstance` along the class value's
prototype chain finds only data properties, no getter and no proxy trap,
and yields the standard method of `Function.prototype`. The checks of
$`\mathsf{checked}(D)`$ see the uses $`M`$ makes of the class's binding by
name; code of other modules, and code reaching the class value otherwise
(`this` in its static code, an instance's `constructor`), is what the
assumption covers. A module of the program is checked on its own; that run checks
$`D`$'s code. Under the assumption the JavaScript test reads the binding,
reads the prototype, which runs no code, and walks `x`'s chain, as the
lowered test does (argued here, not proved; Lean proves the lowered
program's safety). Refused, each with its case: a class expression a
constant holds (`invalid-instanceof-expression-value-import`), a class an
ambient module declares (`invalid-instanceof-ambient-value-import`), one
extending such a class (`invalid-instanceof-ambient-base-value-import`), a
module writing its class's binding, with or without a suppressing comment,
one using the binding otherwise (`invalid-instanceof-hooked-value-import`,
`invalid-instanceof-getter-value-import`), and a local constant holding an imported
class (`invalid-instanceof-alias-value-import`). A local class extending an
imported one is refused already ([derived classes](SOURCE-ELABORATION.md#derived-classes)).

### Types stated by annotations

The written annotations that determine a declaration's exposed type, by its
kind. These, and only these, are read for a declaration a type reaches; no
function body, initializer's code or static block is read. A declaration
without them is refused
([fragment boundary](SOURCE-FRAGMENT.md#refused-on-principle)). The structure is the checker's symbols, not
syntax: what a name or a selection denotes is one symbol, its annotations
the union over its declarations (an overload set's, an accessor pair's, a
merged entity's); a class's members are its instance and static member
symbols, apart; a module's or namespace's are its exported symbols,
`export =`, a default export and ambient members included. A member under
a computed name, which the checker binds late, counts by its declaration,
and its name's entity is swept. A name path, `typeof E.p₁…pₙ` (a qualified name, a property access, a
`typeof` or import type), contributes the determining annotations of every
declared entity on it: the root, which must have them, and each later step
with a declaration, with everything those annotations name. A step the
checker synthesises (a mapped type's member, an instantiation's) has no
declaration and needs none: its type is computed from annotations already
swept. A module or namespace a further step selects from contributes
nothing itself.

| Declaration | Determined by |
| --- | --- |
| Interface, type alias | Its whole syntax |
| Variable, binding element, parameter | Its own annotation, or its enclosing pattern's; a `const` initialized by a literal naming nothing (a string, number, bigint, Boolean or `null`, signed or parenthesized, an object or array literal of these, `as const` or not), each destructuring default on the way a literal too; a `const` initialized by a function literal, its parameter and result annotations |
| Property declaration or signature | Its annotation |
| Property assignment, default export | Its value's: a literal naming nothing; a function's parameter and result annotations; a nested object literal's properties, each by its kind; an assertion's type (`as` or angle-bracket) |
| Function, method, signature | The symbol's overload signatures if it has any, else its parameter and result annotations; a function's or method's defaulted parameter is optional to its callers |
| Accessor | The symbol's getter result or setter parameter, either for the pair |
| Constructor | Its parameter annotations, or its overloads' with the implementation's parameter properties |
| Class | Its type parameters, its heritage, and every instance and static member symbol |
| Namespace, module | Every exported symbol, `export =` and a default export included |
| Enum, enum member | Its value |

## Certified imports

An imported function of the program is read at its declaration's ordinary
signature, which states the effect its [statement](SOURCE-ELABORATION.md#stated-effects)
states and none without one. A **certified import** is read at an
effect-qualified signature that the same run certifies from the imported
declaration's code, its claim within its statement. This is the checked evidence
[inferred call effects](SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification)
require; the import's TypeScript declaration supplies none.

**Eligibility.** A read may be qualified only where its binding's value is
stable: a named import of an exported function declaration that no code of
its module reassigns, or a default import of an `export default function`,
which is the named import of `default`
([default imports](SOURCE-ELABORATION.md#default-imports)). Its terminal
declaration identity is the one TypeScript resolves the import to, through
re-exports; a re-exporting module's own execution is part of the runtime
module graph below. Any other import is read at its ordinary signature. Lean refuses a unit whose module's document writes
its binding, and the parser lists no module whose code it leaves unlowered
writes one.

**Two graphs.** The **qualified-dependency graph** has an edge from a unit to
each unit it reads at a qualified signature; it is acyclic. The pipeline
proposes a module after the modules it imports from, so a read that would
close a cycle is read at its ordinary signature, and Lean refuses a cycle
among the modules the planned reads name. The **runtime
module graph** is the modules' import relation as the host evaluates it,
ordinary imports and re-exports included; it may have cycles. Qualification
reasons about the first; the second bears on initialisation and binding,
below.

**The documents.** The parser lowers its documents before any claim exists,
so it lowers every module the qualified-dependency graph may need: every
program module the checked file imports a function from, transitively,
each under the checked file's TypeScript program and options and the run's
[tag selection](HOST-FAMILIES.md#the-runs-selection), so that both readings
of a declaration resolve alike. The fragment's required `modules`
array ([the wire](FRAGMENT-FORMAT.md)) lists each once: its **artifact**,
the module identity its declarations carry (`location`) and the `sha256` of
the exact bytes lowered, then its declarations, top-level code and
functions, as a file's own fragment holds them, its own identity written as
`location`. A function of such a module is a **unit**, named by its origin:
the module's artifact, the declaration's span and its name. Origins come
from the parser's resolution and snapshot, never from a claim of the
producer's. The claims document's required `modules` array holds one claims
document per fragment module, over that module's own type table, and the
importer's claims list the imports it reads qualified (`qualified`), each by
its declaration identity. A module run certifies its module's units for
the importer's check; the census certifies each module's units in that
module's own check.

**Failure boundary.** A module function the parser cannot lower is absent
from its module, with the parser's reason, and its module's other functions
stay, but for those reading an absent function, which are absent with it,
the read as their reason, until no function left reads one. A module whose
declarations or top-level code cannot be lowered, or whose top-level code
reads an absent function, is absent: its imports are read at their ordinary
signatures. An absent function's code is checked by no run: an import of
it is safe under the assumption that an imported value meets its
declaration ([imported values](#imported-ambient-and-global-values), the
[trust surface](DESIGN.md#trust-surface)). An import read
at its ordinary signature is refused where that signature is not
representable in full.

**What a unit's certification covers.** A unit is checked in its module's
run, as a run of that file alone checks it but for the run's tag selection,
over that module's own type table: its module's initialisation (the existing initialisation unit and
order, `Extraction.lean`), its own code at its claimed signature, the
module's functions its code reads, and, recursively, every unit it reads
at a qualified signature. So the certified set is the closure of the units
the claims read qualified under the module functions they read, together with
the module's initialisation, and, recursively, the same of every unit a
module run's own claims read qualified; the module's other functions are not
checked. Every other fact of its environment is an
explicit assumption, the
[import assumption](SOURCE-CONTRACTS.md#imported-ambient-and-global-values)
its module's own run also makes. An initialiser that is not checked never
supplies a qualified signature. Lean computes the closure and restricts
each module's document and claims to it itself, whatever the producer
chose.

**Binding.** Lean reads an import at a qualified signature only where the
importer's claims list it qualified and the documents hold a unit of its
origin: the import's declaration identity names a module whose artifact
the fragment lists, and a function of it whose name is the declaration's
and whose name lies in the declaration's span. The unit is eligible: one
declaration, binders of its own none, no rest parameter, no receiver, no
guard and no promise. The two readings of
its ordinary signature, the importer's declaration document's and the
module's own annotation, are compared structurally, a mismatch refused:
the parameter and result terms, and recursively every declaration either
reaches, under the identity mapping of declaration identities: its equation,
parameters and heritage, and the written applications listed in it, in the
unit's own declaration alike, with their scopes, arguments and bounds. A
declaration lowering reads by identity rather than through a reference
(`ImplicitDependency`, the one list lowering selects them through) is
reached as a reference's target is where a term reached needs it:
`ArrayProto` for an array or tuple term, `%Stable%` and native `Promise` for
a resolution-qualified binder. Symbol keys compare by the identity of their
symbol's declaration rather than a document's index, and a visited set
closes recursive definitions. Every field of a term takes part, array presence and host
classification among them. Each of the following is refused, named by the
unit's origin: a qualified read naming no unit, a unit of another origin, a
unit not eligible, a structural mismatch, a module's claims about other bytes
than its document's, and a module run whose check fails. The
importer's evidence and the units' are checked by one `--check-units` run,
whose module-run units are the module documents, so the evidence that
certifies the effect is evidence about that declaration's code, not about a
name.

**The ordinary signature is kept.** The unit is checked at its annotation's
signature with the effect added, its annotation obligations retained, as
[elaboration](SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification) states
for a module function. The importer reads the import as the unit's module
reads it (`moduleArrow` of the unit's annotation, with the footprint and
on-throw flag its claim states), which the structural comparison makes its
own declaration's signature with that effect. Its code is then known to
discard further actuals, so it may be passed where a signature binding more
parameters is expected.

**Inference.** OCaml proposes each module's effects as it proposes a
file's own (the greatest fixpoint over that module), then the importer's
claims at them. No effect
follows from a comment, a name or a module's role. The pipeline lists
qualified each eligible read whose unit has claims. Where the search over the
whole document refuses a read or a module run, its footprint refuted or its
initialisation unchecked, the pipeline withdraws the first read or module
run it refuses, proposes the importer again, and the import is read at its
ordinary signature. The search of the importer's units and of every module
run is one search (`--produce-units`), a refusal of each unit its own.
Before proposing the importer at its
reads, the pipeline plans them (`--plan-imports` over the reads and the
modules' claims) and withdraws every read the plan refuses in one round:
a refused plan states, after its first refusal, each other read of the
importer, and of each module an admitted read names, whose two readings it
refuses (`planRefusals`), a line each. Each read is checked on its own, at
that round's documents and claims, as `planImports` checks it. The plan reads of the importer's claims only the list of its
qualified reads, so its answer is the search's at those reads. The final check is one
`--check-units` run over the whole document, a verdict per unit. Dense `map` needs a callback
footprint that keeps dense prefixes
([FOOTPRINTS](FOOTPRINTS.md#the-stable-set-for-density)).

**What the theorem states.** `SourceClaimJson.checkUnitJson_safe` states, for
each unit the check accepts, over its document's frozen store: for a module
run, safety and its footprint for every certified unit of that document's
certified set; for a unit of the importer, safety and its footprint for its
certified requests; each under `EnvOk` of its own inputs, the qualified
import among the importer's, and under `WorldAdm` and `HeapOk`.
It does not construct a module's environment, prove that initialisation
succeeds, or prove that the value an import binds at run time meets the
qualified signature: those are the linking obligation's.

**The linking obligation.** The conclusions combine into safety of the
linked program under a runtime invariant: at every qualified read, the
binding holds the certified unit's closure, whose captures meet its input
contracts in the current heap and world, and the module's initialisation and
all execution after it preserve that. The eligibility rule makes the first
half a property of the parser's resolution and of the host's module loader
(an exported declaration never reassigned holds its closure once its module
is evaluated); the second is the obligation of
[module composition](../WORK.md#module-composition) for units certified
against each other's signatures, on which the units of one module rely too.
A dependency whose initialisation throws stops the importer's evaluation:
certifying a body proves no initialisation succeeds. The invariant is a
review obligation, listed with the import assumption and in the
[parser, extraction, declared-types and host bridges](TRUST-REDUCTION.md#the-bridges).

**A catch.** A certified import's footprint holds on normal return, and on
a throw where its effect states `onThrow`
([exceptional footprints](SOURCE-ELABORATION.md#exceptional-footprints)).

## One equation per declaration

A declaration is one equation, and a type a unit names is a finite term over
the equations ([RECURSIVE-EQUATIONS §5](RECURSIVE-EQUATIONS.md#5-from-source)).
Lowering (`EquationLowering.source`) makes a head per declaration whose
equation is an object type or has bases, per generic method of such a head,
per source type literal and per generic unit, never per instance: a
generic application $`D\langle\vec U\rangle`$ is the label $`D(\vec U)`$,
and its row is $`D`$'s template instantiated at $`\vec U`$ when a check reads
it, which leaves every application inside unexpanded. So a recursive family
of applications, `Pair<[T, U]>` or `Promise`'s `catch`, is finitely many
heads, and there is no budget, colour or depth: an alias reached again before
a constructor is refused as unguarded, and everything else terminates
because heads are keyed by source occurrence.

An interface declared more than once, in the checked file or in a module it
imports (`interface-merge-value-import`), as TypeScript merges it, is one
declaration: its body holds every declaration's members, each at
its own type. Its type parameters are positional: each declaration binds a
prefix of the longest list under the same names (TypeScript requires the
others to have defaults), and its members are read with the parameters it
binds, so a name it does not bind is what that name denotes there. The first
declaration binding the longest list is its identity. A position's bound and
default are those a declaration states there, read in its scope (TypeScript
requires declarations stating one to agree; `interface-merge-parameter-defaults`).
The declarations name
no member twice and state at most one index signature of each key kind, or
the interface is refused:

```math
\frac{\mathtt{interface}\ I\langle X_1\ldots X_{k_i}\rangle\ \{\varphi_i;\ \vec\sigma_i\}\ \ (1\le i\le n)\quad
      k=\max_i k_i\quad
      \mathrm{names}(\varphi_i)\ \text{pairwise disjoint}}
     {⟦I\langle X_1\ldots X_k\rangle⟧=⟦\{\varphi_1\cdots\varphi_n;\ \vec\sigma_1\cdots\vec\sigma_n\}⟧}\ \textsf{interface-merge}
```

with $`\varphi_i`$ a declaration's fields, methods and index signatures and
$`\vec\sigma_i`$ its call signatures, each read in the scope of
$`X_1\ldots X_{k_i}`$ (`interface-merge-prefix-parameters`).

The store a unit is extracted over is the lowering's heads, and extraction
grows it ([Equations/Store.lean](../lean/Verification/Source/Equations/Store.lean)): a union of clauses, a scheme over a closure's
binders and a bounded binder's meet each become a head whose template lifts
the owned parameters it names to arguments. Every unit of a file grows the
one store in turn, and once extraction is done the heads are validated
(`Equations.ofRaw`) and every request is checked over their
`Equations.graph` (`SourceClaimJson.freezePlans`).

### Block-scoped type declarations

A `type` or `interface` declared in a block (a function body, a block
statement, a loop's body, a `switch`'s case block, shared by its clauses)
is erased by TypeScript's emit: the statement has no execution, and it
binds a type name over its whole block, before and after it, as a
module-level declaration binds one over the module. Its equation is read by
the readers every declaration's is, lifted over the type parameters it
closes over: $`\vec X`$, the enclosing type parameters its declaration
names (its equation, its parameters' bounds and defaults), directly or
through a block type it names, each one TypeScript resolves at
the declaration's block (a parameter a nearer declaration of the same
spelling hides there is not one), outermost first, then its own
$`\vec Y`$. The captured arguments are equation arguments: the unit whose
binders they are still owns them ([generic methods](#generic-methods)).

```math
\frac{\mathtt{type}\ L\langle\vec Y\rangle=\tau\ \text{declared in a block}\quad
      \vec X\ \text{the enclosing type parameters}\ \tau\ \text{names, resolved at that block}}
     {L(\vec X,\vec Y)=⟦\tau⟧}\ \textsf{block-type}
\qquad
\frac{\Gamma\vdash_R S}{\Gamma\vdash_R\ \mathtt{type}\ L\langle\vec Y\rangle=\tau;\ S}\ \textsf{type-statement}
```

and an interface the same way, its merged declarations in one block
together. A reference is read at the declaration TypeScript binds it to
(`blockTypes` in `declaration-graph.mts`), so a block declaration shadows
a module declaration, a library type or a type parameter of the same
spelling inside its block and nowhere else, and a type parameter of a
nearer generic function shadows it in turn. This resolution also applies to
computed aliases, before standard `Awaited`, associated-result and
qualification rules. Every collected equation is available to rest-type
expansion by declaration identity, including equations reached through
another block alias. Its captured arguments are the
binders themselves, each required to be the binder TypeScript resolves
that spelling to at the reference:

```math
\frac{L(\vec X,\vec Y)\ \text{a block type}\quad
      \text{each}\ X_i\ \text{resolves to itself at the reference}}
     {⟦L\langle\vec\sigma\rangle⟧=L(\vec X,⟦\vec\sigma⟧)}\ \textsf{block-reference}
```

A reference where a nearer binder hides an $`X_i`$ is refused, since no
argument there denotes $`X_i`$ (`block-type-hidden-binder-refused`), as is
a block type naming another whose captured binder a nearer declaration
hides at its own block; so is a contextual type TypeScript states at a
block type closing over a binder, whose alias arguments state only
$`\vec\sigma`$. An application of a declaration completes its arguments
through `completeArguments`, which takes the captured arguments from its
reader's scope (a binder at a use; in an equation or a default, the
instantiation's argument at the declaration's own captured position for
the same binder, by identity; the written application's binder in the
bounds sweep) or refuses the application. The evaluation of a computed
alias (`computed-types.mts`) completes its own arguments as written, each
in its scope, which a conditional's distribution over a union member needs,
and takes the captured ones through the same identity check at the use
(`capturedAt`). A reference whose captured binder is hidden is refused
before any evaluation, including a default naming a computed alias and a
larger computed form naming a block type: each named block type is checked
at the captured binder identities, transitively through the block types it
names, with cycles visited once. This check precedes consuming a computed
result, including mapped keys and mapped modifiers
(`block-type-computed-hidden-binder-refused`,
`block-type-computed-default-hidden-binder-refused`,
`block-type-computed-form-hidden-binder-refused`,
`block-type-computed-indirect-hidden-binder-refused`,
`block-type-computed-mapped-hidden-binder-refused`). A
block declaration whose equation the readers cannot represent is refused at
its use, as a module declaration is. One TypeScript computes
from its parameters is evaluated at each application
(`computed-types.mts`), its captured parameters at the binders there; a
computed form naming the parameters of one closing over a binder, which
TypeScript evaluates only at an instance, and an associated-result alias
declared in a block are refused.

### Generic methods

A declaration's generic method `m<U⃗>` is a head `D.m` of its own, taking
`D`'s parameters and binding `U⃗`: a scheme whose signatures take the
declaration as receiver, lowered as a host-relative member with quantified
signatures whose receivers admit every value (the member bound to its host
is what meets the scheme, [records](POSITIVE-TYPES.md#records)). Its binders
are owned by its application, $`\mathsf{bound}(D.m,\vec A,j)`$, so two
applications of `D` at different arguments bind different labels, and two
members of different declarations do too. Such members relate by quantified
coverage up to renaming the target's binders to the source's
([RECURSIVE-EQUATIONS §4.1](RECURSIVE-EQUATIONS.md#41-quantified-signatures),
`SchemeRenames`): as many binders, of the same kinds, each target bound
within the source's, and the source's signatures covering the target's
renamed. Members binding different numbers of binders are not related. A generic
member of a library prototype (`ArrayProto`'s `forEach`, whose receiver is an
array of its element binder) stays a readonly view of its scheme. A rest
typed by one of the method's binders makes it a pack parameter, bounded by
its element pack. A value binder $`p`$ with a declared bound $`B_p`$
establishes a parameter's bound $`B`$ through that one:

```math
\frac{p\ \text{a value binder}\quad G\vdash_c B_p\le B}
     {p\ \text{establishes}\ B}\ \textsf{binder-bound}
```

A binder the source spells by its name, in an annotation or a claim, is its
name's placeholder until the unit or closure that binds it is extracted: a
generic unit's binders are the owned parameters of its head
(`EquationLowering.enterUnit`), a generic closure's those of the scheme its
claim states (`Scheme.schemeRowOf`), and each annotation and claim inside
reads the name as that parameter (`EquationStore.rebind`). A call of a
generic closure reads the name, wherever its scheme's signature spells it,
as the call's type argument (`Scheme.closureRows`).

### Generic function and constructor types

A generic function type `<p₁ extends β₁, …>(x⃗: A⃗) => R`, in a declaration
or in an annotation, is the scheme row
$`S=(\vec p;\ \top,\vec A\to R;\ \vec\beta)`$ whose signature takes any
receiver, a binder without a bound bounded by the source values
([scheme rows](POSITIVE-TYPES.md#parameter-and-scheme-rows)). A value of it
meets its signature at every instance within the bounds, in every world,
at every level:

```math
v\in⟦S⟧_n(W)\iff\mathsf{Invocable}(v)\land\forall j\le n.\ \forall\vec X\in\mathcal D_S.\
  \mathsf{Bounded}_j(\vec X)\Rightarrow v\in_j\mathsf{Calls}\bigl((\top,\vec A\to R)[\vec p\mapsto\vec X]\bigr).
```

Three sources give a value of such a type:

```math
\frac{f\ \text{a generic closure}\ \langle\vec p\le\vec\beta\rangle(\vec x:\vec A)\Rightarrow e\quad
      \vec p,\ \vec x:\vec A\vdash e:R}
     {f:(\vec p;\ \top,\vec A\to R;\ \vec\beta)}\ \textsf{closure}
\qquad
\frac{g\ \text{a generic module value}\quad \mathsf{sig}(g)=\forall\vec p\le\vec\beta.\ \vec A\to R\quad g\ \text{read, not called}}
     {g:(\vec p;\ \top,\vec A\to R;\ \vec\beta)}\ \textsf{module-scheme}
```

and the scheme an annotation or a declaration states. A closure without a
result annotation is claimed at its body's type, widened as TypeScript
widens an inferred result's fresh literals (a body returning only calls'
and fields' values keeps the literals their declared types state, and a
generic call's binder whose every candidate type comes from a callback's
result keeps them too),
the object literals it returns with their exact
keys ([literals a spread copies](SOURCE-ELABORATION.md#literals-a-spread-copies)),
which the closure's code is then checked at
([generic closures](CALLABLES.md#overloads-polymorphism-and-binding)). In
**module-scheme**, $`g`$ is a generic module function, certified at every
assignment of its binders (`Parametricity.accept_reassign`), or an import,
assumed at its declaration: either way it meets $`\vec A\to R`$ at each
instance within $`\vec\beta`$, which is membership in the scheme row. Its slot
reads each binder as its meet with its bound, as a closure's scheme does
(`Scheme.moduleScheme`); a binder bounded by another binder, a
resolution-qualified binder and a binder typing a rest are refused there,
since the scheme row states none of them. A generic module value that is
called is read at the instances its calls name (`Scheme.moduleInstances`).

A generic constructor type `new <p⃗ extends β⃗>(x⃗: A⃗) => R` is the construct
scheme $`S=(\vec p;\ \vec A\to R;\ \vec\beta)_{\mathsf{new}}`$: a value of it is a
class value constructing an $`R`$ from $`\vec A`$ at every instance
([scheme rows](POSITIVE-TYPES.md#parameter-and-scheme-rows)). A generic class
read as a value meets its own construct scheme, by **module-scheme** with its
construct signatures: its construct code is checked by the initialization
unit at every assignment of the class's binders. The scheme states the
construct signatures alone; a read of the class's static field reads the class
value at an instance ([classes](#classes)), so a unit reading the class both as
a value and through a static field holds the instances its reads name, which
do not meet the scheme: the slot holds the scheme or the instances, rather
than a scheme carrying the static-field facts.

```math
\frac{C\ \text{a generic class}\quad \mathsf{ctor}(C)=\forall\vec p\le\vec\beta.\ \mathsf{new}\ \vec A\to C\langle\vec p\rangle\quad C\ \text{read, not constructed}}
     {C:(\vec p;\ \vec A\to C\langle\vec p\rangle;\ \vec\beta)_{\mathsf{new}}}\ \textsf{class-scheme}
```

Schemes of one kind relate by quantified coverage up to renaming
([RECURSIVE-EQUATIONS §4.1](RECURSIVE-EQUATIONS.md#41-quantified-signatures));
a call scheme and a construct scheme are never related;
a union of schemes is met by a member of either arm. So `identity<T>` meets
`(<T>(x: T) => T) | (<T>(x: T) => string)` at its first arm, and a function
returning a string at every type argument meets only the second.

**Admitted instantiations.** A call of a scheme-typed value is typed at one
instance $`\vec p\mapsto\vec\theta`$ the claims name, each $`\theta_p`$ a type
of the graph of its binder's kind and within its bound, checked by the
instance rule ([instances](POSITIVE-TYPES.md#instances-of-a-scheme-row),
[claims](SOURCE-CLAIMS.md#quantified-callables-and-their-eliminations)): a
ground type, an enclosing generic unit's binder as its parameter row, or a
scheme type itself, as in `f(identity)` with `f` and `identity` both at
`<T>(x: T) => T`, whose instance is `T := <T>(x: T) => T`. A comparison
instantiates the source scheme's binders at the target's, which it takes
rigidly. This is sound in the step-indexed model for every such instance,
impredicative ones included: the meaning quantifies over every admissible
family $`\vec X\in\mathcal D_S`$, a semantic family closed downward in the
level, not over the types the checker can write, so no instance is defined
by the scheme being defined. The denotation is the guarded fixed point of the
row equations, the body's operands read below the level, and it exists
whatever the families range over (`QInv`, admissibility of
`schemeSemWithArgs`); every type's meaning, a scheme row's included, is such a
family (`mixedMeaning_valid`), so it is an instance. Decidability comes from
the checker comparing the instance a claim names, never searching instances
over schemes. A construct scheme has no instance rule: a value of a generic
constructor type is stored and compared, not constructed
([model limits](SOURCE-FRAGMENT.md#model-limits)).

### Binders met with ground types

An intersection of a value binder with ground types, `V & DepSafe`, is a
meet label ([RECURSIVE-EQUATIONS §2.2](RECURSIVE-EQUATIONS.md#22-meaning)),
whose row is the [meet row](POSITIVE-TYPES.md#parameter-and-scheme-rows)
$`p\sqcap\vec c`$. Lowering an intersection (`meetOf`) distributes it over its
operands' unions, one meet label per choice; on ground operands:

```math
\frac{A_k=[p],\ p\ \text{a value binder}\qquad
      \forall i\ne k.\ A_i\ \text{of clause rows}}
     {⟦A_1\mathbin{\&}\cdots\mathbin{\&}A_n⟧=
      [\,p\sqcap\mathsf{meet}(A_{i\ne k})\,]}\ \textsf{binder-meet}
\qquad
\frac{\forall i.\ A_i\ \text{of clause rows}}
     {⟦A_1\mathbin{\&}\cdots\mathbin{\&}A_n⟧=
      [\,\mathsf{meet}(A_1,\ldots,A_n)\,]}\ \textsf{meet}
```

```math
\frac{\vec p\ \text{the value binders among the}\ A_i\ \text{and the parameters of their meet rows},\ |\vec p|\ge 2\ \text{or a meet row among them}\qquad
      \vec c\ \text{the meet of the other operands' and those rows' clauses, or}\ \top}
     {⟦A_1\mathbin{\&}\cdots\mathbin{\&}A_n⟧=
      [\,p_1\sqcap p_2\cdots\sqcap\vec c\,]}\ \textsf{binders-meet}
```

where $`\mathsf{meet}`$ is the operands' clauses met pairwise and folded from
the right: `meetLists` ([conjunction](POSITIVE-TYPES.md#conjunction-and-normalization)),
except that a record of invariant fields met with a function type is the
callable carrying them (`sourceMeetLists`, [below](#intersections-of-functions-and-records)),
and any other intersection (a scheme, a union holding a binder) is refused
rather than an operand being dropped. A function's own annotation lowers its
intersections so, each binder read as the row the unit
reads it as, its parameter row met with a ground bound or with the binder
bounding it (`binderRows`): `T & U`, `T & "fixed"`, `T & object` and
`A<U> & B<V>` are meet rows or meets of application rows over the binders'
rows. An operand whose row is not yet filled, a declaration being lowered or
a recursive application met inside its own equation
(`TreeNode<T> & TreeLeaf<T>` in `TreeLeaf<T>`'s field), makes the meet a row
of its own that waits for it, a pending row filled once every operand is
(`Equations/Core.lean`); a nullary declaration an intersection names is lowered first, so
the declarations' order does not matter. No lowering ends with a meet left
waiting. A meet row is below each of its parameters, so
it establishes what each does. At an instance $`p_1:=U_1,\ldots,p_k:=U_k`$ it
means $`\mathsf{meetLists}(G(U_1),\ldots,G(U_k),\vec c)`$ (`meetOk`, the meet
folded left to right, or in the reverse order), which is exactly what lowering
the intersection at $`\vec U`$ gives. A producer names a meet it does not compute by
an intersection label in its claims ([`{"meet": ...}`](SOURCE-CLAIMS.md#encoding)),
whose row Lean fills with `meetRow`.

A generic body's bounded binder is interpreted as the intersection of its
parameter row and its declared bound. The bound may contain other parameters
in scope, as in `T extends Ref<U>`, or name one directly, as in `U extends T`.
This retains the parameter's identity and the bound's member contracts
([generic bodies](CALLABLES.md#overloads-polymorphism-and-binding)).

## Implied bounds

A type parameter is constrained by the bound its declaration writes and by the
bounds its signature implies: constraints read off where the parameter occurs
in the signature that binds it. A body implies none. Two forms exist, and they
constrain differently:

| Implied by | Signatures | Constraint |
| --- | --- | --- |
| an occurrence inside a `Promise` or `PromiseLike` argument | imported, ambient and library signatures and their generic methods | the subtype bound $`T\le N`$ |
| `Awaited<T>`, or declared by `T extends Resolvable` | the program's own generic functions | resolution qualification: $`T`$ owns an observation $`O_T`$ and a result $`R_T`$ |
| declared by `T extends Awaitable` | the program's own function declarations | observation qualification: $`T`$ owns an observation $`O_T`$ |

**Promise arguments.** With $`N`$ the stable non-thenable types
([async](#async-functions-and-await)):

```math
\frac{\sigma\ \text{a trusted signature binding}\ T\qquad
      T\ \text{occurs in an argument of the standard}\ \mathsf{Promise}\ \text{or}\ \mathsf{PromiseLike}\ \text{in}\ \sigma}
     {T\le N\ \text{in}\ \sigma}\ \textsf{implied-promised}
```

The occurrence may be nested, `Promise<{ value: T }>` included. A written
bound $`B`$ becomes $`B\mathbin{\&}N`$ (`promisedBinders`, `promisedMethods`).
A trusted signature stating a promise of $`T`$ is truthful only where $`T`$
stays non-thenable, since a fresh resolution of a thenable payload adopts it.
The intrinsics keep the operation-specific contracts they state, and the
program's own signatures imply none of this form: their bodies are checked at
every admitted instantiation.

**`Awaited<T>`.** For the standard library's `Awaited`, recognized by its
declaration and not shadowed by a type parameter of that name:

```math
\frac{\sigma\ \text{a source function's signature binding}\ T\qquad
      \mathsf{Awaited}\langle T\rangle\ \text{occurs in}\ \sigma}
     {T\ \text{resolution-qualified, owning}\ O_T,\ R_T\qquad
      ⟦\mathsf{Awaited}\langle T\rangle⟧=R_T}\ \textsf{implied-resolution}
```

The occurrence may be written through a local type alias the signature names
(`resolutionAliases`). The parser refuses the other uses, each with its own
diagnostic: `Awaited` in a body ("cannot add a qualification to an ordinary
function body"), of anything but a type parameter ("requires the input of a
resolution-qualified parameter"), in a signature with more than one type
parameter ("has exactly one source parameter"), and in an ambient
declaration, which has no body to check ("requires a resolution-qualified
scope"). The fragment lists the two
owned names in the parameter's `resolution` field
([fragment](FRAGMENT-FORMAT.md)), and the request states the triple
$`(T,O_T,R_T)`$ as a resolution descriptor of the scheme
([request protocol](REQUEST-PROTOCOL.md)).

**`T extends Resolvable`.** The qualification `Awaited<T>` implies may be
declared: a function declaration's type parameter bounded by the verifier's
`Resolvable` is resolution-qualified, with no subtype bound:

```math
\frac{\sigma\ \text{a source function declaration's signature binding}\ T\qquad
      T\ \mathtt{extends}\ \mathsf{Resolvable}\ \text{in}\ \sigma}
     {T\ \text{resolution-qualified, owning}\ O_T,\ R_T\qquad T\ \text{unbounded}}\ \textsf{declared-resolution}
```

`Resolvable` is `type Resolvable = unknown` in
[`tools/resolvable.d.ts`](../tools/resolvable.d.ts), which the project of a lone
source lists (`verify-source.mts`), and the parser recognizes the bound by
that declaration, which TypeScript binds the name to, not shadowed by a type
parameter (`qualificationBound` in `fragment-parse.mts`). A program's own alias of that name is an
ordinary bound. `Awaited<T>` in a declared-qualified signature reads
$`R_T`$. The parser refuses the marker on another type parameter ("qualify
a type parameter of a function declaration's signature") and in a signature
with more than one ("has exactly one source parameter").

**`T extends Awaitable`.** A function declaration's type parameter bounded by
the verifier's `Awaitable` is observation-qualified, with no subtype bound:

```math
\frac{\sigma\ \text{a source function declaration's signature binding}\ T\qquad
      T\ \mathtt{extends}\ \mathsf{Awaitable}\ \text{in}\ \sigma}
     {T\ \text{observation-qualified, owning}\ O_T\qquad T\ \text{unbounded}}\ \textsf{declared-observation}
```

`Awaitable` is `type Awaitable = unknown` in the same file, recognized the
same way (`qualificationBound`). Only the marker declares it: a
qualification is implied by the signature alone, and `Awaited<T>` names a
result, so the qualification it implies is `Resolvable`. `Awaited<T>` of an
observation-qualified parameter is refused ("requires a resolvable
parameter"). A body that only awaits $`T`$ needs the observation alone, which
admits instances no result exists for, a native promise of an open record.

We write $`T:\mathsf{Resolvable}`$ for a resolution-qualified $`T`$,
$`T:\mathsf{Awaitable}`$ for an observation-qualified one, and
$`T.\mathsf{Observed}=O_T`$, $`T.\mathsf{Result}=R_T`$.
Neither qualification is a subtype bound: each leaves the values of $`T`$
unconstrained and restricts which assignments of its owned binders are
admitted, $`(T,O_T)`$ to the observations and $`(T,O_T,R_T)`$ to the
descriptors (`ResolutionDescriptors.descriptorDomain`):

```math
\mathsf{Obs}(T,O)\iff\mathsf{Observes}(T,O)\qquad
\mathsf{Desc}(T,O,R)\iff \mathsf{Obs}(T,O)\ \land\ R\le N\ \land\
  \mathsf{Resolves}(T,R)\ \land\ \mathsf{Resolves}(O,R)
```

so every resolvable input is awaitable: $`\mathsf{Desc}(T,O,R)\Rightarrow\mathsf{Obs}(T,O)`$
(`Descriptor` extends `Observation`).

$`\mathsf{Resolves}`$ and $`\mathsf{Observes}`$ are the least relations
closed under the following rules (`ResolutionCapabilities`), with $`P`$ the
native Promise constructor and $`A`$, $`B`$ value families. The stable family
$`N`$ and every native Promise application are contained in the
[source-value universe](SOURCE-MODEL.md#source-value-boundary) $`J`$, checked
from their graph clauses. The rules classify an
input as stable, a native promise or a union of classified inputs:

```math
\frac{A\le N}{\mathsf{Resolves}(A,A)}\ \textsf{stable}\qquad
\frac{\mathsf{Resolves}(A,R)}{\mathsf{Resolves}(P\,A,R)}\ \textsf{native}\qquad
\frac{\mathsf{Resolves}(A,R)\quad\mathsf{Resolves}(B,S)}
     {\mathsf{Resolves}(A\cup B,R\cup S)}\ \textsf{union}
```

```math
\frac{A\le N}{\mathsf{Observes}(A,A)}\ \textsf{stable}\qquad
\frac{A\le J}{\mathsf{Observes}(P\,A,A)}\ \textsf{native}\qquad
\frac{\mathsf{Observes}(A,O)\quad\mathsf{Observes}(B,Q)}
     {\mathsf{Observes}(A\cup B,O\cup Q)}\ \textsf{union}
```

A native promise's input is never stable: $`P\,A\not\le N`$ for every value
family $`A`$, which the verifier proves from the declaration graph: one value
of $`\mathsf{Promise}\langle A\rangle`$ lies outside every clause of $`N`$
(`NativePromiseSeparation.Shape.separate`). Both relations are therefore
exact on stable inputs:

```math
A\le N\ \land\ \mathsf{Resolves}(A,R)\ \Rightarrow\ R=A\qquad
A\le N\ \land\ \mathsf{Observes}(A,O)\ \Rightarrow\ O=A
```

proved by induction on the derivation (`ResolutionCapabilities.Resolves.exact`,
`ResolutionCapabilities.Observes.exact`): a stable leaf is its own result, a
native step contradicts separation, and both arms of a stable union are
stable. An observation of a stable input is that input
(`Observation.exactStable`), and a descriptor with a stable input has it as
its observation and result (`Descriptor.exactStable`): an input of type
`number` is observed and resolves at exactly `number`.

Every input, observation and result in these relations is contained in $`J`$,
proved by induction (`Resolves.source`, `Observes.source`). Hence a qualified
slot $`X`$ equals $`X\cap J`$. Lexical descriptor lookup and instantiation
preserve this equality (`QualifiedGraphs.sourceView_sound`); the associated
slots retain the relations imposed by their owning descriptor.

A written bound within $`N`$ makes the qualified parameter its own
observation and, where it owns one, its own result. The body is certified at
the admitted assignments within the declared bounds, so for a closed bound
$`B`$:

```math
\frac{T\ \text{qualified}\qquad T\le B\qquad B\le N}
     {O_T=T\qquad R_T=T\ \text{where}\ T:\mathsf{Resolvable}}\ \textsf{stable-bound}
```

since every admitted $`T`$ lies within $`N`$ and exactness applies
(`SourceResolution.stableAliases_sound`). The body check reads $`O_T`$ and
$`R_T`$ as the row a body reads $`T`$ at, the meet of $`T`$ and $`B`$, when it
compares two types (`ProgramCertificates.lexicalBodyCheck`), and proof search
proposes such comparisons. `Awaited<T>` and $`T`$ are then interchangeable in
the body of `back<T extends number>(v: Awaited<T>): T`, while a bound admitting
a promise, or no bound, keeps them apart, and a call still checks the bound
(`generic-promise-bounded-result` and its negatives in
`pipeline/cases.mts`).

The body is certified at every admitted assignment
([generic closures](PROGRAM-TYPING.md)), and every call supplies a certificate
classifying its type argument, from which $`O_T`$, and $`R_T`$ where $`T`$
owns it, follow ([claims](SOURCE-CLAIMS.md)). A union certificate's arms
classify the input's parts in any order (`SourceResolution.check`). A
`native` certificate classifies a native promise's payload as well, giving its
result; a `promise` certificate observes a native promise at a payload checked
to lie within $`J`$, and gives no result.

**Resolution operations in the body.** `await` and an async return are the
qualified intrinsics ([async](#async-functions-and-await)), instantiated at
an observation or a descriptor. In the body of a qualified $`T`$, the
certificate `binder` names $`T`$'s own observation or descriptor, for an input
equivalent to $`T`$, or, for a resolution-qualified $`T`$, to its
observation:

```math
\frac{T:\mathsf{Awaitable}}{\mathsf{Obs}(T,O_T)}\ \textsf{binder}
\qquad
\frac{T:\mathsf{Resolvable}}{\mathsf{Desc}(T,O_T,R_T)}\ \textsf{binder}
\qquad
\frac{T:\mathsf{Resolvable}}{\exists O.\ \mathsf{Desc}(O_T,O,R_T)}\ \textsf{forwarded}
```

The second holds since an observation resolves to the result,
$`\mathsf{Resolves}(O_T,R_T)`$, and every resolvable input has a descriptor
with its result (`ResolutionCapabilities.Resolves.describe`). Its
observation is a family no source type names, so the instance is admitted
only for an intrinsic whose type does not read $`X.\mathsf{Observed}`$:
`%AsyncReturn%`, not `%Await%` (`Scheme.moduleInstances`, "unnamed
observation"). Thus `return await v` returns `Promise<Awaited<T>>`, an
observation is neither $`T`$ nor `Awaited<T>`, and a second `await` of an
observation is refused (`generic-promise-resolution` and its negatives in
`pipeline/cases.mts`). An observation-qualified $`T`$ is awaited at $`O_T`$,
while neither $`T`$ nor $`O_T`$ is returned from an async function, which
resolves afresh (`generic-promise-awaitable` and its negatives).

## Explicit type arguments

A method call may state its instance, `o.m<A₁,…,Aₖ>(…)`. The arguments
instantiate the member's binders in order, its own leading; binders past them
(an `ArrayProto` member's element `T`, listed last) are fixed by the receiver
and actuals. Lean reads the member's scheme row $`S`$ from the receiver's
contract (a quantified member's scheme, or a view's), selects an instance map
$`\theta`$ whose images and bounds establish the read's claimed arrows $`M`$
(`selectInstancesUsing`), and requires
each explicit argument to mean what $`\theta`$ gives its binder. With
$`G\vdash S\le_{\mathrm{inst}(\theta)}M`$ for the checked instance rule
([POSITIVE-TYPES](POSITIVE-TYPES.md#instances-of-a-scheme-row)):

```math
\frac{o:O\quad \mathsf{field}_G(O,m)=S=[\forall\vec p.\Sigma]\quad
      G\vdash S\le_{\mathrm{inst}(\theta)}M\quad
      \forall i\le k.\;\theta(p_i)\simeq_G A_i}
     {o.m\langle A_1,\ldots,A_k\rangle(\vec a)\ \text{is called at its stated instance }M}.
```

A plain call or `new` of a generic module value, or a local quantified
closure, states its instance alike (`Scheme.explicitInstance`):

```math
\frac{f\ \text{generic over}\ p_1,\ldots,p_n\quad
      \text{the call's claimed instance}\ \sigma\quad
      k\le n\quad
      \forall i\le k.\;\sigma(p_i)\simeq_G⟦A_i⟧}
     {f\langle A_1,\ldots,A_k\rangle(\vec a)\ \text{is called at its stated instance}\ \sigma},
```

with $`\simeq_G`$ inclusion both ways by certified subtyping. Both rules only
refuse: acceptance rests on the call's typing, so safety does not depend on
them; they make a stated instance honoured. The instance's bounds are checked
as for any call. A declaration's defaults for method binders are not read.

## Classes

A class declares its instance type in the declaration graph, and its value is
a statement of the initialization unit: method closures, the prototype object
`C.[[prototype]]` holding them (allocated once; not allocated when it holds
nothing of its own that `instanceof` tests), its static field initializers and
static blocks in member order, then the class value, construct-only code
holding its static fields; its static methods are bound first, before the
methods. Its own name inside its methods, static ones included, is
`C.[[self]]`
([`class-self`](SOURCE-ELABORATION.md#mutable-bindings-and-module-constants)).

A static field named by a property name is an own enumerable data property of
the class value. JavaScript creates the class value before its static
initializers run, `this` in them being that value, and defines each static
field on it in turn; the model allocates the class value after them, holding
every static field at once. Each initializer binds its value first, `static
C.f`, a binding no source spells, and the class value is allocated holding
them, each at its annotation, or, without one, at the type TypeScript gives
the field (as a term, `contextualTerm`), its initializer's value checked at
it. The two agree wherever no code that can reach the class value runs
during the initializers, which the rules below on static initializers
ensure. A static field names none of the class's binders (TypeScript refuses
one that does), so a generic class value's bag is the same at each instance,
and a read of one off the class value reads it at an instance, each binder at
its bound:

```math
\mathtt{class}\ C\ \{\ \ldots\ \mathtt{static}\ f_1 = e_1\ \ldots\ \mathtt{static}\ f_n = e_n\ \ldots\ \}
\;\equiv\;\ldots;\ \mathsf{const}\ \mathtt{static}\ C.f_1 = e_1;\ \ldots;\ \mathsf{const}\ \mathtt{static}\ C.f_n = e_n;\
\mathsf{const}\ C = \mathsf{make}(\kappa^{\mathsf{new}},\ \kappa_{\mathsf{code}}{=}\mathsf{null},\ \overline{f_i{=}\mathtt{static}\ C.f_i});\ \ldots
```

The class value's type is $`\mathsf{Ctors}(\mathsf{new}(\vec D)\Rightarrow C;\ \overline{f_i{:}T_i})`$
([classes](PROGRAM-TYPING.md#judgments-and-constructor-views)). A read `C.f` of a static
field, where TypeScript binds it to the member (`staticReads`), is the class
value's field read, `C.[[self]]`'s in the class's methods, which run only
once the class value exists, and a call `C.f()` of one is a method call, the
class value its receiver; in a static
initializer of `C`, which runs before the model allocates the class value,
it is the binding $`\mathtt{static}\ C.f`$ of an earlier field, whose value
the field holds, as nothing can reach the class value to write it before.
A static initializer reads its class only so, calls a static method whose
body does not read the class, or constructs it:

```math
\frac{\text{constructing}\ C\ \text{(constructor, instance field initializers) runs no code and mentions no}\ C
      \qquad \text{no static initializer of}\ C\ \text{runs code but}\ \mathtt{new}\ C(\vec a)}
     {\mathtt{new}\ C(\vec a)\ \text{in a static initializer}\;\equiv\;\mathtt{new}\ C.\texttt{[[class]]}(\vec a)}
```

$`C.\texttt{[[class]]}`$ is the class's construct-only code, bound before the
static initializers (as for a class another extends), and the class value is
that code allocated again with the static fields. Construction then reads no
static field and runs no code that could reach the class value: JavaScript
defines the static fields one by one, so a construction reading one may find
it undefined (`invalid-class-static-constructs-early`, which returns
`undefined` for a `number` under Node). A static initializer mentioning `C`
or `this` otherwise, or calling a static method reading the class, would run
code reading the class value, which JavaScript's code reaches with later
static fields undefined and the model has not allocated, and a closure it
creates reading a static field may run after the field changes; both are
refused.

A class value's own properties are its own static fields; a static field its
base class declares the class value reaches through its prototype, the base
class value, which the model's class value does not hold. A copy, an object
pattern's rest and `Object.assign` take own enumerable properties only, so
they agree with the model; a read `C.f` of an inherited static field and
`typeof C` of a class inheriting a static member, whose type would drop it,
are refused, and `Object.assign` from a class value is refused as from any
source whose type bounds no key (it may own `__proto__`). A `for...in` over a
class value visits its base's static fields too, which `%ForIn%`'s strings
admit.

A static method is a binding of its own, `static C.m`, read
where TypeScript binds `C.m` to it, in the class's members too; one keyed by
a symbol (`static [Symbol.hasInstance]`) is also an own property of the class
value, at its annotated signature, which no copy takes, as no copy takes a
symbol key; a private
static field is a binding of its own, bound with the static fields, which
the class's methods cannot hold. A static block runs
where it stands among the static fields, as the closure of its statements
called at once, reading no `this`:

```math
\mathtt{static}\ \{\ \vec s\ \}\;\equiv\;\mathsf{const}\ \textit{b} = (()\Rightarrow\{\ \vec s\ \})()
```

with $`\textit{b}`$ a binding no source spells. An `async` method is a method
whose body reads as an async function's, its returns and `await`s the
[async intrinsics](#async-functions-and-await).

A constructor call may spread tuples of required positions, including readonly
and empty tuples. The callee is evaluated once before the actuals. Each spread
contributes its elements in order; before a later actual executes code, the
spread's elements are saved in a fresh internal store. Constructor parameter
contracts check the expanded argument list. Optional and unbounded tuple
positions require a separate argument-count rule.

**Private names.** A private name `#x` is a key no code outside its class
spells: the declaration reader lists it as a symbol of its own, identified by
the member declaring it ($`\sigma_{C.\#x}`$), as it lists a `unique symbol`
constant, and TypeScript binds each `#x` of the class body to that member. A
private field is an own key of each instance, allocated with the others
(entries $`\sigma_{C.\#x}\mapsto e`$ of $`\varphi_0`$); a private method is held
by the prototype under its key, as a method under its name; a static one is
a static binding `static C.#x`. So `o.#x`, `o.#x = e` and `o.#m(ā)` are the
named read, write and method call at $`\sigma_{C.\#x}`$, and a copy
(`{...o}`) takes no private slot, in JavaScript as in the model. JavaScript
throws where `o` holds no slot of its own; the model reads `o.#x` along the
prototype chain as any key, where only an object inheriting from an instance
differs, and there JavaScript throws, which safety admits.

The instance type states each member as what it is at run time: a field
`f: T`, `f!: T` or `readonly f: T` a required field or view, `f?: T` the
optional field `f?: T | undefined`, a parameter property `p: T` a field and
`p?: T` the optional field `p?: T | undefined`. An optional member is
TypeScript's `T | undefined` there, not the exact `f?: T` (absent or a `T`)
the pipeline reads elsewhere: a class field is defined on every instance, at
`undefined` where nothing assigns it. With $`\varphi_0`$ the entries, in member order, of
the prototype key ($`\texttt{[[proto]]} \mapsto C.\texttt{[[prototype]]}`$,
for a class with methods), the initialized fields ($`f\mapsto e_f`$) and the
parameter properties ($`p\mapsto p`$), $`U`$ the fields without an initializer
and $`T_f`$ each field's annotation, `constructor(x̄) { s̄ }` is
$`\mathsf{class}(\vec x).\,\mathcal{C}(\vec s,\varphi_0,\varnothing)`$ where

```math
\begin{aligned}
\mathcal{C}(\varepsilon,\varphi,A) &= \mathsf{alloc}(\varphi,\ \overline{f\mapsto\mathsf{undefined}}^{\,f\in U\setminus A})\\
\mathcal{C}(\texttt{this.}f\texttt{ = }e;\ \vec s,\varphi,A) &= \mathcal{C}(\vec s,\ \varphi,f\mapsto e,\ A\cup\{f\})
  && f\in U\setminus A\\
\mathcal{C}(\texttt{if (}c\texttt{) }\{\vec t\}\texttt{ else }\{\vec u\},\varphi,A) &=
  \beta(\varphi)\,;\ \mathsf{if}\ c\ \mathsf{then}\ \mathcal{C}(\vec t,\varphi',A)\ \mathsf{else}\ \mathcal{C}(\vec u,\varphi',A)
  && \text{last, assigns a field}\\
\mathcal{C}(s;\ \vec s,\varphi,A) &= \beta(\varphi)\,;\ s\,;\ \mathcal{C}(\vec s,\varphi',A)
  && \text{otherwise}
\end{aligned}
```

and `this` occurs in no $`e`$, $`c`$ or $`s`$. $`\beta(\varphi)`$ binds each entry
$`f\mapsto e`$ that is not a literal or already bound as `const this.f: T_f =
e`, in order, a name no source binding spells, and $`\varphi'`$ reads `this.f`
there, so every value is evaluated where JavaScript evaluates it. The
allocation is checked like any other: a field without an initializer holds
`undefined` until assigned, so `f!: T` holds exactly when the constructor
assigns `f` on every path, and `f?: string` left unassigned holds its
`undefined`. A
derived class's constructor is the [derived form](SOURCE-ELABORATION.md#derived-classes) over
this one; an override must be sound, since the derived class's declared type
is its own members and its base's.

A generic class's constructor uses its declaring unit's parameter rows, one per
spelling, so a generic class may extend a generic base exactly at the base's
own binders, which it declares too: `class D<T> extends B<T>`. The base's
construction uses the derived constructor's parameter rows, and the derived
form is the non-generic one. Its instance type
$`D\langle T\rangle`$ is its application row, as a class with methods is,
holding its own members met with those of $`B\langle T\rangle`$'s row. A base at
other arguments (`extends B<number>`) is refused: its construction would have
to be instantiated there.

An instance method without its own type parameters quantifies the class binders
in its closure, retaining each class parameter's bound.
For example, `Cell<T>.put(value: T)` has the prototype contract
`put: <A>(this: Cell<A>, value: A) => void`. When all methods use these
contracts, the shared prototype's storage contract is closed; each receiver
uses a checked instance of its method's contract. Bounds remain on the
quantified signature, and a bounded binder's occurrences denote its
intersection with its bound. The method body is checked
under its own binders, including its receiver, parameters and result.

Methods with their own type parameters use unit-scoped class binders.
Exporting such a prototype to an unrelated unit can leave an unbound class
parameter and is refused; that export requires partial method instantiation.
A method scheme whose class bounds depend on its own quantified parameters
is refused by the generic-contract boundary.

## Library types

Write $`⟦\tau⟧`$ for the source term the declaration reader
gives type syntax $`\tau`$ (`typeTerm`), and $`\mathit{lib}(N)`$ when every
declaration TypeScript binds $`N`$ to is in a standard library file, one
the compiler's own library resolution gives the program
(`isSourceFileDefaultLibrary`), whatever else is named like one:

```math
\frac{\mathit{lib}(\mathtt{Array})}
     {⟦\mathtt{Array}\langle T\rangle⟧=⟦T[\,]⟧}
\qquad
\frac{\mathit{lib}(\mathtt{ReadonlyArray})}
     {⟦\mathtt{ReadonlyArray}\langle T\rangle⟧=⟦\mathtt{readonly}\;T[\,]⟧}
\qquad
\frac{\mathit{lib}(\mathtt{Function})}{⟦\mathtt{Function}⟧=\mathsf{callable}}
```

with $`\mathsf{callable}`$ the union of `arrs [] []` and `ctors [] []`
([functions and classes](POSITIVE-TYPES.md#functions-and-classes)); `object`
is `refs [] [] []` with $`\mathsf{callable}`$, and `{}` adds every primitive but
`null` and `undefined`. A mapped type whose value does not name its key is
expanded where its key is known, with $`\mathsf{key}(\texttt{"}s\texttt{"})=s`$,
$`\mathsf{key}(n)=\mathsf{ToString}(n)`$ and $`m`$ its modifiers:

```math
\frac{P\notin\mathrm{fv}(V)\quad⟦K⟧=\lambda_1\mid\cdots\mid\lambda_n\ \text{literals}\quad(n\ge0)}
     {⟦\{[P\ \mathtt{in}\ K]^m\colon V\}⟧=\{\mathsf{key}(\lambda_1)^m\colon⟦V⟧;\ \ldots;\ \mathsf{key}(\lambda_n)^m\colon⟦V⟧\}}
\qquad
\frac{P\notin\mathrm{fv}(V)\quad\mathtt{string}\in⟦K⟧\subseteq\mathtt{string}\cup\mathtt{number}\cup\text{literals}\quad\mathtt{?}\notin m}
     {⟦\{[P\ \mathtt{in}\ K]^m\colon V\}⟧=\{[k\colon\mathtt{string}]^m\colon⟦V⟧\}}
```

`number` without `string` is a number index and `symbol` a symbol index
beside the remaining literals' fields; an optional one, a type parameter or
any other key is refused. A mapped type over `keyof X` copies each member's
modifiers from `X` where it writes none of its own; with $`m_k`$ the modifiers
of `X`'s member $`k`$ that TypeScript resolves, overridden by those the
mapped type writes:

```math
\frac{P\notin\mathrm{fv}(V)\quad ⟦\mathtt{keyof}\ X⟧=\lambda_1\mid\cdots\mid\lambda_n\ \text{literals}}
     {⟦\{[P\ \mathtt{in}\ \mathtt{keyof}\ X]^m\colon V\}⟧=\{\mathsf{key}(\lambda_1)^{m\,\triangleleft\,m_{\lambda_1}}\colon⟦V⟧;\ \ldots;\ \mathsf{key}(\lambda_n)^{m\,\triangleleft\,m_{\lambda_n}}\colon⟦V⟧\}}
```

where $`m\triangleleft m_k`$ takes each modifier $`m`$ writes and $`m_k`$'s
otherwise (`mapped-keyof-modifiers`, `invalid-mapped-keyof-readonly`). Over
`keyof` an indexed type, or a type TypeScript resolves to no record, it is
refused. The keys are the union TypeScript computes for $`K`$
([computed types](#computed-types)). A library alias whose equation is a
mapped type is that type at the reference's arguments:

```math
\frac{\mathit{lib}(L)\quad L\langle\vec X\rangle=\{[P\ \mathtt{in}\ K]^m\colon V\}}
     {⟦L\langle\vec A\rangle⟧=
      ⟦\{[P\ \mathtt{in}\ K[\vec A/\vec X]]^m\colon V[\vec A/\vec X]\}⟧}
```

so `Record<"a" | "b", V>` has both fields required and `Record<string, V>` is
the writable string index.

A mapped type whose value is $`X[P]`$, at a record $`X`$ the reader holds as
one (an object type with no call signature, prototype or method), is $`X`$'s
members at the modifiers the mapped type writes: `Readonly`, `Partial`,
`Required` and `Pick`. With $`⟦X⟧`$ the fields $`k_i^{m_i}\colon T_i`$ and the
indexes $`\iota_j^{r_j}\colon U_j`$, and $`m`$ the mapped type's modifiers:

```math
\frac{P\notin\mathrm{fv}(X)\quad⟦X⟧=\{k_1^{m_1}\colon T_1;\ \ldots;\ k_n^{m_n}\colon T_n;\ \iota_1^{r_1}\colon U_1;\ \ldots\}\quad(\mathtt{?}\notin m\ \text{or no index})}
     {⟦\{[P\ \mathtt{in}\ \mathtt{keyof}\ X]^m\colon X[P]\}⟧=\{k_1^{m\,\triangleleft\,m_1}\colon T_1;\ \ldots;\ \iota_1^{m\,\triangleleft\,r_1}\colon U_1;\ \ldots\}}\ \textsf{mapped-identity}
```

```math
\frac{K\ \text{a parameter bounded by}\ \mathtt{keyof}\ X\quad ⟦K⟧=\lambda_1\mid\cdots\mid\lambda_j\ \text{literals}\ (j\ge1)\quad \mathsf{key}(\lambda_l)=k_{i_l}}
     {⟦\{[P\ \mathtt{in}\ K]^m\colon X[P]\}⟧=\{k_{i_1}^{m\,\triangleleft\,m_{i_1}}\colon T_{i_1};\ \ldots;\ k_{i_j}^{m\,\triangleleft\,m_{i_j}}\colon T_{i_j}\}}\ \textsf{mapped-pick}
```

At no key, and over a record with no member, the type is `{}`, every
value but `null` and `undefined` (`mapped-pick-no-key`, `mapped-named-empty`,
`invalid-mapped-named-empty-object`). Where $`m`$ writes `-?`, an optional
field's type $`T`$ becomes $`\mathsf{req}(T)`$, which the project's
`exactOptionalPropertyTypes` decides, as TypeScript's checker reads it under
`strictNullChecks`. With the option $`\mathsf{req}(T)=T`$
(`mapped-required-exact-optional`, `invalid-mapped-required-exact-optional`).
Without it $`\mathsf{req}(T)`$ is $`T`$ with `undefined` taken away: each
`undefined` and `void` of its union dropped, `never` where none is left; a
reference to a record (an interface, an alias of a record literal) kept; a
reference to any other alias, one of a named type included, replaced by its
meaning with `undefined` taken away, followed through each alias to the
types it names, and kept where that meaning holds none
(`mapped-required-undefined`, `invalid-mapped-required-undefined`,
`invalid-mapped-required-alias-undefined`,
`mapped-required-alias-undefined`):

```math
\frac{T=T_1\mid\cdots\mid T_n\quad \text{no}\ T_i\ \text{a type parameter, an intersection or}\ \mathtt{unknown}\quad \{i_1,\ldots,i_k\}=\{i\mid T_i\notin\{\mathtt{undefined},\mathtt{void}\}\}}
     {\mathsf{req}(T)=\mathsf{req}(T_{i_1})\mid\cdots\mid\mathsf{req}(T_{i_k})}\ \textsf{required-strip}
```

with $`\mathsf{req}(A)=\mathsf{req}(E)`$ for an alias $`A`$ of equation
$`E`$ holding `undefined`, $`\mathsf{req}(R)=R`$ for any other part, and the
empty union `never`. A part that is a type parameter, an intersection or
`unknown` has no term for its instance without `undefined`, and the field is
refused (`mapped-required-binder-undefined-refused`); so is every field whose
type may hold `undefined` where the scope reading the mapped type states no
option (a mapped type written outside the standard library, whose
`Required` the reader reads at the project's option). The
cases are `mapped-identity`, `invalid-mapped-readonly-write`,
`invalid-mapped-pick-readonly`, `invalid-mapped-readonly-index-write`,
`invalid-mapped-partial-alias` and
`blocker-readonly-record`. In a library alias $`X`$ is its parameter at the
reference's arguments, so
`Readonly<Record<string, V>>` is the readonly string index. A union, an
array, or a type with call signatures as $`X`$ is refused, as is a written
key union in place of a bounded parameter, over which TypeScript copies no
modifiers (`mapped-literal-keys-value-refused`).

At a named type $`N`$, an interface or an alias applied at arguments
$`\vec A`$, both rules read $`N`$'s outer record shape
$`\mathsf{shape}(N)`$: its definition's equation at $`\vec A`$, an alias
followed to the type it names, with the members of every base:

```math
\frac{D\langle\vec X\rangle=E\ \text{an alias}\quad \mathsf{shape}(E[\vec A/\vec X])=R}
     {\mathsf{shape}(D\langle\vec A\rangle)=R}\ \textsf{shape-alias}
\qquad
\frac{D\langle\vec X\rangle=R_0\ \mathtt{extends}\ B_1,\ldots,B_n\quad \mathsf{shape}(B_i[\vec A/\vec X])=R_i\quad R=R_0[\vec A/\vec X]\oplus R_1\oplus\cdots\oplus R_n}
     {\mathsf{shape}(D\langle\vec A\rangle)=R}\ \textsf{shape-interface}
```

```math
\frac{N\ \text{named}\quad \mathsf{shape}(N)=R\quad ⟦\{[P\ \mathtt{in}\ \mathtt{keyof}\ R]^m\colon R[P]\}⟧=S}
     {⟦\{[P\ \mathtt{in}\ \mathtt{keyof}\ N]^m\colon N[P]\}⟧=S}\ \textsf{mapped-named}
\qquad
\frac{N\ \text{named}\quad \mathsf{shape}(N)=R\quad ⟦\{[P\ \mathtt{in}\ K]^m\colon R[P]\}⟧=S}
     {⟦\{[P\ \mathtt{in}\ K]^m\colon N[P]\}⟧=S}\ \textsf{mapped-named-pick}
```

$`D\langle\vec X\rangle=E`$ is the complete definition, the parts of a
merged interface together. $`\mathsf{shape}(R)=R`$ for a record written as
one; a class, a host type, a library interface read through its overlay, a
union, an array, a tuple, an intersection, and a record with call or
construct signatures, a prototype or a method (whose receiver is the
declaration, of which the mapped field is no member) have no shape.
$`R\oplus R'`$ is $`R`$'s members and indexes with those of $`R'`$ whose key
$`R`$ lacks; it is defined where every member and index both declare is the
same, type and modifiers. Each member keeps the modifiers it is declared
with, inherited ones included, and its type as declared: the shape is one
unfolding, so a field naming $`N`$ keeps that reference. A shape reaching
itself through its equations and bases has none, nor has one a mapped type
inside its own definition needs. The cases are `mapped-identity-named`,
`mapped-named-bases`, `mapped-named-generic`, `mapped-named-default`,
`mapped-named-pick`, `mapped-named-hook-value-import` and
`invalid-mapped-named-readonly-write`, and `-?` over a named type is read as
over a record written in place (`mapped-named-required-undefined`); the
refusals are `mapped-named-conflict-refused`,
`mapped-named-call-refused`, `mapped-named-call-refused-value-import`,
`mapped-named-method-refused`, `mapped-named-cycle-refused` and
`mapped-named-class-refused`. The front end reads $`\mathsf{shape}`$ from
the declaration document once it is complete (`named-record.mts`); a mapped
type the declaration graph reads before then is expanded when its
collection ends, and a document holding one unexpanded is refused.

An interface's `extends` clauses are the meet of
its own clauses with each base's, its own members first (`inheritRows`,
[conjunction](POSITIVE-TYPES.md#conjunction-and-normalization)); a source
intersection has the same meaning (`meetRow`).

An annotation's intersection of records is the one meet, with $`\varphi_i`$
the invariant and $`\psi_i`$ the readonly fields of $`R_i`$ (any other field is
refused):

```math
\frac{\forall i.\ ⟦R_i⟧=\mathsf{Ref}(\varphi_i;\psi_i)}
     {⟦R_1\mathbin{\&}\cdots\mathbin{\&}R_n⟧=
      \mathsf{Ref}(\varphi_1\cdots\varphi_n;\,\psi_1\cdots\psi_n)}\ \textsf{record-meet}
```

with each list sorted and deduplicated (`Fragment.cellConjunction`); it is
exact by `recT_append`.

**Signatures.** A type literal or an interface whose members are call
signatures only is the function type they state, and one of construct
signatures only the constructor type, several signatures being overloads of
the one value; call signatures beside writable fields or methods are the
callable carrying them
([callable-meet](#intersections-of-functions-and-records)), each method a
host-relative member, as a record's, read from the value and invoked on it
(`NumberConstructor`'s call beside `isFinite`).
With $`⟦\sigma_1⟧,\ldots,⟦\sigma_n⟧`$ the signatures' fixed ones $`L`$ and
variadic ones $`S`$, each receiver `top` unless a `this` parameter states it,
$`\varphi`$ writable fields and $`\mu`$ methods, at least one of the two:

```math
\frac{⟦\sigma_1⟧,\ldots,⟦\sigma_n⟧=L;S}
     {⟦\{\,\sigma_1;\ \ldots;\ \sigma_n\,\}⟧=\mathsf{arrs}(L;S)}\ \textsf{call-literal}
\qquad
\frac{⟦\sigma_1⟧,\ldots,⟦\sigma_n⟧=L;S}
     {⟦\{\,\sigma_1;\ \ldots;\ \sigma_n;\ \varphi;\ \mu\,\}⟧=\mathsf{callable}(\varphi;L;S;\mu)}
\qquad
\frac{⟦\mathtt{new}\,\sigma_1⟧,\ldots,⟦\mathtt{new}\,\sigma_n⟧=L;S}
     {⟦\{\,\mathtt{new}\,\sigma_1;\ \ldots;\ \mathtt{new}\,\sigma_n\,\}⟧=\mathsf{ctors}(L;S)}\ \textsf{construct-literal}
```

One construct signature beside required properties describes a class value
holding them as its static fields, a mutable one invariant and a readonly
one a view:

```math
\frac{⟦\mathtt{new}\,\sigma⟧=L;S\quad ⟦\tau_i⟧=T_i\quad ⟦\upsilon_j⟧=U_j}
     {⟦\{\,\mathtt{new}\,\sigma;\ \overline{k_i\colon\tau_i};\ \overline{\mathtt{readonly}\ k'_j\colon\upsilon_j}\,\}⟧=\mathsf{ctors}(L;S;\ \overline{k_i{:}T_i};\ \overline{k'_j{:}U_j})}\ \textsf{construct-fields}
```

Any other member beside construct signatures (a method, an index, a call
signature, an optional property, which a class value's required static fields
do not state) is refused ([model limits](SOURCE-FRAGMENT.md#model-limits)). A rest
parameter over a union of tuples of required positions is one signature per
tuple, all at the signature's result, which a value meets by meeting every
one; the library's `next(...[value]: [] | [TNext])` is `next()` and
`next(value: TNext)`:

```math
\frac{⟦R⟧=[\vec A_1]\mid\cdots\mid[\vec A_n]}
     {⟦(\vec P,\ \ldots r\colon R)\colon B⟧=(\vec P\,\vec A_1)\colon B;\ \ldots;\ (\vec P\,\vec A_n)\colon B}\ \textsf{rest-tuples}
```

A tuple member's name is a label with no runtime meaning: a named member
reads as its unnamed form, at its type and with its optionality and rest, so
`[start: number, end: number]` is `[number, number]`. A named form is
admitted and refused exactly as its unnamed one:

```math
⟦[\ldots,\ x\colon\tau,\ \ldots]⟧=⟦[\ldots,\ \tau,\ \ldots]⟧
\qquad
⟦[\ldots,\ x?\colon\tau,\ \ldots]⟧=⟦[\ldots,\ \tau?,\ \ldots]⟧
\qquad
⟦[\ldots,\ \ldots x\colon\tau]⟧=⟦[\ldots,\ \ldots\tau]⟧\ \ \textsf{named-member}
```

The standard library's `BuiltinIteratorReturn`, an alias TypeScript
declares `intrinsic`, is `undefined` in the interfaces of ECMA-262's
iterators, `ArrayIterator`, `MapIterator`, `SetIterator`, `StringIterator`
and `RegExpStringIterator`: they complete with
`CreateIterResultObject(undefined, true)`, as `strictBuiltinIteratorReturn`,
which `strict` sets, reads it (`builtin-iterator-return-value-import`,
`invalid-builtin-iterator-return-value-import`, run under Node). Anywhere
else, Intl's and the DOM's iterator interfaces among them, it is refused:
another specification states those iterators' done value. An imported
`Intl.SegmentIterator` is refused before it, as a qualified type reference,
so no case reaches this refusal.

### Stated library types

**Audited against:** TypeScript 7.0.2's standard library and `@types/node`
22.20.2 and 22.10.7 (`tools/package.json`,
`pipeline/library-project/package.json`); host behaviour from ECMA-262's
TypedArray objects, Node 25.2.1's `lib/buffer.js`, `lib/internal/buffer.js`
and `lib/internal/fs/utils.js`, and probes run under Node 25.2.1
(2026-10-27).

A type name some host values have, whose declarations the reader does not
read as those values are (`Buffer` names the conditional type
`ImplicitArrayBuffer` and the indexed access `ArrayBufferLike`), is read
through the reviewed overlay of library types (`library-types.mts`). An
entry $`\theta`$ names the type, reviews each of its declaration parts by
the part's origin ([library globals](#library-globals): the standard
library, or an installed package by its name) and heading, the part's text
before its body with white space collapsed, exactly as reviewed, and states
the type the host's values meet, a definition $`D_\theta`$ no declaration
file declares. The pin is of the headings alone: the statement is audited
against the host's code, which the bodies of the declarations do not
describe. With $`P_N`$ the type declarations TypeScript binds $`N`$ to and
$`\Theta`$ the overlay:

```math
\frac{\theta\in\Theta\quad \theta.\mathit{name}=N\quad P_N\neq\emptyset\quad
      \forall p\in P_N.\ (\mathsf{origin}(p),\ \mathsf{heading}(p))\in\theta.\mathit{parts}}
     {⟦N⟧=D_\theta}\ \textsf{library-type}
```

The declarations are not read, and neither are the types they name. A name
with a part the entry reviews beside one whose origin or heading it does
not, a program's declaration merged into it among them, is refused; a name none of whose
parts the entry reviews is another type of that name, read as declared. The
name written with type arguments is refused (`Buffer<ArrayBuffer>`):
$`D_\theta`$ has no parameters. Where TypeScript types a value from its
context at the name (an unannotated closure parameter), it is $`D_\theta`$
at the arguments the entry states, or at any where it states none:

```math
\frac{\theta\in\Theta\quad \theta.\mathit{name}=N\quad
      \bigl(\theta.\mathit{arguments}\ \text{absent, or}\ ⟦\vec A⟧=\theta.\mathit{arguments}\ \text{or}\ \vec A=\varepsilon\bigr)}
     {⟦N\langle\vec A\rangle⟧_{\mathit{ctx}}=D_\theta}\ \textsf{library-type-context}
```

The entries of [library modules](#library-modules) and
[library globals](#nodes-buffer-and-textdecoder) returning or taking such
values name $`D_\theta`$ too. Each $`D_\theta`$ joins the document once,
where a statement or a name reads it. The entries:

- `Uint8Array`, the standard library's parts and Node's part adding `at`, a
  host object of no stated member, $`\mathsf{host}_b\,\{\}`$, with $`b`$
  the marker `"node:bytes"`.
- `Buffer`: $`\mathsf{host}_b\,\{\mathtt{toString}\colon(\texttt{"utf8"})\Rightarrow_\emptyset\mathtt{string};\ \mathtt{subarray}\colon(\mathtt{number},\ \mathtt{number}\mid\mathtt{undefined})\Rightarrow_\emptyset\mathit{Buffer}\}`$,
  each a method, within the empty footprint. `toString("utf8")` reads
  `this.length` and calls `this.utf8Slice`; `subarray` reads `this.length`,
  `this.buffer` and `this.byteOffset`, clamps its integers and constructs a
  `FastBuffer` over the same memory. A `Buffer` is a `Uint8Array`.
- `BigIntStats`: `{ dev, mode, nlink, uid, gid, rdev, blksize, ino, size,
  blocks, atimeMs, mtimeMs, ctimeMs, birthtimeMs, atimeNs, mtimeNs, ctimeNs,
  birthtimeNs: bigint; isFile, isDirectory, isBlockDevice,
  isCharacterDevice, isSymbolicLink, isFIFO, isSocket(): unknown }`, the
  bigints writable, assigned by `StatsBase` and `BigIntStats`; each test
  calls `this._checkModeProperty`, as a `Stats`'s does
  ([library modules](#library-modules)), so it states no effect.
- `Dirent`, at `Dirent<string>`: `{ name, parentPath: string; isFile, …,
  isSocket(): unknown }`, the strings writable, as `readdirSync` with
  `withFileTypes` returns its entries ([library modules](#library-modules)).
- `URL`, Node's global interface extending the class of `node:url`:
  $`\mathsf{host}_u\,\{\}`$, with $`u`$ the marker `"node:url"`, as
  [Node's `URL`](#nodes-url) states it.

$`\mathsf{host}_m\,R`$ is the record $`R`$ with a host family's marker
$`m`$ ([the family contract](HOST-FAMILIES.md#the-family-contract)): a
required readonly view of the model's `[[host]]` at $`m`$, which no
allocation of the program owns, so no program object meets a view's type
(`invalid-node-bytes-program-object`, run under Node: `decode` of such an
object throws), and the steps that copy an object's own properties or
expose their values refuse it ([host objects](HOST-FAMILIES.md#host-objects)).
`Object.keys` and `Object.hasOwn`, which a host object admits, answer a
view's element keys, which the model does not hold: strings and Booleans,
at no type that tells them. A view of bytes
is an integer-indexed exotic object (ECMA-262, "TypedArray Objects"): its
[[Get]] at a canonical numeric key is the element at a valid index, a
number from 0 to 255, and `undefined` at any other, never reading the
prototype chain, and its `length` is `%TypedArray%.prototype`'s getter.
The model holds neither: an element read at a number and a read of
`length` of a value TypeScript types as views of bytes only are calls of
the intrinsics stating them,

```math
⟦b[k]⟧=\%\mathrm{ByteAt}\%(⟦b⟧,⟦k⟧)\qquad ⟦b.\mathtt{length}⟧=\%\mathrm{ByteLength}\%(⟦b⟧)\ \ \textsf{byte-reads}
```

```math
\%\mathrm{ByteAt}\%\colon(\mathit{Uint8Array},\ \mathtt{number})\Rightarrow_\emptyset\mathtt{number}\mid\mathtt{undefined}
\qquad
\%\mathrm{ByteLength}\%\colon(\mathit{Uint8Array})\Rightarrow_\emptyset\mathtt{number}
```

each checked at its argument as any call is, so a read the parser writes
of another value is refused, and one it leaves a member read finds no
member (`invalid-node-bytes-past-end`, run under Node: `undefined` past the
end). A write converts its value by ToNumber, which runs an object's
`valueOf`, and keeps it modulo 256: it is not stated
(`invalid-node-bytes-write`, run under Node: 300 reads back as 44). A
spread copies a view's elements and not `length`, so its copy states no
member (`invalid-node-bytes-spread`), and a view meets no record naming
`length`, whose spread would copy it (`invalid-node-bytes-length-record`,
run under Node: the copy's `length` is `undefined`); `"length" in` a view
is refused (`invalid-node-bytes-in`, run under Node: `true`).
`JSON.stringify` of a `Buffer` calls `Buffer.prototype.toJSON`; a `Buffer`
is no `JsonValue` (`invalid-node-bytes-json`, run under Node). That a view
is a host object, that the intrinsics' reads are the host's, and that a
member read finds the host's code and runs no other, rest on a host
assumption ([trust surface](DESIGN.md#trust-surface)): every `Uint8Array`
and `Buffer`, the program's or external code's, is created by the host,
keeps its standard prototype chain (`Buffer.prototype` →
`Uint8Array.prototype` → `%TypedArray%.prototype` → `Object.prototype` for
a `Buffer`) and owns its elements alone, and a lookup along that chain of
`length`, `buffer` and `byteOffset` finds `%TypedArray%.prototype`'s
getters, and, for a `Buffer`, one of `toString`, `subarray`, `slice` and
`utf8Slice` finds `Buffer.prototype`'s data properties, each the host's own, no object before
it on the chain holding the key, throughout execution, as `Buffer`'s
`allocUnsafe`, `allocUnsafeSlow` and `concat`, which `readFileSync` calls,
are the host's own. A property shadowing a getter on an intervening
prototype answers what it holds (`invalid-node-bytes-length-shadowed`, run
under Node: a string).
A replaced method answers what it returns
(`invalid-node-bytes-method-replaced`, run under Node: a number), and a
getter in a method's place runs where the member is read
(`invalid-node-bytes-method-getter`, run under Node: it pops the array). A
program reaches none of them: `Buffer.prototype`, `Object.defineProperty`
and `Object.getPrototypeOf` but its comparison with `Object.prototype`
are refused. The cases are `node-bytes-buffer`,
`node-bytes-text-decoder`, `node-fs-stat-bigint`, `node-readdir-dirents`,
`blocker-node-buffer-contract`, `blocker-node-hash-contract` and
`invalid-node-stat-bigint` (run under Node: a `BigIntStats`'s `size` is a
bigint).

### Intersections of functions and records

A record type's clause is a plain object, which no function is, so the
model's meet of a function type and a record is empty. TypeScript's record
type also holds functions with those properties, and its intersection with a
function type is exactly those functions: the callable with the record's
fields (`sourceMeetLists`), as an interface with a call signature and fields
is. With $`\varphi`$ invariant fields and no view, optional field, method or
bound:

```math
\frac{⟦F⟧\ni\mathsf{arrs}(L;S)\quad ⟦R⟧\ni\mathsf{Ref}(\varphi)}
     {⟦F\mathbin{\&}R⟧\ni\mathsf{callable}(\varphi;L;S)}\ \textsf{callable-meet}
\qquad
\frac{⟦F⟧\ni\mathsf{callable}(\psi;L;S)\quad ⟦R⟧\ni\mathsf{Ref}(\varphi)}
     {⟦F\mathbin{\&}R⟧\ni\mathsf{callable}(\varphi\psi;L;S)}
```

An interface's `extends` clauses meet so too. An alias that expands to an
intersection contributes every part of that intersection, with its type
arguments substituted, through the same meet as separate bases.
A record with a readonly or
optional field, a method or an index met with a function type has no clause:
that pair is dropped, as the model's meet drops it (so `{}`'s function arm
meets such a record as nothing, and its record arm as the record), and an
intersection it leaves with nothing is refused for it. An array owns its store, so a function is
never one, and their meet is empty. An interface stating no member of its own
is its bases' meet (`interface Callback extends Function {}` is `Function`).
An intersection whose meet is empty (`string & { a: number }`, a function and
an array, `number[] & { map: number }`) has no value, though TypeScript keeps
such a type (a branded primitive). As an arm of a union it adds nothing:
emptiness is decided for the union as written, its arms read together
(`unionOfArms`, for annotations and producer claims alike), so
`number | (number & { brand: symbol })` is `number`. A type with no value as a whole
is refused rather than verified vacuously:

```math
⟦A_1\mid\cdots\mid A_k⟧=\bigcup_i ⟦A_i⟧,\qquad
\text{refused when}\ \bigcup_i ⟦A_i⟧=\varnothing.
```

## Computed types

A generic class or interface with a computed member over its own parameters
is read at a written application with closed arguments. Omitted arguments
are completed from the declaration's defaults. Each instance has the whole
admitted member shape and heritage, with the parameters substituted;
recursive references at those arguments name that instance. A host instance
uses its [reviewed view](COMPILER-API.md), including every listed member.
Written applications retain their [bound obligations](#written-applications).
An open argument, an unavailable written application, an unrepresentable
computed result or more than 256 instance equations in one graph is refused.
The declaration's parameter list supplies arity and defaults; its instance
equations supply the member contracts.


`typeof x`, `keyof T`, `T[K]`, template literal types, conditional types and
intersections of primitives and literals mean the type TypeScript's checker computes
(`computed-types.mts`). With $`\mathit{ts}(\tau)`$ the checker's type of the
node $`\tau`$ and $`\mathsf{lits}(t)`$ for $`t`$ as a union of literals,
primitive families and unique symbols when it is exactly one. A unique symbol
is the type of the one constant or readonly property declaring it, and it is
the singleton of the symbol that declaration names as a
[symbol key](#library-globals), $`\mathrm{sym}(k)`$: the type of
`Symbol.iterator` is $`\mathsf{symbolLit}`$ of the symbol the key
`[Symbol.iterator]` names, so `keyof [number]` holds `Symbol.iterator` and
`Symbol.unscopables` beside `number`, `"0"`, `"length"` and the method
names, and `keyof Promise<number>` holds `Symbol.toStringTag` beside
`"then"`, `"catch"` and `"finally"`:

```math
\frac{\mathit{ts}(\tau)\ \text{the unique symbol declared by}\ k}
     {⟦\tau⟧=\mathsf{symbolLit}(\mathrm{sym}(k))}\ \textsf{unique-symbol}
```


```math
\frac{\mathsf{lits}(\mathit{ts}(\tau))=U}{⟦\tau⟧=U}\ \textsf{computed}
\qquad
\frac{x\ \text{declares}\ x\colon\sigma\quad\mathit{ts}(\sigma)=\mathit{ts}(\mathtt{typeof}\ x)}
     {⟦\mathtt{typeof}\ x⟧=⟦\sigma⟧_{x}}
\qquad
\frac{x\ \text{a function or class value, not generic, no static method or private static}}
     {⟦\mathtt{typeof}\ x⟧=\mathsf{type}(x)}
```

where $`⟦\sigma⟧_x`$ reads $`\sigma`$ where $`x`$ is declared and
$`\mathsf{type}(x)`$ is what an import of $`x`$ reads, for a class with static
fields its construct signature and its static fields
([classes](#classes)). An indexed access projects
$`⟦T⟧`$ at each key of $`\mathsf{lits}(\mathit{ts}(K))`$: a
record's field (with `| undefined` where optional), an array's element at
`number`, a tuple's position, a union's parts, an intersection's operands'
members met, an alias through its equation (a generic one's at the
reference's arguments; an imported one's, read where it is declared), a named type's member through its annotation under
the same identity premise. An alias's record is read as the alias's own
equation, as the declaration graph reads it, each member at the reading the
declaration gives it. An optional method of a record or interface $`D`$ is
an optional field whose function takes $`D`$ as its receiver, so its
projection is that function, received by $`D`$, or `undefined`:

```math
\frac{D=\{\ldots;\ m?(\vec x:\vec\tau):\rho\ \ldots\}\ \text{the one declaration of}\ m,\ \text{in}\ D\quad
      D, m\ \text{without type parameters}\quad
      m\ \text{without a}\ \mathit{this}\ \text{parameter or a polymorphic}\ \mathit{this}\quad
      \text{no part of}\ D\ \text{in the standard library}}
     {⟦D[\texttt{"}m\texttt{"}]⟧=(\mathit{this}{:}\,D,\ ⟦\vec\tau⟧)\Rightarrow⟦\rho⟧\ \mid\ \mathtt{undefined}}\ \textsf{indexed-optional-method}
```

with $`D`$ an alias's record or an interface. A call of the projected
function must give it a $`D`$ as receiver
(`computed-index-optional-method`, `invalid-computed-index-optional-method`,
and `blocker-indexed-optional-method`, which calls it with none). A method
$`D`$ inherits takes the interface declaring it as its receiver, which the
reference does not name, and is refused
(`computed-index-inherited-method-refused`); so is a method of a standard
library interface or of an augmentation of one, whose contract the
library's overlay gives (`invalid-augmented-optional-method`), and a
required method, whose member is relative to the object it is read from
(`invalid-computed-index-generic-method`).

A **computed alias** is a generic alias whose equation is a computed form,
an application of another computed alias, or an application one of whose
arguments is a computed form or an application of a computed alias
(`computedAlias`): `type ElementOf<T> = T[number]`, `type Keys<T> = keyof T`,
the library's `type Omit<T, K> = Pick<T, Exclude<keyof T, K>>`. Over its parameters it
is known only at an application, so it has no equation of its own, and an
application of it, declared in the file or imported, is a computed type,
evaluated where it is written, its equation read with the parameters as the
arguments:

```math
\frac{A\langle\vec X\rangle=\tau\ \text{a computed alias}\quad
      \mathsf{lits}(\mathit{ts}(A\langle\vec\sigma\rangle))=U}
     {⟦A\langle\vec\sigma\rangle⟧=U}
\qquad
\frac{A\langle\vec X\rangle=\tau\ \text{a computed alias}\quad
      \mathsf{lits}(\mathit{ts}(A\langle\vec\sigma\rangle))\ \text{undefined}}
     {⟦A\langle\vec\sigma\rangle⟧=⟦\tau⟧_{\vec X:=⟦\vec\sigma⟧}}\ \textsf{computed-alias}
```

where $`⟦\tau⟧_{\vec X:=\vec S}`$ evaluates $`\tau`$ by the
rules here with each $`X_i`$ read as $`S_i`$: an indexed access projects its
argument, and `keyof` of a type literal is the union of its property names'
string literals (`keysOf`), so `ElementOf<readonly E[]>` is `E` and
`Keys<{ good: E }>` is `"good"`. An equation that is an application of an
alias that is no computed alias is that application read at the evaluated
arguments: `Omit<Entry, "stated">` is `Pick<Entry, U>` with $`U`$ the
literals of `Exclude<keyof Entry, "stated">` by $`\textsf{computed}`$, the
[library mapped type](#library-types) at `Entry`'s other members, each with
its modifiers (`blocker-omit-interface`, `invalid-omit-omitted-member`,
`invalid-omit-readonly`); with `type KeyBox<T> = Box<keyof T>`, `KeyBox<{ a: number }>` is
`Box<"a">` (`computed-argument-alias`,
`invalid-computed-argument-alias`). At a type parameter its keys are known only at an
instance, and the reference is refused. A `typeof` of a constant without an
annotation is the type TypeScript infers for its initializer where that is a
union of literals and primitives or an object literal's record of such
types, each property a writable field and each index a spread copied, read
from the checker (`inferredTerm`):

```math
\frac{\mathtt{const}\ x=e\quad \mathit{ts}(\mathtt{typeof}\ x)=\{\overline{k_i\colon t_i};\ \overline{[\theta_j]\colon u_j}\}\ \text{from}\ e\text{'s literal}\quad
      \forall i.\ ⟦t_i⟧\ \text{inferred}}
     {⟦\mathtt{typeof}\ x⟧=\{\overline{k_i\colon⟦t_i⟧};\ \overline{[\theta_j]\colon⟦u_j⟧}\}}\ \textsf{typeof-inferred}
```

An imported constant initialized by a literal naming nothing is read by the
same reading, where every array type within comes from an array literal and
is read too: an array literal's type is `Array<t>`, $`t`$ the union of its
elements' widened types, read as the annotation `t[]` reads, writable and of
readable presence (`literal-array-constant-value-import`,
`invalid-literal-array-constant-value-import`). A literal `as const`, a
readonly tuple or record of literal types, is refused
(`literal-const-array-constant-value-import`):

```math
\frac{\mathtt{const}\ x=e\ \text{imported},\ e\ \text{a literal naming nothing}\quad \mathit{ts}(x)=\mathtt{Array}\langle t\rangle\ \text{from an array literal of}\ e\quad ⟦t⟧\ \text{inferred}}
     {⟦x⟧=⟦t⟧\mathtt{[]}}\ \textsf{import-inferred-array}
```

A conditional type is read through an alias distributing over a parameter,
`type Extract<T, U> = T extends U ? T : never`, as `Extract`, `Exclude` and a
user alias of that shape are. With $`\mathsf{members}(\sigma)`$ the members of
the union $`\sigma`$ is written as, a union's members and those of the
equation of an alias it names, each alias's parameters read as the
reference's arguments or their defaults, a parameter standing alone in an
equation or a default being the members of what it stands for, an
application TypeScript decides
member by member, whose result is a union of the types of whole members, is
the union of those members, each read where it is written:

```math
\frac{A\langle\vec X\rangle=(X_i\ \mathtt{extends}\ \upsilon\ \mathtt{?}\ \tau_1\ \mathtt{:}\ \tau_2)\quad
      \mathsf{members}(\sigma_i)=\overline{\mu_j}\quad
      \mathit{ts}(A\langle\vec\sigma\rangle)=\textstyle\bigcup_{j\in J}\mathit{ts}(\mu_j)}
     {⟦A\langle\vec\sigma\rangle⟧=\textstyle\bigcup_{j\in J}⟦\mu_j⟧}\ \textsf{distributed}
```

`Extract<Shape, { k: "a" }>` is the member of `Shape` tagged `"a"`, and
`Exclude<Shape, { k: "a" }>` the others. A conditional type TypeScript
computes to a union of literals and primitives is that union by
$`\textsf{computed}`$: `KeysOf<Shape>` with
`type KeysOf<T> = T extends unknown ? keyof T : never` is the union of the
members' keys. The result's identity with the members' types is the premise:
TypeScript's decision selects members, and each kept member's contract is
its declaration's, optional fields included. A naked check type distributes
over no member of `never`, so `Extract<never, U>` is `never`; a wrapped one,
`[T] extends [U] ? X : Y`, decides `never` once, and its branch's literals are
the result by $`\textsf{computed}`$. `Extract<any, U>` is the member `any`,
which TypeScript keeps, read where it is written by the declaration reader as
`unknown` (`any` constrains nothing): a parameter at it accepts every value,
and a result at it promises none.

An alias inferring from a function or constructor type matches every
function (every class): its extends type's rest admits any argument list.
`ReturnType<T>`, `T extends (...args: any) => infer R ? R : any`, infers
the result; `Parameters<T>`, `T extends (...args: infer P) => any ? P : never`,
and `ConstructorParameters<T>`, of `abstract new (...args: infer P) => any`,
the parameter list. At a member that is a function (a class), the answer is
its declared result or parameter list; at an overload set, TypeScript infers
from the last signature, and so does the reader; at a union, the union of
its members' answers:

```math
\frac{A\langle X\rangle=(X\ \mathtt{extends}\ (\ldots a\colon\mathtt{any})\Rightarrow\mathtt{infer}\ R\ \mathtt{?}\ R\ \mathtt{:}\ \tau)\quad
      \mathsf{members}(\sigma)=\overline{\mu_j}\quad
      ⟦\mu_j⟧=\textstyle\bigwedge_{k\le n_j}(\vec A_{jk})\Rightarrow B_{jk}}
     {⟦A\langle\sigma\rangle⟧=\textstyle\bigcup_j B_{j n_j}}\ \textsf{inferred-result}
```

```math
\frac{A\langle X\rangle=(X\ \mathtt{extends}\ (\ldots a\colon\mathtt{infer}\ P)\Rightarrow\mathtt{any}\ \mathtt{?}\ P\ \mathtt{:}\ \tau)\quad
      \mathsf{members}(\sigma)=\overline{\mu_j}\quad
      \mu_j\text{'s last signature}\ (\vec x{:}\vec C,\ \vec y\,?{:}\vec D,\ \ldots r{:}E[\,])}
     {⟦A\langle\sigma\rangle⟧=\textstyle\bigcup_j\,[⟦\vec C⟧,\ ⟦\vec D⟧?,\ \ldots⟦E⟧[\,]]}\ \textsf{inferred-parameters}
```

with $`\vec y`$ the parameters written optional or with a default, each
position at the type that holds the `undefined` an omitted argument gives;
the form `abstract new (...args: infer P) => any`, which every class value
meets, reads a class's constructor the same way, and a class declaring no
constructor and no base has the empty list. A concrete
`new (...args: infer P) => any` is refused: an abstract class does not meet
it, and TypeScript then takes the false arm
(`inferred-concrete-constructor-refused`); so is a class with several
constructor declarations or a constructor with a rest parameter, as the
reader of a class value states one constructor without a rest
(`blocker-returntype-typeof`, `returntype-overloads`, `parameters-typeof`).
A written function type supplies its parameter list directly, including
optional and rest positions. Each position retains its complete annotation,
including a callback's `Within` effect. The enclosing function's result
and effect do not qualify the extracted parameters.

A guard's result is its Boolean, which TypeScript computes as a union of
literals (`returntype-guard`); a generic function's `typeof` is refused, as
its instantiation at its bounds states a value type no reader states. An indexed access of a method is refused
(`blocker-api-indexed-method`).

Each rule above gives what a computed type denotes. That replaces the
applications written in it, which keep their obligations by
[written applications](#written-applications): `ElementOf<number[]>` with
`type ElementOf<T extends readonly string[]> = T[number]` is refused although
TypeScript computes `number` for it, as are `keyof Box<number>` with
`interface Box<T extends string>` and `P<number>` with
`type P<T extends string> = T extends "a" ? T : never`, whose evaluation is
`never`. A computed alias applied without an argument reads its parameter's
default there, at the earlier arguments.

Refused: a conditional type over a function's own type parameter, which
TypeScript defers; one whose result has a part that is no member of the
decided union as written (a branch other than the parameter, `T[]`, or a
member naming a parameter of the alias declaring it inside another type,
which is another type at each instance); a conditional type outside an alias distributing over a
parameter that computes no union of literals and primitives; a template
literal type with a `$`{string}` or ``${number}` hole; a
form over a function's own type parameter (`keyof T`, `T[number]` with `T`
the function's binder), which denotes a function of the type an instance
names, not of the values a parameter row stands for; a unique symbol whose
declaration names no symbol (a constant made neither by `Symbol()` nor by
`Symbol.for` of a string literal); `typeof` of a binding
TypeScript infers another type for (a `let`, a method, a `const` assertion);
`typeof C` of a class with a static method or a private static, bindings of
their own that no member of the class value's type states.

## Written applications

A type application written in source syntax,
$`D\langle\sigma_1,\ldots,\sigma_k\rangle`$ with $`D\langle X_1,\ldots,X_n\rangle`$
an alias, interface or class, $`k\le n`$, its arguments completed with the
defaults $`\delta_j`$ ($`\sigma_j=\delta_j[\vec X:=\vec\sigma]`$, $`j>k`$), in a
lexical scope $`\Gamma`$ of type parameters with their assumptions,
obliges

```math
\Gamma\ \vdash\ ⟦\sigma_i⟧\le⟦\beta_i⟧_{\vec X:=⟦\vec\sigma⟧}\qquad(1\le i\le n)
```

with $`\beta_i`$ the declared bound of $`X_i`$ ($`\mathsf{top}`$ where none):
the inclusion holds at every assignment of $`\Gamma`$'s parameters meeting
its assumptions. The obligation is a function of the syntax and its scope,
whatever term a reader states for the type it is written in (a computed
type's evaluation, a mapped type's expansion, a rest's alias read through its
equation). An application of a declaration with no bounded parameter obliges
only $`\sigma_i\le\mathsf{top}`$, which every type meets.

The front end reads the obligations from the syntax
(`written-applications.mts`): every form naming an alias, interface or
class, at every depth, written with or without arguments: a type reference,
simple or qualified (`ns.B<σ>`, `globalThis.Record<K, V>`), an import type
(`import("m").B<σ>`), and a heritage clause (`extends`, `implements`,
qualified or not). A form instantiating a value's generic signature,
`typeof f<σ>` or `f<σ>` as an expression, is refused: its binders' bounds
are checked only at a call. An expression inside a type or an interface, or in a declared module's
declared types, is erased: no code the client runs evaluates it, so nothing
checks what a call, construction, tagged template, JSX element or decorator
there applies. The sweep visits every node of that syntax (members, keys,
signatures, parameters and their initializers, heritage clauses) and admits
an erased expression only when it is an entity name (an identifier, a
property of an entity read by name) or a literal (a string, a number or a
bigint, signed or not, `true`, `false`, `null`); it refuses any other,
whatever node holds it. A declaration's name, a private name `#x` included,
is no expression. A declared module's bodies, decorators and binding
initializers are its code, not its declared types. A computed key naming an
entity of a string or number literal type, an enum member or a constant, is
the key its value names. In the client's code a
heritage expression is code, swept whole. Swept are the client file's
code, with every type node outside its interfaces and aliases; the declared
types of the values the client reads; and, closed under dependency, every
declaration a swept type's meaning depends on, generic or not, with all its
merged parts. Every name in swept type syntax (a type reference's, a
qualified name's or a member path's every step, a `typeof` query's, an
import type's qualifier, a heritage clause's, a computed key's) resolves
through TypeScript's symbol, aliases followed to their target (re-exports,
renames, type-only imports, `export =`), to all that symbol's declarations;
a member path's step TypeScript gives no symbol resolves to the members of
that name of what the step before it denotes. A member selection depends on
the members it selects: an indexed access on its keys' members (every member
where its keys are no literals), a computed alias's application on every
member of its arguments; a module's or a namespace's member is its export
of that name. The unit swept is exactly the declaration reached (a member, a
property, a method, a variable's declarator, a type), its annotations and
type syntax, with the binders of its enclosing declarations in scope,
whatever path reached it; never its enclosing statement, its executable
body or its initializer. What is swept of a reached declaration is the
written annotations that determine its exposed type
([types stated by annotations](#types-stated-by-annotations));
one they do not determine, whose type TypeScript infers from its code, is
refused at the use reaching it. A name a further step selects a member of
contributes only that member; a whole class, namespace or module
(`typeof import("m")` included) contributes every member by its kind. A module or a namespace contributes nothing by itself,
only the members a further step selects. A name resolving to nothing is
refused. The standard library's declarations are not
swept: the applications inside them belong to the reviewed library
declarations. A call's type arguments are swept for the applications written
in them; whether they meet the callee's binder bounds is the instantiation of
a quantified signature, checked at the call.

The scope is binder groups from the outermost, each binder named freshly per
declaration, so that distinct type parameters of one spelling are distinct
variables. A group is simultaneous: all its names are in scope in all its
bounds (`<T, U extends T>`, `<T extends Node<T>>`). The assumptions:

- a function's, method's, closure's, class's, declaration's or generic
  signature's type parameter: its declared bound;
- a mapped type's key `[K in Q]`: `Q`;
- `infer U`, in its extends type and the true branch: its explicit
  constraint, else none;
- in a conditional's true branch with a naked check type `T`: a fresh `T'`
  bounded by `T & X`, `X` the extends type, as TypeScript narrows `T` there,
  except where `X` holds `infer`.

An entry keeps the binders its arguments name, closed under those their
bounds name; dropping a binder's assumption enlarges the assignments the
obligation must hold for, so it only strengthens the check. A declaration's
entries are checked once, under its parameters' bounds; a use obliges its
arguments to meet them, and an instance is one assignment meeting them.

An application's arguments are completed once, by the one reader every
consumer shares: the written ones, then each omitted parameter's default
read at the arguments before it, $`\sigma_j=\delta_j[\vec X:=\vec\sigma]`$. A
reference in a declaration's equation, in the client's annotations, in a
library overlay and in each entry carries every argument so completed; a
definition states only whether each parameter has a default, and the
verifier and the producer read a reference at exactly its declaration's
arity.

An entry states, per parameter, its completed argument and its bound read at
the arguments, $`\beta_i[\vec X:=\vec\sigma]`$: the front end reads the
bound's syntax, as a default's, with the parameters as the arguments' terms,
so `Pick`'s `K extends keyof T` is read at `T`'s argument. A computed form
there (`keyof`, a conditional, a template literal, an indexed access, a
computed alias's application) naming no parameter is what TypeScript computes
for it where it is written; one naming a parameter is what TypeScript
computes for it at the application. The checker instantiates no declaration's
syntax, so the question is asked in a probe program (`type-probe.mts`): the
project with two declarations added,

```ts
type P</* the declaration's parameters, verbatim */> = /* the form */;
type U = P</* the application's written arguments, verbatim */>;
```

`P`'s parameters are the declaration's by position, its merged declarations
together: each position's name, with the bound and the default a
declaration states for it, copied from that declaration. `P` stands beside
the declaration (in a global augmentation of its module) or, where that file
cannot be read again (a standard library file), beside `U`; `U` at the end of
the statement list holding the application. Their names are fresh; where one
binds to anything other than its generated declaration, another pair is
tried, and after a few the evaluation is refused. A reference's omitted
arguments, and the arity a definition states, count the defaults of all the
merged declarations. TypeScript completes
the omitted arguments with the defaults, substitutes and evaluates: `U`'s
type is the answer. Each name in the copied parameter list, form and
arguments must resolve in the probe to the declarations it resolves to where
it is written, a name declared inside a copy to its original, a parameter of
the declaration (its merged parts included) to `P`'s parameter at its
position; `P` and `U` must be the declarations found where they were placed,
the reference to `P` binding to that `P`, and `U` the one declaration of its
name; otherwise the evaluation is refused, as it is for a `this` type and for a name of the
application's scope that is a type parameter (the form is then computed only
at an instance). The answer is read from the checker's type objects: a union
of literals and primitives (`keyof Record<string, number>` is `string`, of
`{ 0: number }` the number `0`, of a class its public members' keys), each
unique symbol mapped to the constant declaring it in the original program.
A result that is a class instance type (the type of an object created by the
class) or an interface type, naming one declaration, is a reference to that
declaration in the original program, with all its type arguments read by the same rule; unions preserve
every part. Class constructor types, such as `typeof Box`, are refused at the
application: their fields differ from those of objects created by the class.
The same instance check governs references read from contextual types for
closure parameters, inferred static fields, and inferred `Object.assign`
call signatures, including their parameter and result types.
The referenced declaration supplies the whole contract. A result
whose own computed members require another written application is refused,
as are anonymous object results and enum members whose identities have no
literal representation. A computed alias applied in an annotation reads its
defaults and equation the same way, at that application. A
declaration's definition states no bound: bounds are read only here. The
verifier binds
each entry's groups as a unit's binders (`bindNames`), lowers each argument
and bound there, and records one obligation per parameter, checked by the subtype
comparison after closing (`closeObligation`): each bounded placeholder $`p`$
on the actual side becomes $`p\wedge B_p`$, its bound's placeholders closed
in turn up to a cycle, and on the upper side stays $`p`$.

**Closing lemma** (proved here, not mechanized). For an assignment $`\eta`$
with $`\eta(p)\subseteq⟦B_p⟧_\eta`$ for each recorded $`(p,B_p)`$, closing
keeps both sides' meanings: $`⟦\mathsf{close}(A)⟧_\eta=⟦A⟧_\eta`$. By
induction on the closing's fuel: a placeholder cut at a cycle or at fuel
$`0`$ is itself; otherwise
$`⟦p\wedge B_p[\mathsf{close}]⟧_\eta=\eta(p)\cap⟦B_p⟧_\eta=\eta(p)`$, by the
hypothesis on $`B_p`$'s placeholders and the assumption. The upper side is
unchanged. With `comparisonUsing_sound`,
$`\forall\eta.\ ⟦\mathsf{close}(A)⟧_\eta\subseteq⟦B⟧_\eta`$, so the obligation
holds at every assignment meeting the recorded bounds.

Lean checks every supplied entry; that the entries are exactly the
applications written in the swept syntax, read faithfully, is the front
end's (the declared-types bridge of [TRUST-REDUCTION](TRUST-REDUCTION.md#the-bridges)).
`any` in a user declaration reads as
`unknown`, so `Box<any>` with a bounded `Box` is refused. A bound of an
external declaration (the standard library's, a package's) is a type-level
wildcard: each `any` in it is the top type at its position, `unknown` at a
positive one and `never` at a parameter's, each parameter flipping the
polarity, as the declarations a program is checked against read it
([shadow contracts](../tools/shadow-contracts.mts)). A function type whose
rest admits no argument list, `(...args: never) => R`, is every value with
call code, a class value excluded, through which nothing is called, and a
constructor type whose rest admits none, `abstract new (...args: never) => R`,
is every class value: `ReturnType`'s bound `(...args: any) => any` is every
function, and `ConstructorParameters`' every class
(`function-wildcard-parameter`, `invalid-function-wildcard-call`).

Refused, each a limit of the mechanism: an argument computed over a binder,
`B<T["k"]>` in a generic body, which has no term there; `infer U` at a
bounded position, whose implied constraint is not modelled; a narrowing other
than a naked check type's, as of a wrapped check type `[T] extends [X]` or an
extends type with `infer`; a generic signature whose bound names another of
its binders, which a scheme does not represent; an obligation whose
comparison exhausts its budget; an argument outside the fragment, such as a
string pattern.

## Index signatures

An index signature is a view (and, mutable, a writable contract) over a
[key class](POSITIVE-TYPES.md#records). The reader states:

```math
⟦\{[k\colon\mathtt{number}]^m\colon V\}⟧=\mathsf{Dict}(\mathsf{numeric}{:}V)
\qquad
⟦\{[k\colon\mathtt{symbol}]^m\colon V\}⟧=\mathsf{Dict}(\mathsf{symbols}{:}V)
\qquad
⟦\{[k\colon\mathtt{string}]^m\colon S;\ [k\colon\mathtt{number}]^m\colon N\}⟧=
  \mathsf{Dict}(\mathsf{strings}{:}S,\ \mathsf{numeric}{:}N)
```

An index over a union of key types is one per member; one over `string |
number`, or a number index at the string index's contract, is the string
index alone. A named key reads through an index whose class surely admits it,
at $`V\mid\mathtt{undefined}`$ (`readDict`); a computed `string`, `number` or
`symbol` key through an index over a class containing its keys (`indexDict`),
the narrower number index where both admit it. No write in place through an
index is typed: a write at a key known only at run time is a
[key-adding write](PROGRAM-TYPING.md#key-adding-writes) on a local's own
object, its copy with an allocation at the key over it. A numeric property name is the key its value's `ToString` spells
(`numericKey` in `type-term.mts`), and a number key of a receiver claimed only
at records is the [named access](SOURCE-ELABORATION.md#keyed-access-at-a-singleton-key) of that key.

## Open reads

A member read `o.k` at a key $`k\notin\mathrm{objectProtoKeys}`$ of
$`\mathrm{auditedOpenReadKeys}`$ or of $`\mathrm{receiverOpenReadKeys}`$
is an **open read**, a call of the intrinsic $`\%\mathsf{Read}{:}k\%`$
(`openReadIntrinsic` in `intrinsics.mts`), which the parser writes where
the declaration graph finds one of two shapes of syntactic eligibility
(`openReads`):

- **A record part.** TypeScript types `o` as a union each arm of which is
  an object type, alone or intersected with parts of the standard
  library's `Record<"k'", unknown>`, and some arm holds such a part with
  $`k`$ among the $`k'`$: the type `"k" in o` gives an operand of no arm
  stating $`k`$ (`object & Record<"k", unknown>`), or an explicit
  annotation of the same shape.
- **A guarded read.** `o` is a name, and a test `"k" in o` of the same
  name, whose type at the test has an arm stating no $`k`$ (an arm states
  $`k`$ by a property or by a string index signature, whose value type a
  read of $`k`$ has, `in-index-signature-read`), makes the read
  eligible: within one function, the read lies in the right operand of
  `t && …` or of `t || …`, a branch of `t ? … : …` or of `if (t)`, or a statement after
  an `if (t)` without `else` whose branch ends in `return`, `throw`,
  `break` or `continue`, with `t` answering the way that finds $`k`$ in
  `o` (`"k" in o` true, through `!`, a conjunction found true or a
  disjunction found false). TypeScript drops the arm stating no $`k`$,
  which an open record may own at any type (`invalid-in-union-getter`, run
  under Node). Eligibility is syntactic: it does not track a reassignment
  or a call between the test and the read (`in-union-read`), and it
  establishes no presence at the read.

At a key of $`\mathrm{receiverOpenReadKeys}`$ (`body`, `type`) the read is
also restricted by its receiver. Each arm of TypeScript's type of `o` at
the read, and for a guarded read also at the test, either states the key
(a part of it, other than a `Record<"k'", unknown>` part, is an object
type with that property, whose value the read finds as its stated
contract says), or is of the host package: each such part is an object
type all of whose declarations, and transitively every base type's, are
the host package's, whose audit covers the key. Any other arm keeps the
read refused: one of the program's own types stating no key, which may
carry a getter at the unstated key (as a value at `ErrorOptions` may at
`cause`, [`JSON` and `Error`](#json-and-error); `invalid-in-union-getter`,
run under Node), a type extending an external
one (`interface LocalError extends Error {}`), another library's type,
`object` or `unknown` (`invalid-in-union-read-receiver`). The open-read
restriction at these keys then concerns only the audited package's
objects and the stated keys of other receivers.

```math
o.k\;\equiv\;\%\mathsf{Read}{:}k\%(o)
\qquad
\%\mathsf{Read}{:}k\%:(\{\})\Rightarrow_{\emptyset}\mathtt{unknown}
```

```math
\frac{\Gamma\vdash o:A\quad A\le\{\}\quad k\in\mathrm{auditedOpenReadKeys}\cup\mathrm{receiverOpenReadKeys}\quad k\notin\mathrm{objectProtoKeys}\quad
      o.k \text{ eligible}\quad k\in\mathrm{receiverOpenReadKeys}\Rightarrow \text{each arm of } o \text{ states } k \text{ or is the host package's}}
     {\Gamma\vdash o.k:\mathtt{unknown}}\ \textsf{open-read}
```

The parameter is the record of no field, so the argument's type is checked
as any call's: an object without call code, which the slices of `unknown`
that `typeof o === "object"` and `o !== null` leave
([slices of the value universe](SOURCE-MODEL.md#slices-of-the-value-universe-by-tag-tests)) are. The result is
`unknown`, so the read states no type of the key: no field, no ownership
and no write follows from it, and a write at the key stays a
[key-adding write](PROGRAM-TYPING.md#key-adding-writes)
(`invalid-open-read-write`). The eligibility check recognizes the type shape,
which an explicit annotation can also state, or the guard; the signature
holds of every object, so neither proves anything the read relies on, and
each only selects the reads that TypeScript's type of the operand gives
no stated field of.
A passed `in` test does not prove permanent presence: a later lookup can
return `undefined`, which is within `unknown`.

**The open-read restriction.** The signature is an assumption of every
unit that reads one, as each intrinsic's is: for the admitted open-read
keys, lookup on every admissible receiver finds absence, a data property or an
audited transparent host getter, producing a value satisfying the model's
`unknown` contract; external code preserves this condition. A data
property's lookup runs no code; an audited getter executes code that
preserves the modeled heap. The empty footprint rests on this audit and
external restriction. Every result must meet `unknown`, the
[array invariant](DESIGN.md#trust-surface) included; a data descriptor alone
does not establish permission to expose host internals. The
restriction is enforced where the program makes objects: the fragment
admits no accessor, in a literal or a class (`invalid-open-read-getter`,
run under Node: a getter at the key runs at each read), and no proxy
(the [trust surface](DESIGN.md#trust-surface)); it is assumed of every
object external code supplies.

The keys of `Object.prototype` (`toString`, `constructor`, `__proto__`, …)
are no open-read keys: `in` with one is refused
(`invalid-open-read-inherited`), and a read at one stays the model's.

**Audited key capability.** `auditedOpenReadKeys` and
`receiverOpenReadKeys` in
[`host-operations.mts`](../tools/host-operations.mts) own the cross-family
audit and allowlists: `close`, `kill`, `once`, `exitCode`, `signalCode`,
`kind`, `getStart` and `name`, then the receiver-restricted `body` and
`type`. Each key is audited against every admitted
host family, its own and inherited properties, and the library overlays:
absence or transparent data/getters whose results meet `unknown` and whose
reads preserve the modeled heap. The audit covers compiler nodes and node
lists, sync API views and client/channel/child, and Node and standard
library objects. The audit reads the installed implementations (the
package's `dist` sources and Node's); adding a key, family or overlay
requires it again.
The declaration graph checks this capability independently of the apparent
receiver type, so erasure to `unknown` retains the gate. `view`, `parent`
and `_byteIndex` are outside the allowlist; `invalid-compiler-api-open-read-erased`
passes a Node to `expose(x: unknown)` and refuses its `x.view` read.

`tests/compiler-api.mts` (C5) samples that audit under Node: the compiler
client/child data properties and the node's `kind` getter and `getStart`
method along their chains, and, on three nodes of different kinds, the
`body` and `type` getters of `RemoteNode.prototype`, reading the kind's
named child or `undefined`, while the client and its process have neither
key. It checks no other family and no heap preservation; those rest on the
implementation audit.
The source excludes custom inherited getters as well as literal getters
(`invalid-open-read-inherited-getter`, run under Node). External code
preserves the same restriction, including on prototype chains.
An open read's `unknown` establishes no host family: a guard promising a
node from a numeric `kind` is refused, which `{ kind: 1 }` passes
(`invalid-compiler-api-open-read-kind`, run under Node). A receiver a
family's type describes uses that family's stated keys, and a key outside
the allowlist that none of its arms states stays refused
(`invalid-compiler-api-open-read-internal`); an eligible read at an
audited key is an open read on a family's union of kinds too
(`compiler-api-in-union-read`).

## Prototype contracts

`ArrayProto`, `StringProto`, `NumberProto`, `BigIntProto` and `BooleanProto`
are records of readonly members read from TypeScript's `ReadonlyArray`/`Array`
and `String`, `Number`, `BigInt`, `Boolean` through the overlay
(`array-prototype.mts`): only listed members, each read from the declaration
whose text is the reviewed one, at the receiver the entry names (`readonly
T[]` for `ReadonlyArray`, `T[]` for a mutator, the primitive for a
primitive's member), without dropped parameters. `ArrayProto` joins a
unit's declarations wherever an array or tuple type reaches it: one the file
writes, or one a declaration it reads states (an imported value's type, a
declared type's member, a library contract's result). An entry may state its
signature family instead, with $`\omega`$ the entry of member $`m`$ of prototype
$`p`$, and $`R_j`$ its reviewed receiver (defaulting to $`p`$):

```math
\frac{\omega\in\Omega_p\quad \omega.\mathit{text}=\mathsf{text}(m)\quad
      \omega.\mathit{stated}=[(R_j,\vec P_j,Q_j,\epsilon_j)]_{j=1}^n\quad n>0}
     {⟦m⟧_\omega=\bigcap_{j=1}^n
       (\mathsf{this}:R_j,\ \vec P_j)\Rightarrow_{\epsilon_j} Q_j}\ \textsf{proto-stated}
```

Each signature states an effect $`\epsilon_j`$: the entry's own, else its
prototype's, the empty footprint for `StringProto`, `NumberProto`,
`BigIntProto` and `BooleanProto` and the footprint `all: any` for `ArrayProto`. A
signature states the empty footprint where the member, called at it, runs no
client code but callbacks whose own signatures state the same, and writes no
location the call did not allocate. Every primitive member listed meets this:
its receiver is a primitive, it converts only primitives (a string search
reads no `[Symbol.match]` of a primitive pattern, `split` and `replace` are
stated at a string pattern), reads `locales` by index, and allocates only its
result. Of `ArrayProto`, `slice`, `flat`, `join`, `toString`, `indexOf`,
`lastIndexOf`, `includes`, `at`, `[Symbol.iterator]`, `values`, `keys` and
`entries` state it: they read the receiver, convert only numbers and elements meeting the conversion
contract below, compare by strict equality or SameValueZero, and allocate
only their result. `find`, `findIndex`, `filter`, `some`, `every`,
`forEach`, `flatMap`, and `reduce` and `reduceRight` with an initial value,
call a callback; each reads the length once and the
receiver's own numeric keys, data properties (`numericOwn`), and allocates
only its result by ordinary construction (`reduce` and `reduceRight` none:
they return the callback's last answer, or the initial value), so beside the
callback it runs no
client code and is within the callback's footprint: it has one signature per
closed footprint $`\varepsilon`$ (`array-preserving-callbacks`,
`map-stable-filter-push`, `invalid-map-filter-pop`, `map-stable-reduce-push`,
`invalid-map-reduce-pop`):

```math
\frac{m\in\{\mathsf{filter},\mathsf{every},\mathsf{forEach}\}\quad f:(T,\ \mathsf{number},\ \mathsf{ReadonlyArray}(T))\Rightarrow_{\varepsilon}\mathtt{unknown}}
     {\mathit{xs}.m(f):R_m\;!\;\varepsilon}\ \textsf{native-callback}
```

with $`R_m`$ the member's result: $`T[\,]`$, `boolean`,
`undefined`. `Boolean` read as a value is such a callback
([library globals](#library-globals)). The members that write their receiver (`sort`,
`push`, `pop`, `shift`, `unshift`, `reverse`, `splice`) and those that call an
unrestricted callback do not.

`some` admits a sparse receiver through the same prototype-contract
mechanism. Its callback receives a present element of type $`T`$, its numeric
index and the same sparse readonly array. The native captures the length
before visiting positions, tests presence before each read, and skips holes,
including positions removed by an earlier callback. It converts each answer
to a Boolean without calling conversion hooks, stops at the first truthy
answer and otherwise returns `false`. It allocates no result object and
performs no writes beside those of its callback, so each closed callback
footprint is also the call's footprint. Callback throws propagate.

The signature retains sparse presence in the callback's third
argument; visiting one position establishes no other position's presence.
The third argument has this contract even for a readable receiver; indexed
reads through it can return `undefined`.
This contract uses the existing numeric data-property and stable standard
prototype assumptions. `blocker-round-mapped-array-some` checks a mapped
receiver. `invalid-some-sparse-callback` reads a missing position through
the third argument and throws a `TypeError` under Node.

`filter` is stated at TypeScript's guard overload too,
`filter<S extends T>(predicate: (value: T, index: number, array: readonly T[]) => value is S): S[]`,
read at a callback whose [promise signature](SOURCE-ELABORATION.md#user-defined-guards) promises
$`S`$ of its first actual, at each closed footprint $`\varepsilon`$:

```math
\frac{f:(T,\ \mathsf{number},\ \mathsf{ReadonlyArray}(T))\Rightarrow_{\varepsilon} S\,[\mathsf{guards}\ 0]}
     {\mathit{xs}.\mathsf{filter}(f):S[\,]\;!\;\varepsilon}\ \textsf{native-guard-filter}
```

Both ordinary and guard `filter` signatures also admit a sparse receiver.
These signatures pass a sparse readonly array as the callback's third
argument: visiting one present element establishes no presence at other
indices. The native tests presence before each visit and appends each kept
value at the next result index, so the result is dense even when the input
has holes or a callback removes a later input. This uses the same ordinary
construction and standard-object assumptions as the readable signatures.
`blocker-round-conditional-map-cell` exercises a mutable receiver holding
either `map`'s potentially sparse result or `flatMap`'s dense result;
`invalid-filter-sparse-callback` reads a hole through the callback's array
argument and throws under Node.

The native reads each present element $`v`$ once, calls the callback with
$`v`$, its index and the receiver, and appends that same $`v`$ to its fresh
result, by ordinary construction, where the answer converts to `true`; it
skips absent positions and is called without `thisArg`. A promise signature
answers `true` or `false`, and its `true` leaves $`v\in S`$. The callbacks
the native runs afterwards change the heap only by writes the model admits,
each keeping every location's contract, so the world they leave extends the
one $`v\in S`$ held in, and membership of a type is kept by world extension
(`Adm`'s `mono`, [Types.lean](../lean/Verification/Types/Types.lean)).
Every kept value is an $`S`$ without the bound $`S\le T`$, which the
overlay leaves out; at $`S`$ the empty type the result is empty. The
callback's closed footprint also bounds the native on normal return: beside
callbacks it only reads existing locations and writes the fresh result's
store and element cells. This includes reentrant calls; their writes must
meet the callback's contract. No exceptional footprint is stated.
`guard-filter-footprints` exercises pure, value-writing, growing and
shrinking callbacks; `blocker-next-guard-filter-map-density` keeps the
enclosing map's result dense through a preserving guard filter.
`invalid-guard-filter-map-pop` pops the outer map receiver from the guard,
leaving an absent result position that throws `TypeError` when read under Node.
A narrowed readonly field remains a view of an invariant storage contract:
`invalid-guard-filter-field-alias` cannot promise a string field merely by
testing a writable nullable field. Its later callback writes null through an
alias to an earlier selected object, whose string operation throws under Node.
The existing ordinary-construction, species and numeric-data restrictions
apply to every footprint, including the top footprint. A callback whose
promise is about another parameter meets
only the plain signatures, where `filter` keeps `T`. A guard read as a
value meets the guard signature where its value states its promise
signature extended by a rest of `unknown`, the actuals past its parameters
it discards: a module function's slot ([module functions](SOURCE-ELABORATION.md#user-defined-guards))
and a compiler-API guard's entry
([guards as values](HOST-FAMILIES.md#guards-as-values)) state it
(`filter-guard-value`, `blocker-compiler-api-filter-guard-element`). A
value known only by its type states no such extension, and meets only the
plain signatures.

`find` is stated at its guard overload,
`find<S extends T>(predicate: (value: T, index: number, obj: readonly T[]) => value is S): S | undefined`,
at each closed footprint $`\varepsilon`$ keeping array stores
($`\varepsilon.\mathit{store}=\mathsf{keep}`$):

```math
\frac{\varepsilon.\mathit{store}=\mathsf{keep}\quad f:(T,\ \mathsf{number},\ \mathsf{ReadonlyArray}(T))\Rightarrow_{\varepsilon} S\,[\mathsf{guards}\ 0]}
     {\mathit{xs}.\mathsf{find}(f):S\cup\mathtt{undefined}\;!\;\varepsilon}\ \textsf{native-guard-find}
```

At such a callback the receiver's store, and so its length, stays as it
was, and each visit passes an element at the receiver's contract, as for
`find`'s plain signatures. Where the answer converts to `true` the native
returns that very value, which the promise leaves an $`S`$, running no
client code after the callback's call; where no answer does, `undefined`.
At any other footprint `find` visits positions a callback removed and
passes them `undefined`, which a guard TypeScript types at `T` does not
admit. A guard closure meets this signature by its promise signature at
the footprint its body proposes (`blocker-compiler-api-find-promise`), a
guard read as a value at its own footprint (`filter-guard-value`), and
either popping the receiver does not (`invalid-find-guard-closure-shrink`,
`invalid-find-guard-shrink`). `every`'s, `this is readonly S[]`, is not a
contract of the native: a callback may append untested elements or
replace tested ones, so a traversal answering `true` says nothing of the
receiver it leaves.

The reviewed overlay can restrict quantified binders (`bounds`) and weaken a
native's promised result (`result`). These specify trusted natives; source
annotations are still translated in full. `join` bounds `T` to the conversion
contract below,
`find` and `findIndex` visit every index below the length they read first.
At a callback whose footprint keeps array stores (`store: keep`), the
receiver's length stays as it was, so they pass `T` (`find-stable-counter`);
at any other a store may shrink, and they pass `T | undefined`
(`invalid-native-find-mutation`). `map` relies on every index below the length it captured staying
present until it tests it, a fact every closed footprint whose change to stores
is at most `grow` keeps (`map_rely`, `denseCheck_stable`): at each such
footprint $`\varepsilon`$, a dense receiver and a callback within
$`\varepsilon`$ give a dense result, and the call is within $`\varepsilon`$,
since beside the callback `map` reads the receiver and allocates its result.
Any other callback gives a result that may hold holes:

```math
\frac{\varepsilon.\mathit{store}\sqsubseteq\mathsf{grow}\quad \mathit{xs}:\mathsf{dense}\ T[\,]\quad f:(T,\ \mathsf{number},\ \mathsf{ReadonlyArray}(T))\Rightarrow_{\varepsilon}U}
     {\mathit{xs}.\mathsf{map}(f):U[\,]\;!\;\varepsilon}\ \textsf{map-stable-callback}
```

Source `U[]` requires readability; the fresh qualified map result may choose that
lifetime contract even when its initial contents are physically dense.
`flatMap` appends the present elements of each array its callback returns,
and appends any other result as it is: the declared `U | ReadonlyArray<U>`
is unsound where `U` admits an array, since such a result is flattened
(`invalid-array-flat-map-value`). It is stated at a callback returning an
array, of which only present entries are read, with `thisArg` and its
binder `This` dropped:

```math
\mathsf{flatMap}:\forall U.\ (\mathsf{this}:\mathsf{sparse\ ReadonlyArray}(T),\ (T,\ \mathsf{number},\ \mathsf{sparse\ ReadonlyArray}(T))\Rightarrow\mathsf{sparse\ ReadonlyArray}(U))\Rightarrow U[\,]
```

The signature accepts a sparse receiver and passes that same
sparse array as the callback's third argument. Only present positions are
visited, so the first argument has type $`T`$; an arbitrary read through
the third argument can produce `undefined`. The captured initial length,
presence tests before each visit and each flattened read, and ordinary
result construction give a readable fresh result even if a callback
shrinks either array. Each closed callback footprint gives the same
footprint for the native call. This extends the existing prototype
contract and its standard-object assumption.
`invalid-flat-map-sparse-callback` checks the third argument's presence:
its mapped receiver has a hole, and its unchecked read throws a
`TypeError` under Node.

`flat()`, at its default depth 1, appends the present elements of each
present element that is an array (`IsArray`), as they are, and appends any
other element as it is; the result holds no hole. TypeScript's
`FlatArray<A, D>` result is unsound where an element's type admits an array
it does not state as one: at `object[]` holding `[1]` the result holds `1`
(`invalid-array-flat-objects`). The overlay states `flat` at a receiver of
arrays, with its own binder $`U`$ in place of the declaration's `A` and `D`,
and without `depth`, which a call must omit:

```math
\mathsf{flat}:\forall U.\ (\mathsf{this}:\mathsf{sparse\ ReadonlyArray}(\mathsf{sparse\ ReadonlyArray}(U)))\Rightarrow\mathsf{dense}\ U[\,]
```

Each element of the result is an element of one of the receiver's arrays,
a $`U`$, flattened one level only (`array-splice-flat`). `flat` reads the
receiver's and its arrays' lengths and own numeric data properties, runs no
client code, writes no existing location, and allocates its result by
ordinary construction.

The installed `splice(start: number, deleteCount?: number): T[]` and
`splice(start: number, deleteCount: number, ...items: T[]): T[]` overloads
share one reviewed variadic contract: fixed `number` and
`number | undefined` parameters, rest elements $`T`$, a mutable readable
$`T[\,]`$ receiver and a readable $`T[\,]`$ result. An omitted deletion
count removes the remaining suffix; explicit `undefined` removes nothing.
Both behaviors meet the same result and effect contract. The source's
argument count and evaluation order are retained.

[ECMA-262's splice algorithm](REFERENCES.md#ecma-262) captures the receiver's length, converts only those primitive
offsets, and copies the removed range to fresh array storage by ordinary
construction. Presence tests preserve holes in that range; the result has
the receiver's readable element contract. Holes are readable where the
element contract admits `undefined`; a sparse string receiver does not meet
this contract (`invalid-splice-insert-sparse`). It shifts or deletes remaining
indices, inserts the already evaluated values, and sets the new length.
Its normal-return footprint permits value writes and changes to the
receiver's store, while keeping other existing stores. It states a fresh
result store and no exceptional preservation. A tuple, whose required
positions a removal would lose, is no such receiver
(`invalid-array-splice-tuple`). Insertion can accompany shrinking;
`invalid-splice-insert-map-density` leaves a hole in an enclosing map's
result and throws under Node.

Inserted values are captured before the call mutates its receiver, including
when a spread aliases that receiver. The existing spread snapshot also
captures values before a later argument runs client code. Object elements
retain their identities in both the receiver and removed result; freshness
concerns array storage. `blocker-next-splice-insert-spread` and
`array-splice-insert` exercise alias replacement, legacy calls, insertion,
argument order, holes and mutation of fresh removed storage.

A reviewed signature's optional rest element passes through the same
`TypeTerm` function contract as declared variadic functions. Its fixed
parameters, receiver, result and effect travel with it through instantiation
and checking. Forged claims widening splice's rest or erasing its
receiver-store exception are refused in evidence production and consumption.
The standard constructor/species, numeric-data and prototype restrictions
below apply to both overloads.

Native array results rely on the ordinary-construction invariant: an array owns
neither `constructor` nor any key declared by `ArrayProto`; the host keeps the
standard array constructor/species behavior. The same own-key exclusion is used
in array lowering and the built-ins' invariant (`RequestJson.arrayExcludedKeys`).
Thus `filter` and `slice` can promise ordinary arrays, and certified callback effects
justify the dense `map` overload.

**Standard array conversion.** Let P be the primitive types, including
`undefined`, and define the regular recursive contract

```math
D=\mu X.\;P\;\cup\;\mathsf{ReadonlyArray}(X).
```

This is the synthetic declaration `StringConvertible`, lowered by the ordinary
recursive declaration mechanism. The built-in arrays exclude own `toString`,
`join` and `Symbol.toPrimitive`; the prototype contract states an optional
`Symbol.toPrimitive` field whose only possible value is `undefined`. Standard
prototype behavior is required of external code too. Thus string conversion of
an admitted array reaches standard `toString`, which calls standard `join`,
whose element conversions meet the same D contract. No client conversion hook
is called. Primitives may throw (a symbol, for example); termination is not
claimed for recursive arrays. Without a library identity for `Symbol.toPrimitive`,
D conservatively contains primitives only.

`join` and `toString` each quantify `T` with bound `T ≤ D`. `join` takes
`sparse ReadonlyArray<T>` as its receiver, with either no separator or one
`string | undefined` separator, and returns `string` within the empty
footprint. [ECMA-262](REFERENCES.md#ecma-262)'s `Array.prototype.join`
captures the length, converts the separator, then reads every index in that
range. A missing own index yields `undefined` under the standard prototype
assumption and contributes empty text, as does `null`. Each present element
meets D, so its conversion runs no client code; the separator is a primitive,
and the result is a string. No array result is constructed and no constructor
or species lookup occurs. Numeric own properties are data properties, and
the standard prototypes have no numeric properties or getters. These are
the existing array and standard-object assumptions, also required of
external code. `blocker-census-effect-map-result` permits its callback to
remove source elements; `invalid-sparse-join-coercion` checks the conversion
bound on the result and, under Node, calls an unsafe element's `toString`
with `undefined` where its annotation requires a number.

For `sort`, let
A(T) be the mutable array contract, V(D) its readonly view at D, and C(T) the
comparator `(T,T) → number`.
Its one scheme offers the intersection:

```math
\forall T.\quad
 ((\mathsf{this}:A(T),\ C(T))\Rightarrow A(T))
 \;\cap\;
 ((\mathsf{this}:A(T)\cap V(D),\ \mathtt{undefined})\Rightarrow A(T)).
```

The comparator signature is also offered once per closed footprint
$`\varepsilon`$ whose store change is at most `grow`, at a comparator
$`C_\varepsilon(T)`$ within $`\varepsilon`$, and states the call within
`{value: any, store: grow}` ([native footprints](#native-footprints)).

These are audited native contracts, consumed by the existing quantified call
and subtype rules, not new calculus axioms or a proof of ECMA-262's algorithms.
Custom array conversion is deliberately outside the admitted language: it adds
dispatch and alias obligations without helping the motivating programs.
`native-array-conversion` and the unchanged tuple-sort examples verify;
`invalid-array-conversion-override` refuses the conflicting own-key contract.
Runtime controls show why accepting externally overridden hooks would invalidate
the assumption. See [ECMA-262](REFERENCES.md#ecma-262), `ToPrimitive`,
`Array.prototype.toString` and `CompareArrayElements`.

Omitting the comparator supplies `undefined`, so it needs the second receiver
contract. A comparator on arbitrary objects needs only the first. These are
ordinary scheme instantiation and arrow application; the result is the same
mutable array contract throughout. Selecting one signature never erases the
other signature or its receiver condition from the declared scheme.

`Set<T>`, `Map<K, V>`, `WeakMap<K, V>` and `Date` are read through the same mechanism
(`interfaceOverlay`), as an interface with only its listed members:

```math
\frac{\mathit{lib}(I)\quad \Omega_I=[\omega_1,\ldots,\omega_n]\quad
      m_j\ \text{the member of}\ I\ \text{with}\ \mathsf{text}(m_j)=\omega_j.\mathit{text}}
     {⟦I\langle\vec X\rangle⟧_\Omega=\{k_1:⟦m_1⟧_{\omega_1};\ \ldots;\ k_n:⟦m_n⟧_{\omega_n}\}}\ \textsf{library-interface}
```

a supertype of the declared interface in its members and their
signatures; the effects, and a `Set`'s and a `Map`'s marked iterators below,
are host assumptions about the built-in prototypes, not consequences of
that structure. A member's signatures state the
entry's effect: the empty footprint for the readers, `has`, `get`, `keys`,
`values`, `entries`, `[Symbol.iterator]` and `Date`'s getters, `valueOf`,
`toString` and `toISOString`; `{value: any, store: keep}` for the members
that change the collection or the date, `add`, `set`, `delete`, `clear` and
`setTime`, which compare by SameValueZero or take a number, run no code and
write only the receiver's internal slots, which hold no array store; none for
`forEach`, which calls a callback. `new Set` and `new Map` of an array, of a
host collection or of nothing state the empty footprint on their construct
signatures: they read the array or the collection through the host's iterator
and allocate. $`⟦m⟧_\omega`$ drops
`thisArg`, reads a `this` result as the receiver, and reads a declared
iterator result as `Iterator<T>`, which it extends, or, for `Set`'s and
`Map`'s `keys`, `values`, `entries` and `[Symbol.iterator]`, as the native
collection iterator, `Iterator<T>` marked as the built-in one
([loops and spreads](SOURCE-ELABORATION.md#loops-and-spreads-over-iterables)). A property is a readonly
view. A string's own `length` and indices are the calculus's `lenStr` and
`elemStr`, never the prototype's; `s[i]` is `string | undefined`.

#### Weak tables

`WeakMap<K, V>` uses the collection interface overlay, with `get(K): V |
undefined`, `has(K): boolean`, `set(K, V): this`, `delete(K): boolean` and
its readonly standard tag. The declared key bound is retained. `get` and
`has` state the empty footprint; `set` and `delete` state
`{value: any, store: keep}`. A lookup may be absent regardless of an earlier
`has`, particularly after alias mutation. `set` returns the receiver.
Only zero-argument `new WeakMap<K, V>()` is admitted, with the empty
footprint; an iterable argument is refused.

The native contract is audited against [ECMA-262](REFERENCES.md#ecma-262):
empty construction allocates the weak table without reading an iterator or
an adder. The four methods check the receiver's internal slots and compare
keys by identity; they perform no key conversion, property read, iteration,
callback, thenable assimilation, constructor lookup or species operation.
Their only mutations affect the table's internal entries. Invalid receivers
throw `TypeError`. A weak key is an object (including a function) or a
non-registered symbol. `set` throws `TypeError` for every other key;
`get` returns `undefined`, and `has` and `delete` return `false` for such
keys. The overlay retains TypeScript's key parameter, so calls outside
that parameter are refused even where native reads return absence. Its
result types describe normal returns; they do not assert that a call
cannot throw. The ES2022 declaration's key bound admits objects; a
`WeakKey` bound computed over multiple registry members is outside the
indexed-access fragment and is refused.
Weak reachability imposes no collection deadline. A reachable key's entry
persists until explicit deletion or replacement.

These are assumptions about the standard constructor and prototype methods:
no code, including external code, replaces them or wraps them in getters.
The ordinary native receiver's methods obey these contracts; structural
client implementations must establish the stated signatures and effects.
The source boundary excludes forging the standard tag. Lean checks uses of
these assumed signatures; it does not prove the JavaScript implementation
or garbage collection. Declaration collection follows only the constructor
and members used by the source and their type dependencies; the WeakMap
contract introduces no iteration intrinsic or unrelated collection contract.

`ReadonlySet<T>` and `ReadonlyMap<K, V>`, the readers' views of a `Set` and a
`Map`, are read through the same mechanism at the restriction of the
collection's own readers (`forEach` without `thisArg`, `has`, `get`, `size`,
`keys`, `values`, `entries` and `[Symbol.iterator]`, the result of
`[Symbol.iterator]` an `Iterator` and those of `keys`, `values` and
`entries` an `IterableIterator`, each of which the native collection
iterator meets), so that `Set<T>` meets `ReadonlySet<T>` and `Map<K, V>` meets
`ReadonlyMap<K, V>` by width and by the callback's parameter, as `Array`
meets `ReadonlyArray` (`readonly-collection-views`). They state no
`[Symbol.toStringTag]`, so a program's object may meet them: each member
states the effect its declaration does, which is no footprint
(`invalid-readonly-set-has-effect`, run under Node), and a loop or a spread
over one runs the [iterator protocol](SOURCE-ELABORATION.md#the-iterator-protocol).

### Function.prototype.toString

`FunctionProto` is the record of one readonly member, `toString`, read from
TypeScript's `Function` through the overlay (`functionOverlay`), at the
receiver `Function` and the empty footprint:

```math
\mathsf{FunctionProto}=\{\mathsf{toString}:(\mathsf{this}:\mathsf{Function})\Rightarrow_{\emptyset}\mathtt{string}\}
```

[ECMA-262](REFERENCES.md#ecma-262)'s `Function.prototype.toString` returns
a string for a receiver with call code (its source text, or a
`NativeFunction` string) and throws a `TypeError` for any other receiver, an
outcome; it reads no property and calls no code. A function's lookup of
`toString` finds it where the function owns no `toString` and no object along
its prototype chain before `Function.prototype` holds one. The program's
functions meet this by a restriction of the fragment, which refuses each way
a function of the program comes to own `toString`:

- a class's static member named `toString`, a method or a field
  (`invalid-function-own-to-string`, run under Node);
- a key `toString`, or a spread, in the literal of `Object.assign`'s callable
  form, the key as the literal's allocation resolves it: a name, a string,
  or a computed key TypeScript types as that one literal
  (`invalid-function-own-to-string-assign`,
  `invalid-function-own-to-string-computed`, both run under Node);
- a write of `toString` on a receiver TypeScript types as a function, by a
  member name or at a computed key TypeScript types as `"toString"`
  (`invalid-function-to-string-write`,
  `invalid-function-to-string-write-computed`).

A class's static side inherits from its base: a class of the program, which
the first rule covers, or the standard `Error`, whose constructor owns no
`toString`; any other base is refused
([a class extending `Error`](SOURCE-ELABORATION.md#a-class-extending-error)).
`Object.defineProperty` and
`Object.setPrototypeOf` are outside the overlay of library globals. A write
types only at a record contract (`writeCell`), of which a function is no
value; `Object.assign` copying onto a parameter's or a local's function is
refused, as onto an object another reference may hold (observed, not a rule
of its own). External
code's functions are assumed to meet the same ([trust surface](DESIGN.md#trust-surface)).
With both, a member read at `toString` of a value $`x`$ of a function's shape
reads through a fresh object whose prototype is the slot `[[Function.prototype]]`,
at $`\mathsf{FunctionProto}`$, as a primitive's member is read through its
wrapper's prototype:

```math
\frac{x:F\quad F\ \text{a callable, an arrow set or a class value}}
     {x.\mathsf{toString}\ \leadsto\ \mathsf{new}\{\mathtt{[[proto]]}:\mathit{FP}\}.\mathsf{toString}}\ \textsf{function-to-string}
```

A read of `toString` on a union dispatches on each shape, a test `isFun`
selecting this arm (`primitiveArms`); the call passes $`x`$ as the receiver.
`blocker-function-member-read` reads it on an `unknown` a `typeof` test found
a function, and `function-to-string` on a signature type, a class value and a
union with a string.

### Native footprints

A native's **footprint** is the closed footprint its signatures state
([FOOTPRINTS](FOOTPRINTS.md#changes-and-footprints)): for the locations that
existed before a call, the change the call may make to those holding a value
and to those holding an array store. Each row's footprint is trusted input
of acceptance; its argument is proved of a model of the specification steps
where the native is modelled, and audited otherwise:

| Native | Footprint | Argument |
| --- | --- | --- |
| `push`, `unshift` | `{value: any, store: grow}` | proved of the specification steps: `Arr.push_grow`, `Arr.unshift_grow`, `array_native_post`; that each changes nothing but its store and element contents is audited |
| `sort` at a comparator within `ε`, `ε` one of the four of the stable set | `{value: any, store: grow}` | one signature per such `ε`: proved of the specification steps, the snapshot then the writeback grow the receiver's store over the whole call when the comparator keeps its locations among the entry's and fresh ones, which `ε` states (`sort_grow`); beside the comparator's calls it reads the length and the present elements, data properties, converts the comparator's numeric answer, and changes only its receiver's store and element contents (audited) |
| `sort` at any other comparator, and at `undefined` | none stated | another comparator is client code that may change any store (`invalid-sort-comparator-shrink`, run under Node); the conversion signature states no footprint |
| `pop`, `shift`, `reverse`, `splice` | `{value: any, store: keep}` but for the receiver's store (`receiverStore`) | each changes only its receiver's store, which it can make lose a present index (controls in `FootprintControls.lean`), and element contents (audited) |
| `filter`, `map`, `flatMap`, `flat`, `slice`, `splice`, a string's `split` | a fresh result, beside the rows' footprints | each allocates its result by ordinary construction, a store no earlier heap held (audited) |
| `map` at a dense receiver and a callback within `ε`, `ε` one of the four of the stable set | `ε` | one signature per such `ε`, with a dense result (`map_rely`); `map` reads its receiver and allocates its result (audited) |
| `map` at any receiver and any callback | `{value: any, store: any}` | the unrestricted signature, with a result that may hold holes |
| `every` at a guard within the empty footprint promising `R`'s type, `R` one of `string`, `number`, `boolean` | the empty footprint, and on a `true` result every present element of the receiver of kind `R` (`elements R`) | `every` reads the length once, tests presence and calls the guard with each present element, answering `false` at the first falsy answer; the guard changes no location, so the store and each element keep their contents through the call, and a guard's answer is a Boolean, so `true` follows only from `true` at every visit, which leaves that element in `R` ([ECMA-262](REFERENCES.md#ecma-262), `Array.prototype.every`; audited) |
| `map` at a callback within the empty footprint taking `R`'s type, its receiver's present elements of kind `R` at the call (`requires R`), at a dense receiver and at any receiver | the empty footprint, a fresh result, dense at a dense receiver | the callback changes no location, so the fact holds at every visit (`elems_rely`) and each element `map` passes is in `R`; `map` skips a hole and leaves it in its result, built by ordinary construction ([ECMA-262](REFERENCES.md#ecma-262), `Array.prototype.map`; audited) |
| a global or sticky native regex's `exec`, `test`, `[Symbol.match]`, `[Symbol.replace]` at a string | `{value: any, store: keep}` | they write only `lastIndex`, a number (audited) |
| a native regex's other members; a regex neither global nor sticky's `exec`, `test`, `[Symbol.match]` at a string and `[Symbol.replace]` at a string and a string replacement | the empty footprint | they write nothing (audited) |
| a native regex's `[Symbol.replace]` at a replacement callback, the regex a literal written at the call | none stated | it calls the callback, client code (`invalid-regexp-replace-callback-effect`) |
| `%Dispatch:replace%` | its target member's footprint | one signature per closed footprint (audited, as its target's) |
| `%Iterate%` over an array; its step, called with the iterator as its receiver | the empty footprint, its result a fresh object (`freshObject`); the empty footprint on every location but the receiver's own (`receiverOwn`), which may change their values | creating the iterator runs no client code; the iterator is a fresh object holding its internal state (the array, the next index and whether it is done) at its own locations, none an array store; a step reads the array's current length and the element at the index, which runs no client code on an array of the program (no proxy, an element a data property, `Array.prototype` standard: the [trust surface](DESIGN.md#trust-surface)'s rows), writes only that state, and allocates what it yields (audited against [ECMA-262](REFERENCES.md#ecma-262)'s array iterator objects) |
| an iteration intrinsic over a string, a `Set`, a `Map`, a host iterator and a native match iterator; its step; a spread form `%Spread:K%` | the empty footprint; `{value: any, store: keep}`; `{value: any, store: keep}` | they run no client code; a step writes only the iterator's position and, for a match iterator, its clone's `lastIndex`, each a number, and allocates what it yields (audited) |
| `Math.max`, `Math.min`, `String.fromCodePoint`, `String.fromCharCode` at primitives | the empty footprint | they convert primitives, which runs no code, and allocate only their result (audited) |
| `forEach`, `every`, `some`, `filter`, `find`, `findIndex`, `flatMap`, and `reduce`, `reduceRight` with an initial value, at a callback within `ε` | `ε` | one signature per closed footprint; beside the callback each reads the receiver and allocates only its result (audited) |
| `new Set`, `new Map` of an array, a host collection or nothing | the empty footprint | they read the array or the collection through the host's iterator and allocate (audited) |
| `Set` and `Map` `add`, `set`, `delete`, `clear`; `Date` `setTime` | `{value: any, store: keep}` | they run no code and write only the receiver's internal slots, which hold no array store (audited) |


**A non-empty `split`.** `String.prototype.split` with a non-empty string
separator and no limit returns at least one element: the separator is no
`RegExp`, so no `[Symbol.split]` runs, and ECMA-262's `split` returns `[S]`
where the separator does not occur, so `"".split("\n")` is `[""]`
([ECMA-262](REFERENCES.md#ecma-262), `String.prototype.split`). It returns
`[]` in two cases only: a limit whose `ToUint32` is `0`, and an empty
receiver with an empty separator (`"".split("")`). The overlay states, beside
the general form, one further form ([prototype contracts](#prototype-contracts),
the forms of a member without binders being their intersection), whose
separator is the union $`\Lambda`$ of the non-empty string literals written in
the separators of the source's `split` calls that pass no limit
(`splitSeparators`), and whose result is the tuple of one required position
and a rest, the representation the fragment has for an array with a known
prefix (a position read at its index is its type, `elemReadPlan`):

```math
\mathtt{split}\colon(\Lambda)\Rightarrow[\mathtt{string},\ \ldots\mathtt{string}]
\qquad \Lambda=\lambda_1\mid\cdots\mid\lambda_n,\ \text{each}\ \lambda_i\ \text{a string literal other than}\ \texttt{""}
```

The form holds at any union of non-empty separators; which literals are
collected bounds only which calls it serves. A call of a string's `split`,
its receiver's type deciding as for a primitive's prototype, collects the
array prototype its result's members need; a structural `split` does not
(`tests/trusted-inputs.mts`). Its result's store contract has
a required position, which forbids a removal, so the producer proposes the
form only for a call whose result nothing shrinks (`Source.unshrunk`): read
by index at once, or bound to an unannotated constant every use of which
reads it (an element, its `length`, a member that reads, an iteration),
directly or as a conditional's arm; any other call takes the general form,
and Lean checks whichever is proposed: a shrunk, aliased or annotated result
forged at the non-empty form is refused in search and in checking
(`pipeline/test.mts`). It has no limit parameter, so a
call passing a limit takes the general form: a limit is not stated, since a
numeric literal of at least `1` does not exclude `[]`, `ToUint32` reducing it
modulo $`2^{32}`$ (`split(",", 4294967296)` is `[]`). A `RegExp` separator
keeps the general form: an empty receiver and a pattern matching the empty
string give `[]`. The form states the same footprint and fresh result as the
general one (audited). Controls: `split-non-empty` (a literal and a union of
literals, a conditional's arm, results popped, aliased and annotated),
`invalid-split-empty-separator`, `invalid-split-limit` (beside a stated form
for the same separator), `invalid-split-string-separator`,
`invalid-split-alias-shrink`, `invalid-split-element-write`, each with a Node
run, and a separator forged at `string`, refused in search and in
checking (`pipeline/test.mts`).

What is proved and what is audited:

- **Proved** in the model, of the array mutators' specification steps
  (`Set` of an index, `Delete`, a length change, in the order ECMA-262 gives
  them; `lean/Verification/Semantics/FootprintNatives.lean`), and read by no
  acceptance theorem: a native signature's footprint enters acceptance as
  stated, and these lemmas are the argument for stating it
  ([native footprints from their steps](drafts/native-footprints-from-steps.md)
  makes them part of acceptance): `push`, `unshift`, a
  longer length and `sort` over the whole call change the store by `grow`
  (`Arr.push_grow`, `Arr.unshift_grow`, `Arr.setLength_grow`, `sort_grow`);
  `pop`, `shift`, `reverse` of a store with a hole and a shorter length do
  not (controls in `Tests/FootprintControls.lean`). `array_native_post`
  turns a store change by `grow`, with element contents the only other old
  locations changed, into the footprint's postcondition. `map_rely` proves
  `map`'s density below its captured length at every presence test from
  callbacks within the stable set ([FOOTPRINTS](FOOTPRINTS.md#the-stable-set-for-density)).
- **Audited** for every row: that the native changes no old location beyond
  its footprint; for an array mutator, that it changes nothing but its store
  and element contents, and for `map`, that it tests presence only between
  callbacks. These are host assumptions, with the Node runs of
  `tests/node-runs.mts` as their counterexample controls: each removing
  mutator in a `map` callback leaves a hole and each growing one none; a
  regex literal is fresh at each evaluation, and a shared global regex keeps
  `lastIndex`; a `Map` written by a callback holds what it wrote.

## Library globals

**Audited against:** TypeScript 7.0.2's standard library and `@types/node`
22.20.2 and 22.10.7 (`tools/package.json`,
`pipeline/library-project/package.json`); host behaviour observed under Node 25.2.1
(2026-10-19).

The overlay files (`library-globals.mts` here, `library-modules.mts` for
[library modules](#library-modules), `array-prototype.mts` for
[prototype contracts](#prototype-contracts)) restate this review in a
comment beside each entry; the catalogue owns it, and each file's header
cites the section it implements.

### The overlay

A standard library global is read only through the reviewed overlay
(`library-globals.mts`), one entry per signature, with exactly the
declaration text it was reviewed against. With $`s`$ a selected signature,
$`\Omega`$ the overlay and $`\omega`$ an entry:

```math
\frac{\mathit{lib}(x)\quad \omega\in\Omega\quad
      \omega.\mathit{global}=x\quad \omega.\mathit{text}=\mathsf{text}(s)\quad
      \omega\ \text{admits}\ (i, S)}
     {⟦s⟧_\Omega=⟦s⟧\bigl[\,p_i:=S\,\bigr]}\ \textsf{library-global}
```

and an entry without `admit` reads $`s`$ as declared. Replacing a parameter by
a subset gives a supertype of the declared signature. An entry may state the
signature the host meets (`stated`), for a construct signature, a method (a
scheme over its binders, host-relative) or a property (its type the result):

```math
\frac{\mathit{lib}(x)\quad \omega\in\Omega\quad \omega.\mathit{global}=x\quad
      \omega.\mathit{text}=\mathsf{text}(s)\quad
      \omega.\mathit{stated}=\forall\vec X.\ \mathsf{new}(\vec P)\Rightarrow R\quad
      |\vec a|\le|\vec P|\ \text{for each}\ \mathsf{new}\ x(\vec a)\ \text{selecting}\ s}
     {⟦s⟧_\Omega=\forall\vec X.\ \mathsf{new}(\vec P)\Rightarrow R}\ \textsf{library-construct}
```

**Several stated forms of one declaration.** TypeScript resolves
`new Set("∀∃λΛμ")` to `new <T>(iterable?: Iterable<T> | null): Set<T>`. One
stated form cannot cover both an array and a string: a parameter
`readonly T[] | string` with result `Set<T>` is false at `T := number`, and
`Iterable<T>` admits client iterators, which run code. An entry may state a
list of forms, each a signature the host meets, under the entry's binders,
a form naming none of them included:

```math
\frac{\omega.\mathit{stated}=[\forall\vec X.\ \mathsf{new}(\vec P_1)\Rightarrow R_1,\ \ldots,\ \forall\vec X.\ \mathsf{new}(\vec P_n)\Rightarrow R_n]\quad n\ge 1}
     {⟦s⟧_\Omega=\forall\vec X.\ \bigwedge_i\ \mathsf{new}(\vec P_i)\Rightarrow R_i}\ \textsf{library-construct-forms}
```

The value is a construct scheme with $`n`$ signatures, which every instance
meets, as a native method's overloads are (`map`'s forms). `new` selects one
per call: the construction rule requires the selected signature to be a
member of the callee's with each argument's premise checked
(`ProgramCertificates`, `construct`); no selection is accepted without them.
`Set`'s iterable overload states `new <T>(values?: readonly T[] | null):
Set<T>` and `new (values: string): Set<string>`, both at the empty footprint:
the host iterates a string by its own iterator, which runs no client code
(the assumption `%Iterate:String%` makes). It states a third form, `new
<T>(values: NativeSetView<T>): Set<T>`, and a fourth form, `new <T>(values:
readonly T[] | NativeSetView<T>): Set<T>`. Its array arm uses the array
contract of the first form, so a union of arrays and host sets fixes one
element type (`blocker-census-set-copy`). `Map`'s iterable overload
states, beside its array of pairs, `new <K, V>(entries: NativeMapView<K, V>):
Map<K, V>` and `new <K, V>(entries: NativeMapView<K, V> | undefined): Map<K, V>`.
For `undefined`, [ECMA-262's Map constructor](REFERENCES.md#ecma-262)
allocates an empty map and returns before reading its `set` member or
obtaining an iterator. This result meets every key and value contract and
preserves existing values and stores. The present-input form retains its
own signature for inference. `blocker-next-optional-native-map-copy` checks
the optional form with explicit key and value arguments.
The host arms take a collection's reading view, which a
`Set<T>` and a `Map<K, V>` meet, at the empty footprint. The construction
gets the argument's
`[Symbol.iterator]`, the host's collection iterator by the assumption
`%Iterate:Set%` and `%Iterate:Map%` make of a value at the view, and steps it
with the host's `next`, which runs no client code; a `Map`'s iterator yields a
fresh `[key, value]` array per entry, whose `0` and `1` are own data elements,
so reading them runs no getter. It adds each element by `Set.prototype.add`, or
sets each entry by `Map.prototype.set`, which it gets from the fresh
collection, whose prototype is the untampered standard one, and which writes
only that collection. A `ReadonlySet` or `ReadonlyMap` meets no view: any
object with the readers meets it, and its iterator, and a `Map` entry's
getters, are client code (`invalid-set-from-readonly-set`,
`invalid-map-from-readonly-map`, run under Node). Every form keeps its parameters,
result, effect and binder substitution. The declaration's text matches the
reviewed one exactly; every form is decoded, and an empty or malformed list,
or an unsupported combination of binders, is refused, never an arm dropped
(`set-string-construction`, `blocker-collection-from-iterable`; `invalid-set-string-at-number`,
`invalid-set-iterator-construction`, `invalid-set-excess-arguments`).

An entry may read a call signature as the global's construct (`construct`),
where the host's call runs the construct's steps: `Error(m)` called takes the
error constructor itself as its new target (ECMA-262, "Error ( message [ ,
options ] )"). The call is written as the construct, and its statement joins
the global's construct signatures:

```math
\frac{\mathit{lib}(x)\quad \omega\in\Omega\quad
      \omega=(x,\ \cdot,\ \mathsf{text}(s),\ \mathsf{construct},\ \mathsf{stated}\ \forall\vec X.\ (\vec P)\Rightarrow R)\quad
      |\vec a|\le|\vec P|\ \text{for each}\ x(\vec a)\ \text{selecting}\ s}
     {⟦x(\vec e)⟧=\mathsf{new}\ x(⟦\vec e⟧)\qquad ⟦s⟧_\Omega=\forall\vec X.\ \mathsf{new}(\vec P)\Rightarrow R}\ \textsf{library-call-construct}
```

```math
\frac{\mathit{lib}(x)\quad \omega\in\Omega\quad \omega=(x,\ m,\ \mathsf{text}(s),\ \mathsf{stated}\ \forall\vec X.\ (\vec P)\Rightarrow R)\quad
      |\vec a|\le|\vec P|\ \text{for each}\ x.m(\vec a)\ \text{selecting}\ s}
     {⟦s⟧_\Omega=\forall\vec X.\ (\mathsf{this}:\mathsf{self},\ \vec P)\Rightarrow R}\ \textsf{library-stated}
```

A statement may end in a rest whose element $`E`$ every further argument
meets, a spread's elements included, and may state a call signature of the
global, read at each call $`x(\vec a)`$ as a member's is:

```math
\frac{\mathit{lib}(x)\quad \omega\in\Omega\quad \omega=(x,\ m,\ \mathsf{text}(s),\ \mathsf{stated}\ (\vec P,\ \ldots E)\Rightarrow R)\quad
      \text{no spread among the first}\ |\vec P|\ \text{actuals of each}\ x.m(\vec a)}
     {⟦s⟧_\Omega=(\mathsf{this}:\mathsf{self},\ \vec P,\ \ldots E)\Rightarrow R}\ \textsf{library-stated-rest}
```

A standard library global is read as a value only where the overlay marks
each of its call signatures for one (`value`): whoever receives the value may
call it with any receiver and any arguments its type admits, so the entry
states what the host does at every one of them.

```math
\frac{\mathit{lib}(x)\quad x\ \text{read as a value}\quad
      \forall s\in\mathsf{calls}_I.\ \exists\omega\in\Omega.\ \omega=(x,\ \cdot,\ \mathsf{text}(s),\ \mathsf{value})}
     {\Gamma(x)=⟦\mathsf{sel}_{M,O,\mathsf{calls}_I}(I)⟧_\Omega}\ \textsf{library-value}
```

An entry may state that its signature preserves the input heap
(`effect`), where a call at the parameters the signature states runs no
client code and writes no location it did not allocate:

```math
\frac{⟦s⟧_\Omega=\forall\vec X.\ (\vec P)\Rightarrow R\quad \omega.\mathit{effect}=\emptyset}
     {⟦s⟧_\Omega=\forall\vec X.\ (\vec P)\Rightarrow_{\emptyset} R}\ \textsf{library-effect}
```

`String`, `Number` and `BigInt` of a primitive, `Number.isFinite`, `Number.isInteger`,
`Number.isSafeInteger`, `Object.is` and `Boolean` state it: each converts
only a primitive, or nothing, and reads and writes no location
(`library-preserving-callback`, `library-preserving-tests`). An object
argument, whose conversion runs its methods, is outside the stated
parameter (`invalid-number-object`). `Object.keys` of an object, and the
generic `Object.values` and `Object.entries` of a dictionary, state it too:
each lists the object's own keys, which runs no code (no object is a proxy),
reads a dictionary's values, which are data properties by the
[caller contract](DESIGN.md#trust-surface) and the fragment's own objects
alike, a dictionary being no host object, and writes only the arrays it
allocates (`library-preserving-reflection`). `Object.keys` reads no value
at all. The overloads at `{}` read the values of keys the object's type
need not state, by [[Get]], and state no preservation
(`object-entries-sparse`, `invalid-object-entries-preserving`).

### Reviewed entries

The entries below are grouped by global, each with the code its restriction
keeps from running.

#### Conversions and `Math`

- `Boolean(v, …)` is ToBoolean of its first argument, which runs no code and
  reads no property, and ignores the rest: $`(\mathtt{unknown},\ \ldots\mathtt{unknown})\Rightarrow\mathtt{boolean}`$,
  a value too (`xs.filter(Boolean)`). It is stated with no promise about its
  argument: its declaration, `<T>(value?: T): boolean`, states none, so
  `filter(Boolean)` keeps its receiver's element type, as TypeScript keeps it
  (`invalid-boolean-filter-narrowing`).
- `Number(v, …)` is ToNumber of its first argument, which runs an object's
  `Symbol.toPrimitive`, `valueOf` or `toString`, and ignores the rest. It is
  stated at a primitive, defined below: $`(\mathsf{Prim},\ \ldots\mathtt{unknown})\Rightarrow\mathtt{number}`$,
  a value too (`texts.map(Number)`; `number-value`; `invalid-number-value-object`,
  run under Node).
- `String(v, …)` called with no new target (ECMA-262, "String ( value )") is
  `""` of no argument, SymbolDescriptiveString of a symbol, and ToString of
  any other first argument, which runs an object's `Symbol.toPrimitive`,
  `toString` or `valueOf`; it ignores the rest and reads no receiver. It is
  stated at a primitive: $`(\mathsf{Prim},\ \ldots\mathtt{unknown})\Rightarrow\mathtt{string}`$,
  a value too (`xs.map(String)`; `string-value`; `invalid-string-value-object`,
  run under Node). A global whose entries state no value, such as `BigInt`,
  is refused as one (`library-global-value-unreviewed`).
- `parseInt(s, r)`, `Math.abs(x)` and `Math.ceil(x)` convert a string and
  numbers, primitives no conversion code runs on, and write nothing: as
  declared, within the empty footprint (`library-parse-int`,
  `library-math-abs`, `library-math-ceil`). No argument of their
  parameter types converts by code.
- `Math.random()` reads no argument and writes no location a program
  reaches: as declared, within the empty footprint (`library-math-random`).
- `Object.freeze(o)` of an ordinary object makes every own property
  non-writable and non-configurable and the object non-extensible, runs no
  code and returns `o` (ECMA-262, SetIntegrityLevel); a later write to it,
  or a key added to it, throws, which no write of the model does. It is
  admitted of an object literal written as its argument whose members are
  named fields `k: e` or `k`, `k` an identifier or a string other than
  `__proto__`, and refused of anything else
  ([refusal index](SOURCE-FRAGMENT.md#fragment-boundary)). The call is one
  of the intrinsic for the fields' names $`k_1,\ldots,k_n`$:

  $`\%\mathsf{Freeze}{:}[k_1,\ldots,k_n]\%:\forall A_1\ldots A_n.\ \{\mathtt{readonly}\ k_i{:}A_i\}_i\Rightarrow\{\mathtt{readonly}\ k_i{:}A_i\}_i`$,
  stating no effect. No other reference to the literal exists, so the
  call's result is the only one to the frozen object, and it holds the
  fields as readonly views: a writable field is covered only by a writable
  field, a writable index by no record without an own-key bound, and a
  key-adding write and `Object.assign` copy only onto an allocation its
  holders own, which a call's result is not. So no write the program makes
  reaches the frozen object (`object-freeze-literal`;
  `invalid-object-freeze-writable-alias`,
  `invalid-object-freeze-writable-parameter`,
  `invalid-object-freeze-key-add`, `invalid-object-freeze-assign-target`,
  run under Node). An object a field holds is not frozen.
- `Math.max(…)`, `Math.min(…)`, `String.fromCodePoint(…)` and
  `String.fromCharCode(…)` convert each argument by ToNumber, which runs an
  object's `Symbol.toPrimitive`, `valueOf` or `toString`. Every argument is stated at the primitives,
  $`\mathsf{Prim}=\mathtt{null}\mid\mathtt{undefined}\mid\mathtt{boolean}\mid\mathtt{number}\mid\mathtt{string}\mid\mathtt{bigint}\mid\mathtt{symbol}`$,
  so a hole a spread reads is admitted and an object is not
  (`invalid-math-max-object`, `invalid-math-min-spread-object`,
  `invalid-from-code-point-object`, `invalid-from-char-code-object`):
  $`(\ldots\mathsf{Prim})\Rightarrow\mathtt{number}`$ and
  $`(\ldots\mathsf{Prim})\Rightarrow\mathtt{string}`$. A symbol or a bigint
  throws a TypeError and an invalid code point a RangeError, outcomes; the
  number may be `NaN`, `Infinity` or `-Infinity`.

#### `Object` and `Reflect`

- `Object.fromEntries(entries)` steps its argument's iterator, reads each
  element's 0 and 1, converts the key and defines it on a fresh object. Over
  an array the iterator is the host's and a pair an array of data, so it runs
  no code and writes nothing it did not allocate:
  $`\forall T.\ (\mathtt{readonly}\ (\mathtt{readonly}\ [\mathtt{string},\ T])[\,])\Rightarrow\{[k:\mathtt{string}]:T\}`$,
  within the empty footprint (`object-from-entries`). A program's iterable
  runs its iterator (`invalid-from-entries-iterable`, run under Node).
- `Object.getOwnPropertyDescriptor(o, k)` converts `o` by ToObject (a
  TypeError of `null` or `undefined`) and `k` by ToPropertyKey, which runs an
  object's `toString` (`invalid-own-property-descriptor-key-object`), then
  looks the key up by `o`'s [[GetOwnProperty]], which calls no getter. That
  lookup runs no code on the objects a program holds, none of which is a
  proxy ([trust surface](DESIGN.md#trust-surface)). The result is
  `undefined` or a fresh descriptor, nothing known of what it holds
  (`invalid-own-property-descriptor-value`). Its object is a non-host value
  ($`\mathsf{NonHost}`$ below), since a host object's own fields are the
  package's internal ones:

```math
\mathtt{getOwnPropertyDescriptor}:(\mathsf{NonHost},\ \mathtt{string}\mid\mathtt{number}\mid\mathtt{symbol})\Rightarrow\mathsf{Desc}\mid\mathtt{undefined}
```

```math
\mathsf{Desc}=\{\mathtt{readonly}\ \mathit{configurable}:\mathtt{boolean};\ \mathtt{readonly}\ \mathit{enumerable}:\mathtt{boolean};\ \mathtt{readonly}\ \mathit{value}?:\mathtt{unknown};\ \mathtt{readonly}\ \mathit{writable}?:\mathtt{boolean};\ \mathtt{readonly}\ \mathit{get}?:\mathtt{unknown};\ \mathtt{readonly}\ \mathit{set}?:\mathtt{unknown}\}
```
- The descriptor's `value` read only as a string admits any operand. Where
  `Object.getOwnPropertyDescriptor(o, k)?.value` initializes a `const`,
  unannotated or annotated `unknown`, that no export names, and each
  reference of the constant is the operand of `typeof … === "string"` or
  `!==` (either side) or a read TypeScript types `string`, which at that
  declared type only those tests' narrowing gives, the initializer is a
  call of $`\%\mathsf{OwnString}\%`$ at `o` and `k` (`ownStringRead` in
  `declaration-graph.mts`). The intrinsic is the string `o` holds at its
  own key `k` as a data property, and `undefined` otherwise: at every
  admitted reference it agrees with the descriptor's value, so the
  constant's reading is unchanged. Its steps are the descriptor's: ToObject
  (a TypeError of `null` or `undefined`), the key's conversion and
  [[GetOwnProperty]], which calls no getter and runs no code on any object,
  a host object's included, as `Object.hasOwn` reads it, no object being a
  proxy. Of the field's value only a string reaches the program, which
  holds none of a host package's heap, so a host object is admitted
  (`caught-message`). A constant read any other way, or declared at another
  type, keeps the call's contract above
  (`invalid-caught-message-declared`, run under Node: an `Error`-derived
  object's `message` is a number):

```math
\%\mathsf{OwnString}\%:(\mathtt{unknown},\ \mathtt{string}\mid\mathtt{number}\mid\mathtt{symbol})\Rightarrow_{\emptyset}\mathtt{string}\mid\mathtt{undefined}
```
- `Object.getOwnPropertyDescriptors(o)` converts `o` by ToObject, then
  takes its own keys by [[OwnPropertyKeys]] and looks each up by
  [[GetOwnProperty]]: neither calls a getter or runs code on the objects a
  program holds. Each descriptor is a fresh object, defined at its key on a
  fresh object, a `"__proto__"` key among them. The result is a dictionary
  of descriptors at the string keys, nothing known of what each holds, its
  index and the descriptors' fields writable, since no other reference
  holds them (`object-own-property-descriptors`); a key the record's type
  does not state may be owned at another type
  (`invalid-own-property-descriptors-value`, run under Node). Its object
  is a $`\mathsf{NonHost}`$ value, as above, and $`\mathsf{Desc}^{w}`$ is
  $`\mathsf{Desc}`$ with every field writable:

```math
\mathtt{getOwnPropertyDescriptors}:(\mathsf{NonHost})\Rightarrow\{[k:\mathtt{string}]:\mathsf{Desc}^{w}\}
```
- `Object.hasOwn(o, k)` converts `o` by ToObject, an object here, and `k` by
  ToPropertyKey, which runs no code of a string, number or symbol, then looks
  the key up by [[GetOwnProperty]], which runs no code (no object is a
  proxy): as declared, $`(\mathtt{object},\ \mathtt{string}\mid\mathtt{number}\mid\mathtt{symbol})\Rightarrow\mathtt{boolean}`$,
  within the empty footprint. No value of `o` reaches the program, so a host
  object is admitted (`object-has-own`).
- `Object.values(o)` and `Object.entries(o)` at TypeScript's `{}` overload
  read the values of `o`'s own enumerable string keys:
  $`(\mathsf{NonHost})\Rightarrow\mathtt{unknown}[]`$ and
  $`(\mathsf{NonHost})\Rightarrow[\mathtt{string},\mathtt{unknown}][]`$;
  their dictionary overloads are stated at a dictionary.

$`\mathsf{NonHost}`$, which no source spells, is every value but a host
object ([restricted values](HOST-FAMILIES.md#restricted-values)): the
primitives, the callables and the objects owning no `[[host]]`, the record
clause bounded by an exclusion of that key. A type is below it when each of
its clauses is: an object clause names an invariant field or an index, or
bounds its own keys without the key (`CoversBounds`), so `{ a: number }` is
below it and `{ readonly a: number }`, `object` and `unknown` are not
(`host-exclusion-reflection`, `object-values-readonly-refused`).

`Object.getPrototypeOf(o)` names built-in prototypes, among them
`Array.prototype`, an array that does not inherit from `Array.prototype`.
The `isArray` test stands for both `Array.isArray` and `instanceof Array`
because no program can name such an array, so the call is read only
compared with `Object.prototype`, by `===` or `!==`, either side, the two
references to the global `Object`: the comparison is a call of
$`\%\mathsf{PrototypeIs}{:}\mathsf{Object}\%`$ at `o` (`prototypeTest` in
`library-globals.mts`), negated for `!==`. ECMA-262 fixes the
[[GetPrototypeOf]] and [[OwnPropertyKeys]] of an ordinary object and of
each of its exotic objects (arrays, typed arrays, `String` objects,
arguments objects, module namespaces, bound functions), none of which runs
code, the proxy's excepted, which no object is
([trust surface](DESIGN.md#trust-surface)). A host exotic object's internal
methods are the host's to define (a V8 interceptor's enumerator is code),
so both intrinsics take $`\mathsf{NonHost}`$, every value but a host object
(above): an `object` is refused at the argument
(`invalid-prototype-is-object-host`, `invalid-reflect-own-keys-object`).
That a value no host family types is an ordinary or ECMAScript exotic
object holds of every object the program makes; of one external code
supplies at a program type it is the assumption
`Object.getOwnPropertyDescriptor` and `Object.values` make at the same
parameter. ToObject throws a TypeError of `null` or `undefined` and wraps
another primitive, `Object.prototype` is a non-writable, non-configurable
property of the untampered `Object`, and the identity test converts
nothing; the Boolean hands the program no prototype and narrows nothing
(`prototype-is-object`). A loose `==` is no test
(`invalid-prototype-loose-equality`), and a local named `Object` is no
global (`prototype-shadowed-object`):

```math
\mathtt{Object.getPrototypeOf}(e)\ \texttt{===}\ \mathtt{Object.prototype}\;\equiv\;\%\mathsf{PrototypeIs}{:}\mathsf{Object}\%(e)
\qquad
\%\mathsf{PrototypeIs}{:}\mathsf{Object}\%:(\mathsf{NonHost})\Rightarrow_{\emptyset}\mathtt{boolean}
```

Any other read of `Object.getPrototypeOf` is refused
(`invalid-get-prototype-array-prototype`; under Node its write lands in
`Array.prototype`, where every array's holes read it). The compiler client's
prototype is inspected through [its audited boundary](SOURCE-REWRITES.md#the-compiler-clients-prototype).

`Reflect.apply(target, receiver, list)` extends the receiver application
lowering used for `Function.prototype.apply`: it evaluates the three
arguments in order, reads the array list's length and indices, and invokes
the target with that receiver and those actuals. The target's checked
signature supplies its result and effect; the broad library overload's
`any` result supplies no claim. A fresh array literal's elements are the
actuals directly. A tuple supplies its required positions; an array of
unknown length requires a target taking only a rest parameter, whose
contract admits `undefined` at a hole. `Reflect.apply` requires an array
list; a missing, null or undefined list is refused. The `requiredList`
[field](FRAGMENT-FORMAT.md#expression-closures-and-calls) carries this distinction; the
closed-expression lowering refuses an array list.

This is audited against [ECMA-262](REFERENCES.md#ecma-262), `Reflect.apply`,
`CreateListFromArrayLike` and `Call`. It reads no `apply` property of the
target, so a function parameter is admitted without the local confinement
required for `f.apply`. Array reads use the existing array contracts;
standard `Reflect.apply` is untampered. `reflect-apply` checks receiver and
list order, and `invalid-reflect-apply-arguments` and
`invalid-reflect-apply-receiver` return a number at a promised string under
Node and are refused by the verifier.

`Reflect` is a namespace, whose functions are no annotated variable's
members: each use calls one, whose overload an entry of the overlay states
as an intrinsic or receiver application; a function read as a value or by a computed key is refused
(`invalid-reflect-extracted`, `invalid-reflect-computed`), as is a function
no entry reviews (`invalid-reflect-unreviewed`). `Reflect.ownKeys(o)` of a
$`\mathsf{NonHost}`$ value is its [[OwnPropertyKeys]], which runs no code
there (above), as a fresh dense array (CreateArrayFromList) of strings and
symbols; no value of the object is read, and a primitive is a TypeError
(`reflect-own-keys`):

```math
\mathtt{Reflect.ownKeys}(e)\;\equiv\;\%\mathsf{OwnKeys}\%(e)
\qquad
\%\mathsf{OwnKeys}\%:(\mathsf{NonHost})\Rightarrow_{\emptyset}(\mathtt{string}\mid\mathtt{symbol})[\,]
```

`Reflect.get(o, k)` runs [[Get]], which calls an accessor's getter, code no
type of `o` states: it is refused (`invalid-reflect-get-array`, run under
Node), as is every other function of `Reflect` (`invalid-reflect-unreviewed`,
`invalid-reflect-method-replaced`, run under Node).

#### `Array.from`, `RegExp` and `instanceof Error`

- `Array.from(xs)` of an array copies it through the host's iterator,
  a hole read as `undefined`: $`\forall T.\ (\mathtt{readonly}\ T[\,])\Rightarrow T[\,]`$
  within the empty footprint (`array-from-copy`). Of a string it steps
  `String.prototype[Symbol.iterator]`, which yields each code point as a
  string of one or two code units, a lone surrogate as itself, and runs no
  client code: $`(\mathtt{string})\Rightarrow\mathtt{string}[\,]`$ within the
  empty footprint; with a callback, $`\forall U.\ (\mathtt{string},\ (\mathtt{string},\ \mathtt{number})\Rightarrow U)\Rightarrow U[\,]`$,
  stating no effect, as the callback may write anything but the string, a
  primitive (`array-from-string`; `invalid-array-from-string-callback`, run
  under Node). Both are stated at each declaration of `Array.from` as
  overloads beside the array's and the record's. `Array.from(items, f)` of a
  length record steps the record's own iterator where it holds one, client
  code yielding any value, and else reads its length and indices; it calls
  `f` with each value and index:
  $`\forall U.\ (\{\mathtt{readonly}\ \mathit{length}:\mathtt{number}\},\ (\mathtt{unknown},\ \mathtt{number})\Rightarrow U)\Rightarrow U[\,]`$,
  stating no effect (`array-from-length`; `invalid-array-from-iterator`, run
  under Node).
- `new RegExp(p, flags)` of strings compiles a pattern known only at run
  time, a SyntaxError where it or the flags are invalid: the structural regex
  $`⟦\mathtt{RegExp}⟧=P(\Sigma_\top)`$ ([regular expressions](#regular-expressions)),
  no native mark stated, within the empty footprint on its throw too
  (`regexp-dynamic`). A regex pattern would be read by its `Symbol.match`,
  `source` and `flags` (`invalid-regexp-object-pattern`, run under Node).
- `e instanceof Error` walks `e`'s prototype chain for `Error.prototype`,
  which runs no code, `Error` owning no `[Symbol.hasInstance]`:
  `%InstanceOf:Error%`, $`(\mathtt{unknown})\Rightarrow\mathtt{boolean}`$ within
  the empty footprint (`instanceof-error`, run under Node). It narrows
  nothing: an object gets `Error.prototype` without `Error` constructing it,
  its `message` any value (`invalid-instanceof-error-message`, run under
  Node; [source fragment](SOURCE-FRAGMENT.md)).
- `e instanceof Map` and `e instanceof Set` walk `e`'s prototype chain for
  `Map.prototype` or `Set.prototype` alike, neither owning a
  `[Symbol.hasInstance]`: `%InstanceOf:Map%` and `%InstanceOf:Set%`, each a
  guard of its operand within the empty footprint, promising the
  collection's [reading view](#collections-passing-instanceof).

#### Collections passing `instanceof`

The reading view of a host collection states the members of the `Set<T>`
and `Map<K, V>` overlays ([prototype contracts](#prototype-contracts)) that
take no element, each as the overlay reads it:

```math
\begin{aligned}
\mathsf{NativeSetView}(T) &= \{\texttt{[Symbol.toStringTag]}:\mathtt{string},\ \mathit{size}:\mathtt{number},\
  \texttt{[Symbol.iterator]}:()\Rightarrow_\emptyset I(T),\\
&\qquad \mathit{keys},\mathit{values}:()\Rightarrow_\emptyset I(T),\ \mathit{entries}:()\Rightarrow_\emptyset I([T,T])\}\\
\mathsf{NativeMapView}(K,V) &= \{\texttt{[Symbol.toStringTag]}:\mathtt{string},\ \mathit{size}:\mathtt{number},\
  \texttt{[Symbol.iterator]},\mathit{entries}:()\Rightarrow_\emptyset I([K,V]),\\
&\qquad \mathit{keys}:()\Rightarrow_\emptyset I(K),\ \mathit{values}:()\Rightarrow_\emptyset I(V)\}
\end{aligned}
```

with $`I(E)`$ the native collection iterator over $`E`$ and each member
host-relative, within the empty footprint. A `Set<T>` is a
$`\mathsf{NativeSetView}(T)`$ and a `Map<K, V>` a
$`\mathsf{NativeMapView}(K,V)`$, by width; a view states no member taking an
element, so it is covariant, and nothing is written through it. Only a host
collection meets it, as only one meets the overlay: no source value is an
$`I(E)`$, and no object the fragment builds writes `Symbol.toStringTag`.
`%Iterate:Set%` and `%Iterate:Map%` take the collection at its view, and so
do their spreads. The two tests are guards
([user-defined guards](SOURCE-ELABORATION.md#user-defined-guards)):

```math
\frac{\Gamma\vdash e:A}
     {e\ \mathtt{instanceof}\ \mathtt{Map}\;\equiv\;\texttt{\%InstanceOf:Map\%}(e)
       :\ (\mathtt{unknown})\Rightarrow_\emptyset\mathtt{boolean}\ \land\
         (\mathtt{unknown})\Rightarrow_\emptyset\mathsf{NativeMapView}(\mathtt{unknown},\mathtt{unknown})\,[\mathsf{guards}\ 0]}\ \textsf{instanceof-map}
```

and `instanceof Set` alike at $`\mathsf{NativeSetView}(\mathtt{unknown})`$
(`blocker-instanceof-map-set`, run under Node). The test reads the contents
at `unknown` and establishes no element contract to write by: a write
through it would break a caller's `Map<string, number>`
(`invalid-instanceof-map-write`, run under Node: a string in it).

**What it assumes.** The promise is a host assumption, beyond the
non-tampering of standard objects: a value passing the realm's
`instanceof Map` (`instanceof Set`) is a host collection, with the internal
slots its methods read and the standard, unshadowed `[Symbol.iterator]`,
`keys`, `values`, `entries`, `size` and `[Symbol.toStringTag]` of
`Map.prototype` (`Set.prototype`), and external code keeps it so
([trust surface](DESIGN.md#trust-surface)). The prototype on a chain is no
evidence of the slots: an object made by `Object.create(Map.prototype)`
passes the test and the native `get` throws on it
(`invalid-instanceof-map-counterfeit`, run under Node), and the Set
analogue's `has` (`invalid-instanceof-set-counterfeit`); an instance of a
class extending `Map` passes it with its own `[Symbol.iterator]`, which the
loop calls (`invalid-instanceof-map-shadowed`, run under Node). The fragment
makes neither: `Object.create` and a class extending a library class are
refused ([source fragment](SOURCE-FRAGMENT.md)). Implementation:
`nativeCollectionViewDefinition` (`tools/array-prototype.mts`),
`instanceOfCollection` (`tools/intrinsics.mts`).

#### Node's timers, `structuredClone` and `console`

- Node's `clearTimeout(t)` of any value cancels a timer by id or by object,
  reading and writing an object's `_onTimeout`, which may be an accessor:
  $`(\mathtt{unknown})\Rightarrow\mathtt{undefined}`$, stating no effect.
- Node's `setTimeout(f, ms)`, a function merged with a namespace, schedules
  `f`, which the host calls with no argument between synchronous jobs, as it
  calls a listener ([Node's process](#nodes-process)), and returns a timer
  read at no member:
  $`(()\Rightarrow\mathtt{unknown},\ \mathtt{number}^?)\Rightarrow\mathtt{unknown}`$,
  stating no effect, scheduling running the asynchronous-resource hooks other
  code installed (`node-set-timeout`). Arguments after the delay reach the
  callback and are refused (`invalid-node-set-timeout-parameter`, run under
  Node).
- Node's `structuredClone(v)` reads every own enumerable property of `v` by
  [[Get]], so a getter runs, and builds a copy of data properties whose
  prototypes are `Object.prototype`. A getter may change what the traversal
  reads after it, so the copy of a `JsonValue` may be none: one beside a JSON
  array's elements popping the enclosing array leaves a hole in its copy
  (`invalid-node-structured-clone-result`, run under Node). It is stated at
  any value, $`(\mathtt{unknown})\Rightarrow\mathtt{unknown}`$, stating no
  effect (`node-structured-clone`; `invalid-node-structured-clone-preserving`,
  run under Node: such a getter shrinks a mapped array); a transfer list is
  not admitted. `JSON.stringify` of such an array serializes its elements
  alone (run under Node).
- `console.log(…)` formats every reachable key of an object argument; its
  arguments are stated at $`\mathsf{Prim}`$:
  $`(\ldots\mathsf{Prim})\Rightarrow\mathtt{undefined}`$
  (`console-log-object-refused`).

#### Node's `Buffer` and `TextDecoder`

Each entry names the declaration of each pinned `@types/node` installation
where the two differ; the types are the
[stated library types](#stated-library-types).

- `Buffer.from(s)` of a string returns a fresh `Buffer` (Node's
  `lib/buffer.js`, `fromString`), its own memory or a view into the
  module's pool, into which it writes the string's UTF-8 bytes through
  `utf8Write`, a writable property of `Buffer.prototype` other code may
  replace, whose answer also sets the view's length and the pool's next
  offset; so its contents, and its memory's disjointness from the pool's
  other views, hold only where that method is Node's own. The stated type
  depends on neither: $`(\mathtt{string})\Rightarrow\mathit{Buffer}`$.
  It reads `Buffer.poolSize`, a writable property other code may make a
  getter, to choose, so it states no effect.
- `Buffer.compare(a, b)` checks that each is a `Uint8Array` by its internal
  slots, throwing otherwise, and compares the bytes in the native layer:
  $`(\mathit{Uint8Array},\ \mathit{Uint8Array})\Rightarrow\texttt{-1}\mid\texttt{0}\mid\texttt{1}`$,
  within the empty footprint (`node-bytes-buffer`).
- `TextDecoder`, whose declared type is a conditional type over
  `globalThis`, is read through an entry naming the variable's declaration
  (`constructs`): its type is not read, and every reference to the global
  is a `new` expression of at most as many arguments as the entry's
  statement, read at that construct signature:

```math
\frac{\omega\in\Omega\quad \omega.\mathit{global}=x\quad \omega.\mathit{text}=\mathsf{text}(d_x)\quad
      \omega.\mathit{constructs}=(\vec P)\Rightarrow R\quad
      \text{every use of}\ x\ \text{is}\ \mathtt{new}\ x(\vec a),\ |\vec a|\le|\vec P|}
     {\Gamma(x)=\mathsf{new}(\vec P)\Rightarrow R}\ \textsf{library-global-constructs}
```

with $`d_x`$ the variable's one declaration. `new TextDecoder(label,
options)` (Node's `lib/internal/encoding.js`, the ICU build) converts the
label by a template, a string's own value, throws where it names no
supported encoding, and reads the options' `fatal` and `ignoreBOM` by
ToBoolean:
$`(\mathtt{string}^?,\ \{\mathtt{fatal}^?,\ \mathtt{ignoreBOM}^?\colon\mathtt{boolean}\mid\mathtt{undefined}\}^?)\Rightarrow\mathit{TextDecoder}`$,
with $`\mathit{TextDecoder}=\{\mathtt{decode}\colon(\mathit{Uint8Array})\Rightarrow\mathtt{string}\}`$,
`decode` a method of `TextDecoder.prototype`. The construction writes the
decoder's state to symbol-keyed properties of the fresh decoder, which a
setter other code defines on `TextDecoder.prototype` would intercept, and
`decode` reads them and, outside UTF-8 and windows-1252, the `encoding`
getter other code may replace: neither states an effect. `decode` of a
view gives its text; a malformed byte at `fatal: true`, and a value of the
view's type that is no view, throw (`node-bytes-text-decoder`, run under
Node). That `decode` finds Node's method and that reading it runs no code
rest on a host assumption ([trust surface](DESIGN.md#trust-surface)): every
`TextDecoder` keeps `TextDecoder.prototype` as its prototype and owns no
`decode`, and `TextDecoder.prototype` holds `decode` as an own data
property, Node's own function, throughout execution. A replaced `decode`
answers what it returns (`invalid-node-bytes-decoder-replaced`, run under
Node: a number); the program reads the global only to construct it, so it
reaches no prototype. The standard library's DOM, which declares
`TextDecoder` too, gives the global a second declaration, which the entry
does not review.

#### Node's `URL`

**Audited against:** `@types/node` 22.20.2 and 22.10.7; host behaviour
from Node 25.2.1's `lib/internal/url.js` and probes run under Node 25.2.1
(2026-10-29).

`URL` is read only as a constructor through `library-global-constructs`.
Its contract admits string inputs and an optional string base:
$`(\mathtt{string},\ \mathtt{string}^?)\Rightarrow_\emptyset\mathit{URL}`$.
The native parser writes the fresh object's private fields. The empty
footprint holds on normal return; error construction may run
`Error.prepareStackTrace` on a throw.

The [stated library type](#stated-library-types) is opaque:
$`\mathit{URL}=\mathsf{host}_u\,\{\}`$.
Property reads, writes and URL-valued bases are refused. A URL the program
holds may reach other code, passed at the declared `URL`, at an `unknown`
parameter or returned at `unknown`, and that code may give it an own
member or give its search parameters an own `toString`,
`Symbol.toPrimitive` or `size`, without replacing any standard method: a
later read of `href` or a conversion to a string then runs that code
(`invalid-node-url-fresh-escape`, `invalid-node-url-unknown-parameter`,
`invalid-node-url-unknown-return`, run under Node: a getter answering a
number), and so do `fileURLToPath`'s reads of `auth`, `path`, `hostname`
and `pathname` (`invalid-node-url-input`, run under Node). `href` is a
setter too, which parses again (`invalid-node-url-write`,
`invalid-node-url-write-only`, run under Node).

One read of a URL is admitted: `href` written directly on the expression
that makes it, `new URL(e₁, e₂).href` or `pathToFileURL(e).href`, a plain
read (no optional chain, no write, update, `delete` or call of it). Between
the construction and the read no code but Node's runs: Node's construction
publishes the URL to no other code (no diagnostics channel), so no code has
given it an own member or read its search parameters, and the getter
`URL.prototype` holds serializes the parsed record. The read is a call of
an intrinsic at the construction's arguments, the entry's `serialized`
(`library-globals.mts`, `library-modules.mts`):

```math
\mathtt{new\ URL}(e_1, e_2)\mathtt{.href}\;\equiv\;\%\mathsf{URL{:}href}\%(e_1, e_2)
\qquad
\%\mathsf{URL{:}href}\%:(\mathtt{string},\ \mathtt{string}^?)\Rightarrow_\emptyset\mathtt{string}
```

```math
\mathtt{pathToFileURL}(e)\mathtt{.href}\;\equiv\;\%\mathsf{PathToFileURL{:}href}\%(e)
\qquad
\%\mathsf{PathToFileURL{:}href}\%:(\mathtt{string})\Rightarrow\mathtt{string}
```

The first keeps the constructor's empty footprint on normal return; the
second states no effect, as `pathToFileURL`'s entry does (it reads
`process.cwd()`, a writable property). That the receiver is the
construction itself is checked by the front end, which writes the call; the
same URL bound to a name, passed on or parenthesized is read as before and
refused (`node-url-fresh-href`, `invalid-node-url-fresh-escape`). The front
end's own reads are of this form
([URLs as strings](SOURCE-REWRITES.md#urls-as-strings)). The approved policy is that standard objects
and prototypes are not tampered with ([trust surface](DESIGN.md#trust-surface)):
`URL.prototype` and `Object.prototype` hold their standard properties.
`tests/node-runs.mts` executes the serialization and own-getter
counterexamples and the fixtures `blocker-node-url-import`,
`node-url-strings`, `node-url-fresh-href`, `invalid-node-url-write`, `invalid-node-url-spread`,
`invalid-node-url-member`, `invalid-node-url-program-object` and
`invalid-node-url-replaced`.

### `JSON` and `Error`

Overloads stated alike are one signature. A statement may name a library
interface (`Set<T>`, read through [its overlay](#prototype-contracts)) or a
declaration no library has, which joins the document with the entry:

```math
\mathsf{JsonValue}=\mathsf{null}\mid\mathsf{boolean}\mid\mathsf{number}\mid\mathsf{string}\mid\mathsf{readonly}\ (\mathsf{JsonValue}\mid\mathsf{undefined})[\,]\mid\{\mathsf{readonly}\ [k:\mathsf{string}]:\mathsf{JsonValue}\}
```

(`JSON.stringify`'s parameter), and

```math
\mathsf{ParsedJson}=\mathsf{null}\mid\mathsf{boolean}\mid\mathsf{number}\mid\mathsf{string}\mid\mathsf{ParsedJson}[\,]\mid\{[k:\mathsf{string}]:\mathsf{ParsedJson}\}
```

(`JSON.parse`'s result). [ECMA-262](REFERENCES.md#ecma-262)'s `JSON.parse`
without a reviver builds a fresh array (ArrayCreate) with an element at every
index below its length for each JSON array, and a fresh ordinary object of
`%Object.prototype%` for each JSON object, defining every member as an own
data property (CreateDataProperty: a `"__proto__"` member becomes an own key
and sets no prototype); InternalizeJSONProperty runs only with a reviver. In
the model an object of a dictionary type owns no prototype key, and a read at
a key `Object.prototype` may provide is refused, so an ordinary object meets
the dictionary arm. The arms are writable, as the client may go on writing
what is fresh. `JSON.parse` runs no code of the client's and writes only
what it allocates, also before it throws a SyntaxError: the empty
footprint, on a throw too. A reviver is client code: the call is read with
the text only (`invalid-json-parse-reviver`). A dictionary arm is no array
(its members own no prototype key), so `Array.isArray` of a `ParsedJson`
leaves its array arm, whose `map` stays dense (`json-parse-data`).
`ParsedJson` is a `JsonValue`: each of its arms is one read-only. A
`JsonValue` array owns no `toJSON` (the arrays' own-key exclusion,
[arrays](SOURCE-MODEL.md#arrays)), inherits none (no object along its chain
holds one, a host assumption), and holds `JsonValue`s or `undefined`.
Its readable element contract admits holes. ECMA-262's SerializeJSONArray
reads each index below the captured length and writes `null` when
SerializeJSONProperty returns `undefined`; this covers both a hole and an
explicit `undefined`, recursively at every array depth
(`json-stringify-sparse`, `blocker-round-mapped-json`). Neither
`Array.prototype` nor `Object.prototype` owns a numeric key
([trust surface](DESIGN.md#trust-surface)). Root `undefined` is outside
`JsonValue`, since its serialization returns `undefined`
(`invalid-json-stringify-undefined`, run under Node). A nested array element
with a callable `toJSON` is outside this contract too
(`invalid-json-stringify-sparse-hook`, run under Node: the hook shrinks
the array visited by an enclosing `map`).
A dictionary owns no prototype key and holds `JsonValue`s at every string key
it owns, none callable: a member `JSON.parse` defines under the name
`"toJSON"`, at any depth, is JSON data, which `JSON.stringify` reads and does
not call (`json-parse-stringify-tojson-member`, run under Node). At a `JsonValue`, `JSON.stringify` reads own data properties,
calls no `toJSON` and no getter, and allocates its string, so it returns a
string and states the empty footprint, on a throw too (a cycle); so does `Error`
at a string message, which it stores without conversion code
([exceptional footprints](SOURCE-ELABORATION.md#exceptional-footprints);
`map-stable-json-error`,
`json-stringify-recursive`, `json-stringify-arrays`). A record a declaration
types by its fields (an interface, a type literal) is no `JsonValue`: a
record is open, and nothing bounds the own string keys it does not declare,
one of which may hold a `toJSON` (`invalid-json-stringify-record`, run under
Node: `JSON.stringify` of it returns the hook's `undefined`). An
array owning a `toJSON` is no array (`invalid-array-own-tojson`, run under
Node: `JSON.stringify` of it returns the hook's `undefined`); neither an
inherited declaration (`invalid-array-tojson-inherited`), a write
(`invalid-array-tojson-write`), an alias (`invalid-array-tojson-alias`,
`invalid-array-tojson-view`) nor
an element at `unknown` (`invalid-json-stringify-hidden-hook`) gives one.
A declaration merging a `toJSON` into the global `Array`, `ReadonlyArray` or
`Object` states a hook the host's prototypes do not hold: a merged member is
admitted only where the overlay reviews it at the same contract ([source fragment](SOURCE-FRAGMENT.md)), so a unit an
array reaches under such a merge is refused at the first array type the
reader meets (`invalid-merged-array-param`,
`invalid-merged-readonly-array-param`); in `invalid-merged-array-callback`
and `invalid-merged-readonly-array-callback`, whose callbacks take an array
by context, that is a written annotation.
`JSON.stringify` is read with a replacer that
is `null`, absent or a list of keys (primitive numbers and strings, read by
length and index), and an indent that is a primitive number or string:
none runs code (`json-stringify-space`). A boxed key or indent would run
its `toString` or `valueOf` (`invalid-json-stringify-boxed-key`,
`invalid-json-stringify-boxed-space`, run under Node). A `toJSON` hook and a
replacer function run code of the client's, which may write what a footprint
excludes (`invalid-json-stringify-tojson`, `invalid-json-stringify-replacer`,
each run under Node).

`Error` is read with a message and options. After converting the message,
[ECMA-262](REFERENCES.md#ecma-262)'s `Error ( message [ , options ] )` runs
InstallErrorCause: where the options are an object and `HasProperty(options,
"cause")` holds, it reads `Get(options, "cause")` and defines the value as the
error's own non-enumerable data property `cause`. The options are stated at

```math
\mathsf{ErrorOptions}=\{\mathsf{readonly}\ \mathit{cause}?:\mathsf{unknown}\}\mid\mathsf{undefined}
```

and the construct, called or with `new`, at

```math
\frac{\mathit{lib}(\mathtt{Error})\quad \omega\in\Omega\quad
      \omega=(\mathtt{Error},\ \cdot,\ \mathsf{text}(s),\ \mathsf{stated}\ (\mathsf{string},\ \mathsf{ErrorOptions})\Rightarrow\mathsf{Err})}
     {⟦s⟧_\Omega=\mathsf{new}(\mathsf{string},\ \mathsf{ErrorOptions})\Rightarrow\mathsf{Err}\quad\text{within}\ \varnothing,\ \text{on a throw too}}\ \textsf{library-error-options}
```

with $`\mathsf{Err}`$ the object owning neither `message` nor `name`, whose link
holds both, strings
([a class extending `Error`](SOURCE-ELABORATION.md#a-class-extending-error)):

```math
\mathsf{Err}=\{\texttt{[[proto]]}{:}\,\{\mathsf{readonly}\ \mathit{message}:\mathsf{string};\ \mathsf{readonly}\ \mathit{name}:\mathsf{string}\}\}\ \text{owning neither key}
```
Neither step runs code at $`\mathsf{ErrorOptions}`$: no object is a proxy, a
value meeting a stated field holds it as a data property, and
`Object.prototype` owns no `cause` ([trust surface](DESIGN.md#trust-surface)).
A type not stating `cause` is open at it, and no rule derives it at
$`\mathsf{ErrorOptions}`$: the object may own a getter there, which `Get` runs
(`invalid-error-options`, `invalid-error-options-spread`, run under Node). A
getter written at `cause` and a proxy are outside the fragment
(`invalid-error-options-getter`, `invalid-error-options-class-accessor`,
`invalid-error-options-proxy`, run under Node). The error's own `cause` is not stated: a read of it is refused
(`invalid-error-cause-read`), and a write of it is reserved, as `stack`'s
is ([reserved writes](SOURCE-ELABORATION.md#reserved-writes)). The host is
trusted to follow ECMA-262's description of the `Error` constructor
(`error-options`, `map-stable-json-error`).

The constructor's normal result also states `nonHostObject`, the ordinary
object arm of [host exclusion](HOST-FAMILIES.md#excluding-host-values), and
the existing `freshObject` effect: each own location belongs to the
allocation. `OrdinaryCreateFromConstructor` allocates that object before
installing its message and cause. The allocation has a fresh identity and
reaches no client code before the constructor returns. String messages and
the checked options run no client code. This contract uses the standard-object assumption
of the [trust surface](DESIGN.md#trust-surface). The library's structural
`Error` interface retains its existing contract.

The existing [merge checks](PROGRAM-TYPING.md#allocation-from-parts) validate
`Object.assign` onto a constructed target at an audited native constructor
binding whose contract allocates an unpublished identity. The standard global
`Error` is such a binding; a local or parameter of the same name has a
different declaration descriptor. Every constructor signature must also
state both `freshObject` and the empty footprint with no receiver exception.
Own-location freshness alone permits a shared object with no own keys, so it
does not establish this source requirement. In the copy,
the target's prototype value is retained and source properties are copied
in order. `blocker-prep-assign-error-value` covers called and constructed
Errors with a code field and an optional cause. A constructor returning a
shared object needs a stronger contract (`invalid-assign-constructor-alias`).
`ObjectMerge.merge_values_safe` proves the modeled copy's safety; the native
allocation and its correspondence with this lowering are source-contract
obligations under the stated trust.

`TypeError` is read, with `new`, at the same two statements: ECMA-262's
`NativeError ( message [ , options ] )` runs `Error`'s steps, with
`TypeError.prototype` as the error's prototype, an object whose `name` is
`"TypeError"` and which inherits from `Error.prototype`. So the construct
is stated at $`\mathsf{Err}`$ too, within $`\varnothing`$, on a throw too:

```math
\frac{\mathit{lib}(\mathtt{TypeError})\quad \omega\in\Omega\quad
      \omega=(\mathtt{TypeError},\ \cdot,\ \mathsf{text}(s),\ \mathsf{stated}\ (\mathsf{string},\ \mathsf{ErrorOptions})\Rightarrow\mathsf{Err})}
     {⟦s⟧_\Omega=\mathsf{new}(\mathsf{string},\ \mathsf{ErrorOptions})\Rightarrow\mathsf{Err}\quad\text{within}\ \varnothing,\ \text{on a throw too}}\ \textsf{library-type-error}
```

and at the message alone, $`(\mathsf{string})\Rightarrow\mathsf{Err}`$
(`type-error-construct`, run under Node); options typed without `cause` are
refused as `Error`'s are (`invalid-type-error-options`, run under Node).
The host is trusted to follow ECMA-262's description of the `TypeError`
constructor, as of `Error`'s;
`TypeError` called without `new`, `instanceof TypeError` and
`AggregateError` have no entry.

The library's `Error` interface, its members declared as reviewed, is read as
what `Error` constructs:

```math
\frac{\mathit{lib}(\mathtt{Error})\quad \mathsf{members}(\mathtt{Error})\subseteq\{\mathit{name}:\mathsf{string},\ \mathit{message}:\mathsf{string},\ \mathit{stack}?:\mathsf{string},\ \mathit{cause}?:\mathsf{unknown}\}}
     {⟦\mathtt{Error}⟧=\mathsf{Err}}\ \textsf{library-error-type}
```

so an error the program builds, by `Error` or by a class extending it, meets
it (`error-name`, `blocker-error-options-return`,
`blocker-error-super-options-return`, run under Node). By
[ECMA-262](REFERENCES.md#ecma-262), `Error.prototype.name` is a data property
whose initial value is `"Error"`, writable, not enumerable and configurable,
as every data property of a built-in prototype is; each NativeError's
prototype and `AggregateError.prototype` holds its constructor's name the
same way. An error `Error` constructs owns no `name` and reads this one; so
does an instance of a class extending `Error`, whose prototype holds no `name`
(the parser refuses a member, a parameter property and a constructor's
`this.name = e` of that name, `invalid-error-subclass-name-field`,
`invalid-error-subclass-name-write`, run under Node). The model states the
name on the error's link, `"Error"` where a class constructs it, so a read,
a destructuring and `in` find it and neither a copy nor `Object.keys` takes
it, as in JavaScript. A write of `name` onto an error creates an own
enumerable property in JavaScript, as a write does in the model, so `name`
is no reserved key; the calculus refuses the write at $`\mathsf{Err}`$, which
excludes an own `name`, and an error meets no record owning `name`
(`invalid-error-name-write`, run under Node: a number written over it). A
copy of an error lacks `name` (`invalid-error-name-spread`, run under Node).
The engine's `stack`, an own accessor in V8 whose getter may run
`Error.prepareStackTrace`, and the `cause` the options give are left
unstated: a read of either is refused. `cause?: unknown` admits every value
an error holds or lacks. Inside the program `stack` is read only by calls
whose contracts state no footprint where they read it and nothing of
`stack` in their results: Node's `structuredClone` (an `unknown` result),
`assert.throws` with a validation object (`void`),
`assert.ifError` of an error, which reads it as it throws, where its stated
empty footprint does not apply, and an `assert` call's failure where it
builds an `AssertionError` (observed under Node: each calls an installed
`Error.prepareStackTrace`). Every other operation reading it is refused
(`e.stack`; `console.log`, `console.error`, `String`, a template literal or
`+` of an error; `JSON.stringify`). `stack?: string` is an obligation on
the errors the program gives external code at a type stating `stack`
(TypeScript's `Error`): returned, thrown, rejected, passed to external code
or a callback, or written where such a type is stated. V8's `stack` reads a
string unless an `Error.prepareStackTrace` returns another value or code
writes another value through its setter (observed under Node: a hook
returning 5, or `e.stack = 5`, makes it a number, still not enumerable; the
source writes no `Error.prepareStackTrace` and no `stack`). The trust this reading states:
`Error.prototype` holds `name` as a data property whose value is `"Error"`
throughout execution: external code installs no accessor there and writes no
other value (`invalid-error-prototype-name-getter`, run under Node: a getter
returns a number; the source reaches neither `Object.defineProperty` nor
`Error.prototype`); an error the program gives external code at a type
stating `stack` reads a string at `stack` wherever `in` finds it, whenever external code reads it: external code installs no `Error.prepareStackTrace` returning
another value for it and writes no other value there; and a value a unit receives at `Error`, or at an
interface extending it, meets the
[caller contract](DESIGN.md#trust-surface)'s clause for errors.

### `Array.isArray` and `instanceof Array`

An entry may
read a member as a test of the
calculus (`test`), and the variable's declaration as the right operand of
`instanceof`:

```math
\frac{\mathit{lib}(\mathtt{Array})\quad \omega\in\Omega\quad
      \omega=(\mathtt{Array},\ \mathtt{isArray},\ \mathsf{text}(s),\ \mathsf{test}\ \mathsf{isArray})}
     {⟦\mathtt{Array.isArray}(e)⟧=\mathsf{test}\ \mathsf{isArray}\ ⟦e⟧}\ \textsf{library-test}
\qquad
\frac{\mathit{lib}(\mathtt{Array})\quad \omega\in\Omega\quad
      \omega=(\mathtt{Array},\ \cdot,\ \mathsf{text}(d),\ \mathsf{test}\ \mathsf{isArray})}
     {⟦e\ \mathtt{instanceof}\ \mathtt{Array}⟧=\mathsf{test}\ \mathsf{isArray}\ ⟦e⟧}\ \textsf{library-instanceof}
```

The branch rule is the tag rule on $`\mathsf{isArray}`$
([SEMANTICS](SEMANTICS.md#operational-language)); the declared guard `arg is
any[]` is not read.

### `Promise` and `Symbol`

An entry may read a member, or a construct signature, as
a call of an [intrinsic](#async-functions-and-await) stating the same step
(`intrinsic`), instantiated at each call by $`\textsf{instances}`$:

```math
\frac{\mathit{lib}(x)\quad \omega\in\Omega\quad
      \omega=(x,\ m,\ \mathsf{text}(s),\ \mathsf{intrinsic}\ \iota)}
     {⟦x.m(\vec e)⟧=\iota(⟦\vec e⟧)}\ \textsf{library-intrinsic}
\qquad
\frac{\mathit{lib}(x)\quad \omega\in\Omega\quad
      \omega=(x,\ \cdot,\ \mathsf{text}(s),\ \mathsf{intrinsic}\ \iota)\quad s\ \text{a construct signature}}
     {⟦\mathsf{new}\ x(\vec e)⟧=\iota(⟦\vec e⟧)}\ \textsf{library-construct-intrinsic}
```

`Promise.resolve(v)` is `%PromiseResolve%(v)`, `Promise.resolve()` is
`%AsyncComplete%()`, `Promise.all` is `%PromiseAll%`, `Promise.reject` is
`%PromiseReject%` and `new Promise` is `%NewPromise%`. `Symbol.for(k)` is
`%SymbolFor%(k)` and `Symbol.keyFor(s)` is `%SymbolKeyFor%(s)`, members that
read no receiver; so `Symbol` called and read through them is a value of its
call signature alone, a fresh symbol of a string or number description:

```math
\%\mathrm{SymbolFor}\%:(\mathsf{string})\Rightarrow\mathsf{symbol}
\qquad
\%\mathrm{SymbolKeyFor}\%:(\mathsf{symbol})\Rightarrow\mathsf{string}\mid\mathsf{undefined}
```

### Symbol keys

A computed key `[k]`, in a type, a literal or a read,
names a `const k: unique symbol` (or a readonly property so declared), and
the symbol it names is what made the constant: `Symbol()` makes a fresh one,
the declaration's own, and `Symbol.for(s)`, with $`s`$ a string literal, the
registry's symbol for $`s`$, which every constant made so holds. A declared
constant (`declare const`) holds its own. Any other initializer is refused,
the symbol it holds not being known:

```math
\mathrm{sym}(k)=\begin{cases}
\sigma_k & k=\mathtt{Symbol}(\ldots)\ \text{or}\ \mathtt{declare\ const}\ k\\
\sigma_{\mathtt{for}\,s} & k=\mathtt{Symbol.for}(s)
\end{cases}
```

So two constants made by `Symbol.for` of one string name one key, and a
type naming both names that key twice, which is refused, though TypeScript
types each constant a distinct `unique symbol`.

### Merged library interfaces

A declaration outside the standard library may merge a member into an
interface a unit reads at TScert's reviewed contract: `Object` or `Function`
(in every unit that reaches the declarations), `Array`, `ReadonlyArray` or a
primitive's wrapper (where an array or the primitive's member reaches the
unit), and the interfaces those contracts name with their library bases
(`Iterator`, `ArrayIterator`, `IteratorObject`). Every value of the interface
is read at the overlay, TScert's reviewed interpretation of the host's
prototype. A merge states a member of every value of the type and installs
nothing at run time, so a member the overlay does not review at that
contract (a `toJSON` stating that every array or object holds a hook) would
be erased from the annotations it changes: such a merge is refused
(`invalid-merged-array-param`, `invalid-merged-readonly-array-callback`,
`invalid-merged-array-generic-param`, `invalid-merged-object`, `invalid-merged-function`, `invalid-merged-iterator`,
`invalid-merged-iterator-set`, `invalid-merged-values-iterator`,
`invalid-merged-string`; the `collections-*` cases, under Node's types).

A member a merge states at a reviewed contract is read at the reviewed
translation, its corrections and effects included, from the reviewed
signature where the project's library declares none: Node's `at` polyfill
(`RelativeIndexable<T>`) under ES2021 (`node-at-polyfill`). Contracts are
compared as the type reader reads them, the merged declaration and the
reviewed signature alike: binders by position, a base at the arguments each
heritage path gives it, a member's own binders with their bounds,
optionality, each overload on its own; a parameter's name is no part of a
contract (`merged-restated-at`, `merged-renamed-at`,
`invalid-merged-narrowed-at`, `invalid-merged-two-paths-at`). A form the
comparison does not read (a named type, a computed key, a call, construct or
index signature, a base outside the merge) is refused. An interface a source
names (`Iterable<T>`) is read at its merged declarations, not at a reviewed
contract, so a merge into it is read, not erased: a required member it adds
is one an array does not meet (`invalid-merged-iterable`; unmerged,
`array-iterable`).

### Node's `process`

Node's `process` and `console` are read through the overlay at the members
the repository's code uses, each pinned to its declaration in the pinned
`@types/node` installations, their origin the package `@types/node`. A member read at a stated contract,
and every reviewed method, is a readonly view: no write of it is admitted,
through `process` or through the process a registration returns
(`invalid-node-process-replace-result`, `invalid-node-process-replace-alias`).

- `process.argv`: an array of strings Node builds at start-up, read as
  $`\mathtt{readonly\ string}[\,]`$. The property is writable: no code
  replaces it or writes a non-string into it, an assumption.
- `process.execPath`, a string, and `process.pid`, a number.
- `process.execArgv`: the Node options the process started with, an array
  of strings built at start-up, read as `argv` is,
  $`\mathtt{readonly\ string}[\,]`$, with the same assumption.
- `process.platform` and `process.arch`: the names of the operating system
  and the processor, strings fixed at start-up; their declared unions of
  names are read as `string` (`node-process-platform`).
- `process.env`: an object whose own entries hold strings and on which no
  accessor can be defined (`defineProperty` with a getter throws), its chain
  a prototype holding `constructor` and then `Object.prototype`: read as the
  readonly dictionary $`\{[k:\mathtt{string}]:\mathtt{string}\mid\mathtt{undefined}\}`$,
  at no key a prototype may provide (the dictionary rule;
  `invalid-collections-process-env`). A write is refused where it is written
  (`node-process-env-write`, a gap): an assignment converts its value by
  ToString, which runs an object's `toString`, stores `undefined` as the
  string `"undefined"` and throws on a symbol, and a new key is visible
  through every alias of the object, which the model's key addition, a copy
  of a local object, does not represent ([WORK.md](../WORK.md#nodes-process)).
- `process.exit(code)` at a number or nothing: `never`, stating no effect. It
  runs the `exit` listeners synchronously, and one may throw into the caller
  (`invalid-node-process-exit-handler`, run under Node).
- `process.kill(pid, s)` at a number and an admitted signal $`\mathsf{Sig}`$:
  `true`, a throw, or the process ending; neither delivery nor termination is
  promised, and no effect is stated.
- `process.on(e, f)` and `process.once(e, f)` at a named event: `exit` and
  `beforeExit`, whose listener is called with the exit code, a number, and
  $`\mathsf{Sig}=\texttt{"SIGINT"}\mid\texttt{"SIGTERM"}\mid\texttt{"SIGHUP"}\mid\texttt{"SIGUSR1"}\mid\texttt{"SIGUSR2"}`$,
  whose listener is called with the signal's name, each with the process as
  `this` (`node-process-listeners`, run under Node, `beforeExit` emitted again
  after its listener scheduled another job). The listener is a value of
  the checked callable type $`(\mathtt{number})\Rightarrow\mathtt{unknown}`$ or
  $`(\mathtt{string})\Rightarrow\mathtt{unknown}`$, stating no effect; a
  listener of another parameter type is refused
  (`invalid-collections-process-listener`, and with borrowed claims and
  evidence in `pipeline/test.mts`). Registering emits `newListener`, and
  `once`'s removal `removeListener`, synchronously: the call states no
  effect, its throw included, and returns the process. An event known only as
  a string, a meta-event, or an event no entry lists (`message`) is refused
  (`collections-process`; `invalid-node-process-meta-event`,
  `invalid-node-process-message-event`); so are `emit`, reading listeners back
  and replacing a method, which no entry lists.
- `console.log` and `console.error`, of the DOM's library and Node's, at
  primitive arguments, stating no effect (`node-console`). Writing the text
  calls the output stream's `write`, a property other code may replace while
  `console.log` keeps its identity, and a stream calls listeners other code
  registered: no effect is stated, which covers that code.

A listener runs after the unit that registered it, between synchronous jobs,
or inside an operation stating no effect (`process.exit`, `kill`, a
registration): its body is checked as any closure is, its captured mutable
state read at its declared types, no narrowing made at registration retained
(`invalid-node-process-listener-stale`, run under Node). At an `await`, the
ordinary effect of `%Await%` drops every fact another job may change. The
scheduling is a host assumption ([trust surface](DESIGN.md#trust-surface)):
the calculus does not prove Node's scheduler.

### Module metadata

**Audited against:** Node 25.2.1, `src/module_wrap.cc`
(`DefaultImportMetaObjectInitializer`) and
`lib/internal/modules/esm/loader.js` (`createImportMetaResolve`,
`resolveSync`); `@types/node` 22.20.2 and 22.10.7.

A read of a member of `import.meta` is a call of an intrinsic stating no
effect, whose value is `unknown`: `import.meta.k` is $`\%\mathsf{ImportMeta{:}}k\%()`$
for $`k\in\{\mathtt{url},\mathtt{dirname},\mathtt{filename}\}`$, and
`import.meta.resolve(s)` at one argument is
$`\%\mathsf{ImportMeta{:}resolve}\%(s)`$ at
$`s:\mathtt{string}`$. Each member is pinned to its declaration in
`@types/node`'s `ImportMeta`. Every reference reads a member by name, and
`resolve` appears only as a call's callee; any other reference, which would
hand the object to other code, is refused (`invalid-import-meta-escape`,
run under Node: code handed the object writes a number at `url`). A use of
a member as a string checks it first (`import-meta`).

The module's first evaluation of `import.meta` fills a fresh object, with a
null prototype, from the module's wrapper. Other code reaches the wrapper
of a module it requires, through `require.cache`, and may write it or
define getters on it:

- `url` is the wrapper's `url`, copied whatever value it holds
  (`invalid-import-meta-url`, run under Node: a number);
- the wrapper's `isMain` is read, and a getter defined there runs code of
  any module's (`invalid-import-meta-stale`, run under Node: the getter
  empties a field the function tested before);
- `dirname` and `filename` are defined for a `file:` URL alone, as lazy
  data properties whose first read converts the URL to a path in native
  code; a module at another URL (a `data:` module, a URL a resolve hook
  chose) has neither (`invalid-import-meta-dirname`, run under Node);
- `resolve`, outside the loader hooks' worker thread, is a lazy data
  property whose first read makes the function by Node's own
  `createImportMetaResolve`; on that thread it is absent, and the call
  throws. The call converts the specifier by a template, the string
  itself, and resolves it through every resolve hook `module.registerHooks`
  and `module.register` installed, code of any module's, which may throw. A
  URL a hook returns is checked to be a string; where a hook throws an
  error with the code `ERR_MODULE_NOT_FOUND` or `ERR_UNSUPPORTED_DIR_IMPORT`
  and a truthy `url`, that `url` is returned, whatever value it holds
  (`invalid-import-meta-resolve`, run under Node), and without a truthy
  `url` the error is thrown again. Node ignores a second argument unless
  `--experimental-import-meta-resolve` is set.

A `vm` module whose own `initializeImportMeta` fills the object may hold
anything there, which the `unknown` values and the absent effect cover.

## Library modules

**Audited against:** `@types/node` 22.20.2 and 22.10.7 (`tools/package.json`,
`pipeline/library-project/package.json`); host
behaviour from Node 25.2.1's `lib/` sources and probes run under Node 25.2.1
(2026-10-19).

A value a client imports from one of Node's built-in modules (`node:fs`, or
`fs`; a specifier Node's `isBuiltin` answers true of) is read through the
reviewed overlay of library modules (`library-modules.mts`), and only where
an entry lists it: any other value of such a module, named, a namespace's
member or a default object's member, is refused where it is imported. The module is the one whose
ambient declaration (`declare module "os"`) holds the value's declarations,
however the client reaches it: a program module's re-export, by name or by
`export *`, binds the same export, so it is read at that module's entry for
the export's own name, and refused where none lists it
(`node-reexport-tmpdir`, `invalid-node-reexport-named`,
`invalid-node-reexport-star`, run under Node). No entry lists an enum, so
an enum of a Node module, which only an augmentation of its declarations
states, is refused before it is read: `declare module "node:crypto" { enum
argon2 { tag = 1 } }` states `argon2.tag` as 1, where Node's `argon2` is a
function whose `tag` is undefined (`invalid-node-augmented-enum`, run under
Node). A
declaration need not state what Node binds: `node:crypto` declares
`const fips: boolean`, and Node's module object holds a deprecated
accessor answering 0, which no named export holds
(`invalid-node-default-import-unreviewed`, run under Node). The class values
`Dirent` and `Stats`, which no entry lists, are refused alike
(`invalid-node-dirent-prototype-write`); a name imported for its type alone
is read as a type.
An entry names one overload of the function's declaration in Node's
declarations, with exactly the text it was reviewed against, its
$`\mathit{texts}`$ the text and the same overload's text in the other pinned
installation where they differ, and states the signature the host meets at
the arguments it admits, $`(\vec P)\Rightarrow R`$. With $`\Omega_m`$ the overlay, $`f`$
imported from module $`\mu`$ and $`O_f`$ the overloads TypeScript binds it to,
or, where $`f`$ is a `const` whose declared type is one interface of Node's
declarations holding call signatures alone, with no base but the standard
library's `Function` (`statSync: StatSyncFn`), those call signatures; a
`let`, another base or another member is refused
(`invalid-node-types-let-stat`, `invalid-node-types-heritage-stat`):

```math
\frac{\{\omega\in\Omega_m\mid \omega.\mathit{module}=\mu,\ \omega.\mathit{name}=f\}=\{\omega_1\ldots\omega_n\}\neq\emptyset\quad
      \forall i.\ \exists s\in O_f.\ \mathsf{text}(s)\in\omega_i.\mathit{texts}\quad
      \omega_i.\mathit{stated}=(\vec P_i)\Rightarrow R_i}
     {\Gamma(f)=\bigwedge_{i}(\vec P_i)\Rightarrow R_i}\ \textsf{library-module}
```

The declaration's types are not read, and neither are the types they name
(`Buffer`, `URL`, streams). Each statement is an assumption a result is
relative to, as an import's declared type is, and each says what the host
does at its parameters, where the declaration may say otherwise. A call is
unrestricted in its effect unless its entry states one. A statement may name
a type that no declaration file declares, which its entry defines: with
$`D_\omega`$ the definitions of $`\omega`$, each $`D\in D_\omega`$ joins the
document's definitions where $`\omega`$ is read, as a declaration a value's
type names does, and a definition's methods name it as their receiver
(`this`), so a method may return it. The entries:

- `execFileSync(file, args, options)` runs `file` and returns its standard
  output when it exits with status 0; a failure to run, a nonzero status, a
  signal, a timeout and output past `maxBuffer` throw. The output is a
  string at a text encoding and `null` where standard output is not piped to
  the parent, though the declaration says `string` at every text encoding
  (`invalid-node-exec-stdout-ignored`). It is stated at the options the
  host returns a string under: $`(\mathtt{string},\ \mathtt{readonly\ string[]},\ O)\Rightarrow\mathtt{string}`$ with

  `O = { encoding: "utf8"; input?: string; maxBuffer?: number; stdio?: readonly [S, "pipe", S]; env?: { readonly [k: string]: string | undefined } }`,
  `S = "pipe" | "ignore" | "inherit"`.

  The host copies the options' own properties and converts each value `env`
  owns to a string before it reads the `stdio` array the copy shares; an
  object value's `toString` may set `stdio[1]` to "ignore", and the result is
  then `null` (`invalid-node-exec-env-object`). A record type states nothing
  of the keys it does not name, so `env` is stated at strings. Every other
  option the host reads it validates without converting, throwing on a type
  it does not accept: an object at each such key ran no code of the client's.
- `execFileSync` has a second stated form, the **restricted form**. Its
  options state every key the synchronous path reads, each at a type Node
  validates without running code of the client's:
  $`(\mathtt{string},\ \mathtt{readonly\ string[]},\ O_r)\Rightarrow\mathtt{string}`$ with

  `O_r = { encoding: "utf8"; stdio: readonly [S, "pipe", S]; input?: string; maxBuffer?: number; env?: undefined; shell?: false; cwd?: string; argv0?: string; detached?: boolean; uid?: number; gid?: number; windowsHide?: boolean; windowsVerbatimArguments?: boolean; timeout?: number; killSignal?: string | number }`.

  A record type is open, so a key it does not name may hold any value; a key
  it names at `undefined` or `false` is absent or holds that value. The form
  states the empty footprint on normal return and on a throw
  ([exceptional footprints](SOURCE-ELABORATION.md#exceptional-footprints)). A call
  meeting only the first form keeps an unrestricted effect. The audit of Node's
  `lib/child_process.js` and `lib/internal/child_process.js` covers every
  write the call makes before it returns, and before each throw: a
  validation error, a failure to spawn, and a failed command.

  - `normalizeExecFileArgs` and `normalizeSpawnArguments` copy `args`
    (`ArrayPrototypeSlice`) and the options (an object spread) into fresh
    objects.
  - `env` is absent or `undefined`, so the environment is a fresh copy of
    `process.env`. `copyProcessEnvToEnv` writes `NODE_V8_COVERAGE` into it,
    and, under the permission model, `copyPermissionModelFlagsToEnv` writes
    `NODE_OPTIONS`. With `options.env`, both write into the caller's object,
    and the host converts each of its values to a string, which runs an
    object value's `toString`.
  - `shell` is absent or `false`. A string or `true` runs
    `process.emitWarning` when arguments are passed, whose `warning`
    listeners are client code.
  - `cwd` is a string, which `getValidatedPath` checks as is; an object
    would be read as a file URL and its `pathname` converted.
  - `detached`, `uid`, `gid`, `argv0`, `windowsHide`,
    `windowsVerbatimArguments`, `timeout`, `maxBuffer` and `killSignal` are
    validated by type and range. A rejected value throws an error built from
    a primitive, after only the copies above were written.
  - `getValidStdio` pushes `undefined` into the caller's `stdio` array while
    it is shorter than 3. The stated tuple has length 3, so no push happens.
    Its reduction is a fresh array, which `spawnSync` stores before it writes
    the input pipe into it.
  - `execFileSync` writes the child's standard error through
    `process.stderr` when `stdio` is omitted. The restricted form requires
    `stdio`.
  - The input is a string (`Buffer.from`), and the outputs are decoded at
    `"utf8"`. The thrown error is the fresh `ret.error` or a fresh
    `genericNodeError`, with `ObjectAssign` copying the result onto it.
  - `for…in` over the environment copy reads `Object.prototype`, which
    holds no enumerable key under the
    [ordinary-prototype assumption](SOURCE-MODEL.md#exact-contracts-and-native-effects).

  The form also assumes that `NODE_DEBUG` does not name `child_process`:
  `debuglog` would otherwise write the options through `process.stderr`.
- `writeFileSync(file, data)` with a path and a string writes the string to
  the file as UTF-8 and returns `undefined`; a path it cannot write throws:
  $`(\mathtt{string},\ \mathtt{string})\Rightarrow\mathtt{undefined}`$.
  With options $`W`$ stating each property it reads (`getOptions`, then
  `flush`, `flag`, `encoding` and `mode`),
  $`(\mathtt{string},\ \mathtt{string},\ W)\Rightarrow\mathtt{undefined}`$ with

  `W = { mode: number; encoding?: "utf8"; signal?: undefined; flush?: boolean; flag?: "w" }`,

  it opens the file with that mode; a mode that is no 32-bit unsigned
  integer throws. Without `encoding: "utf8"` the host calls `fs.openSync`,
  `fs.writeSync` and `fs.closeSync` through the module's object, writable
  properties other code may replace, so the call states no effect
  (`node-fs-stat`).
- `mkdirSync(path, o)` with a string path and
  $`o=\{\mathtt{recursive}\colon\mathtt{true};\ \mathtt{mode}^?\colon\mathtt{number}\mid\mathtt{undefined}\}`$,
  the two properties it reads, creates the directory and the missing ones
  above it and returns the first it created, or `undefined` where the
  directory exists:
  $`(\mathtt{string},\ o)\Rightarrow\mathtt{string}\mid\mathtt{undefined}`$.
  `chmodSync(path, mode)` with a string and a number sets the mode and
  returns `undefined`:
  $`(\mathtt{string},\ \mathtt{number})\Rightarrow\mathtt{undefined}`$. A
  mode that is no 32-bit unsigned integer, or a path the host cannot
  change, throws; neither runs code of the client's (`node-fs-stat`).
- `statSync(path)` with a string path and no options returns a fresh `Stats`
  of what the path names, its symbolic links followed, and throws where the
  path names nothing (`throwIfNoEntry` defaults to true). The declaration is
  the constant `statSync: StatSyncFn`, whose call signature
  `(path: PathLike, options?: undefined): Stats` the entry names:
  $`(\mathtt{string})\Rightarrow S`$ with

  `S = { dev, mode, nlink, uid, gid, rdev, blksize, ino, size, blocks, atimeMs, mtimeMs, ctimeMs, birthtimeMs: number; isFile, isDirectory, isBlockDevice, isCharacterDevice, isSymbolicLink, isFIFO, isSocket(): unknown }`,

  the numbers writable. That the constructors' assignments define own data
  properties and that reading a test runs no code rest on a host assumption
  ([trust surface](DESIGN.md#trust-surface)): a `Stats` keeps its audited
  prototype chain, `Stats.prototype` → `StatsBase.prototype` →
  `Object.prototype`, whose two Node prototypes hold the seven tests,
  `_checkModeProperty` and the date getters `atime`, `mtime`, `ctime` and
  `birthtime`, none named by $`S`$'s numbers, the seven tests data
  properties holding callable values throughout execution, also in external
  code. A getter in a test's place runs where the member is read, a read no
  call's effect covers (`invalid-node-stat-method-getter`, run under Node: a
  `map` callback reading `s.isFile` leaves a hole). A test calls
  `this._checkModeProperty`, a writable property of `Stats.prototype` other
  code may replace, so each is $`()\Rightarrow\mathtt{unknown}`$, its effect
  unrestricted (`invalid-node-stat-test-result`, run under Node: 7); a
  caller wanting a Boolean compares it with `true`. The date getters are not
  stated (`invalid-node-stat-date-getter`, run under Node: a replaced
  getter answers a number). An options object may hold a getter the host
  reads inside the call (`invalid-node-stat-options-getter`, run under
  Node). With options $`o`$ stating the two properties the host reads,
  $`o=\{\mathtt{bigint}\colon\mathtt{true};\ \mathtt{throwIfNoEntry}^?\colon\mathtt{true}\mid\mathtt{undefined}\}`$,
  it returns a fresh `BigIntStats`
  ([stated library types](#stated-library-types)), its numbers bigints,
  throwing where the path names nothing as without options:
  $`(\mathtt{string},\ o)\Rightarrow\mathit{BigIntStats}`$, stating no
  effect (`node-fs-stat-bigint`; `invalid-node-stat-bigint`, run under
  Node). That a `BigIntStats` owns its bigints and that reading a test runs
  no code rest on the assumption a `Stats` rests on, of its chain
  `BigIntStats.prototype` → `StatsBase.prototype` → `Object.prototype`.
- `readFileSync(path, "utf8")` with a string path returns the file's
  contents decoded as UTF-8; a path it cannot read throws:
  $`(\mathtt{string},\ \texttt{"utf8"})\Rightarrow\mathtt{string}`$
  (`node-fs-read`). Without an encoding it reads the file into a fresh
  `Buffer` ([stated library types](#stated-library-types)):
  $`(\mathtt{string})\Rightarrow\mathit{Buffer}`$, stating no effect, as it
  opens, reads and closes the file through `fs.openSync`, `fs.readSync` and
  `fs.closeSync`, writable properties of the module's object other code may
  replace (`node-bytes-buffer`).
- `existsSync(path)` with a string returns whether the path exists, and does
  not throw: $`(\mathtt{string})\Rightarrow\mathtt{boolean}`$.
- `mkdtempSync(prefix)` with a string creates a directory named by the prefix
  and six random characters and returns its path:
  $`(\mathtt{string})\Rightarrow\mathtt{string}`$; an encoding option, which
  may select a `Buffer`, is outside the stated call. `rmSync(path, options)`
  with a string path and `{ recursive: true, force: true }` removes the path
  and everything under it and returns `undefined`; the host reads the options'
  properties, so the call is unrestricted in its effect (`node-fs-temp`).
- `realpathSync(path)` with a string returns the canonical path, its
  symbolic links followed, and throws where the path does not exist:
  $`(\mathtt{string})\Rightarrow\mathtt{string}`$; an encoding option, which
  may select a `Buffer`, is outside the stated call
  (`invalid-node-realpath-options`).
- `spawnSync(command, args, options)` at options $`O`$ stating
  `encoding: "utf8"`, `stdio` and `env` absent, and an optional `timeout`,
  `cwd`, `maxBuffer` and `input`, runs the command and returns a fresh
  record:
  $`(\mathtt{string},\ \mathsf{readonly}\ \mathtt{string}[\,],\ O)\Rightarrow\{\mathtt{pid}\colon\mathtt{number};\ \mathtt{status}\colon\mathtt{number}\mid\mathtt{null};\ \mathtt{signal}\colon\mathtt{string}\mid\mathtt{null};\ \mathtt{stdout},\mathtt{stderr}\colon\mathtt{string}\mid\mathtt{undefined};\ \mathtt{error}^?\colon\mathtt{unknown}\}`$,
  stating no effect: the host reads the options' properties
  (`node-spawn-sync`). Both streams are piped, so each output is a string
  where the child ran and absent where it could not be spawned, which the
  declared `string` omits (`invalid-node-spawn-sync-stdout`, run under
  Node); `stdio` naming no pipe leaves it `null` and is outside the stated
  call (`invalid-node-spawn-sync-stdio`, run under Node).
- `readdirSync(path, o)` with a string path reads `o.encoding` and
  `o.signal`, then `o.recursive`, `o.encoding` and `o.withFileTypes` (Node's
  `lib/fs.js`). The four are stated,
  $`o=\{\mathtt{withFileTypes}\colon\mathtt{true};\ \mathtt{encoding}^?\colon\texttt{"utf8"}\mid\mathtt{undefined};\ \mathtt{recursive}^?\colon\mathtt{false}\mid\mathtt{undefined};\ \mathtt{signal}^?\colon\mathtt{undefined}\}`$,
  so under the caller contract ([trust surface](DESIGN.md#trust-surface))
  each is a data property whose reads agree. `recursive: true` collects
  entries from subdirectories; that walk is not audited, so it is refused
  (`invalid-node-readdir-recursive`, run under Node: a nested file appears in
  the result; [source fragment](SOURCE-FRAGMENT.md)). The call returns
  a fresh array of entries, whose constructors assign each its `name` and
  `parentPath`, writable strings; a path it cannot read throws, and the call
  states no effect (`node-readdir-dirents`). That the assignments define own
  data properties and that reading a test runs no code rest on a host
  assumption ([trust surface](DESIGN.md#trust-surface)): `Dirent` and `DirentFromStats` instances keep their audited prototype chains, `DirentFromStats.prototype` → `Dirent.prototype` → `Object.prototype`, whose two Node prototypes hold data properties only, the seven `is…` tests among them callable throughout execution, also in external code.
  An accessor on either prototype or on an inserted ancestor breaks the
  first two, and a replaced or deleted test the third
  (`invalid-node-dirent-name-accessor`, `invalid-node-dirent-method-getter`,
  `invalid-node-dirent-chain-insert`, `invalid-node-dirent-test-replaced`,
  run under Node). A program reaches neither prototype: a class value's
  `prototype`, an entry's `constructor`, `Object.getPrototypeOf` but its
  comparison with `Object.prototype`, `Object.setPrototypeOf`,
  `Object.defineProperty` and `Reflect.set` are refused
  (`invalid-node-dirent-prototype-write`, run under Node,
  `invalid-node-dirent-constructor-prototype`,
  `invalid-node-dirent-get-prototype`, `invalid-node-dirent-set-prototype`). `encoding: "buffer"` names the entries by
  Buffers, and options of a type stating no `encoding`, or no `signal`, may
  hold it or a getter switching it between the reads
  (`invalid-node-readdir-buffer-encoding`, `invalid-node-readdir-options-alias`,
  `invalid-node-readdir-options-signal`, run under Node). An entry is a
  `Dirent`, or, where the directory reports an unknown type, a
  `DirentFromStats` built from `fs.lstatSync`; its seven `is…` tests dispatch
  through prototypes other code may change (`Stats.prototype`'s call
  `this._checkModeProperty`), so each is
  $`()\Rightarrow\mathtt{unknown}`$, its effect unrestricted
  (`invalid-node-readdir-test-result`, run under Node: a replaced test
  answers a number).
  The declared `Dirent.path` is absent at run time, so the entry states
  none (`invalid-node-readdir-dirent-path`, run under Node). The element is
  the `Dirent` the overlay of library types states
  ([stated library types](#stated-library-types)), which an annotation
  names and a closure whose parameter TypeScript types as `Dirent<string>`
  reads (`node-readdir-dirents`).
- `readdirSync(path)` with a string path and no options reads the default
  options, a frozen object of no property, and returns a fresh array of the
  entries' names, decoded as UTF-8; a path it cannot read throws:
  $`(\mathtt{string})\Rightarrow\mathtt{string}[\,]`$, stating no effect
  (`node-fs-stat-bigint`).
- `createHash("sha256")` returns a fresh `Hash`, of the type its entry
  defines,
  $`\mathit{Hash}=\{\mathtt{update}\colon(\mathtt{string}\mid\mathit{Uint8Array})\Rightarrow\mathtt{this};\ \mathtt{digest}\colon(\texttt{"hex"})\Rightarrow\mathtt{string}\}`$,
  each member a method, so $`\Gamma(\mathtt{createHash})=(\texttt{"sha256"})\Rightarrow\mathit{Hash}`$
  (`node-crypto-hash`, `blocker-node-hash-contract`). By Node's
  `lib/internal/crypto/hash.js`, the call validates the algorithm and
  allocates the native handle and a state record. `LazyTransform` then
  assigns the hash's `_options`, which a setter the hash inherits from other
  code would intercept, so the call states no effect
  (`invalid-node-crypto-hash-callback`, run under Node: the setter shrinks
  the array `map` visits). Every use in `tools/` calls `update` next, which
  states none either.
  At a SHAKE algorithm without an output length it emits a deprecation
  warning, which reads `process.noDeprecation` during the call, a property
  other code may make a getter, so the algorithm is stated at `"sha256"`
  alone (`invalid-node-crypto-hash-algorithm`, run under Node).
  `update(data)` checks the hash is not finalized, hashes a string as UTF-8
  and a view of bytes (`isArrayBufferView`), a `Uint8Array` or a `Buffer`
  ([stated library types](#stated-library-types)), as its bytes, and
  returns its receiver; a value of the view's type that is no view throws; `digest("hex")` checks the
  same, marks the hash finalized and returns the digest as hexadecimal
  digits. Either throws on a hash already digested, an outcome
  (`node-crypto-hash`, run under Node). Each reads the hash's state
  through a symbol-keyed property, on which other code may install a getter, and
  writes host state: both state no effect. `digest` at
  another encoding, and without one, which returns a `Buffer`, are outside
  the stated method (`invalid-node-crypto-hash-encoding`,
  `invalid-node-crypto-hash-buffer`, run under Node), and so is `update`
  with an input encoding. The methods are `Hash.prototype`'s,
  which a copy does not take (`invalid-node-crypto-hash-spread`, run under
  Node). That a member read finds them rests on a host assumption
  ([trust surface](DESIGN.md#trust-surface)): every `Hash`, created by the
  program or by external code, keeps `Hash.prototype` as its prototype and
  owns no `update` or `digest`, and `Hash.prototype` holds `update` and
  `digest` as own data properties, Node's own functions, throughout
  execution, as its native handle holds Node's own methods. A getter there
  would run at the member read, before the call
  (`invalid-node-crypto-hash-method-getter`, run under Node: it pops the
  array).
- `node:url`'s `fileURLToPath(url)` admits one string argument:
  $`(\mathtt{string})\Rightarrow_\emptyset\mathtt{string}`$.
  It parses the string into a URL that reaches no other code and decodes
  its pathname. The platform selects the default path rules:
  POSIX rejects hosts and encoded `/`; Windows accepts UNC hosts and also
  rejects encoded backslashes. A protocol other than `file:` throws.
  URL objects are refused, avoiding own `auth`, `path`, `hostname` and
  `pathname` members and search-parameter serialization callbacks.
  Options are refused (`invalid-node-url-options`, run under Node).
- `pathToFileURL(path)` admits one string argument and returns an opaque
  URL ([Node's `URL`](#nodes-url)):
  $`(\mathtt{string})\Rightarrow\mathit{URL}`$.
  It resolves paths using `path.posix.resolve` on POSIX and
  `path.win32.resolve` on Windows, reads `process.cwd()` for relative paths,
  and encodes URL control characters. It states no effect.
- `node:path`'s `dirname` and `basename` with an optional suffix compute a
  string from their strings alone, within the empty footprint on their throw
  too (Node's `lib/path.js`). `join` at any number of primitive strings is
  within the empty footprint on normal return under the standard-object
  assumption: the module's platform-specific `normalize`, and the standard
  array and string operations it uses, are untampered. The Node 26.13.0
  POSIX and Windows implementations validate each string, collect nonempty
  pieces into private arrays, and concatenate and normalize strings. The
  Windows reserved-device checks run only internal string predicates. They
  read no client object, invoke no client callback or coercion, and write
  only fresh private arrays; the result is a string. No exceptional footprint
  is stated. The string-pattern `split` contract gives a fresh dense array,
  and the checked map callback preserves stores, so `Set` receives readable
  string elements (`blocker-prep-set-mapped-paths`). No source rewrite or
  extra trust beyond untampered standard objects is needed.
  `invalid-node-path-join-callback` explicitly replaces `path.posix.normalize`
  and demonstrates a hole under Node; the module-overlay gate refuses the
  native implementation object it accesses. External code obeys the same
  standard-object assumption. `resolve` and `relative` keep unrestricted
  effects: they read `process.cwd()` for relative paths, as `realpathSync`
  does (`invalid-node-path-resolve-callback`, run under Node).
  The module exports one object (`export = path`), whose methods are the
  overloads an entry names (`node-path-strings`, including the safe map from
  the normalizer-tampering example).
- `node:os`'s `tmpdir()` returns a string: on POSIX the native
  `getTempDir`, the first of `TMPDIR`, `TMP` and `TEMP` set, or `"/tmp"`; on
  Windows `process.env`'s `TEMP` or `TMP`, or `SystemRoot` or `windir`
  joined to `\temp` (Node's `lib/os.js`). That the result is a string rests
  on the approved assumption that standard objects are not tampered with:
  `process.env` is Node's, whose values are strings, where a replaced
  `process.env` holding `TEMP: 7` makes Windows return 7. The call reads
  `process.env`, so it is unrestricted in its effect (`node-os-tmpdir`).
- `node:os`'s `availableParallelism()` is the native
  `getAvailableParallelism`, libuv's `uv_available_parallelism`, an
  unsigned integer returned as a number: it reads no property, runs no
  code of the client's, allocates nothing and does not throw, so it is
  within the empty footprint (Node's `lib/os.js`, `src/node_os.cc`;
  `node-os-host-info`, `blocker-node-os-host-info`).
- `node:os`'s `userInfo()`, at no argument, calls the native `getUserInfo`
  with `null` options, which reads no property, and encodes libuv's
  password entry as UTF-8: a fresh object of null prototype owning the
  writable data properties `uid` and `gid`, numbers, `username` and
  `homedir`, strings, and `shell`, a string or `null`,

  ```text
  { username: string; uid: number; gid: number; shell: string | null; homedir: string }
  ```

  A failure of `uv_os_get_passwd` throws a `SystemError`, whose
  construction runs Node's error code, so the call is unrestricted in its
  effect. An options object may select the `"buffer"` encoding, which
  answers `Buffer`s: no entry states a call with an argument
  (`invalid-node-os-user-info-buffer`, run under Node).
- `node:module`'s `stripTypeScriptTypes(code)` takes one string and returns
  the string with its TypeScript annotations erased, or throws. The entry
  admits no options argument. Node 26.13.0's
  `internal/modules/typescript` validates the string and runs its native
  TypeScript parser in strip-only mode; the parser's result is the output
  string, with syntax or unsupported-syntax failures thrown. The experimental
  warning and error paths may run client code, so the effect is unrestricted.
  `blocker-prep-namespace-descriptor` reads the export and calls this form.
- `node:module`'s `isBuiltin(id)` at a string tests the id in the set of
  built-ins requirable without a scheme, and, after a `node:` prefix, in
  the set of those requirable by users (Node's
  `lib/internal/bootstrap/realm.js`): `SafeSet`s and primordial string
  functions, which run no code of the client's, write and allocate nothing
  and do not throw, so it is within the empty footprint. The sets are
  filled while Node starts, so the answer is the running Node's
  (`blocker-node-module-hooks`). `@types/node` 22.10.7 declares it as a
  static member of the module's class, which no entry names. No entry
  lists `registerHooks`, whose hooks run inside every later resolution
  and load of the process (`invalid-module-register-hooks`, run under
  Node): the front end runs it through the host boundary
  [module customization hooks](SOURCE-REWRITES.md#module-customization-hooks).
- `node:path`'s `sep`, a constant: a data property of the exported object,
  `"/"` on POSIX and `"\\"` on Windows, set when Node loads the module
  (`lib/path.js`). It is writable: no code writes it, an assumption, as of
  `process.argv`. An entry for a constant names its property declaration,
  exactly as reviewed, and states the value's type, with $`\omega.\mathit{text}=\mathsf{text}(d)`$
  for $`d`$ the declaration TypeScript binds $`x`$ to:

```math
\frac{\{\omega\in\Omega_m\mid \omega.\mathit{module}=\mu,\ \omega.\mathit{name}=x\}=\{\omega\}\quad
      \omega.\mathit{text}=\mathsf{text}(d)\quad \omega.\mathit{constant}=T}
     {\Gamma(x)=T}\ \textsf{library-module-constant}
```

  so `sep` is $`\mathtt{"\backslash\backslash"}\mid\mathtt{"/"}`$, as declared (`blocker-node-path-sep`).

### The default import of a Node module

Node's default export of a built-in module is the module's object,
`module.exports`, and its named exports are bound from that object's own
properties when Node loads the module (Node 25.2.1,
`lib/internal/bootstrap/realm.js`, `BuiltinModule.prototype.syncExports`;
probed under Node 25.2.1: `(await import("node:fs")).default` is
`require("node:fs")`, and its `existsSync` is the named export). A default
import of a module $`\mu`$ the overlay lists whose `default` it reviews no
entry of (`import fs from "node:fs"`, `import path from "node:path"`;
`moduleObjectDefault`, `library-modules.mts`) is read as a namespace import
of $`\mu`$ ([namespace imports](SOURCE-ELABORATION.md#namespace-imports)):
every mention of `fs` is a member read `fs.x` or a qualified type name
`fs.T`, and each member is the binding `fs.x` of the named export $`x`$:

```math
\frac{\mathrm{mentions}(d)\subseteq\{\,d.x_1,\ldots,d.x_n\,\}\quad \mathsf{objectDefault}(\mu)\quad \Gamma(x_i@\mu)=T_i}
     {\Gamma(d.x_i)=T_i}\ \textsf{module-object-default}
```

$`\Gamma(x_i@\mu)`$ is the named import's reading, through the overlay's
entries for $`x_i`$ (`library-module`, `library-module-constant`), so a
member and the named export share one model, and a member no entry lists is
refused, as its named import is. The binding `fs` itself is not read. That `fs.x` holds the named
export at each read rests on the approved assumption that standard objects
are not tampered with ([trust surface](DESIGN.md#trust-surface)): no code
replaces a member of a Node module's object. A write of a member and any
other mention of the default import, an alias that could write one, are
refused where they are written (`invalid-node-default-import-write`,
`invalid-node-default-import-value`, run under Node: a replaced `dirname`
shrinks the array `map` visits). A member call passes the module's object
as the receiver, which none of the listed functions reads (their sources
under Node 25.2.1 mention no `this`); a callee whose declaration states a
`this` parameter is refused, as a namespace member's is.

TypeScript declares `node:path`'s `path` twice, `namespace path`, which
declares interfaces alone, and `const path: path.PlatformPath`, the module's
value (`export = path`). Only the constant has a value, so the checker
resolves each member read to a member of `PlatformPath`, the declaration a
named import of the same export resolves to (`blocker-node-default-import`,
`blocker-fs-default-import`).

### `node:assert/strict`

A file may import `node:assert/strict` by default (`import assert from
"node:assert/strict"`). Node declares that module's export as a function
merged with a namespace (`function strict(value, message?): asserts value`
beside `namespace strict { export { ok, strictEqual as equal, … } }` and
`export = strict`), or, in an earlier `@types/node`, as a constant of a type
with that call signature and those members; its members are `node:assert`'s
functions. The module `node:assert` itself, whose `equal` is loose equality,
is not read.

**Reading.** As a namespace import's member is
([namespace imports](SOURCE-ELABORATION.md#namespace-imports)), each
member read `assert.m` is a binding of the file, named `assert.m`, of the
export `default.m`, and a call `assert(…)` is a call of the import's own
binding; any other mention (passing `assert`, a member read uncalled) is
refused (`namespace-members.mts`), a default import beside named bindings
included (`invalid-node-assert-default-and-named`). A value imported from
`node:assert/strict` any other way (a named import, a namespace import) or
from `node:assert` is refused rather than read at its declaration, whose
promises only it asserts (`invalid-node-assert-named-import`,
`invalid-node-assert-namespace-import`, `invalid-node-assert-loose-import`). A member call passes the function as its
receiver, which none of these functions reads. Each binding is the forms of
the overloads its calls resolve to, each an entry of the overlay of library
modules (module `assert/strict`, name `default`, the member, and the
declaration's text, pinned as every entry is), so a changed declaration is
refused and reviewed again; a generic entry's binders are the binding's type
parameters.

**Footprints.** By probes run under Node, a passing `ok`, `equal`, `notEqual` and `ifError` run no code:
ToBoolean, `Object.is` and a comparison with `null` and `undefined`. A failing
call builds an `AssertionError`: it calls no `inspect.custom` hook, but it
reads the compared values' accessors while building the message, sets and
restores `Error.stackTraceLimit`, and runs a program's
`Error.prepareStackTrace`; a message that is an `Error` is thrown as it is.
Each entry states a footprint for normal return only, and unrestricted
effects on the exceptional edge: `onThrow` false, so a handler catching an
`AssertionError`, or whatever a hook throws instead, holds no fact about the
heap that the call's footprint would preserve, as the
[effect](SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification)
of any call reaching a handler (`invalid-node-assert-catch-continue`, run
under Node). A message is stated at `string`.

**Entries.** With $`M=\mathtt{string}\mid\mathtt{undefined}`$, the message:

- `assert(v, m)` and `assert.ok(v, m)`: a falsy `v` throws. A statement call
  whose message is absent or a string literal is the calculus's own test,
  `if (!v) throw %AssertionFailure%(m)`, so the argument narrows exactly as
  an `if` narrows it, the literal evaluated after `v` with nothing observable
  between (`node-assert-strict`). Any other call is read at
  $`(\mathtt{unknown},\ M)\Rightarrow\mathtt{void}`$, the empty footprint on
  normal return, and narrows nothing. `%AssertionFailure%` returns a fresh
  `AssertionError` and states no effect.
- `assert.equal(a, e, m)` (`strictEqual`):
  $`\forall T.\ (\mathtt{unknown},\ T,\ M)\Rightarrow\mathtt{void}`$, the empty
  footprint on normal return. `Object.is(a, e)` makes $`a`$ the value $`e`$, of
  type $`T`$; that promise, $`(\mathtt{unknown},\ T,\ M)\to T\,[\mathsf{asserts}\ 0]`$,
  is not stated, as the producer encodes no generic promise signature. `notEqual`:
  $`(\mathtt{unknown},\ \mathtt{unknown},\ M)\Rightarrow\mathtt{void}`$, the empty
  footprint on normal return.
- `assert.deepEqual(a, e, m)` (`deepStrictEqual`) and `notDeepEqual` compare
  by traversal, which can traverse enumerable own string and symbol
  properties, including extra array properties, accessors among them
  (observed: a passing comparison calls an enumerable symbol getter and an
  extra array property's getter). No type the fragment states bounds all of
  these, `JsonValue` included:
  $`(\mathtt{unknown},\ \mathtt{unknown},\ M)\Rightarrow\mathtt{void}`$, stating
  no effect, on normal return too (`invalid-node-assert-deep-preserving`, run
  under Node). Neither narrows: deep equality to a value of type $`T`$ is not
  shown to give type $`T`$.
- `assert.match(s, r, m)` and `doesNotMatch`: Node checks `r`'s regex slot,
  throwing on another value, and runs `RegExp.prototype.exec` on it, which
  reads `lastIndex` by ToLength (observed: an object `lastIndex` runs its
  `valueOf`): $`(\mathtt{string},\ \mathtt{unknown},\ M)\Rightarrow\mathtt{void}`$,
  stating no effect. No narrowing.
- `assert.throws(f, m)`, `assert.throws(f, x, m)` and `doesNotThrow` call `f`,
  and `throws` tests the thrown value against `x`: a regex converts it by
  `String`, which runs an object's `toString` (observed); `f` at
  `() => unknown`, `x` at `unknown`, stating no effect
  (`invalid-node-assert-throws-callback`, run under Node). No narrowing.
- `assert.ifError(v)`: $`(\mathtt{unknown})\Rightarrow\mathtt{void}`$ and the
  promise $`(\mathtt{unknown})\to\mathtt{null}\mid\mathtt{undefined}\,[\mathsf{asserts}\ 0]`$,
  the empty footprint on normal return; a failure reads `v`'s `message` and
  `stack` (observed).
- `assert.fail(m)`: $`(M)\Rightarrow\mathtt{never}`$, no effect.

Each entry is an assumption about the host, as a library module's is: the
promise of `ifError` follows from the comparison the host makes before it
returns, and the footprints from the steps observed above; nothing in Lean
proves them. The module's object is assumed unmodified: no code replaces
`assert.ok`. A passing call with an empty footprint keeps a fact across it,
a `map` calling `equal` staying dense (`node-assert-strict`); the failure
leaves the callback by its throw.

## Regular expressions

A regex is an object of host-relative methods (`regexp.mts`), read in two
forms: the **native** regex a literal evaluates to, which states its
literal's capture shape and a mark only the host's construction gives, and
the **structural** regex a `RegExp` annotation states, a behavioural
contract any value may meet. Neither states a property: a regex's
`lastIndex`, `source` and flags are read through no type.

**Shapes.** A literal's shape $`\Sigma=(A,\nu,g)`$ lists, for each capture
group $`k`$ in order, whether it takes part in every successful match
($`k\in A`$), whether a group is named ($`\nu`$), and whether the flags hold
`g` (`regexp-shape.mts`). On the pattern's tree under ECMA-262's grammar
([ECMA-262](REFERENCES.md#ecma-262), "Patterns", with Annex B outside
Unicode mode),

```math
k\in A\iff \text{no ancestor of group}\ k\ \text{is a disjunction of two or more alternatives, a quantifier with minimum}\ 0,\ \text{or a lookaround}
```

A quantifier with minimum at least 1 keeps its atom's groups: on success its
last iteration matched the whole atom (`RepeatMatcher` rejects an empty
iteration beyond the minimum). Escapes are read by mode: in Unicode mode
`\p{…}`, `\u{…}` and `\k<…>` are single escapes; outside it `\p` is the
letter, `\u` takes four hex digits or is the letter, `\k<…>` is a back
reference only in a pattern naming a group, and `[]` and `[^]` are complete
classes. A pattern the reading leaves out (the `v` flag, modifier groups), or
whose group count or names differ from the host's own compilation of it,
has the conservative shape $`\Sigma_\top`$, every group maybe unmatched.

**Types.** With $`G_k`$ `string` where $`k\in A`$ and `string | undefined`
otherwise,

```math
\begin{aligned}
\mathsf{Exec}(\Sigma)&=\mathtt{readonly}\ [\mathtt{string},G_1,\ldots,G_n]\ \&\ \{\mathtt{readonly\ index}\colon\mathtt{number};\ \mathtt{readonly\ input}\colon\mathtt{string};\ \mathtt{readonly\ groups}\colon\Gamma\}\\
\mathsf{Match}(\Sigma)&=\mathtt{readonly}\ [\mathtt{string},\ \ldots\mathtt{string}[\,]]\ \text{if}\ g,\ \text{else}\ \mathsf{Exec}(\Sigma)\\
\mathsf{Split}(\Sigma)&=\mathtt{string}[\,]\ \text{if}\ A=\{1,\ldots,n\},\ \text{else}\ (\mathtt{string}\mid\mathtt{undefined})[\,]
\end{aligned}
```

with $`\Gamma`$ `undefined` where no group is named and else a readonly
dictionary of `string | undefined`. At $`\Sigma_\top`$ the tuple is
`readonly [string, ...(string | undefined)[]]`, $`\Gamma`$ either, a match
that tuple, and a split the readonly view `readonly (string | undefined)[]`,
which both writable splits meet. The regex of shape $`\Sigma`$ is the record
of host-relative methods

```math
P(\Sigma)=\{\ \mathtt{exec}\colon(\mathtt{string})\Rightarrow\mathsf{Exec}(\Sigma)\mid\mathtt{null};\ \mathtt{test}\colon(\mathtt{string})\Rightarrow\mathtt{boolean};\ [@@\mathrm{match}]\colon(\mathtt{string})\Rightarrow\mathsf{Match}(\Sigma)\mid\mathtt{null};\ [@@\mathrm{replace}]\colon(\mathtt{string},\mathtt{string})\Rightarrow\mathtt{string};\ [@@\mathrm{search}]\colon(\mathtt{string})\Rightarrow\mathtt{number};\ [@@\mathrm{split}]\colon(\mathtt{string},\mathtt{number}\mid\mathtt{undefined})\Rightarrow\mathsf{Split}(\Sigma)\ \}
```

with each member's effect below; the native and structural regexes are

```math
N(\Sigma)=P(\Sigma)\ \&\ \{[@@\mathrm{matchAll}]\colon(\mathtt{string})\Rightarrow I_N(\mathsf{Exec}(\Sigma));\ \mathtt{readonly}\ [\mu]\colon\mathtt{undefined}\}
\qquad
⟦\mathtt{RegExp}⟧=P(\Sigma_\top)
```

where $`\mu`$ is the synthetic symbol `RegExpMatcher` (`tscert/regexp`), the
model's reading of the native `[[RegExpMatcher]]` slot, and
$`I_N(T)=\mathtt{Iterator}\langle T\rangle\ \&\ \{\mathtt{readonly}\ [\mu_I]\colon\mathtt{undefined}\}`$
the native match iterator, $`\mu_I`$ the synthetic `RegExpStringIterator`.
Where $`\Sigma\ne\Sigma_\top`$, the regex a literal written as the first
argument of a string's `replace` or `replaceAll` evaluates to, $`N^R(\Sigma)`$
(the intrinsic `%RegExp:Σ:replacer%`), also takes a replacement callback at
its `[@@replace]`, an overload of its own:

```math
N^R(\Sigma)=N(\Sigma)\ \&\ \{[@@\mathrm{replace}]\colon(\mathtt{string},\ \mathsf{Rep}(\Sigma))\Rightarrow_\top\mathtt{string}\}
\qquad
\mathsf{Rep}(\Sigma)=(\mathtt{string},G_1,\ldots,G_n,\mathtt{number},\mathtt{string}\,[,\Gamma])\Rightarrow_\top\mathtt{string}
```

with the last parameter $`\Gamma`$ present exactly where a group is named
($`\nu`$). ECMA-262 (`RegExp.prototype[@@replace]`) and V8 collect every
match before the first call, then call the callback once per match with
`undefined` as `this`, the whole match, each capture (`undefined` where its
group did not take part), the match's clamped position, the input string
and, where the match's `groups` is not `undefined`, that object (a fresh
object with a `null` prototype per match); the result is converted by
`ToString`, which runs no code on a string, so the callback's result is
`string`. The callback is client code, so this overload states no effect
(`invalid-regexp-replace-callback-effect`, run under Node); its arguments
follow the shape (`regexp-replace-callback`, `invalid-regexp-replace-capture`,
`invalid-regexp-replace-groups`, run under Node). The arguments follow the
shape only while the regex keeps its pattern: `RegExpBuiltinExec` converts
`lastIndex` first, and a `lastIndex` holding an object runs its `valueOf`,
which may `compile` another pattern. A literal at the call is a regex no
other code holds, its `lastIndex` the number 0; a regex held in a binding
may reach code that sets it (`invalid-regexp-replace-shared`, run under
Node: the offset arrives where the capture was), so its `[@@replace]` takes
a string alone. A callback binding fewer
parameters is claimed at $`\mathsf{Rep}(\Sigma)`$, the further actuals
discarded at binding, and its body is checked there. No
source declaration has a synthetic symbol's identity, so no source type,
literal or class states $`\mu`$ or $`\mu_I`$; a source `unique symbol` of the
same name is a key of its own (`invalid-regexp-forged-mark`).
$`N(\Sigma)\le⟦\mathtt{RegExp}⟧`$: results widen by readonly covariance and the
mark and `[@@matchAll]` are left out. TypeScript's `RegExpExecArray` and
`RegExpMatchArray` are $`\mathsf{Exec}(\Sigma_\top)`$ and $`\mathsf{Match}(\Sigma_\top)`$,
a supertype of each declaration with its element type corrected, and an
array pattern or loop over one steps it as an array. `RegExp`'s stated
members are pinned to their declaration texts (`reviewedRegExpMembers`).

**Effects.** A member of $`⟦\mathtt{RegExp}⟧`$, any value's, states no
effect. A native regex's members at string arguments run no client code,
read its pattern and flags, and allocate only their result; what they write
is `lastIndex`; the cases below are at string arguments. With
$`g`$ and $`y`$ whether the flags hold `g` and `y`,

```math
\epsilon_{N(\Sigma)}(m)=\begin{cases}
\emptyset & m\in\{[@@\mathrm{search}],[@@\mathrm{split}],[@@\mathrm{matchAll}]\},\ \Sigma\ne\Sigma_\top\\
\emptyset & m\in\{\mathtt{exec},\mathtt{test},[@@\mathrm{match}],[@@\mathrm{replace}]\},\ \Sigma\ne\Sigma_\top,\ \neg g,\ \neg y\\
\{\mathit{value}{:}\,\mathsf{any},\ \mathit{store}{:}\,\mathsf{keep}\} & m\in\{\mathtt{exec},\mathtt{test},[@@\mathrm{match}],[@@\mathrm{replace}]\},\ \Sigma\ne\Sigma_\top,\ g\lor y\\
\top & \text{otherwise}
\end{cases}
```

`[@@search]` restores the `lastIndex` it saved, `[@@split]` and
`[@@matchAll]` step a fresh clone, and a regex neither global nor sticky
writes no `lastIndex`; one that is leaves it where its last match ended,
changing one location, which holds a number by its contract
(`map-stable-regexp-test`). At $`\Sigma_\top`$ the flags are not read, and
no member states an effect. A native regex's `exec` and `test` take
`string | undefined`: they convert their argument by `ToString`, which runs no
code on `undefined` and gives `"undefined"` (`/^undefined$/.test(undefined)`
is true); a structural regex's keep their declared `string` (audited).

**Literals and dispatch.** Each evaluation of a literal allocates a regex;
a call of `String.prototype`'s `match`, `matchAll`, `replace`, `replaceAll`,
`search` or `split` with an object first argument runs `GetMethod` on it and
returns what that method returns:

```math
\frac{\Sigma=\mathsf{shape}(P,F)}
     {⟦/P/F⟧=\%\mathrm{RegExp}{:}\Sigma\%()\qquad \%\mathrm{RegExp}{:}\Sigma\%\colon()\Rightarrow_{\emptyset} N(\Sigma)}\ \textsf{regexp-literal}
```

```math
\frac{s\ \text{a string}\quad o\ \text{an object}\quad m\in\{\mathtt{match},\mathtt{search},\mathtt{split},\mathtt{replace},\mathtt{matchAll},\mathtt{replaceAll}\}}
     {⟦s.m(o,\vec e)⟧=\%\mathrm{Dispatch}{:}m\%(⟦s⟧,⟦o⟧,⟦\vec e⟧)}\ \textsf{regexp-dispatch}
```

as TypeScript types the receiver and the argument, evaluated as written, with

```math
\begin{aligned}
\%\mathrm{Dispatch}{:}\mathtt{split}\%&\colon\forall X.\ (\mathtt{string},\ \{[@@\mathrm{split}]\colon(\mathtt{string},\mathtt{number}\mid\mathtt{undefined})\Rightarrow X\},\ \mathtt{number}\mid\mathtt{undefined})\Rightarrow X\\
\%\mathrm{Dispatch}{:}\mathtt{replace}\%&\colon\forall X.\ (\mathtt{string},\ \{[@@\mathrm{replace}]\colon(\mathtt{string},X)\Rightarrow\mathtt{string}\},\ X)\Rightarrow\mathtt{string}\\
\%\mathrm{Dispatch}{:}\mathtt{matchAll}\%&\colon\forall X.\ (\mathtt{string},\ \{[@@\mathrm{matchAll}]\colon(\mathtt{string})\Rightarrow X;\ \mathtt{readonly}\ [\mu]\colon\mathtt{undefined}\})\Rightarrow X
\end{aligned}
```

and `match` and `search` as `split` without the limit, `replaceAll` as
`replace` with the mark. Each states one signature over the same binder per
closed footprint $`\varepsilon`$: the one above at a target whose member
states $`\varepsilon`$, stating it too, the one at $`\top`$ taking any
target. Beside that member's call, the dispatch reads `o`'s members and
converts only strings, so it writes nothing the member does not
(`map-stable-regexp-replace`):

```math
\frac{\%\mathrm{Dispatch}{:}m\%\colon\forall X.\ (\mathtt{string},\ \{[@@m]\colon\vec P\Rightarrow Q\},\ \vec R)\Rightarrow S}
     {\%\mathrm{Dispatch}{:}m\%\colon\forall X.\ (\mathtt{string},\ \{[@@m]\colon\vec P\Rightarrow_{\varepsilon} Q\},\ \vec R)\Rightarrow_{\varepsilon} S}\ \textsf{dispatch-footprint}
```
 `matchAll` and `replaceAll` first read
`o[@@match]` and `o.flags` and convert `flags` (ECMA-262,
`String.prototype.matchAll`), client code for an object `flags`
(`invalid-regexp-structural-matchall`): their argument must be native, whose
standard `flags` is a string. A non-global native regex makes them throw, an
outcome. A loop or spread over what TypeScript types `RegExpStringIterator`
steps `%Iterate:RegExpString%`, whose parameter is $`I_N(T)`$: a structural
iterator meets it not, and is refused there.

**What is refused.** A property of a regex is no member of either type:
`re.lastIndex`, `re.source`, `re.flags` are refused at the read, a regex meets
no view stating one (a copy would lack the non-enumerable `lastIndex`,
`invalid-regexp-lastindex-view`), and `in` with a key a regex owns or
inherits from `RegExp.prototype` is refused whatever the operand
(`inKeyRefusal`, `invalid-regexp-lastindex-in`). `compile`, which replaces a
regex's pattern and so its shape, is no member (`invalid-regexp-compile`); a
library class is no base (`invalid-regexp-subclass`). A structural regex's
`[@@replace]` takes no replacement callback. `new RegExp` of strings is the structural regex
$`⟦\mathtt{RegExp}⟧`$ ([library globals](#library-globals); `regexp-dynamic`).
Match results are readonly views.

## Async functions and await

The parser writes each async form as a call of an intrinsic, a value named
`%…%` that no source identifier spells (`intrinsics.mts`):

```math
\begin{aligned}
⟦\mathsf{await}\ e⟧&=\mathtt{\%Await\%}(⟦e⟧)\\
⟦\mathsf{return}\ e⟧_{\mathsf{async}}&=\mathsf{return}\ \mathtt{\%AsyncReturn\%}(⟦e⟧)\\
⟦\text{completion}⟧_{\mathsf{async}}&=\mathsf{return}\ \mathtt{\%AsyncComplete\%}()
\end{aligned}
```

in an async function, arrow or function expression's own body. The
declaration reader lists the intrinsics among the module's values. Let $`P`$
be the primitive types, and $`N`$ the supported stable non-thenable types:

```math
\begin{aligned}
P&=\mathsf{null}\mid\mathsf{undefined}\mid\mathsf{boolean}\mid\mathsf{number}\mid\mathsf{string}\mid\mathsf{bigint}\mid\mathsf{symbol}\\
N&=P\mid\{\,\mathtt{readonly\ then?}:P\,\}\mid\mathsf{readonly\ unknown[]}
\end{aligned}
```

The record arm requires a lifetime read contract for `then`, or its absence;
an observation of its current contents is insufficient. Ordinary arrays
exclude an own `then` and have stable standard prototypes without one,
including for external arrays. These contracts make every value of $`N`$
non-thenable throughout its lifetime. $`N`$ is the intrinsic type
`%Stable%`, listed with the native `Promise` wherever a resolution descriptor
is checked (`stableDefinition`). With $`X : \mathsf{Awaitable}`$ an
observation-qualified binder, owning its observation $`X.\mathsf{Observed}`$,
and $`X : \mathsf{Resolvable}`$ a resolution-qualified one, owning also its
result $`X.\mathsf{Result}`$ ([implied bounds](#implied-bounds)), the
intrinsic signatures are:

```math
\begin{aligned}
\mathtt{\%Await\%}&:\forall X:\mathsf{Awaitable}.\ (\mathit{value}:X)\Rightarrow X.\mathsf{Observed}\\
\mathtt{\%AsyncReturn\%}&:\forall X:\mathsf{Resolvable}.\ (\mathit{value}:X)\Rightarrow\mathsf{Promise}\langle X.\mathsf{Result}\rangle\\
\mathtt{\%PromiseResolve\%}&:\forall X:\mathsf{Awaitable}.\ (\mathit{value}:X)\Rightarrow\mathsf{Promise}\langle X.\mathsf{Observed}\rangle\\
\mathtt{\%AsyncComplete\%}&:()\Rightarrow\mathsf{Promise}\langle\mathsf{void}\rangle\\
\mathtt{\%PromiseAll\%}&:\forall T.\ (\mathit{values}:\mathsf{readonly}\ \mathsf{Promise}\langle T\rangle[\,])\Rightarrow\mathsf{Promise}\langle T[\,]\rangle\\
\mathtt{\%PromiseReject\%}&:\forall T.\ (\mathit{reason}:\mathsf{unknown})\Rightarrow\mathsf{Promise}\langle T\rangle\\
\mathtt{\%NewPromise\%}&:\forall T\le P.\ (\mathit{executor}:(\mathit{resolve}:(T)\Rightarrow\mathsf{void},\ \mathit{reject}:(\mathsf{unknown})\Rightarrow\mathsf{void})\Rightarrow\mathsf{void})\Rightarrow\mathsf{Promise}\langle T\rangle
\end{aligned}
```

A call instantiates an awaitable $`X`$ at an observation $`(B,O)`$, written
$`\mathsf{Obs}(B,O)`$, and a resolvable one at a descriptor $`(B,O,S)`$,
written $`\mathsf{Desc}(B,O,S)`$ ([implied bounds](#implied-bounds)), which
its certificate establishes. Instantiated so, with $`R`$ the async function's
result annotation, they derive:

```math
\frac{\Gamma\vdash e:B\quad \mathsf{Obs}(B,O)}{\Gamma\vdash\mathsf{await}\ e:O}\ \textsf{await}
\qquad
\frac{\Gamma\vdash e:B\quad \mathsf{Desc}(B,O,S)\quad \mathsf{Promise}\langle S\rangle\le R}{\Gamma\vdash_R\mathsf{return}\ e}\ \textsf{async-return}
\qquad
\frac{\mathsf{Promise}\langle\mathsf{void}\rangle\le R}{\Gamma\vdash_R\text{completion}}\ \textsf{async-complete}
```

Observation takes a native promise of any payload,
$`\mathsf{Obs}(\mathsf{Promise}\langle A\rangle,A)`$: it reads the
fulfillment value once, so `Promise<{ n: number }>` is awaited at
`{ n: number }` although no descriptor resolves it. A stable $`B`$ is its own
observation and descriptor, $`\mathsf{Desc}(B,B,B)`$, so a stable operand is
awaited and returned at its own type. Each rule is the host contract its
qualification selects: `%Await%` yields the observation, `%PromiseResolve%`
returns a native input itself and wraps a stable one in a fresh promise, a
promise of the observation, and `%AsyncReturn%` resolves afresh. These are
reviewed host contracts ([trust surface](DESIGN.md#trust-surface)) over the
relations `ResolutionCapabilities.Observes` and `ResolutionCapabilities.Resolves`.

`Promise<void>` is `Promise<unknown>` (both payload types denote $`J`$); async completion
fulfills it with `undefined`. A throw in an async body leaves it as a throw
in the model, where JavaScript rejects the promise the call returns. A
footprint the body meets on normal return therefore bounds no run of the
call, and an async definition's footprint is `top`
([async definitions](FOOTPRINTS.md#the-checked-callback-contract)).
A non-promise operand is awaited at its own type when its lifetime contract
establishes membership in $`N`$. This includes ordinary arrays and records
with a stable primitive-valued or absent `then`.

**Native promise invariant.** `Promise<A>` denotes a native promise of the
built-ins, with the stable standard `Promise.prototype` and constructor.
Its declared members and `constructor` are inherited; it owns none of those
keys. The constructor's species behavior is standard. These requirements
apply to external values and code as well as the checked source. The
annotation's prototype and own-key bounds prevent a writable structural
alias from replacing those members. Reading `constructor` yields `unknown`;
the inherited constructor is present. No object the program makes meets the
contract ([objects owning `then`](#objects-owning-then)). The native identity and standard
prototype behavior remain [host assumptions](DESIGN.md#trust-surface). Source
augmentations of the standard `Promise` interface are refused: native
factory results meet the reviewed standard declaration, and an augmentation
cannot add a runtime field or method contract to those results.

Under this invariant, the [ECMA-262 operations](REFERENCES.md#ecma-262) give
the following contracts. `Promise.resolve(p)` preserves an existing native
promise through its standard constructor identity path. `await` observes its
fulfillment value without resolving that value again. `Promise.all` obtains each input
through the same native identity path and stores its fulfillment value in a
fresh ordinary array. Thus both operations admit arbitrary payload types.
A fulfilled record may acquire a callable `then` through external mutation;
that does not alter its existing promise's fulfillment value. Fresh
resolution of that record can adopt its `then` instead. In particular,
`catch` and `finally` forward a fulfilled receiver's value by resolving a
fresh promise, so their receiver payload must remain non-thenable.

**Resolvable inputs.** Async return checks that its input is classified:
stable, a native promise of a classified payload, or a union of classified
inputs. Its resulting promise may then be used at a wider result annotation,
including `Promise<unknown>`, while the instance's certificate is still
checked. A bounded numeric parameter and a generic array retain their
precise types. An open record without the lifetime `then` contract has no
classification. An object literal an async body returns, through the
positions of $`\mathrm{returned}(f)`$
([literals a spread copies](SOURCE-ELABORATION.md#literals-a-spread-copies)),
is claimed with its exact keys, the own-key bound
$`\mathsf{among}\ \vec k`$ over the keys it writes. With `then` outside
$`\vec k`$, or written at a primitive, the literal is in the record arm of
$`N`$: its prototype is `Object.prototype`, which has no `then`
([exact contracts](SOURCE-MODEL.md#exact-contracts-and-native-effects), a host assumption).
The claim is a proposal, and Lean checks the bound at the allocation
(`async-object-result`; `invalid-async-return-literal-thenable`, run under
Node).

`Promise.resolve(value)` and `await` require an observation only: a stable
value, a native promise of any payload, or a union of those. Consequently a
native promise containing an open record can be awaited and returned by
`Promise.resolve` while forwarding it through async return requires
additional evidence.

The reaction methods quantify a receiver payload $`U\le N`$ at each call.
`catch` returns `Promise<U | R>`, where $`R\le N`$ is the rejection
callback's result type; `finally` returns `Promise<U>`. This requirement
applies to the operation. `Promise<T>` itself admits arbitrary payload
types, including records, and retains covariance.

A `finally` callback must return a value of $`N`$ or a native
`Promise<unknown>`. The native operation resolves the callback result before
forwarding the receiver's value. An open record result could hide a `then`
that mutates captured storage; discarding its value does not prevent those
effects. A native cleanup promise uses the constructor identity path, and
its fulfillment value is discarded. Its payload therefore needs no
non-thenable bound.

A `Promise` or `PromiseLike` argument of an imported, ambient or library
signature implies the bound $`N`$ on the type parameters it names, and
`Awaited<T>` in a source signature qualifies $`T`$
([implied bounds](#implied-bounds)). The producer proposes intrinsic
arguments from the operand, receiver and expected result. Its union inference
assigns operand parts to matching structured arms or the bare binder; an
unused arm contributes `never`. When comparing named result types, context
supplies missing candidates while retaining those supplied by arguments,
including `never` for an unused arm. This proposal heuristic assumes no
variance of the named type: Lean checks the complete substituted parameter,
result and binder bounds before accepting an instance.
A `Promise` method's binder written beside a promise of itself is inferred
the same way: `then`'s callback returns `TResult1 | Promise<TResult1>` and
`catch`'s `TResult | Promise<TResult>` (each a `PromiseLike` in TypeScript's
declaration, read as below), so a callback returning a promise of $`U`$, or a
primitive $`V`$, instantiates the binder at $`U`$ or $`V`$:

```math
\frac{\Gamma\vdash f:(\vec A)\Rightarrow\mathsf{Promise}\langle U\rangle\mid V\quad V\le P}
     {\mathit{TResult}:=U\mid V\ \ \text{at}\ \ (\vec A)\Rightarrow\mathit{TResult}\mid\mathsf{Promise}\langle\mathit{TResult}\rangle}
```

The instance is the producer's proposal, checked as any instance of a
scheme ([`compareInstArrsState`](POSITIVE-TYPES.md#instances-of-a-scheme-row)).
Background: [promises and flattened types](REFERENCES.md#promises-and-flattened-types).

### Objects owning `then`

An object the program makes may own a `then` member, a field or a method of
any type (`then-member-fields`). Two facts keep such an object from passing
for a promise or being adopted as one.

**No object the program makes meets `Promise<T>`.** The native `Promise`
contract holds, on its prototype record, the methods' slots, `constructor`
and the required readonly field $`\sigma_{\mathit{tag}}:\mathsf{string}`$, with
$`\sigma_{\mathit{tag}}`$ the standard library's `Symbol.toStringTag`. A
record with a prototype record is the model's `refs` clause owning
`[[proto]]` at that record, so a value of `Promise<T>` owns `[[proto]]` at an
object owning $`\sigma_{\mathit{tag}}`$. Lean checks:

- the symbol list names $`\sigma_{\mathit{tag}}`$ by its declaration identity
  (the module `lib.es2015.symbol.wellknown.d.ts`, the name `toStringTag`),
  and the native `Promise` definition, selected by its identity, states it on
  its prototype as a readonly `string`; a document lacking either is refused
  (`tagDeclarations` in `Claims/Preparation.lean`);
- every prototype a lowered head's row states under `[[proto]]`, through its
  bases, intersections and instances as lowering resolves them, is a head
  whose row is records (`refs` or `dict` clauses; a callable object or any
  other shape is refused), and the only such records holding
  $`\sigma_{\mathit{tag}}`$ are the native `Promise`'s (`tagPrototypes` in
  `Equations/Store.lean`). A copy of
  that record is the same record, so a declaration extending `Promise` holds
  it (`tag-fake-holder`);
- no allocation of the source's code (a literal, a class's prototype or
  instance), no class value's static and no named write is keyed by it
  (`tagGate`), and a key-adding write refuses a key whose possible values
  include it: one typed `symbol`, listed or not, or the tag's literal
  (`executionGrowth` in `Lowering/Execution.lean`;
  `invalid-tag-computed-write`, `symbol-key-growth-refused`); a `unique
  symbol` key other than the tag is admitted (`symbol-key-write`). The parser
  refuses the keys the source writes (`writtenSymbol`, the write at
  `Symbol.toStringTag`).

The symbol list's authenticity and completeness, that its entry is the
library's own symbol and that a symbol the source reaches is listed, are the
parser's, a trusted extraction obligation: Lean checks duplicate entries and
the identity's module and name.

The exclusion these give is conjectured, not proved. It concerns the
ordinary objects certified code allocates, its literals, classes' prototypes
and instances, class values and merges, not the promises the native
operations make:

```math
\frac{o\ \text{an ordinary allocation of certified code}\quad o'\ \text{reached from}\ o\ \text{through}\ [[\mathit{proto}]]}
     {o'\notin⟦\mathsf{Promise}\langle A\rangle⟧}
```

for every $`A`$. The argument:

- such an object owns no $`\sigma_{\mathit{tag}}`$: every key of a literal, a
  class's prototype or instance and a class value is checked above, a
  key-adding write adds no key that may be it, and a merge copies string keys
  only (`copiedKey`, $`\mathsf{data}_h`$);
- its `[[proto]]` is a class's prototype, itself such an allocation, or no
  key at all (a literal owns none). A prototype is reached by no source
  expression, so no write, alias or prototype change reaches it: `__proto__`,
  `Object.create`, `Object.setPrototypeOf` and accessors are outside the
  fragment ([fragment](SOURCE-FRAGMENT.md));
- a class's base is a class of the same file (`invalid-tag-ambient-base`
  refuses a declared one), so the chain holds only such prototypes.

`checkUnitJson_safe` does not depend on it: the theorem gives the modeled safety
of every accepted unit under its premises, and the exclusion is part of the
correspondence between that model and JavaScript, beside the native-promise
invariant on the [trust surface](DESIGN.md#trust-surface). Promises come from
the native operations: async functions and the intrinsics make them during
certified execution, and the native identity and standard prototype of every
value of the external heap at a `Promise` type are host assumptions. A
declaration's tag is no evidence of that identity. A declared class's
`[Symbol.toStringTag]`, own or inherited (`Map`'s), is a field of its
instance, which states no prototype (`declared-symbol-members`,
`invalid-tag-inherited-declaration`, refused first at its methods' binders;
the forged controls of `tag-fake-holder` give a declaration the native
methods, and without the tag it is refused at the return). Other well-known
symbols keep their own restrictions: a declaration's `[Symbol.iterator]` is
read as declared.

**Identity by structure.** A value the program builds is kept out of
`Promise<T>` by structure: certified code writes no `[Symbol.toStringTag]`,
which the native prototype record requires. A native internal slot (the
`[[PromiseState]]` that [ECMA-262](REFERENCES.md#ecma-262)'s `IsPromise`
tests) accepts the same programs, and is the cheaper mechanism for a program
that writes its own `[Symbol.toStringTag]` or subclasses `Promise`, or for
one mechanism shared by `Set`, `Map`, `Date`, `RegExp` and `Promise`. A
survey of 12.9 M lines of library and tooling code in `node_modules`
(2026-10-19, no application code) found custom thenables in 19 packages,
about 30 hand-written tags and about 7 `Promise` subclasses in 5 packages,
against `extends Error` 1,150 times in 236 packages; TScert's own source
has none of the first three.

**A callable `then` reaching a resolution is refused.** The obligations above
stay at each resolving operation:

- `%Await%` and `%PromiseResolve%` require $`\mathsf{Obs}`$ and `%AsyncReturn%`
  $`\mathsf{Desc}`$;
- a `finally` cleanup result is $`N`$ or a native `Promise<unknown>`;
- `%NewPromise%`'s `resolve` takes $`T\le P`$.

A record with a callable `then` is in neither $`N`$, whose record arm
requires `then` absent or a primitive as a lifetime contract, nor `Promise`.
So is an open record such as `{ a: number }`, which admits one. Each
operation refuses it with its own diagnostic (`invalid-await-thenable-literal`,
`invalid-await-thenable-width`, `invalid-await-inherited-then`,
`invalid-async-return-thenable`, `invalid-promise-resolve-thenable`,
`invalid-finally-thenable`, `invalid-new-promise-thenable`, each run under
Node: the `then` is called). An object whose `then` is an array, a
statement list, passes allocation and stays outside $`N`$, so awaiting or
resolving it is refused too. No checked thenable protocol (calling `then`
with resolving functions and adopting the result) exists.

`PromiseLike<T>` is structural: an object whose `then` meets its signature
meets it, and `await` refuses one (`invalid-await-promise-like`). The native
`then` and `catch` resolve their callbacks' results, so there, and only
there, the parser reads TypeScript's `PromiseLike<R>` as the native
`Promise<R>`, by the declaration's identity, and Lean refuses a native
`Promise` definition naming `PromiseLike` (`invalid-then-callback-thenable`,
`invalid-catch-callback-thenable`). The native contract is then no
`PromiseLike`: its `then` takes fewer callbacks (`invalid-promise-like`). `Awaited<T>`
qualifies its binder through an alias as written ([implied bounds](#implied-bounds);
`awaited-alias`, `invalid-awaited-alias-thenable`). `for await` stays refused.
This reading covers the native `Promise` declaration; it is no audit of the
`PromiseLike` positions of imported signatures.

The forged controls (`pipeline/test.mts`) refuse a document whose tag is
renamed or dropped, stated of another prototype or of a base's, whose
native `then` names `PromiseLike`, or whose allocation is keyed by the tag; a
declaration given the native methods without the tag; claims putting a
thenable at each resolving operation's instance, claiming an allocation with
a callable `then` as a `Promise<number>`, or a key-adding write's key at
`symbol`.

## Enums

With $`m_1,\ldots,m_n`$ an enum's members and $`v_i`$ the value TypeScript
computes for $`m_i`$ (`getConstantValue`), $`\bot`$ where it computes none.
No member of any enum is named `__proto__`: TypeScript's emit writes a member
by assignment, which for that name runs the prototype's setter and creates
no property.

```math
\frac{\forall i.\ v_i\ \text{computed by TypeScript, finite if a number}\quad
      \text{no reverse key names a member}}
     {\texttt{enum E}\{\vec m\}\ \leadsto\ \texttt{const E}:\mathcal O(E)=\{\overline{m_i:v_i},\ \overline{\mathrm{str}(v_j):\text{"}m_j\text{"}}^{\,v_j\in\mathbb R}\}}
```

with $`\mathcal O(E)`$ the object type of those fields, each readonly at its
value's literal type, in JavaScript's key order where the declaration is. The
type `E` is $`\bigcup_i\{v_i\}`$, `E.A` the literal type of `A`'s value, and
`typeof E` is $`\mathcal O(E)`$. A `const enum` read is its member's value
(`constEnumReads`), and the declaration runs nothing.

A member TypeScript computes no value for has an initializer $`e_i`$ whose
value, a number (TypeScript requires it), is known only at run time, and so
is the key of its reverse mapping. With $`\tau_i`$ a member's value type,
$`\{v_i\}`$ or $`\mathtt{number}`$ where $`v_i=\bot`$, the object of its
members, and the object of its members and of the reverse keys of the values
TypeScript computes, are

```math
\mathcal O^{\circ}(E)=\{\overline{\mathtt{readonly}\ m_i:\tau_i}\},\qquad
\mathcal O^{\rho}(E)=\mathcal O^{\circ}(E)\uplus
  \{\overline{\mathtt{readonly}\ \mathrm{str}(v_j):\mathtt{string}}^{\,v_j\in\mathbb R}\},\qquad
E=\textstyle\bigcup_i\tau_i ,
```

$`\mathcal O^{\rho}(E)`$ in JavaScript's key order where its keys are known.
At $`\mathrm{str}(v_j)`$ the emit writes $`m_j`$'s name, and a later member
whose value, known only at run time, is $`v_j`$ writes its own name there,
so the key holds a member's name; no member's own write reaches it, since
no member is named by a canonical numeric string (below).
The declaration runs each such initializer in order, bound to a constant of
its own, then builds the object with the trusted step
$`\%\mathsf{Enum{:}E}\%:(\mathcal O^{\circ}(E))\Rightarrow\mathcal O^{\rho}(E)`$,
which adds the reverse mapping
([intrinsics](../tools/intrinsics.mts)):

```math
\frac{\exists i.\ v_i=\bot\qquad
      \forall i.\ m_i\notin\{\texttt{NaN},\texttt{Infinity}\}\qquad
      \forall i.\ v_i=\bot\Rightarrow \mathrm{reads}_E(e_i)\subseteq\{m_j\mid j<i\}}
     {\texttt{enum E}\{\vec m\}\ \leadsto\
      \overline{\texttt{const}\ \%E.m_i\%:\mathtt{number}=e_i[\overline{m_j:=u_j}]}^{\,v_i=\bot};\
      \texttt{const E}:\mathcal O^{\rho}(E)=\%\mathsf{Enum{:}E}\%(\{\overline{m_i:u_i}\})}
```

with $`u_j`$ the constant $`\%E.m_j\%`$ where $`v_j=\bot`$ and the literal
$`v_j`$ otherwise, and $`\mathrm{reads}_E(e)`$ the members of `E` that $`e`$
reads, bare, `E.M` or `E["M"]`, as TypeScript binds them (`enumMemberRead`);
any other read of `E` in $`e_i`$ is refused. JavaScript writes each member's
property and its reverse entry between the initializers; only a read of `E`
could observe that order, and a call in an initializer that can read `E`
before it is bound is refused by the initialization order check. A member
named by a canonical numeric string other than `NaN` and `Infinity` is a
TypeScript error (TS2452), so no reverse key is a member's name.

An ambient enum (`declare enum`, not `const`) runs nothing: its object is
the environment's, read as a `declare const` is
([ambient values](#imported-ambient-and-global-values)), with $`v_i=\bot`$ for a
member it does not initialize, which TypeScript leaves opaque:

```math
\frac{\texttt{declare enum E}\{\vec m\}}
     {\Gamma(E)=\mathcal O^{\circ}(E)}\ \textsf{ambient-enum}
```

The type `E` is $`\bigcup_i\tau_i`$ there too.

An enum another module declares, imported or reached through a
declaration, merged declarations together, is the object of its members,
with its reverse keys where that object is built by TypeScript's emit or
checked to hold them:

```math
\frac{\text{every declaration of }E\text{ in a program module, outside an ambient context}\ \lor\
      E\ \text{a host enum whose object is checked}}
     {\Gamma(E)=\mathcal O^{\rho}(E)}\ \textsf{emitted-enum}
```

and $`\Gamma(E)=\mathcal O^{\circ}(E)`$ otherwise. A program module is a
source file outside the standard library, the host packages and installed
packages; an ambient context is a `declare` modifier on the declaration or
an enclosing one, or a declaration file. The import assumption of
[the trust surface](DESIGN.md#trust-surface), that an imported value meets
its declaration, covers a program module's enum as its emit builds it: its
members, and at each value TypeScript computes the name of a member with
that value, as above (`enum-reverse-value-import`, imported directly and
through a re-export). A host enum is read as a value only where the contract
lists it (`hostEnums` in [`compiler-api.mts`](../tools/compiler-api.mts)),
whose runtime object `tests/compiler-api.mts` compares with the declaration
(C1), or as a family's tag enum, whose runtime object activation compares
with the declaration ([activation](HOST-FAMILIES.md#activation)); both by
one condition (`enumObjectMatches`): each member an own data property
holding its value, at each numeric value's key an own data property holding
the name of a member with that value, and no other own key. Any other enum,
a declaration file's or the program's ambient one, is the environment's
object, of which its members alone are assumed
(`invalid-enum-reverse-declared-value-import`, `invalid-ambient-enum-reverse`).
`E.M` is the literal type of `M`'s value and `typeof E` is $`\Gamma(E)`$. An
imported `const enum` has no object to read and is refused as a value. At a
position of a declaration of a
[host package](COMPILER-API.md#host-declarations) the type `E` is `number`
(reading rule 3): TypeScript admits any number at a numeric enum type, and
the flag enums hold combinations of members, which are no member's value.

A read `E[k]` is the keyed read of the enum's object: at a key whose type is
a union of the literals of numeric values the object type states, per
singleton that reverse key's field, the last member's name for
$`\mathcal O(E)`$ and `string` for $`\mathcal O^{\rho}(E)`$
(`enum-reverse-keys`, `compiler-api-enum-reverse`). At `number`, or at a
literal outside those values, the object type states no field, and the read
is refused (`invalid-enum-reverse-number`, `invalid-enum-reverse-outside`):
there the object may hold `undefined` (an enum with a member known only at
run time holds further reverse keys), which TypeScript types `string` by the
enum object's index signature `[x: number]: string` (`string | undefined`
under `noUncheckedIndexedAccess`). A string member has no reverse key
(`invalid-string-enum-reverse`). Each negative but the declaration file's
runs under Node, the ambient one over an object without the reverse
mapping; claims bypassing the producer that read a reverse key at `number`
or of an ambient enum are refused (`pipeline/test.mts`).

## Const assertions

`e as const` returns its operand, claimed at the operand's *const type*:

```math
\mathsf{const}(\ell)=\{\ell\},\qquad
\mathsf{const}([e_1,\ldots,e_k])=\mathsf{readonly}\;[\mathsf{const}(e_1),\ldots,\mathsf{const}(e_k)],
```
```math
\mathsf{const}(\{f_1:e_1,\ldots\})=\{\mathsf{readonly}\;f_1:\mathsf{const}(e_1),\ldots\},\qquad
\mathsf{const}(x)=\Gamma(x),\qquad
\mathsf{const}(e\;\texttt{as const})=\mathsf{const}(e),
```

for a literal $`\ell`$; any other operand is refused. An element or field of a
literal that is none of these (`[x.f] as const`) keeps its own type,
$`\mathsf{const}(e_i)=\tau(e_i)`$, as TypeScript's const context does. The const type is a
proposal: Lean checks the operand's allocation at it and the cast's claim
from the operand's. Other assertions (`e as T`, `e satisfies T`, `e!`) are
the same node with $`T`$ an obligation the operand meets; nothing decides an
assertion true.
