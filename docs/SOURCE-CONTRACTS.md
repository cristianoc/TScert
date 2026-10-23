# Reading the source

Source verification requires a faithful interpretation of annotations, module
bindings and library contracts. This document specifies their translation into
graph types and core operations, together with statement, iterator and guard
lowering that consumes those contracts.

The prerequisites are the judgments and state rules in
[Program typing](PROGRAM-TYPING.md), declaration equations and binders in
[Recursive equations](RECURSIVE-EQUATIONS.md), and graph types in
[Positive types](POSITIVE-TYPES.md). Types are finite unions of graph labels;
$`\Gamma`$ assigns types to variables, and $`\Gamma\vdash_G t:A`$ is the core
term judgment. Source extraction and evidence search are specified in
[Source elaboration](SOURCE-ELABORATION.md); runtime values and worlds in
[Semantics](SEMANTICS.md). The trusted source model and refusal boundaries are
specified in [Source model](SOURCE-MODEL.md) and
[Source fragment](SOURCE-FRAGMENT.md).

Throughout, $`⟦T⟧`$ is the graph type a
declared or written term lowers to, and $`T[\vec p:=\vec U]`$ the term with its
binders fixed to ground types.

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
binding more parameters, as JavaScript calls it. A function with a rest
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

and $`C\sqsubseteq_G A`$ implies $`⟦C⟧_G\subseteq⟦A⟧_G`$
(by `check_sound`; the first rule compares rows with identical clauses). A
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
exactly those; an implementation's own signature is not callable from outside:

```math
\frac{x\ \text{declared with overloads}\ S_1,\ldots,S_n\ (n>1),\ \text{none generic}}
     {\Gamma(x)=\bigwedge_i⟦S_i⟧}\ \textsf{overloads}
```

Each call is checked against the conjunction, so it is typed by any overload
whose parameters admit its actuals. A generic overload is refused.

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
`this` result is the host. A declaration's `any` is read as `unknown`. A
global both called and read through a method, or both constructed and read
through members, has no clause and is refused, unless the overlay reads those
members as intrinsics. A global both read as a value and constructed is
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

An interface the checked file declares more than once, as TypeScript merges
it, is one declaration: its body holds every declaration's members, each at
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
reads the name as that parameter (`EquationStore.rebind`).

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
widens an inferred result, the object literals it returns with their exact
keys ([literals a spread copies](SOURCE-MODEL.md#literals-a-spread-copies)),
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
do not meet the scheme (a gap, `class-static-generic-value-refused`: the slot
holds the scheme or the instances, not the scheme with the static-field
facts).

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
intersections so (`annotationClaim`), each binder read as the row the unit
reads it as, its parameter row met with a ground bound or with the binder
bounding it (`binderRows`): `T & U`, `T & "fixed"`, `T & object` and
`A<U> & B<V>` are meet rows or meets of application rows over the binders'
rows. An operand whose row is not yet filled, a declaration being lowered or
a recursive application met inside its own equation
(`TreeNode<T> & TreeLeaf<T>` in `TreeLeaf<T>`'s field), makes the meet a row
of its own that waits for it (`waitingMeet`), filled once every operand is
(`settle`); a nullary declaration an intersection names is lowered first, so
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
parameter (`resolvableBound`). A program's own alias of that name is an
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
derived class's constructor is the [derived form](SOURCE-ELABORATION.md#derived-source-forms) over
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
the writable string index. One whose value names its key, as `Pick`'s and
`Readonly`'s $`T[P]`$, is refused. An interface's `extends` clauses are the meet of
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
the one value; call signatures beside writable fields are the callable
carrying them ([callable-meet](#intersections-of-functions-and-records)).
With $`⟦\sigma_1⟧,\ldots,⟦\sigma_n⟧`$ the signatures' fixed ones $`L`$ and
variadic ones $`S`$, each receiver `top` unless a `this` parameter states it,
and $`\varphi`$ writable fields:

```math
\frac{⟦\sigma_1⟧,\ldots,⟦\sigma_n⟧=L;S}
     {⟦\{\,\sigma_1;\ \ldots;\ \sigma_n\,\}⟧=\mathsf{arrs}(L;S)}\ \textsf{call-literal}
\qquad
\frac{⟦\sigma_1⟧,\ldots,⟦\sigma_n⟧=L;S}
     {⟦\{\,\sigma_1;\ \ldots;\ \sigma_n;\ \varphi\,\}⟧=\mathsf{callable}(\varphi;L;S)}
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
reference's arguments), a named type's member through its annotation under
the same identity premise.

A **computed alias** is a generic alias whose equation is a computed form or
an application of another computed alias (`computedAlias`): `type
ElementOf<T> = T[number]`, `type Keys<T> = keyof T`. Over its parameters it
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
`Keys<{ good: E }>` is `"good"`. A `typeof` of a constant without an
annotation is the type TypeScript infers for its initializer where that is a
union of literals and primitives or an object literal's record of such
types, each property a writable field and each index a spread copied, read
from the checker (`inferredTerm`):

```math
\frac{\mathtt{const}\ x=e\quad \mathit{ts}(\mathtt{typeof}\ x)=\{\overline{k_i\colon t_i};\ \overline{[\theta_j]\colon u_j}\}\ \text{from}\ e\text{'s literal}\quad
      \forall i.\ ⟦t_i⟧\ \text{inferred}}
     {⟦\mathtt{typeof}\ x⟧=\{\overline{k_i\colon⟦t_i⟧};\ \overline{[\theta_j]\colon⟦u_j⟧}\}}\ \textsf{typeof-inferred}
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
([types stated by annotations](SOURCE-FRAGMENT.md#types-stated-by-annotations));
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
unique symbol mapped to the constant declaring it in the original program;
an enum member, whose identity the fragment has no literal for, and any
other type are refused. A computed alias applied in an annotation reads its
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
`unknown`, so `Box<any>` with a bounded `Box` is refused.

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
at records is the [named access](SOURCE-ELABORATION.md#derived-source-forms) of that key.

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
result. Of `ArrayProto`, `slice`, `join`, `toString`, `indexOf`,
`lastIndexOf`, `includes`, `at`, `[Symbol.iterator]`, `values`, `keys` and
`entries` state it: they read the receiver, convert only numbers and elements meeting the conversion
contract below, compare by strict equality or SameValueZero, and allocate
only their result. `find`, `findIndex`, `filter`, `some`, `every`,
`forEach` and `flatMap` call a callback; each reads the length once and the
receiver's own numeric keys, data properties (`numericOwn`), and allocates
only its result by ordinary construction, so beside the callback it runs no
client code and is within the callback's footprint: it has one signature per
closed footprint $`\varepsilon`$ (`array-preserving-callbacks`,
`map-stable-filter-push`, `invalid-map-filter-pop`):

```math
\frac{m\in\{\mathsf{filter},\mathsf{some},\mathsf{every},\mathsf{forEach}\}\quad f:(T,\ \mathsf{number},\ \mathsf{ReadonlyArray}(T))\Rightarrow_{\varepsilon}\mathtt{unknown}}
     {\mathit{xs}.m(f):R_m\;!\;\varepsilon}\ \textsf{native-callback}
```

with $`R_m`$ the member's result: $`T[\,]`$, `boolean`, `boolean`,
`undefined`. `Boolean` read as a value is such a callback
([library globals](#library-globals)). The members that write their receiver (`sort`,
`push`, `pop`, `shift`, `unshift`, `reverse`) and those that call an
unrestricted callback do not.

`filter` is stated at TypeScript's guard overload too,
`filter<S extends T>(predicate: (value: T, index: number, array: readonly T[]) => value is S): S[]`,
read at a callback whose [promise signature](#user-defined-guards) promises
$`S`$ of its first actual:

```math
\frac{f:(T,\ \mathsf{number},\ \mathsf{ReadonlyArray}(T))\Rightarrow S\,[\mathsf{guards}\ 0]}
     {\mathit{xs}.\mathsf{filter}(f):S[\,]\;!\;\top}\ \textsf{native-guard-filter}
```

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
signature states the callback at the top footprint, the one a closure's
promise signature is checked at, so the call may change any location; its
result is fresh. A callback whose promise is about another parameter, or a
promise signature at fewer parameters than the callback takes (a guard read
as a value, `nodes.filter(ts.isIdentifier)`), meets only the plain
signatures, where `filter` keeps `T` (`compiler-api-guard-values`,
`filter-guard-value-refused`).

`find`'s guard overload is not stated: at the top footprint `find` visits
positions a callback removed and passes them `undefined`, so its callback
there takes `T | undefined`, which a guard closure TypeScript types at `T`
does not admit. `every`'s, `this is readonly S[]`, is not a contract of the
native: a callback may append untested elements or replace tested ones, so
a traversal answering `true` says nothing of the receiver it leaves.

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
\mathsf{flatMap}:\forall U.\ (\mathsf{this}:\mathsf{ReadonlyArray}(T),\ (T,\ \mathsf{number},\ \mathsf{ReadonlyArray}(T))\Rightarrow\mathsf{sparse\ ReadonlyArray}(U))\Rightarrow U[\,]
```

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

`join` and `toString` each quantify `T` with bound `T ≤ D`. For `sort`, let
A(T) be the mutable array contract, V(D) its readonly view at D, and C(T) the
comparator `(T,T) → number`.
Its one scheme offers the intersection:

```math
\forall T.\quad
 ((\mathsf{this}:A(T),\ C(T))\Rightarrow A(T))
 \;\cap\;
 ((\mathsf{this}:A(T)\cap V(D),\ \mathtt{undefined})\Rightarrow A(T)).
```

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

`Set<T>`, `Map<K, V>` and `Date` are read through the same mechanism
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
`forEach`, which calls a callback. `new Set` and `new Map` of an array or of
nothing state the empty footprint on their construct signatures: they read the
array through the host's iterator and allocate. $`⟦m⟧_\omega`$ drops
`thisArg`, reads a `this` result as the receiver, and reads a declared
iterator result as `Iterator<T>`, which it extends, or, for `Set`'s and
`Map`'s `keys`, `values`, `entries` and `[Symbol.iterator]`, as the native
collection iterator, `Iterator<T>` marked as the built-in one
([loops and spreads](#loops-and-spreads-over-iterables)). A property is a readonly
view. A string's own `length` and indices are the calculus's `lenStr` and
`elemStr`, never the prototype's; `s[i]` is `string | undefined`.

`ReadonlySet<T>` and `ReadonlyMap<K, V>`, the readers' views of a `Set` and a
`Map`, are read through the same mechanism at the restriction of the
collection's own readers (`forEach` without `thisArg`, `has`, `get`, `size`,
`keys`, `values`, `entries` and `[Symbol.iterator]`, each iterator result an
`Iterator`, which the native collection iterator meets), so that `Set<T>` meets `ReadonlySet<T>` and `Map<K, V>` meets
`ReadonlyMap<K, V>` by width and by the callback's parameter, as `Array`
meets `ReadonlyArray` (`readonly-collection-views`). They state no
`[Symbol.toStringTag]`, so a program's object may meet them: each member
states the effect its declaration does, which is no footprint
(`invalid-readonly-set-has-effect`, run under Node), and a loop or a spread
over one runs the [iterator protocol](#the-iterator-protocol).

### Native footprints

A native's **footprint** is the closed footprint its signatures state
([FOOTPRINTS](FOOTPRINTS.md#changes-and-footprints)): for the locations that
existed before a call, the change the call may make to those holding a value
and to those holding an array store. Each row states its argument, proved
where the native is modelled and audited otherwise:

| Native | Footprint | Argument |
| --- | --- | --- |
| `push`, `unshift` | `{value: any, store: grow}` | proved of the specification steps: `Arr.push_grow`, `Arr.unshift_grow`, `array_native_post`; that each changes nothing but its store and element contents is audited |
| `pop`, `shift`, `reverse` | `{value: any, store: keep}` but for the receiver's store (`receiverStore`) | each changes only its receiver's store, which it can make lose a present index (controls in `FootprintControls.lean`), and element contents (audited) |
| `filter`, `map`, `flatMap`, `slice`, a string's `split` | a fresh result, beside the rows' footprints | each allocates its result by ordinary construction, a store no earlier heap held (audited) |
| `map` at a dense receiver and a callback within `ε`, `ε` one of the four of the stable set | `ε` | one signature per such `ε`, with a dense result (`map_rely`); `map` reads its receiver and allocates its result (audited) |
| `map` at any receiver and any callback | `{value: any, store: any}` | the unrestricted signature, with a result that may hold holes |
| a global or sticky native regex's `exec`, `test`, `[Symbol.match]`, `[Symbol.replace]` at a string | `{value: any, store: keep}` | they write only `lastIndex`, a number (audited) |
| a native regex's other members, a regex neither global nor sticky | the empty footprint | they write nothing (audited) |
| `%Dispatch:replace%` | its target member's footprint | one signature per closed footprint (audited, as its target's) |
| an iteration intrinsic, `%Iterate%` over an array and those over a string, a `Set`, a `Map`, a host iterator and a native match iterator; its step; a spread form `%Spread:K%` | the empty footprint; `{value: any, store: keep}`; `{value: any, store: keep}` | they run no client code; a step writes only the iterator's position and, for a match iterator, its clone's `lastIndex`, each a number, and allocates what it yields (audited) |
| `Math.max`, `Math.min`, `String.fromCodePoint`, `String.fromCharCode` at primitives | the empty footprint | they convert primitives, which runs no code, and allocate only their result (audited) |
| `forEach`, `every`, `some`, `filter`, `find`, `findIndex`, `flatMap` at a callback within `ε` | `ε` | one signature per closed footprint; beside the callback each reads the receiver and allocates only its result (audited) |
| `new Set`, `new Map` of an array or nothing | the empty footprint | they read the array through the host's iterator and allocate (audited) |
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

- **Proved** of the array mutators' specification steps (`Set` of an index,
  `Delete`, a length change, in the order ECMA-262 gives them;
  `lean/Verification/Semantics/FootprintNatives.lean`): `push`, `unshift`, a
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
(the assumption `%Iterate:String%` makes). Every form keeps its parameters,
result, effect and binder substitution. The declaration's text matches the
reviewed one exactly; every form is decoded, and an empty or malformed list,
or an unsupported combination of binders, is refused, never an arm dropped
(`set-string-construction`; `invalid-set-string-at-number`,
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

The entries, each with the code its restriction keeps from running:

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
- `parseInt(s, r)` and `Math.ceil(x)` convert a string and numbers, primitives
  no conversion code runs on, and write nothing: as declared, within the empty
  footprint (`library-parse-int`, `library-math-ceil`). No argument of their
  parameter types converts by code.
- `Object.fromEntries(entries)` steps its argument's iterator, reads each
  element's 0 and 1, converts the key and defines it on a fresh object. Over
  an array the iterator is the host's and a pair an array of data, so it runs
  no code and writes nothing it did not allocate:
  $`\forall T.\ (\mathtt{readonly}\ (\mathtt{readonly}\ [\mathtt{string},\ T])[\,])\Rightarrow\{[k:\mathtt{string}]:T\}`$,
  within the empty footprint (`object-from-entries`). A program's iterable
  runs its iterator (`invalid-from-entries-iterable`, run under Node).
- `Array.from(xs)` of an array copies it through the host's iterator,
  a hole read as `undefined`: $`\forall T.\ (\mathtt{readonly}\ T[\,])\Rightarrow T[\,]`$
  within the empty footprint (`array-from-copy`). `Array.from(items, f)` of a
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

- `Object.values(o)` and `Object.entries(o)` at TypeScript's `{}` overload
  read the values of `o`'s own enumerable string keys:
  $`(\mathsf{NonHost})\Rightarrow\mathtt{unknown}[]`$ and
  $`(\mathsf{NonHost})\Rightarrow[\mathtt{string},\mathtt{unknown}][]`$;
  their dictionary overloads are stated at a dictionary.
- `console.log(…)` formats every reachable key of an object argument; its
  arguments are stated at $`\mathsf{Prim}`$:
  $`(\ldots\mathsf{Prim})\Rightarrow\mathtt{undefined}`$
  (`console-log-object-refused`).

$`\mathsf{NonHost}`$, which no source spells, is every value but a host
object ([restricted values](HOST-FAMILIES.md#restricted-values)): the
primitives, the callables and the objects owning no `[[host]]`, the record
clause bounded by an exclusion of that key. A type is below it when each of
its clauses is: an object clause names an invariant field or an index, or
bounds its own keys without the key (`CoversBounds`), so `{ a: number }` is
below it and `{ readonly a: number }`, `object` and `unknown` are not
(`host-exclusion-reflection`, `object-values-readonly-refused`).

`Reflect` is a namespace, whose functions are no annotated variable's
members, and `Reflect.get(o, k)` runs [[Get]], which calls an accessor's
getter, code no type of `o` states: it is refused.

Overloads stated alike are one signature. A statement may name a library
interface (`Set<T>`, read through [its overlay](#prototype-contracts)) or a
declaration no library has, which joins the document with the entry:

```math
\mathsf{JsonValue}=\mathsf{null}\mid\mathsf{boolean}\mid\mathsf{number}\mid\mathsf{string}\mid\mathsf{readonly}\ \mathsf{JsonValue}[\,]\mid\{\mathsf{readonly}\ [k:\mathsf{string}]:\mathsf{JsonValue}\}
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
the text only (`json-parse-reviver-refused`). A dictionary arm is no array
(its members own no prototype key), so `Array.isArray` of a `ParsedJson`
leaves its array arm, whose `map` stays dense (`json-parse-data`).
`ParsedJson` is a `JsonValue`: each of its arms is one read-only. A
`JsonValue` array owns no `toJSON` (the arrays' own-key exclusion,
[arrays](SOURCE-MODEL.md#arrays)), inherits none (no object along its chain
holds one, a host assumption), and holds `JsonValue`s. It is dense: a
readable array admits a hole only where `undefined` meets its element
contract, which `JsonValue` excludes, and neither `Array.prototype` nor
`Object.prototype` owns a numeric key ([trust surface](DESIGN.md#trust-surface)).
A dictionary owns no prototype key and holds `JsonValue`s at every string key
it owns, none callable: a member `JSON.parse` defines under the name
`"toJSON"`, at any depth, is JSON data, which `JSON.stringify` reads and does
not call (`json-parse-stringify-tojson-member`, run under Node). At a `JsonValue`, `JSON.stringify` reads own data properties,
calls no `toJSON` and no getter, and allocates its string, so it returns a
string and states the empty footprint, on a throw too (a cycle); so does `Error`
at a string message, which it stores without conversion code
([exceptional footprints](SOURCE-MODEL.md#exceptional-footprints);
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
array reaches under such a merge is refused, whether the array is written or
a callback's parameter by context (`invalid-merged-array-param`,
`invalid-merged-array-callback`, `invalid-merged-readonly-array-param`,
`invalid-merged-readonly-array-callback`).
`JSON.stringify` is read with a replacer that
is `null`, absent or a list of keys (primitive numbers and strings, read by
length and index), and an indent that is a primitive number or string:
none runs code (`json-stringify-space`). A boxed key or indent would run
its `toString` or `valueOf` (`invalid-json-stringify-boxed-key`,
`invalid-json-stringify-boxed-space`, run under Node). `Error` is read with its one
argument. A `toJSON` hook, a replacer function and `Error`'s options run
code of the client's, which may write what a footprint excludes
(`invalid-json-stringify-tojson`, `invalid-json-stringify-replacer`,
`invalid-error-options`, each run under Node). An entry may
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
any[]` is not read. An entry may read a member, or a construct signature, as
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

**Symbol keys.** A computed key `[k]`, in a type, a literal or a read,
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

### Node's `process`

Node's `process` and `console` are read through the overlay at the members
the repository's code uses, each pinned to its declaration in the pinned
`@types/node` installations, their origin the package `@types/node`,
observed under Node 25.2.1 (2026-10-19). A member read at a stated contract,
and every reviewed method, is a readonly view: no write of it is admitted,
through `process` or through the process a registration returns
(`invalid-node-process-replace-result`, `invalid-node-process-replace-alias`).

- `process.argv`: an array of strings Node builds at start-up, read as
  $`\mathtt{readonly\ string}[\,]`$. The property is writable: no code
  replaces it or writes a non-string into it, an assumption.
- `process.execPath`, a string, and `process.pid`, a number.
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
  (`collections-process` and `collections-main`, gaps; `invalid-node-process-meta-event`,
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

## Library modules

A function a client imports from one of Node's modules (`node:fs`, or `fs`)
is read through the reviewed overlay of library modules
(`library-modules.mts`) where an entry lists it, and otherwise as an
imported value ([imported values](#imported-ambient-and-global-values)).
An entry names one overload of the function's declaration in Node's
declarations, with exactly the text it was reviewed against, and states the signature the host meets at the arguments it
admits, $`(\vec P)\Rightarrow R`$. With $`\Omega_m`$ the overlay, $`f`$
imported from module $`\mu`$ and $`O_f`$ the overloads TypeScript binds it to:

```math
\frac{\{\omega\in\Omega_m\mid \omega.\mathit{module}=\mu,\ \omega.\mathit{name}=f\}=\{\omega_1\ldots\omega_n\}\neq\emptyset\quad
      \forall i.\ \exists s\in O_f.\ \omega_i.\mathit{text}=\mathsf{text}(s)\quad
      \omega_i.\mathit{stated}=(\vec P_i)\Rightarrow R_i}
     {\Gamma(f)=\bigwedge_{i}(\vec P_i)\Rightarrow R_i}\ \textsf{library-module}
```

The declaration's types are not read, and neither are the types they name
(`Buffer`, `URL`, streams). Each statement is an assumption a result is
relative to, as an import's declared type is, and each says what the host
does at its parameters, where the declaration may say otherwise. A call is
unrestricted in its effect unless its entry states one. The entries:

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
  it does not accept: an object at each such key ran no code of the client's
  under Node 25.2.1.
- `execFileSync` has a second stated form, the **restricted form**. Its
  options state every key the synchronous path reads, each at a type Node
  validates without running code of the client's:
  $`(\mathtt{string},\ \mathtt{readonly\ string[]},\ O_r)\Rightarrow\mathtt{string}`$ with

  `O_r = { encoding: "utf8"; stdio: readonly [S, "pipe", S]; input?: string; maxBuffer?: number; env?: undefined; shell?: false; cwd?: string; argv0?: string; detached?: boolean; uid?: number; gid?: number; windowsHide?: boolean; windowsVerbatimArguments?: boolean; timeout?: number; killSignal?: string | number }`.

  A record type is open, so a key it does not name may hold any value; a key
  it names at `undefined` or `false` is absent or holds that value. The form
  states the empty footprint on normal return and on a throw
  ([exceptional footprints](SOURCE-MODEL.md#exceptional-footprints)). A call
  meeting only the first form keeps an unrestricted effect. The audit of Node 25.2.1's
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
- `readFileSync(path, "utf8")` with a string path returns the file's
  contents decoded as UTF-8; a path it cannot read throws:
  $`(\mathtt{string},\ \texttt{"utf8"})\Rightarrow\mathtt{string}`$. Without
  an encoding it returns a `Buffer`, outside the stated call
  (`node-fs-read`, `invalid-node-fs-read-buffer`).
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
  record (Node 25.2.1):
  $`(\mathtt{string},\ \mathsf{readonly}\ \mathtt{string}[\,],\ O)\Rightarrow\{\mathtt{pid}\colon\mathtt{number};\ \mathtt{status}\colon\mathtt{number}\mid\mathtt{null};\ \mathtt{signal}\colon\mathtt{string}\mid\mathtt{null};\ \mathtt{stdout},\mathtt{stderr}\colon\mathtt{string}\mid\mathtt{undefined};\ \mathtt{error}^?\colon\mathtt{unknown}\}`$,
  stating no effect: the host reads the options' properties
  (`node-spawn-sync`). Both streams are piped, so each output is a string
  where the child ran and absent where it could not be spawned, which the
  declared `string` omits (`invalid-node-spawn-sync-stdout`, run under
  Node); `stdio` naming no pipe leaves it `null` and is outside the stated
  call (`invalid-node-spawn-sync-stdio`, run under Node).
- `readdirSync(path, o)` with a string path reads `o.encoding` and
  `o.signal`, then `o.recursive`, `o.encoding` and `o.withFileTypes` (Node
  25.2.1's `lib/fs.js`). The four are stated,
  $`o=\{\mathtt{withFileTypes}\colon\mathtt{true};\ \mathtt{encoding}^?\colon\texttt{"utf8"}\mid\mathtt{undefined};\ \mathtt{recursive}^?\colon\mathtt{false}\mid\mathtt{undefined};\ \mathtt{signal}^?\colon\mathtt{undefined}\}`$,
  so under the caller contract ([trust surface](DESIGN.md#trust-surface))
  each is a data property whose reads agree. `recursive: true` walks the
  subdirectories, calling each entry's `isDirectory` through its prototype,
  `path.join` and a stat of the joined path to choose what to read next, and
  collects entries of every depth; that walk is not audited, so it is refused
  (`invalid-node-readdir-recursive`, run under Node: a replaced test runs
  during the call; [source fragment](SOURCE-FRAGMENT.md)). The call returns
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
  `prototype`, an entry's `constructor`, `Object.getPrototypeOf`,
  `Object.setPrototypeOf`, `Object.defineProperty` and `Reflect` are refused
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
  The declared `Dirent.path` is absent under Node 25.2.1, so the entry states
  none (`invalid-node-readdir-dirent-path`, run under Node), and a closure
  whose parameter TypeScript types as `Dirent` is refused.
- `node:path`'s `dirname` and `basename` with an optional suffix compute a
  string from their strings alone, within the empty footprint on their throw
  too (Node 25.2.1's `lib/path.js`). `join` of any number of strings,
  `resolve` of any number and `relative` of two compute one too, but `join`
  calls `posix.normalize` and `resolve` and `relative` call `process.cwd()`
  for a relative path, writable properties other code may replace, so they
  are unrestricted in their effect, as `realpathSync` is, which resolves its
  path the same way (`node-path-strings`; `invalid-node-path-join-callback`
  and `invalid-node-path-resolve-callback`, run under Node). The module
  exports one object (`export = path`), whose methods are the overloads an
  entry names.

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
([namespace imports](SOURCE-ELABORATION.md#derived-source-forms)), each
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

**Footprints.** Under Node 25.2.1 (observed 2026-10-19 by probes run under
Node), a passing `ok`, `equal`, `notEqual` and `ifError` run no code:
ToBoolean, `Object.is` and a comparison with `null` and `undefined`. A failing
call builds an `AssertionError`: it calls no `inspect.custom` hook, but it
reads the compared values' accessors while building the message, sets and
restores `Error.stackTraceLimit`, and runs a program's
`Error.prepareStackTrace`; a message that is an `Error` is thrown as it is.
Each entry states a footprint for normal return only, and unrestricted
effects on the exceptional edge: `onThrow` false, so a handler catching an
`AssertionError`, or whatever a hook throws instead, holds no fact about the
heap that the call's footprint would preserve, as the
[effect](SOURCE-MODEL.md#inferred-call-effects-elaboration-and-certification)
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
  is not stated, as the producer encodes no generic promise signature
  (`node-assert-equal-promise`, a gap). `notEqual`:
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
the native match iterator, $`\mu_I`$ the synthetic `RegExpStringIterator`. No
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
effect. A native regex's members run no client code, read its pattern and
flags, and allocate only their result; what they write is `lastIndex`. With
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
library class is no base (`invalid-regexp-subclass`). A replacement callback
is not stated. `new RegExp` of strings is the structural regex
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
fulfills it with `undefined`. A throw in an async body leaves it as a throw.
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
contract ([source objects and the tag](#source-objects-and-the-tag)). The native identity and standard
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
classification.

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

### Source objects and the tag

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

`checkJson_safe` does not depend on it: the theorem gives the modeled safety
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
`PromiseLike`: its `then` takes fewer callbacks (`promise-like`). `Awaited<T>`
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

## Loops and spreads over iterables

`for (const x of e) S` steps a trusted **iteration intrinsic**, one per kind
of host iterable, which the parser picks by TypeScript's type of $`e`$
(`iterationKind` in `declaration-graph.mts`, every part of a union alike).
With $`\mathit{Step}(E)=()\Rightarrow\{\mathsf{readonly}\ \mathit{value}:E\}\mid\mathsf{null}`$:

```math
\begin{array}{ll}
\mathtt{\%Iterate\%}:\forall T.\ (\mathsf{readonly}\ T[\,])\Rightarrow\mathit{Step}(T) & \text{an array or tuple}\\
\mathtt{\%Iterate{:}string\%}:(\mathsf{string})\Rightarrow\mathit{Step}(\mathsf{string}) & \text{a string, by code point}\\
\mathtt{\%Iterate{:}Set\%}:\forall T.\ (\mathsf{Set}\langle T\rangle)\Rightarrow\mathit{Step}(T) & \\
\mathtt{\%Iterate{:}Map\%}:\forall K\,V.\ (\mathsf{Map}\langle K,V\rangle)\Rightarrow\mathit{Step}([K,V]) & \text{a fresh entry per step}\\
\mathtt{\%Iterate{:}Iterator\%}:\forall T.\ (\mathsf{NativeCollectionIterator}\langle T\rangle)\Rightarrow\mathit{Step}(T) & \text{a SetIterator or MapIterator}
\end{array}
```

`Set` and `Map` are the [interface overlay](#library-types)'s, whose
`keys`, `values`, `entries` and `[Symbol.iterator]` give a `SetIterator` or
`MapIterator` read as the native collection iterator
$`\mathsf{NativeCollectionIterator}\langle T\rangle`$: `Iterator<T>` with
a key $`\langle\mathit{CollectionIterator}\rangle`$ at `undefined`, a
synthetic symbol no source declaration, literal or class states, so no
other value meets it. A value TypeScript types `SetIterator` or
`MapIterator` from any other source, a `ReadonlySet`'s or `ReadonlyMap`'s
iterator included, is no argument of `%Iterate:Iterator%`, and its loop is
refused (`invalid-readonly-set-iterator-native`, run under Node). None of these iterators has a `return`, so a
loop left early by `break`, `return` or a throw calls nothing. An iterable of
any other kind with a `[Symbol.iterator]` (an `Iterable<T>`, a class or a
record with one), or a union with one, is the program's, and runs the
[iterator protocol](#the-iterator-protocol); any other steps `%Iterate%`,
whose typing then refuses what is no array. Lean compiles the loop over a
host iterable itself (`SourceExtraction.body`), $`\mathit{it}`$ the picked
intrinsic:

```math
⟦\mathsf{for}\ (\mathsf{const}\ x\ \mathsf{of}\ e)\ S⟧=
n\leftarrow\mathit{it}(⟦e⟧);\
\mathit{head}:\ r\leftarrow n();\
\mathsf{if}\ r\ \mathsf{is\ null}\ \mathsf{then}\ \mathit{exit}\
\mathsf{else}\ x\leftarrow r.\mathit{value};\ ⟦S⟧;\ \mathsf{goto}\ \mathit{head}
```

`n` is a slot at the call's claimed type, the head a cut stated by the loop's
entry claims, `continue` and the body's end go to the head and `break` to the
exit; the tag dispatch refines `r` on each arm (`tagBind isNul`). The derived
rule, with $`\mathit{it}:\forall\vec\alpha.\ (P)\Rightarrow\mathit{Step}(E)`$ and
$`\sigma`$ the call's instance:

```math
\frac{\Gamma\vdash e:A\quad A\le P\sigma\quad
      \Gamma_{\mathit{head}},x:E\sigma\vdash S\quad \Gamma_{\mathit{head}}\ \text{the loop's entry claims}}
     {\Gamma\vdash\mathsf{for}\ (\mathsf{const}\ x\ \mathsf{of}\ e)\ S}\ \textsf{for-of}
```

The native iterator requires a readable array receiver, so every in-bounds
read yields `T`, including a hole when `T` admits `undefined`. A sparse store
needs a separate proof of readability before it satisfies that contract. Array patterns read positions under the same trust
([patterns](SOURCE-ELABORATION.md#patterns)).

An argument spread `f(…, ...e, …)` over an iterable of one of the other kinds
is the spread of the fresh array its iterator yields, collected where the
spread is written: $`\ldots e\equiv\ldots\mathtt{\%Spread{:}K\%}(e)`$, with
$`\mathtt{\%Spread{:}K\%}:\forall\vec\alpha.\ (P)\Rightarrow E[\,]`$ for each
$`\mathtt{\%Iterate{:}K\%}:\forall\vec\alpha.\ (P)\Rightarrow\mathit{Step}(E)`$, the
array of what that step yields until $`\mathsf{null}`$. It is an ordinary call
of a trusted value, and the array an ordinary spread into a variadic
callee. A spread of a program's iterable is collected by the
[protocol](#the-iterator-protocol).

A tuple meets `Iterable<T>` through the readonly array of its positions: the
producer claims a tuple expected at an iterable other than an array at
$`\mathsf{readonly}\ (A_0\cup\ldots\cup A_{n-1})[\,]`$, which Lean derives from
the tuple ($`\mathsf{list}`$ inclusion) and relates to the iterable through
`Array.prototype[Symbol.iterator]`, as for any array. A compiler-API node
list is read as a dense readonly array of its elements
([node lists in the model](COMPILER-API.md#node-lists-in-the-model)): its own
`Symbol.iterator` yields what indexing reads, which T4 states and C4 runs, so
it is iterated as that array in every position, under the host assumption on
the package's values (`compiler-api-node-list-spread`).

## The iterator protocol

An iterable the program defines is iterated as
[ECMA-262](REFERENCES.md#ecma-262)'s ForIn/OfBodyEvaluation runs it, in
ordinary forms the parser writes (`protocolForOf`), each an ordinary call or
read typed by the declarations TypeScript gives the iterable (`Iterable<T>`,
`Iterator<T, TReturn, TNext>`, `IteratorResult<T, TReturn>`, or the program's
own class or record), under names no source spells:

```math
\begin{array}{l}
[\![\mathsf{for}\ (\mathsf{const}\ x\ \mathsf{of}\ e)\ S]\!]=
\{\ \mathsf{const}\ i=e[@@\mathit{iterator}](),\ n=i.\mathit{next}.\mathsf{bind}(i);\\
\quad\mathsf{while}\ (\mathsf{true})\ \{\ \mathsf{const}\ r=n();\ \mathsf{if}\ (r.\mathit{done})\ \mathsf{break};\
  \mathsf{const}\ x=r.\mathit{value};\ \mathsf{closing}\ \{S\}\ \mathsf{close}\ C_i\ \}\ \}\\[2pt]
C_i=\mathsf{const}\ m=i.\mathit{return};\ \mathsf{if}\ (\mathsf{typeof}\ m\ne\texttt{"undefined"})\ \{\ \mathsf{const}\ \_:\mathsf{object}=m.\mathsf{call}(i)\ \}
\end{array}
```

The protocol lowering writes `.bind` in the fragment to save a method with
its receiver. Source-written `.bind` is admitted by the parser only on a
known local function.

GetIterator reads `next` once, and each step calls it on the iterator: the
bound function is that call ([`bindMember`](PROGRAM-TYPING.md#judgments-and-constructor-views)). A
`return` the iterator's type declares a required method is read bound the
same way, $`C_i=\mathsf{const}\ m=i.\mathit{return}.\mathsf{bind}(i);\ \mathsf{const}\ \_:\mathsf{object}=m()`$;
an optional one or a property is read, tested and called on the iterator, as
GetMethod and IteratorClose do. The result must be an object, which is the
TypeError IteratorClose throws otherwise, made impossible by the annotation's
obligation. The test of `r.done` refines $`r`$ to the arms whose `done` may be
falsy (a [field slice](PROGRAM-TYPING.md#refinement-under-an-observed-outcome) through the
read's link, optional where `IteratorYieldResult` leaves `done` optional), so
`r.value` is read at the not-done arm's type, `T`. An iterator whose type
states no `return` is refused where the loop could close it: an open record
may own any `return`. An array's `values`, `keys` and `entries` give the
`ArrayIterator` the library declares, read at the overlay as
`IterableIterator` of the declared argument (`[number, T]` for `entries`):
the iterator is its own, and a program's iterable by this rule, its `return`
read `undefined` and the close calling nothing, by the
[host assumption](DESIGN.md#trust-surface) that its chain holds none.

GetIterator on an iterable of a union type gives a union of iterators, and
the protocol binds the `next` (and a required `return`) of whichever iterator
it is: a [member bound to a union of hosts](PROGRAM-TYPING.md#judgments-and-constructor-views),
each host's member taken at the signature it binds alone. Each step's result
is then the union of the hosts' results, `IteratorResult<T_j, TReturn_j>`
each, and `r.value` past the test of `r.done` the union of the not-done arms'
`T_j`. The `next` the protocol admits, per host, is a method member whose
signature takes no required parameter (`next()`, or the rest-tuple union
`next(...[value]: [] | [TNext])`, whose first signature is `next()`), with no
promise, under a receiver the iterator is within, returning a record with
`done` and `value`; the hosts' `next` signatures take the same parameters at
the same effect. Refused: a required parameter (the step's call passes none),
hosts' signatures that differ in parameters or effect, a result that is no
object (IteratorStepValue throws on it; the step's `done` read has no rule on
a primitive), a receiver the iterator is
not (`this: S`), an optional `next` or an accessor (outside the fragment), and
a `next` that is a field holding a function in a union, which no rule binds.
A `next` with effects changes what the loop's body and what follows know, as
any call of its footprint does.

The library's declarations are read by the rules of
[library types](#library-types): `Iterable<T>` is the record of its one
method under the built-in `Symbol.iterator` key, returning an `Iterator`, and
so no `Iterator`, whose `next` it lacks; `Iterator`'s
`next(...[value]: [] | [TNext])` is the two signatures `next()` and
`next(value: TNext)` (**rest-tuples**), and its `return?` and `throw?` are
optional methods: optional fields whose functions take the iterator as
receiver ([records](POSITIVE-TYPES.md#records)), which is what the close's
test of `return` reads.

The closing region is a `finally` that runs on some ways out of $`S`$ only,
compiled by the machinery of `try` (`SourceExtraction.body`, `Finalizer`):

```math
\frac{\begin{array}{c}
\Gamma\vdash_R S\ \text{with}\ \mathsf{break}\mapsto C;\mathit{exit},\quad
  \mathsf{return}\ v\mapsto C;\mathsf{return}\ v,\quad
  \mathsf{continue}\mapsto\mathit{head},\quad
  \mathsf{throw}\ u\mapsto(\mathsf{try}\ C\ \mathsf{catch}\ \{\});\mathsf{throw}\ u\\
\Gamma\vdash_R C\ \text{on each of those ways}
\end{array}}
     {\Gamma\vdash_R\ \mathsf{closing}\ \{S\}\ \mathsf{close}\ C}\ \textsf{closing}
```

The close runs before a `break` of the loop leaves it, before a `return`
returns the value held in a slot of its own (as through any `finally`), and,
its own throws discarded by a handler that drops them, before a throw out of
the body is thrown again: IteratorClose with a throw completion keeps the
body's. Its end and a `continue` go to the head, and a done result leaves
without it, as IteratorClose is not called there. A jump past the loop to an
outer target passes it as it passes a `finally`. Every edge is checked as
any other; the close's statement entries state each cell at its contract.

A pattern $`p`$ binding the loop binds the step's value to a name no source
spells, where $`x`$ is bound, and destructures it as the closing region's
first statement:

```math
\mathsf{const}\ r=n();\ \mathsf{if}\ (r.\mathit{done})\ \mathsf{break};\
\mathsf{const}\ \%e=r.\mathit{value};\
\mathsf{closing}\ \{\ \mathsf{const}\ p=\%e;\ S\ \}\ \mathsf{close}\ C_i
```

ForIn/OfBodyEvaluation runs ForDeclarationBindingInitialization of $`p`$ on
the step's value after IteratorValue and before the body, and on its abrupt
completion returns IteratorClose with it: a throw of a default or of a read
the pattern makes closes the iterator, its own throw discarded, as a throw out
of $`S`$ does, and a default has no other way out. The pattern runs between two
steps of the protocol, so its code runs where JavaScript runs it. The inner
declaration is a `const` pattern's over a value another reference may hold
(the iterator may keep it), with every rule of
[patterns](SOURCE-ELABORATION.md#patterns): an array pattern reads the
positions of an array, with no code that may change it between its steps, its
nested patterns and defaults included
(`for-of-pattern-program-iterable-default-refused`); an array pattern over a
value that is no array (a string, a `Set`, an iterable the program defines)
is refused by the typing of those reads
(`for-of-pattern-nested-iterable-refused`), and a position past a short
array is `undefined` (`invalid-for-of-pattern-program-iterable`, run under
Node). It is the same lowering as a pattern over an array's loop
(`forOfPattern`), inside the region (`for-of-pattern-program-iterable`).

A spread of a program's iterable (`collect`) that is the first evaluation
able to run code of the statement's value (an expression statement's, a
`return`'s or a declaration's one initializer), every evaluation before it
a literal or a name the file never assigns whose read cannot throw nor run
code: a parameter, a function declaration with a body (an ambient
`declare function` is none, `spread-program-iterable-ambient-function-refused`),
a function body's `let` or
`const` the early-binding analysis finds initialized at every read, or a
name the file declares nowhere that TypeScript binds to the standard
library's `var`s or functions alone, whose read runs no code by the
[host assumption](DESIGN.md#trust-surface) on standard-library global
bindings. A module binding, an import, a class,
an ambient declaration or an unresolved name is none
(`spread-program-iterable-uninitialized-refused`,
`spread-program-iterable-global-getter-refused`,
`spread-program-iterable-global-tdz-refused`, each run under Node). Such a
spread is collected before the statement, where nothing the statement evaluates before the spread can be
changed by the iterator's code. Evaluation is followed in JavaScript's
order: an array literal's elements, a call's or a construction's callee then
arguments (a callee that is such a name, or a method read off a value whose
first evaluation is the spread), a member read's object. So the spread may
be the first element of an array literal before others, an argument of
`new Set(…)`, or the receiver of a method call (`spread-program-iterable-first`,
run under Node: the iterator's steps precede the later element's code): $`\mathsf{const}\ a=[\,],\ i,\ n;\ \mathsf{while}\ (\mathsf{true})\ \{\ \mathsf{const}\ r=n();\ \mathsf{if}\ (r.\mathit{done})\ \mathsf{break};\ a.\mathit{push}(r.\mathit{value})\ \}`$, then $`\ldots a`$ (or $`a`$ for the literal);
a spread steps to the end and closes nothing. An array literal's spread of
a host iterable (a string, a `Set`, a `Map`, a host collection iterator)
spreads its spread intrinsic's array, `[…, ...e, …]` $`\equiv`$
`[…, ...%Spread:K%(e), …]`, the fresh array of what the host's iterator
yields, as an argument spread of one is; the literal is a fresh array of its
own, at the store contract its claim states, also where the spread is its
one element (`array-literal-host-spread`). An array pattern
`const [p₀, …, ...q] = e` over one (`protocolPattern`) steps once per element,
a hole too, into cells $`v_j`$ starting `undefined`, leaves a labeled block when
a step is done, collects the rest to the end, and without a rest closes the
iterator after the elements, as IteratorBindingInitialization does; the
source's names are then bound from the cells, which binding names does not
observe. A default or a nested pattern, which run code between the steps, is
refused.

## Statement forms

The statement forms of a body are lowered to the graph compiler's where the
lowering is exact ([as graphs](PROGRAM-TYPING.md#statement-forms-as-graphs)). $`\Gamma\vdash_R S`$
reads "the statements $`S`$ are safe under $`\Gamma`$ in a function whose result
is $`R`$". An unbraced arm is the block holding it and `else if (c) S` is
`else { if (c) S }`; `return;` is `return undefined`, and a block closure that
does not return on every terminal arm ends with `return undefined`:

```math
\frac{\mathsf{undefined}\le R}{\Gamma\vdash_R\ \mathsf{return};}\ \textsf{return-bare}
\qquad
\frac{\Gamma\vdash_R S_1\quad S_1\ \text{always jumps}\quad \mathit{names}(S_2)\ \text{free in no live statement, none hoisted}}
     {\Gamma\vdash_R S_1;S_2}\ \textsf{dead}
```

`for (init; cond; update) S` is `{ init; loop }` with a `while (cond)` whose
body's end and every `continue` run `update`, then go to the head (a closure
capturing a `for` loop's `let` is refused, since JavaScript copies it per
iteration):

```math
\frac{\Gamma\vdash_R \mathit{init}:\Gamma'\quad \Gamma_h\ \text{the head's entry claims}\quad
      \Gamma'\le\Gamma_h\quad \Gamma_h\vdash c:\mathsf{boolean}\quad
      \Gamma_h\wedge c\vdash_R S\ \text{with}\ \mathsf{continue}\mapsto u\quad
      \Gamma_u\vdash \mathit{update}\ \text{back to}\ \Gamma_h}
     {\Gamma\vdash_R\ \mathsf{for}\ (\mathit{init};c;\mathit{update})\ S}\ \textsf{for}
```

`switch (d) { … }` is a labeled block per clause, nested in source order
inside one for the whole switch: the innermost holds the dispatch, each case
label in order `if (d === l) break` to the end of its clause's block, and
each clause's statements follow its block's end, so fall-through is ordinary
sequencing. The discriminant is evaluated once into a slot no source names,
unless it is a name or a field of a name and every label a literal or a name,
when it is re-read at each test. A name declared in one clause and read in
another is refused.

```math
\frac{\Gamma\vdash_R S\ \text{with}\ \mathsf{break}\ \ell\mapsto\Gamma_{\mathit{after}}\quad
      \Gamma_{\mathit{after}}\vdash_R S'}
     {\Gamma\vdash_R\ \ell:\{S\};S'}\ \textsf{labeled-block}
```

`for (const k in o) S` is `for (const k of %ForIn%(o)) S` with the trusted

```math
\mathtt{\%ForIn\%}:(o:\mathsf{unknown})\Rightarrow\mathsf{readonly}\ \mathsf{string}[\,],
```

the keys the loop visits: strings, for any value. Where the body reads the
entry at the key, `P[k]` with `P` the loop's operand spelled again (a name,
or a chain of named reads from one), before anything that could change the
entry runs, the loop steps the entries instead,
`for (const e of %Iterate:ForIn%(P)) { const k = e[0]; S' }` with each such
read in $`S'`$ the step's value `e[1]`:

```math
\mathtt{\%Iterate{:}ForIn\%}:\forall V.\ (o:\{\mathsf{readonly}\ [k:\mathsf{string}]:V\})\Rightarrow
  ()\Rightarrow\{\mathsf{readonly}\ \mathsf{value}:[\mathsf{string},V]\}\mid\mathsf{null},
```

each step a fresh array of a key the loop visits and the value the object
holds under it at the step. A dictionary holds no prototype, and a plain
object's, `Object.prototype`, no enumerable key, so every key visited is the
object's own, whose value the index's contract states. The reads rewritten
are those of the statements the body starts with that run no code and write
no property, outside the functions they define, and the whole initializer of
the declaration after them; the operand's name is written nowhere in the
outermost function holding the loop (the file, at the top level), and a
chain of reads is read from a body that runs no code and writes no
property, so each read finds the object the loop enumerates and the value
the step read (`forInEntryReads` in `tools/fragment-support.mts`). A read
after a call is the dictionary's read, `V | undefined`: the call may have
removed the key. `try B catch (e) C finally
F` names $`C`$'s entry as the handler of $`B`$'s nodes that may throw, with `e`
at `unknown` (the only annotation admitted), and compiles $`F`$ on every way
out: after a normal completion, before each `return` with the value held,
before each `break` or `continue` leaving it, then on to the jump's target
through the `finally` of every enclosing `try` the jump also leaves, after a
throw with the thrown value held and rethrown. A `return`, `throw`, `break`
or `continue` in $`F`$ leaves by its own way, as JavaScript's replaces the
pending completion:

```math
\frac{\Gamma\vdash_R B\ \text{with throws}\mapsto(\mathsf{unknown},\Gamma)\vdash_R C\quad
      \Gamma\vdash_R F\ \text{on each way out}}
     {\Gamma\vdash_R\ \mathsf{try}\ B\ \mathsf{catch}\ (e)\ C\ \mathsf{finally}\ F}\ \textsf{try}
```

The handler's and finalizer's entries state each cell at its contract, since
a throw may leave after any part of the body ran.

## Guards

Every guard is a tag test ([SEMANTICS](SEMANTICS.md#operational-language)),
refining a tested immutable binding by the tag slice $`T_q`$ of its type on
each edge ([refinement](PROGRAM-TYPING.md#refinement-under-an-observed-outcome)).
A call of a [user-defined guard](#user-defined-guards) narrows by such tests
of its argument, run again after the call:

```math
\frac{\Gamma(x)=A\quad\Gamma[x:T_{\mathsf{typeofObject}}(A)]\vdash_R S_1\quad\Gamma[x:T_{\lnot\mathsf{typeofObject}}(A)]\vdash_R S_2}
     {\Gamma\vdash_R\ \mathsf{if}\ (\texttt{typeof}\ x\equiv\texttt{"object"})\ S_1\ \mathsf{else}\ S_2}\ \textsf{if-typeof-object}
```

```math
\frac{\Gamma(x)=A\quad A\ \text{objects, no class value}\quad \kappa\notin\mathcal B\quad
      \Gamma[x:T_{\mathsf{hasKey}(\kappa)}(A)]\vdash_R S_1\quad\Gamma[x:T_{\lnot\mathsf{hasKey}(\kappa)}(A)]\vdash_R S_2}
     {\Gamma\vdash_R\ \mathsf{if}\ (\texttt{"}\kappa\texttt{"}\ \mathtt{in}\ x)\ S_1\ \mathsf{else}\ S_2}\ \textsf{if-in}
```

with $`\mathcal B`$ the refused keys (`inKeyRefusal`: `Object.prototype`'s,
`Array.prototype`'s and `Function.prototype`'s own string keys, array
indices, and the keys the model reserves). `in`'s answers are by keys the
types state (`inAnswer`): a failed test drops an arm owning the key, a passed
one drops an arm whose key bounds exclude it and the prototype key, and every
primitive; a passed test promotes an optional key to a field (`promote`). A
test against a claimed singleton $`c`$ of any primitive kind, and against a
field of an immutable binding's object, narrows the binding or the object's
arms:

```math
\frac{\Gamma\vdash a:A\quad \Gamma\vdash k:\{c\}\quad
      \Gamma[x:T_{\mathsf{eq}(c)}(\Gamma(x))]\vdash_R S_1\quad
      \Gamma[x:T_{\lnot\mathsf{eq}(c)}(\Gamma(x))]\vdash_R S_2}
     {\Gamma\vdash_R\ \mathsf{if}\ (x\equiv k)\ S_1\ \mathsf{else}\ S_2}\ \textsf{if-singleton}
\qquad
\frac{\Gamma\vdash k:\{c\}\quad
      \Gamma[o:F^{f}_{\mathsf{eq}(c)}(\Gamma(o))]\vdash_R S_1\quad
      \Gamma[o:F^{f}_{\lnot\mathsf{eq}(c)}(\Gamma(o))]\vdash_R S_2}
     {\Gamma\vdash_R\ \mathsf{if}\ (o.f\equiv k)\ S_1\ \mathsf{else}\ S_2}\ \textsf{if-field}
```

with $`F^f`$ the field slice. The truthiness of a field of an immutable
binding's object, where an arm of it leaves the field optional or unnamed (so
that no fact about what the field holds is claimed, as of an
`IteratorResult`'s `done`), narrows the object's arms the same way, the read
dispatched on its truthiness:

```math
\frac{\Gamma[o:F^{f}_{\mathsf{truthy}}(\Gamma(o))]\vdash_R S_1\quad
      \Gamma[o:F^{f}_{\lnot\mathsf{truthy}}(\Gamma(o))]\vdash_R S_2}
     {\Gamma\vdash_R\ \mathsf{if}\ (o.f)\ S_1\ \mathsf{else}\ S_2}\ \textsf{if-field-truthy}
```

Where the singleton $`c`$ is a string or a number other than a zero, a passed
test leaves the operand $`c`$ alone, whatever its type was, `unknown`
included: $`T_{\mathsf{eq}(c)}(A)=\{c\}`$ for every $`A`$ the test may pass
on (`tagMember`). A disjunction's passed outcome came from either operand,
and each slot holds what either path left it, a slot one path leaves at its
input type keeping that type:

```math
\frac{\Gamma_1=\Gamma[a\mapsto\mathsf{true}]\quad
      \Gamma_2=\Gamma[a\mapsto\mathsf{false}][b\mapsto\mathsf{true}]\quad
      \Gamma_1\sqcup_\Gamma\Gamma_2\vdash_R S_1\quad
      \Gamma[a\mapsto\mathsf{false}][b\mapsto\mathsf{false}]\vdash_R S_2}
     {\Gamma\vdash_R\ \mathsf{if}\ (a\parallel b)\ S_1\ \mathsf{else}\ S_2}\ \textsf{if-or}
\qquad
(\Gamma_1\sqcup_\Gamma\Gamma_2)(x)=\begin{cases}\Gamma(x)&\Gamma_1(x)=\Gamma(x)\lor\Gamma_2(x)=\Gamma(x)\\
  \Gamma_1(x)\cup\Gamma_2(x)&\text{otherwise}\end{cases}
```

with $`\Gamma[a\mapsto q]`$ the refinement by $`a`$'s answer $`q`$, and `&&`'s
false outcome the same join. Each edge into $`S_1`$ is checked against the
joined context, so `v === "dense" || v === "sparse"` leaves `v` at
`"dense" | "sparse"` (`literal-union-narrowing`). An operand testing a field
of an immutable binding's object refines that object by its field slice
$`F^f`$, as `if-field` does, so `n.kind === 1 || n.kind === 2` leaves `n` at
the arms whose `kind` admits 1 or 2 (`field-test-disjunction`).

`x === y` with `x` claimed at a union of
singletons is dispatched as the disjunction over its singletons $`c`$ of
$`x\equiv c\land y\equiv c`$ (`savedSplit` where `x` has effects). Strict
equality without a singleton is the $`\equiv`$ operator of `arith`, which
narrows nothing and is refused between two operands that may both be objects
without a field. `x instanceof C`, for a class the file declares at its top
level, is $`\mathsf{hasKey}(\kappa_C)`$ ([derived form](SOURCE-ELABORATION.md#derived-source-forms)).
It does not narrow `unknown`: an object gets $`C`$'s prototype without $`C`$'s
constructor running (`Object.create(C.prototype)`), so the key is no evidence
of $`C`$'s fields. `Array.isArray(x)` narrows a record or dictionary arm of $`x`$
to the built-in `sparse ReadonlyArray<unknown>` where it holds
([**tag-array**](PROGRAM-TYPING.md#refinement-under-an-observed-outcome)), and keeps
`unknown`, which the array invariant says nothing of:

```math
\frac{\Gamma(x)=A\quad A\preceq_{\mathsf{isArray}=\mathsf{true}}B\quad \Gamma[x:B]\vdash_R S_1\quad
      \Gamma[x:T_{\lnot\mathsf{isArray}}(A)]\vdash_R S_2}
     {\Gamma\vdash_R\ \mathsf{if}\ (\mathtt{Array.isArray}(x))\ S_1\ \mathsf{else}\ S_2}\ \textsf{if-array}
```

### User-defined guards

A type guard `function g(x: A): x is T` and an assertion function
`function f(x: A): asserts x is T` have function types of two signatures each,
the plain one and a **promise signature** about the parameter $`x`$, the
$`p`$-th:

```math
g : (A) \to \mathtt{boolean}\ \land\ (A) \to T\,[\mathsf{guards}\ p]
\qquad
f : (A) \to \mathtt{void}\ \land\ (A) \to T\,[\mathsf{asserts}\ p]
```

A promise signature's result operand is the promise's type. Its meaning is the
[effect-qualified call contract](SEMANTICS.md#effect-qualified-call-contracts)
whose result family relates the result $`v`$ to the $`p`$-th actual $`v_p`$:
a call of $`g`$ returns `true` with $`v_p \in T`$, or `false`; a normal return
of $`f`$ is `undefined` with $`v_p \in T`$. The same declaration reads the
same in every position: a function type, a method, an imported module's
declaration and a closure's annotation all carry both signatures.

The promise is proved at the definition. The body is checked at the promise
signature with the goal that each return meets the result family for the
argument $`v`$ the call passed. The checker tracks the slots holding $`v`$,
which a write of the parameter or a default replacing it leaves, and at each
return asks for the answer and the argument's type where that answer is
possible:

```math
\frac{\begin{array}{c}\Gamma_0 = x{:}A \qquad
      \forall\ \mathsf{return}\ e \text{ at } \Gamma \text{ with } x \text{ holding } v:\
      \Gamma\vdash e : \mathtt{boolean} \quad
      \bigl(\Gamma\vdash e : \mathtt{false}\ \lor\ \Gamma_{e=\mathtt{true}} \vdash v : T\bigr)\end{array}}
     {\vdash g : (A) \to T\,[\mathsf{guards}\ p]}\ \textsf{guard-def}
```

```math
\frac{\forall\ \text{normal completion at } \Gamma \text{ with } x \text{ holding } v:\
      \Gamma\vdash v : T}
     {\vdash f : (A) \to T\,[\mathsf{asserts}\ p]}\ \textsf{assert-def}
```

$`\Gamma_{e=\mathtt{true}}`$ is $`\Gamma`$ refined by what the returned value
being `true` establishes: a test of a slot (`typeof x === "string"`, a strict
equality, a conjunction or disjunction of these), a Boolean slot carrying such
a test's answer, or a call at a promise signature. A test of a value read
from a field refines the object it was read from, while the read is current,
to the arms whose field answers the test so (`return s.kind === "circle"`).
A branch before the return refines $`\Gamma`$ itself. A return
is claimed at its value's own type, so a `return false` answers `false`
alone.

A call consumes the promise. The callee is any expression whose type holds
a promise signature its actuals meet: a name, a method or a field of an
object, a bound function. Of an overloaded callee's promise signatures, the
call narrows by one whose parameters admit its actuals. The call's `true`
result, or its normal return, leaves the promised actual $`a`$, a name, a
$`T`$:

```math
\frac{\Gamma\vdash g : (\vec A)\to T\,[\mathsf{guards}\ p]\quad \Gamma\vdash \vec a : \vec A\quad
      \Gamma[a_p : T]\vdash_R S_1\quad \Gamma\vdash_R S_2}
     {\Gamma\vdash_R\ \mathsf{if}\ (g(\vec a))\ S_1\ \mathsf{else}\ S_2}\ \textsf{if-guard}
\qquad
\frac{\Gamma\vdash f : (\vec A)\to T\,[\mathsf{asserts}\ p]\quad \Gamma\vdash \vec a : \vec A\quad
      \Gamma[a_p : T]\vdash_R S}
     {\Gamma\vdash_R\ f(\vec a);\ S}\ \textsf{assert-call}
```

A conditional expression narrows its first arm the same way, a closure the
arm creates reading the actual at $`T`$ (`guard-ternary-closure`):

```math
\frac{\Gamma\vdash g : (\vec A)\to T\,[\mathsf{guards}\ p]\quad \Gamma\vdash \vec a : \vec A\quad
      \Gamma[a_p : T]\vdash e_1 : B\quad \Gamma\vdash e_2 : B}
     {\Gamma\vdash g(\vec a)\ ?\ e_1 : e_2 : B}\ \textsf{cond-guard}
```

A `false` outcome narrows nothing: the promise states nothing of it
(`invalid-type-guard-false-branch`). Passing a guard where a plain predicate
is expected forgets its promise signature, as an intersection's operand.
Binding a prefix of a guard's actuals (`g.bind(r, …)`) keeps a promise about
an actual past the prefix, at its new position.

A closure's written promise is proved whatever its claim offers: one of the
signatures its code is checked at states that promise over the annotation's
whole domain, admitting every receiver and argument the annotation admits,
at a type within the written one, or the closure is refused. A guard
closure passed where a callback binding more parameters is expected
(`every`'s or `filter`'s predicate) is claimed at its own signature, its
promise and the longer signature, its body checked at each
(`guard-closure-callback`). Where the longer signature states the
closure's written promise (`filter`'s guard overload,
[`native-guard-filter`](#prototype-contracts)), the closure is claimed at it
with that promise, and its body is checked at it with the promise goal. The
reviewed `every` states no guard overload (`every<S>`), so a call passing a
guard does not narrow its receiver.

An imported guard is read at its declared type, both signatures; its promise
is the import assumption of [the trust surface](DESIGN.md#trust-surface),
discharged where the imported module's own run verifies the guard. A guard
of a host family is read instead from its audited table entry
([guard recognition](HOST-FAMILIES.md#guard-recognition)), never at its
declared predicate; the entry rests on the host assumption that the
package's enum objects and its guards' bindings are never written, by the
program or by external code, and a source write to them is refused.

Implementation: `CallEffects.Effect` (`guards p`, `asserts p`) gives the
contract; `ControlFlow.Goal` states a body's goal and `checkReturnResult` its
check at a return; [PromiseCalls.lean](../lean/Verification/Programs/PromiseCalls.lean)
holds the yields of a returned value (`yieldFollows_sound`) and the promise
call (`promiseCall_sound`); `Lowering.Control.promiseNarrowing` places the
narrowed claim after a call, which the edge check verifies. Pipeline cases:
`type-guards`, `type-guard-objects`, `type-guard-methods`,
`type-guard-value-import` and `type-guard-overload-value-import` verify;
`invalid-type-guard-promise`, `invalid-type-guard-undefined`,
`invalid-type-guard-default`, `invalid-type-guard-object`,
`invalid-type-guard-field-test`,
`invalid-type-guard-method` and
`invalid-assertion-promise` are refused at the return where the argument is
not a $`T`$, each run under Node by `node-runs.mts`.

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
