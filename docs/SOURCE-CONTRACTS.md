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
refused too. A standard library global is
read through the reviewed overlay ([Library globals](#library-globals)), and
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
widens an inferred result, which the closure's code is then checked at
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
declaration TypeScript binds $`N`$ to is in a standard library file:

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
any other key is refused. The keys are the union TypeScript computes for $`K`$
([computed types](#computed-types)). A library alias whose equation is a
mapped type is that type at the reference's arguments:

```math
\frac{\mathit{lib}(L)\quad L\langle\vec X\rangle=\{[P\ \mathtt{in}\ K]^m\colon V\}}
     {⟦L\langle\vec A\rangle⟧=
      ⟦\{[P\ \mathtt{in}\ K[\vec A/\vec X]]^m\colon V[\vec A/\vec X]\}⟧}
```

so `Record<"a" | "b", V>` has both fields required and `Record<string, V>` is
the writable string index. An interface's `extends` clauses are the meet of
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
application of it is a computed type, evaluated where it is written, its
equation read with the parameters as the arguments:

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
equation of an alias without bounded parameters it names, each alias's
parameters read as the reference's arguments or their defaults, an
application of an alias with a bounded parameter being one member read as
written, with its bound obligation, an application TypeScript decides
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

Refused: a conditional type over a function's own type parameter, which
TypeScript defers; an application of a conditional type alias with a bounded
parameter, which what TypeScript computes for it would replace together with
the obligation that its arguments meet their bounds; one whose result has a part that is no member of the
decided union as written (a branch other than the parameter, `T[]`, or a
member naming a parameter of the alias declaring it, which is another type at
each instance); a conditional type outside an alias distributing over a
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
primitive's member), without dropped parameters. An entry may state its
signature family instead, with $`\omega`$ the entry of member $`m`$ of prototype
$`p`$, and $`R_j`$ its reviewed receiver (defaulting to $`p`$):

```math
\frac{\omega\in\Omega_p\quad \omega.\mathit{text}=\mathsf{text}(m)\quad
      \omega.\mathit{stated}=[(R_j,\vec P_j,Q_j,\epsilon_j)]_{j=1}^n\quad n>0}
     {⟦m⟧_\omega=\bigcap_{j=1}^n
       (\mathsf{this}:R_j,\ \vec P_j)\Rightarrow_{\epsilon_j} Q_j}\ \textsf{proto-stated}
```

Each signature states an effect $`\epsilon_j`$: the entry's own, else its
prototype's, `preservesInputHeap` for `StringProto`, `NumberProto`,
`BigIntProto` and `BooleanProto` and `unrestricted` for `ArrayProto`. A
signature states `preservesInputHeap` where the member, called at it, runs no
client code but callbacks whose own signatures state the same, and writes no
location the call did not allocate. Every primitive member listed meets this:
its receiver is a primitive, it converts only primitives (a string search
reads no `[Symbol.match]` of a primitive pattern, `split` and `replace` are
stated at a string pattern), reads `locales` by index, and allocates only its
result. Of `ArrayProto`, `slice`, `join`, `toString`, `indexOf`,
`lastIndexOf`, `includes`, `at` and `[Symbol.iterator]` state it: they read
the receiver, convert only numbers and elements meeting the conversion
contract below, compare by strict equality or SameValueZero, and allocate
only their result; so do the overloads of `map`, `find` and `findIndex` that
take a preserving callback, which they call, the ordinary construction below
allocating `map`'s result. The members that write their receiver (`sort`,
`push`, `pop`, `shift`, `unshift`, `reverse`) and those that call an
unrestricted callback do not.

The reviewed overlay can restrict quantified binders (`bounds`) and weaken a
native's promised result (`result`). These specify trusted natives; source
annotations are still translated in full. `join` bounds `T` to the conversion
contract below,
unrestricted `find`/`findIndex` callbacks receive `T | undefined`, and unrestricted
`map` callbacks produce a sparse result. Qualified overloads require a certified
`preservesInputHeap` callback and respectively pass `T` or promise a dense result.
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

a supertype of the declared interface. A member's signatures state the
entry's effect: `preservesInputHeap` for the readers, `has`, `get`, `keys`,
`values`, `entries`, `[Symbol.iterator]` and `Date`'s getters, `valueOf`,
`toString` and `toISOString`, none for the members that change the
collection or the date or call a callback. $`⟦m⟧_\omega`$ drops
`thisArg`, reads a `this` result as the receiver, and reads a declared
iterator result as `Iterator<T>`, which it extends. A property is a readonly
view. A string's own `length` and indices are the calculus's `lenStr` and
`elemStr`, never the prototype's; `s[i]` is `string | undefined`.

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

The entries, each with the code its restriction keeps from running:

- `Boolean(v, …)` is ToBoolean of its first argument, which runs no code and
  reads no property, and ignores the rest: $`(\mathtt{unknown},\ \ldots\mathtt{unknown})\Rightarrow\mathtt{boolean}`$,
  a value too (`xs.filter(Boolean)`). It is stated with no promise about its
  argument: its declaration, `<T>(value?: T): boolean`, states none, so
  `filter(Boolean)` keeps its receiver's element type, as TypeScript keeps it
  (`invalid-boolean-filter-narrowing`).
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
  (`invalid-own-property-descriptor-value`):

```math
\mathtt{getOwnPropertyDescriptor}:(\mathtt{unknown},\ \mathtt{string}\mid\mathtt{number}\mid\mathtt{symbol})\Rightarrow\mathsf{Desc}\mid\mathtt{undefined}
```

```math
\mathsf{Desc}=\{\mathtt{readonly}\ \mathit{configurable}:\mathtt{boolean};\ \mathtt{readonly}\ \mathit{enumerable}:\mathtt{boolean};\ \mathtt{readonly}\ \mathit{value}?:\mathtt{unknown};\ \mathtt{readonly}\ \mathit{writable}?:\mathtt{boolean};\ \mathtt{readonly}\ \mathit{get}?:\mathtt{unknown};\ \mathtt{readonly}\ \mathit{set}?:\mathtt{unknown}\}
```

`Reflect` is a namespace, whose functions are no annotated variable's
members, and `Reflect.get(o, k)` runs [[Get]], which calls an accessor's
getter, code no type of `o` states: it is refused.

Overloads stated alike are one signature. A statement may name a library
interface (`Set<T>`, read through [its overlay](#prototype-contracts)) or a
declaration no library has, which joins the document with the entry:

```math
\mathsf{JsonValue}=\mathsf{null}\mid\mathsf{boolean}\mid\mathsf{number}\mid\mathsf{string}\mid\{\mathsf{readonly}\ [k:\mathsf{string}]:\mathsf{JsonValue}\}
```

(`JSON.stringify`'s parameter). An entry may read a member as a test of the
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

## Library modules

A function a client imports from one of Node's modules (`node:fs`, or `fs`)
is read through the reviewed overlay of library modules
(`library-modules.mts`) where an entry lists it, and otherwise as an
imported value ([imported values](#imported-ambient-and-global-values)).
An entry names one overload of the function's declaration in Node's
declarations, with exactly the text it was reviewed against (white space
collapsed), and states the signature the host meets at the arguments it
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
unrestricted in its effect. The entries:

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
- `writeFileSync(file, data)` with a path and a string writes the string to
  the file as UTF-8 and returns `undefined`; a path it cannot write throws:
  $`(\mathtt{string},\ \mathtt{string})\Rightarrow\mathtt{undefined}`$.

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
\mathsf{preservesInputHeap} & m\in\{[@@\mathrm{search}],[@@\mathrm{split}],[@@\mathrm{matchAll}]\},\ \Sigma\ne\Sigma_\top\\
\mathsf{preservesInputHeap} & m\in\{\mathtt{exec},\mathtt{test},[@@\mathrm{match}],[@@\mathrm{replace}]\},\ \Sigma\ne\Sigma_\top,\ \neg g,\ \neg y\\
\mathsf{unrestricted} & \text{otherwise}
\end{cases}
```

`[@@search]` restores the `lastIndex` it saved, `[@@split]` and
`[@@matchAll]` step a fresh clone, and a regex neither global nor sticky
writes no `lastIndex`; one that is leaves it where its last match ended
(`invalid-regexp-global-callback-effect`). At $`\Sigma_\top`$ the flags are
not read, and no member states the effect.

**Literals and dispatch.** Each evaluation of a literal allocates a regex;
a call of `String.prototype`'s `match`, `matchAll`, `replace`, `replaceAll`,
`search` or `split` with an object first argument runs `GetMethod` on it and
returns what that method returns:

```math
\frac{\Sigma=\mathsf{shape}(P,F)}
     {⟦/P/F⟧=\%\mathrm{RegExp}{:}\Sigma\%()\qquad \%\mathrm{RegExp}{:}\Sigma\%\colon()\Rightarrow_{\mathsf{preservesInputHeap}} N(\Sigma)}\ \textsf{regexp-literal}
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
`replace` with the mark. Each states two signatures over the same binder:
the one above, unrestricted, and the same at a target whose member states
$`\mathsf{preservesInputHeap}`$, stating it too. Beside that member's call, the
dispatch reads `o`'s members and converts only strings, so it writes nothing
the member does not:

```math
\frac{\%\mathrm{Dispatch}{:}m\%\colon\forall X.\ (\mathtt{string},\ \{[@@m]\colon\vec P\Rightarrow Q\},\ \vec R)\Rightarrow S}
     {\%\mathrm{Dispatch}{:}m\%\colon\forall X.\ (\mathtt{string},\ \{[@@m]\colon\vec P\Rightarrow_{\mathsf{preservesInputHeap}} Q\},\ \vec R)\Rightarrow_{\mathsf{preservesInputHeap}} S}\ \textsf{dispatch-preserving}
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
and `new RegExp` are not stated. Match results are readonly views.

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
the inherited constructor is present. The source refuses objects with a
`then` member that could forge a promise. The native identity and standard
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
A `Promise` method's binder written beside a
`PromiseLike` of itself is inferred the same way: `then`'s callback returns
`TResult1 | PromiseLike<TResult1>` and `catch`'s `TResult | PromiseLike<TResult>`,
so a callback returning a promise of $`U`$, or a primitive $`V`$, instantiates
the binder at $`U`$ or $`V`$:

```math
\frac{\Gamma\vdash f:(\vec A)\Rightarrow\mathsf{Promise}\langle U\rangle\mid V\quad V\le P}
     {\mathit{TResult}:=U\mid V\ \ \text{at}\ \ (\vec A)\Rightarrow\mathit{TResult}\mid\mathsf{PromiseLike}\langle\mathit{TResult}\rangle}
```

The instance is the producer's proposal, checked as any instance of a
scheme ([`compareInstArrsState`](POSITIVE-TYPES.md#instances-of-a-scheme-row)).
Background: [promises and flattened types](REFERENCES.md#promises-and-flattened-types).

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
\mathtt{\%Iterate{:}Iterator\%}:\forall T.\ (\mathsf{Iterator}\langle T\rangle)\Rightarrow\mathit{Step}(T) & \text{a SetIterator or MapIterator}
\end{array}
```

`Set` and `Map` are the [interface overlay](#library-types)'s, whose
`keys`, `values` and `entries` give a `SetIterator` or `MapIterator` read as
an `Iterator` of its argument. None of these iterators has a `return`, so a
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
`Array.prototype[Symbol.iterator]`, as for any array.

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
may own any `return`.

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

A spread of a program's iterable (`collect`), the one element of an array
literal or an argument of a call of a name after names and literals the file
never assigns, and the statement's value, is collected before the
statement, where nothing the statement evaluates before the spread can be
changed by the iterator's code: $`\mathsf{const}\ a=[\,],\ i,\ n;\ \mathsf{while}\ (\mathsf{true})\ \{\ \mathsf{const}\ r=n();\ \mathsf{if}\ (r.\mathit{done})\ \mathsf{break};\ a.\mathit{push}(r.\mathit{value})\ \}`$, then $`\ldots a`$ (or $`a`$ for the literal);
a spread steps to the end and closes nothing. The one element of an array
literal spreading a host iterable (a string, a `Set`, a `Map`, a host
collection iterator) is its spread intrinsic's call, `[...e]` $`\equiv`$
`%Spread:K%(e)`, the fresh array of what the host's iterator yields, as an
argument spread of one is. An array pattern
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
`"dense" | "sparse"` (`literal-union-narrowing`).

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

A `false` outcome narrows nothing: the promise states nothing of it
(`invalid-type-guard-false-branch`). Passing a guard where a plain predicate
is expected forgets its promise signature, as an intersection's operand.
Binding a prefix of a guard's actuals (`g.bind(r, …)`) keeps a promise about
an actual past the prefix, at its new position.

A closure's written promise is proved whatever its claim offers: one of the
signatures its code is checked at states that promise over the annotation's
whole domain, admitting every receiver and argument the annotation admits,
at a type within the written one, or the closure is refused.

An imported guard is read at its declared type, both signatures; its promise
is the import assumption of [the trust surface](DESIGN.md#trust-surface),
discharged where the imported module's own run verifies the guard.

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
is the key of its reverse mapping. Such an enum's object type states its
members only, each at its value's type
$`\tau_i`$, $`\{v_i\}`$ or $`\mathtt{number}`$ where $`v_i=\bot`$:

```math
\mathcal O^{\circ}(E)=\{\overline{\mathtt{readonly}\ m_i:\tau_i}\},\qquad
E=\textstyle\bigcup_i\tau_i .
```

The declaration runs each such initializer in order, bound to a constant of
its own, then builds the object with the trusted step
$`\%\mathsf{Enum{:}E}\%:(\mathcal O^{\circ}(E))\Rightarrow\mathcal O^{\circ}(E)`$,
which adds the reverse mapping
([intrinsics](../tools/intrinsics.mts)):

```math
\frac{\exists i.\ v_i=\bot\qquad
      \forall i.\ m_i\notin\{\texttt{NaN},\texttt{Infinity}\}\qquad
      \forall i.\ v_i=\bot\Rightarrow \mathrm{reads}_E(e_i)\subseteq\{m_j\mid j<i\}}
     {\texttt{enum E}\{\vec m\}\ \leadsto\
      \overline{\texttt{const}\ \%E.m_i\%:\mathtt{number}=e_i[\overline{m_j:=u_j}]}^{\,v_i=\bot};\
      \texttt{const E}:\mathcal O^{\circ}(E)=\%\mathsf{Enum{:}E}\%(\{\overline{m_i:u_i}\})}
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
