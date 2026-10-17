# Program typing over positive recursive types

[ProgramTyping.lean](../lean/Verification/Programs/ProgramTyping.lean) gives syntactic program-typing rules for the stateful language,
over [TypingBasics.lean](../lean/Verification/Programs/TypingBasics.lean) (types, environments, code entries),
[OperatorTyping.lean](../lean/Verification/Programs/OperatorTyping.lean) (binary operators) and
[VariadicTyping.lean](../lean/Verification/Programs/VariadicTyping.lean) (variadic functions).
Its fundamental theorem
connects those rules to the model in [SEMANTICS.md](SEMANTICS.md). Subsumption uses
the certificate checker specified in [POSITIVE-TYPES.md](POSITIVE-TYPES.md).
The ordinary and graph rules below are used by the current verifier, as are the
[current-content rules](#current-content-rules-semantic-layer): supplied source
observations reach checked obligations, specified under
[source observation checkpoints](#source-observation-checkpoints). This document owns
the core expression, control-flow and heap rule statements, their side
conditions and soundness scope. Source verification also requires
[evidence search and source elaboration](SOURCE-ELABORATION.md) and
[declaration and library contracts](SOURCE-CONTRACTS.md);
[Callables](CALLABLES.md) specifies invocation and property contracts and the
proposed broader callable rules. These documents state the obligations source
claims and callable extensions must meet.
[Design](DESIGN.md) owns the principles, architecture and trust boundary.

## Notation

|                          | Ranges over                                                                                           |
| ------------------------ | ----------------------------------------------------------------------------------------------------- |
| $`t`$, $`u`$                 | [terms](SEMANTICS.md#operational-language)                                                            |
| $`t_1`$, $`t_2`$             | a branch's two arms, in that order                                                                    |
| $`a`$, $`a'`$                | terms, where a rule admits an arbitrary one rather than a variable                                    |
| $`x`$, $`y`$, $`z`$            | variables, which are terms                                                                            |
| $`c`$                      | a term in condition position                                                                          |
| $`\gamma`$                 | a [clause](POSITIVE-TYPES.md#types-and-clauses)                                                       |
| $`r`$                      | the binding a rule gives its result                                                                   |
| $`k`$                      | one of the tests in [the operational language](SEMANTICS.md#operational-language)                     |
| $`A`$, $`B`$, $`C`$            | types, each a finite list of graph labels read as their union                                         |
| $`R`$                      | a finite disjunction of primitive predicates                                                          |
| $`\mathrm{pred}(A)`$ | the predicate disjunction $`A`$ denotes, defined for supported primitives (`HeapKnowledge.atoms`)       |
| $`G`$                      | the normalized positive graph                                                                         |
| $`\Gamma`$                 | a typing context, one type per variable                                                               |
| $`\Pi`$, $`\Sigma`$          | the [equality and heap parts](#checked-expression-postconditions) of the assertion state              |
| $`\rho`$, $`h`$, $`W`$, $`n`$    | an environment, heap, world and budget, from [the model](SEMANTICS.md#computations-and-recursive-types)         |
| $`\Delta`$                 | a target claim environment, and in [POSITIVE-TYPES](POSITIVE-TYPES.md) a table of subtype obligations |

$`r`$ never names an operand, and a premise can never mention it: it is bound by
the rule's conclusion and scoped to the postcondition.

## Expressions

Typing a term against the positive graph, with no notion of state. Everything
later rests on this layer and none of it changes these rules.

### Judgments and constructor views

Fix a normalized positive graph $`G`$. A type $`A`$ is a finite list of graph labels,
interpreted as their union. Write $`A\equiv_G\gamma`$ when every label of $`A`$ is a
[clause row](POSITIVE-TYPES.md#parameter-and-scheme-rows) and expanding those
labels yields exactly the singleton clause $`[\gamma]`$ (`Represents`). A type
holding a parameter or scheme row has no expansion, so no constructor view of
it exists. This is a finite syntactic equality, not a
semantic-equivalence oracle. Below, writing a constructor as a type abbreviates
such a view of its graph labels.

The judgment $`\Gamma\vdash_G t:A`$ is `HasTyWith G images subtyping`, and
`HasTyUsing G images` is its instance at the ordinary subtyping checker. Its rules are
stated once, for every proved image checker `images` (an
[`InstanceImageCheck`](RECURSIVE-EQUATIONS.md#3-metatheory)): the checker
decides whether an instance table's named images are substitution images (over
equations, or types proved equal to them), and it carries the proof

```math
\mathrm{check}(\vec b,c)=\mathsf{true}\ \land\ \mathrm{kinds}(\vec b,c)
\ \Longrightarrow\ \forall\eta.\ \mathrm{InstanceImages}_G(\eta,\vec b,c).
```

Subtype certificates in `sub` are checked by the body's subtyping checker
(`BodySubtyping`), which carries its own soundness proof; the ordinary one is
`PositiveCertificates.checkUsing` with the image checker, which also checks
member coverage, and every rule's soundness
depends on it only through this implication. Over equations the checker also
carries the renaming and the computed variances, with which `subset` and `fallback`
steps apply `Var` ([RECURSIVE-EQUATIONS §4.3](RECURSIVE-EQUATIONS.md#43-variance)),
each proved sound. The proof is Lean code, never certificate data. `HasTyUsing G images`
is the judgment at an image checker; source requests use the finite
closed-table checker `finiteInstanceImages G`. Constructor names below are
`HasTyUsing`'s. The rules are:

```math
\frac{\Gamma(x)=A}{\Gamma\vdash_G x:A}
\qquad
\frac{}{\Gamma\vdash_G \mathsf{null}:\mathsf{Null}}
\qquad
\frac{}{\Gamma\vdash_G \mathsf{undefined}:\mathsf{Undefined}}
\qquad
\frac{}{\Gamma\vdash_G \mathsf{true},\mathsf{false}:\mathsf{Bool}}
```

Singleton introduction is also available, retaining the ordinary Boolean rules:

```math
\frac{}{\Gamma\vdash_G \mathsf{true}:\mathsf{boolLit}(\mathsf{true})}
\qquad
\frac{}{\Gamma\vdash_G \mathsf{false}:\mathsf{boolLit}(\mathsf{false})}.
```

A numeric literal has the same pair and only that pair: `numLit` gives it its
own singleton, and `num` gives it the family. Neither reaches a union above
either one; that is the subsumption rule's work, exactly as for a Boolean. A
literal claimed at $`\mathsf{Number}`$ need not have a singleton label in the graph to be coerced from,
which is why the family rule is separate rather than derived.

```math
\frac{}{\Gamma\vdash_G n:\mathsf{numLit}(n)}
\qquad
\frac{}{\Gamma\vdash_G n:\mathsf{Number}}.
```

A literal's $`n`$ is the double its decimal lexeme rounds to: TypeScript's
decimal spelling of a hexadecimal, octal or binary literal or of one with
separators, and the source's decimal text of one past the largest double
(`1e309`, which TypeScript spells `Infinity`), so a literal type and a value
of it name the infinity alike (`numericLexeme`).

A bigint literal has the same pair, `bigintLit` and `bigint`:

```math
\frac{}{\Gamma\vdash_G i\mathtt{n}:\mathsf{bigintLit}(i)}
\qquad
\frac{}{\Gamma\vdash_G i\mathtt{n}:\mathsf{BigInt}}.
```

Functions take ordered parameter lists and a receiver. Write $`\vec A`$ for a
signature's parameter types, $`|\vec A|`$ for its length and $`R`$ for its
receiver: the `this` a call passes, which is not a parameter. In the
closure creation rules below, every signature offers at least the code's
arity, and the code runs from that signature's receiver, then its first
$`\mathit{arity}`$ parameters, then the captured bindings (`bodyFrame`). A
signature may offer more: the call binds the first $`\mathit{arity}`$ actuals
and discards the rest, as JavaScript does. Code with a rest keeps exact fixed
parameters: its extra actuals go to the rest, not away.
This holds of the code, not of any value at a shorter signature: code with a
rest collects extra actuals and a bound function forwards them, so no
subtyping rule widens an arrow's parameters; a module function's slot states
the fact of its code as a variadic signature
([module rules](SOURCE-CONTRACTS.md#modules-and-code-units)). For the same reason code without
a rest also meets a variadic signature $`(R;\vec A,\ldots E\to B)`$ whose fixed
parameters cover its arity: a call through it writes any number of actuals,
the code binds its first $`\mathit{arity}`$, all at fixed positions, and
discards the rest (`restsT_of_graph`). Its code is checked at that
signature's fixed row $`(R,\vec A,B)`$, with the fixed signatures
(`offerRows`); a closure binding a position of the rest, which a call may
leave unwritten, is not created at it. A call passes its receiver $`r`$ and
types it at the selected signature's receiver:

```math
\frac{\Gamma\vdash_G f:\bigwedge_{(Q,\vec C,D)\in L}(Q;\vec C\to D)
      \quad(R,\vec A\,\vec U,B)\in L\quad\Gamma\vdash_G r:R\quad\forall i.\;\Gamma\vdash_G a_i:A_i
      \quad\forall U\in\vec U.\;\Gamma\vdash_G \mathsf{undefined}:U}
     {\Gamma\vdash_G \mathsf{invoke}(f,r,\vec a):B}
```

with $`S^\flat=\{(R,\vec A,B)\mid(R,\vec A,E,B)\in S\}`$. A plain call $`f(\vec a)`$ is $`\mathsf{invoke}(f,\mathsf{undefined},\vec a)`$,
and `.call` and `.apply` of a function (the standard intrinsics) pass their
first argument as the receiver, so it meets the selected signature's
receiver, the function's `this` parameter:

```math
f.\mathtt{call}(r,\vec a)\;\equiv\;\mathsf{invoke}(f,r,\vec a)
\qquad
f.\mathtt{apply}(r,[\vec a])\;\equiv\;\mathsf{invoke}(f,r,\vec a)
```

In
de Bruijn form the receiver's slot precedes the parameters, $`\mathit{this}`$
then $`\vec x`$, before the captures; an arrow's code has that slot too and
never reads it, and a source `this` in an arrow resolves to an enclosing
ordinary function's slot as a capture. The rule's receiver premise is
contravariant under subsumption like each domain
([`CallArrow`](POSITIVE-TYPES.md#function-and-class-coverage)), so a
function indifferent to its receiver, typed at $`\top`$, meets any receiver
requirement, and one that reads its receiver cannot be widened to arbitrary ones.

Every closure's body is a graph ([graph code](SEMANTICS.md#graph-code)),
checked where its code is, not where it is created. Code $`\kappa`$ of arity
$`m`$ with captures at $`\vec C`$ meets a signature, written
$`\vec C\vdash_G\kappa:(R;\vec A\to B)`$ (`GraphCodeSpec`), when $`m\le|\vec A|`$
and every run of it entered from an environment meeting
$`R,\vec A_{<m},\vec C`$ is safe at $`B`$. Code with a rest is entered with the
store of the further actuals first: $`\vec C\vdash_G\kappa:(Q;R;\vec A\to B)`$
when every run entered from $`Q,R,\vec A_{<m},\vec C`$ is safe at $`B`$
(`codeFrame`). The [graph checker](#checked-control-flow-graphs) establishes
either from the code's own certificate at that entry and the result $`B`$
(`GraphCode.codeChecked_sound`). What code offers depends on whether it
collects a rest (`CodeOffers`): code without one meets each fixed signature
and each variadic one's fixed row; code with one offers only variadic
signatures, each taking exactly its fixed parameters, from a frame whose
store $`Q`$ is one its rest's pack describes
($`\mathrm{Store}_G`$, below):

```math
\mathrm{Offers}_G(\kappa,\vec C,L,S)\iff
\begin{cases}
\forall(R,\vec A,B)\in L\cup S^\flat.\;\vec C\vdash_G\kappa:(R;\vec A\to B) & \kappa\ \text{collects no rest}\\
L=\varnothing\ \land\ \forall\sigma=(R,\vec A,P,B)\in S.\;|\vec A|=m\land\mathrm{Store}_G(Q_\sigma,P)\land\vec C\vdash_G\kappa:(Q_\sigma;R;\vec A\to B) & \kappa\ \text{collects a rest}
\end{cases}
```

Code has a kind $`k`$ ([graph code](SEMANTICS.md#graph-code)): `call` code
binds every receiver; `sloppy` code, sloppy code that reads `this`, binds an
object only. Code of a kind offers a signature when the kind binds every
receiver the signature admits (`KindOffers`, `kindOffers`): any signature for
`call`; for `sloppy`, one whose receiver type is of clause rows, each an
object clause (`objectClause`: a record, a dictionary, a function, a callable
or a constructor):

```math
\mathrm{Kind}_G(k,L,S)\iff k\ne\mathsf{construct}\ \land\
  \forall(R,\vec A,B)\in L\cup S^\flat.\;
  k=\mathsf{call}\ \lor\ \bigl(R\ \text{plain}\land\forall c\in\mathrm{expand}_G(R).\;c\ \text{an object clause}\bigr)
```

Every receiver such a signature admits is then an object (`kindOffers_binds`,
from `objectClause_member`). Soundness is `offers_sem`: code without a rest
meets its signatures by `callsT_of_graph` and `restsT_of_graph`, code with one
its variadic signatures by `restsT_of_graphRest`, whose invocation allocates
the store before the run starts (`graphRest_invoke`); each invocation steps,
since the code's kind binds the receiver. Creation then reads the captures
only:

```math
\frac{\mathrm{Kind}_G(k,L,S)\quad\mathrm{Offers}_G(\kappa,\vec C,L,S)
      \quad\forall i.\;\Gamma\vdash_G x_i:C_i}
     {\Gamma\vdash_G \mathsf{make}(\kappa[\vec x],\mathsf{null}):\bigwedge_{(R,\vec A,B)\in L}(R;\vec A\to B)
       \land\bigwedge_{(R,\vec A,E,B)\in S}(R;\vec A,\ldots E\to B)}\ (\texttt{funGraph})
```

where $`\kappa[\vec x]`$ is $`\kappa`$, of kind $`k`$, capturing the slots $`\vec x`$. Its evidence
(`Rule.funGraph`) names each signature as an entry of the unit's code table:
the codes a request carries, each checked in order against the table of those
before it (`GraphCode.checkCodesUsing`), so that every entry meets its signature
(`CodesSound`, `checkCodes_sound`); code created inside code is checked first.
No code check reads the graph's assignment (`Parametricity.checkEntry_reassign`),
so an entry meets its signature in the graph reassigned at every assignment
$`\eta`$ of its parameter rows, $`\vec C\vdash_{G[\eta]}\kappa:\sigma`$, which is
what `CodesSound` states. For code with a rest the evidence also lists the
store types $`Q_\sigma`$, in the signatures' order (`Rule.funGraph arrays`), and
each table entry the store its frame starts with (`CodeEntry.store`).

A generic closure is graph code at a scheme row $`j`$, $`G(j)=\forall\vec p.\,(L,S)`$
with binders $`\vec p`$ (parameter rows) and signatures $`L`$ and $`S`$ over them
(`HasTyUsing.funScheme`). Its code is checked once, at the scheme's own signatures:
a table entry holds at every assignment of $`\vec p`$ the graph's domain admits
(`G.domain.allowed`), so at every instantiation of $`\vec p`$; for an
unqualified row every assignment is admitted, and a row is qualified by the
bounds its source signature implies ([implied bounds](SOURCE-CONTRACTS.md#implied-bounds)). The arity and rest-store
requirements are checked once, independently of the assignment (`CodeOffersShape`).
Its captures' types read none of $`\vec p`$ (`capturesFree`: their free parameter
rows, computed and checked by `FreeOk`,
exclude the binders), so a capture means at every instantiation what it means
here (`meaning_assign_free`):

```math
\frac{G(j)=\forall\vec p.\,(L,S)
      \quad\mathrm{Kind}_G(k,L,S)
      \quad\forall\eta\,\vec B\in\mathrm{allowed}(j).\;\mathrm{Offers}_{G[\eta,\vec p:=\vec B]}(\kappa,\vec C,L,S)
      \quad\mathrm{fv}(\vec C)\cap\vec p=\emptyset
      \quad\forall i.\;\Gamma\vdash_G x_i:C_i}
     {\Gamma\vdash_G \mathsf{make}(\kappa[\vec x],\mathsf{null}):j}\ (\texttt{funScheme})
```

Soundness is **Call-Scheme-I** ([callable scheme rules](CALLABLES.md#overloads-polymorphism-and-binding))
with each instance's signatures read in the graph reassigned at that instance.
The evidence is `Rule.funGraph` at a scheme row: the checker reads the row's
signatures instead of an arrow clause's (`graphCodesChecked`, `schemeOf`). A
binder with a bound of clause rows is read, in the signatures and inside the
closure, as the meet row $`p\sqcap B`$, as a generic unit's is: at every
instantiation within the bound the meet is the binder. A binder bounded by
another of the closure's binders, `U extends T`, is read as the meet of the two
parameter rows, $`p_U\sqcap p_T`$ within $`T`$'s clauses if it has any
(`dependentMeet`): its bound reads a binder, which a scheme row's bounds, read
outside its binders, cannot, so the meet alone states it. A call of a binding
at the scheme row names its instance: the callee is read at the instance's
signature, below the scheme by a checked instance (`compareInstArrsState`), a meet row
mapped to the meet of its parameters' type arguments with its clauses
(`meetOk`).

A call writes a prefix of the positions the selected signature declares:
$`|\vec a|=|\vec A|`$, and $`\vec U`$ are the positions it omits. Omission is
admissible exactly when each omitted contract admits `undefined`: that is part
of what the signature promises (below), and closure code keeps the promise
because `CallArguments.parameters` pads a short actual list, so the body
dispatched for $`f(\vec a)`$ is the same term as for the call that writes those
`undefined`s out (`CallArguments.parameters_pad`, in `frame_envOk`, the
frame every code is entered with). With $`\vec U`$ empty this is the exact-arity rule.
No actual is invented: the call term keeps the arguments the source writes.

Optionality is therefore a property of a declared contract, not a separate
arity record: `x?: T` is carried as `T | undefined`, which is what the body
reads and what licenses the omission. Declared arity is not observable in this
fragment, so a call may also omit a trailing position a producer declared as
`T | undefined` without writing `?`, which TypeScript rejects; the verifier
proves such a call safe rather than enforcing that surface rule. An empty
parameter list is a zero-argument call, not an absent one. A tuple rest
parameter and a tuple spread are a fixed number of positions each, so they need
no rule of their own here: the signature carries the positions, and the array a
rest parameter binds is allocated by the ordinary store and allocation rules.
Into fixed parameters, or into a rest that is one tuple contract (an argument
pack's instance), each spread's positions are ordinary element reads of
its operand's store, made once every actual is evaluated, in position order,
and the call takes them as actuals where the spread is written; the lowering
admits no actual that runs code after the first spread, so the reads see what
JavaScript's spreads, each read where it is written, would.
That array is fresh, so a rest parameter's contract may also be `readonly`
(`readonly T[]`, a readonly tuple) or name one through a declared alias: the
body sees the fresh array through that view, which gives up only writes. A
generic alias is read through its equation at the reference's arguments,
$`\mathit{Alias}\langle\vec A\rangle = E[\vec A/\vec X]`$, in a definition, a
function type and a declared function alike, as TypeScript reads it:

```math
\frac{\mathsf{type}\ \mathit{Alias}\langle\vec X\rangle = E\quad E[\vec A/\vec X]\ \text{an array or a tuple of required positions}}
     {\ldots x : \mathit{Alias}\langle\vec A\rangle\ \text{collects into}\ E[\vec A/\vec X]}
```

A module function's rest typed by one of its own type parameters,
`function f<P extends B>(…, ...x: P): R`, makes $`P`$ an
[argument pack](POSITIVE-TYPES.md#argument-packs) bounded by the pack of its
bound $`B`$, an array or a tuple of required positions written as one: every
call instantiates $`P`$ at the list it collects, checked within that pack
(scheme elimination). The array a call collects is fresh, with the actuals and
none of an instance's other members, so the body takes $`x`$ at $`B`$, the
elements every instance's list has, and $`P`$ types nothing else:

```math
\frac{P\notin\mathrm{fv}(\vec A,R,\mathit{body})\quad B\ \text{an array or a tuple of required positions}
      \quad \vec y:\vec A,\ x:B\vdash\mathit{body}:R}
     {\mathsf{function}\ f\langle P\le B\rangle(\vec y:\vec A,\ldots x:P):R\ :\ \forall P\le\mathsf{Pack}(\tau_B).\,(\vec A,\ldots P)\to R}
```

Here $`\tau_B`$ is $`B`$'s tuple contract. A list within an instance $`X\le\mathsf{Pack}(\tau_B)`$
is within $`\mathsf{Pack}(\tau_B)`$, so the store a call collects meets the store type $`B`$
describes (this step has no Lean proof); that each call meets the body's input at
$`B`$ is the module function's interface ([module rules](SOURCE-CONTRACTS.md#modules-and-code-units)).
In a module function a type parameter typing a rest and anything else is
[refused on principle](SOURCE-FRAGMENT.md#refused-on-principle).

A declared function's type parameter $`T`$ typing a value and a rest,
`declare function f<T extends B>(…, ...x: T): R`, is instantiated at each call
at a type $`X`$, as any value binder is. The rest's argument lists are those
of $`X`$'s tuple contract $`\tau_X`$, which requires $`X`$ to be an array or
tuple type, and the declaration's contract at the call reads

```math
\frac{X\le B\quad X=\mathsf{Array}_{\rho}(\tau_X)}
     {f:(\vec A,\ldots\mathsf{Pack}(\tau_X))\to R\ \text{at}\ T:=X}
```

with $`\mathsf{Array}_\rho(\tau)`$ the built-in array over a store of contract
$`\tau`$, readonly or not. That is the contract's meaning at $`X`$: every
argument list in $`\mathsf{Pack}(\tau_X)`$ collects into a fresh array of
$`X`$, and these are the lists a call collects into one. An instance with
further members (`string[] & { tag: string }`) or no array is refused
(`instancePack`). The contract is an input's, assumed as declared
([trust surface](DESIGN.md#trust-surface)); a call instantiates $`T`$ at the
tuple of its actuals.

A rest typed by anything else is refused by its form: by a type parameter
of a closure or of an enclosing declaration (a closure's scheme reads a bound
as the meet of its binder with it, and argument lists have no meet row), by
an intersection (its contract can be empty
at an instance TypeScript admits, [refused on principle](SOURCE-FRAGMENT.md#refused-on-principle)), by a tuple with
optional or rest elements (several lengths), or by what is no array.

A function type is a promise about the actual lists a caller may write, not
about the callee's code. A fixed signature $`\vec A\to B`$ admits the prefixes of
$`\vec A`$ whose omitted positions admit `undefined`. A variadic signature
$`\vec A,\ldots P\to B`$ has a rest type $`P`$, an [argument pack](POSITIVE-TYPES.md#argument-packs):
it admits the lists whose first actuals $`\vec A`$ admits, as a fixed signature
does, and whose actuals past them are, as one list, in $`P`$'s argument lists,
at the current level (`argMeaning`). An element rest `...xs: E[]` admits any
number of actuals in $`E`$, $`\mathsf{Pack}([\,],[\,],E)`$ (`restElem_args`); a
tuple rest `...xs: [A, B]` exactly those positions:

```math
\mathrm{Adm}(\vec A)=\{\vec v\mid |\vec v|\le|\vec A|,\ \forall i<|\vec v|.\,v_i\in A_i,\ \forall |\vec v|\le i<|\vec A|.\,\mathsf{undefined}\in A_i\}
```

```math
\mathrm{Adm}(\vec A;P)=\{\vec v\mid \vec v_{<|\vec A|}\in\mathrm{Adm}(\vec A),\ \mathsf{args}(\vec v_{\ge|\vec A|})\in P\}
\qquad(\texttt{ArgsRest}).
```

A list shorter than $`\vec A`$ passes the empty pack, which an element rest
admits and a tuple rest with required positions does not.

A value meets a signature when every admitted list of values invokes it safely
at $`B`$, at every later world and budget (`Safety.Promise`, `callsT`, `restsT`).
This instantiates the [common behavioral equation](SEMANTICS.md#one-meaning-for-callable-contracts),
which also explains overload conjunction, callable fields and quantification.
Code enters only where it is created: graph code pads a short list
(`graph_invoke`), and code with a rest collects the actuals past its $`k`$
fixed parameters into a fresh store, which its entry allocates with the
ordinary steps before the run starts (`graphRest_invoke`):

```math
\mathrm{invoke}(\kappa^{\ldots}[\vec c],r,\vec v)=
\mathsf{let}\ x=\mathsf{arr}(v_k,v_{k+1},\ldots)\ \mathsf{in}\ \mathsf{goto}(E,K,s,[x,r,\mathrm{pad}_k(\vec v),\vec c])
\qquad(\texttt{graphEntry})
```

A pack holds its actuals at their positions only below the current level. The
allocation is a step, after which the budget is one lower, so that is all the
fresh store's contracts need (`arr_alloc_rule_below`, `pack_alloc_safe`).

So one value may meet fixed and variadic signatures at once, and a graph call
clause carries both: `arrs L S`, `callable P Ps L S`. Write
$`\mathrm{Store}_G(Q,P)`$ when $`Q`$ is the store $`P`$'s one tuple contract
describes, writable since the store is fresh (`RestStore`), and $`\mathrm{Spreads}_G(S,E)`$ when $`S`$ is a
store contract every position of which is within $`E`$, and either it is
dense or $`E`$ includes `undefined` (`SpreadsInto`). A hole yields
$`\mathsf{undefined}`$ and must therefore be admitted by $`E`$. Creation checks the code once per variadic signature, from the
frame with the rest store in slot 0, the receiver in slot 1, then the fixed
parameters: the second case of $`\mathrm{Offers}_G`$ (`funGraph`;
`callableGraph` adds a field bag). The code's entry node wraps the store into
the array the rest parameter names, an ordinary allocation the extractor
emits.

[RestCalls.lean](../lean/Verification/Programs/RestCalls.lean) proves variadic calls: eliminating a variadic signature, allocating the rest store, spreading actuals.

A call writes the fixed actuals, or a prefix whose omitted positions admit
`undefined`, then parts that fit the rest; a call that omits a fixed position
writes no part (`callRest`). With a spread among the parts, the rest is an
element rest $`\mathsf{Pack}([\,],[\,],E)`$ ($`\mathrm{elem}_G(P)=E`$,
`restElem`), and each part is an actual in $`E`$ or a spread of a store whose
elements are. Without one, $`P`$ is one tuple contract $`\tau`$, and the parts are
at its positions within its length bounds (`RestParts`):

```math
\frac{\begin{array}{c}\Gamma\vdash_G f:F\quad(\vec A\,\vec U,P,B)\in\mathrm{restSigs}_G(F)
      \quad\forall i.\;\Gamma\vdash_G a_i:A_i\quad\forall U\in\vec U.\;\Gamma\vdash_G\mathsf{undefined}:U\\
      \vec U=\varepsilon\lor\vec p=\varepsilon\qquad\mathrm{Parts}_G(P,\vec p)\end{array}}
     {\Gamma\vdash_G f(\vec a,\vec p):B}
```

```math
\mathrm{Parts}_G(P,\vec p)\iff
\begin{cases}
\mathrm{elem}_G(P)=E\ \land\ \forall p\in\vec p.\;\Gamma\vdash_G p:E\ \lor\ (p={\ldots}s\land\Gamma\vdash_G s:S\land\mathrm{Spreads}_G(S,E)) & \text{a spread in }\vec p\\
P=\mathsf{Pack}(\tau)\ \land\ |\tau.R|\le|\vec p|\ \land\ (\tau.E=\varnothing\Rightarrow|\vec p|\le|\tau.R|+|\tau.O|)\ \land\ \forall i.\;\Gamma\vdash_G p_i:\mathsf{pos}_\tau(i) & \text{otherwise}
\end{cases}
```

The first case is `rest_call_safe`: the actuals collected at $`E`$ form a list
the element rest admits (`restElem_args`). The second is `pack_call_safe`: the
actuals at the positions form a list $`\tau`$ admits (`restParts_pack`). The
rest store is allocated from those actuals at the current level; the
allocation step consumes the level (`restStore_safe`,
`RestCalls.argument_alloc_safe`). `RestStore` checks identical element positions
and length bounds and requires a writable result. The fresh store may use any
presence mode: all collected positions exist. Pack metadata does not impose a
lifetime presence contract on this allocation.

A spread is read by the call once every earlier actual is a value, the store's
elements replacing it in order, `undefined` at a hole
(`Step.callSpread`, `spread_parts_safe`):

```math
(h,\ f(\vec v,\ {\ldots}\mathsf{arr}(\vec\ell),\ \vec p))\longrightarrow
(h,\ f(\vec v,\ h(\ell_1),\ldots,h(\ell_m),\ \vec p))
```

Into a rest, a spread followed by an actual that runs code is copied where it
is written, `[...s]`, a fresh store the call then spreads, so the later actual
cannot change what it passes ([a literal with spreads](#a-literal-with-spreads),
`arrParts`); into fixed parameters the lowering admits no such actual (above).
A hole read from the source becomes a present `undefined` value in the copy.

For a required tuple, source lowering instead reads its known positions in
order into an ordinary array literal before evaluating later actuals. The
existing element-read and array-literal rules preserve the tuple's exact
contract, including density. This avoids weakening a dense Boolean tuple to
an unbounded store that would require `undefined` when spread again.

Covering compares admitted lists. A variadic source with an element rest
covers a fixed target whose first positions are within its fixed parameters and
whose further positions are within its element (`RestFixed`, a `CallArrow`
case). A variadic source covers a variadic target whose parameters are within
its own, the target's further fixed positions taken into the source's rest,
which needs an element rest unless there are none (`IntoRest`), and whose rest
is within its own as a pack (`RestCovers`); results are covariant. A fixed
source never covers a variadic target with an element rest: it promises nothing past its positions. It covers
one whose rest is one exact tuple, of any positions, its parameters within the
source's first and the tuple's positions within the rest
(`FixedCallsPack`, as `FixedCoversPack` for construct signatures in
[POSITIVE-TYPES.md](POSITIVE-TYPES.md#function-and-class-coverage));
at level zero the call exists and nothing past it is owed.

```math
\frac{k=|\vec P|\le|\vec A|\quad\forall i<k.\;A_i\le P_i\quad\mathrm{elem}_G(P')=E\quad\forall k\le i<|\vec A|.\;A_i\le E\quad B\le D}
     {(\vec P,\ldots P'\to B)\le(\vec A\to D)}
```

```math
\frac{k=|\vec P|\le|\vec Q|\quad\forall i<k.\;Q_i\le P_i\quad
      (k=|\vec Q|\ \lor\ \mathrm{elem}_G(P')=E\land\forall k\le i<|\vec Q|.\;Q_i\le E)\quad Q'\le P'\quad B\le D}
     {(\vec P,\ldots P'\to B)\le(\vec Q,\ldots Q'\to D)}
```

```math
\frac{Q'=\mathsf{Pack}(\vec E)\ \text{exact}\quad\forall E\in\vec E.\,\mathsf{stable}(E)\quad
      |\vec P|=|\vec Q\vec E|\quad\forall i.\;(\vec Q\vec E)_i\le P_i\quad B\le D}
     {(\vec P\to B)\le(\vec Q,\ldots Q'\to D)}
```

```math
\frac{\Gamma\vdash_G a:A\quad\Gamma,x:A\vdash_G b:B}
     {\Gamma\vdash_G \mathsf{let}\ x=a\ \mathsf{in}\ b:B}
```

A bound function (`bindE`) is allocated from saved slots: the target $`f`$, the
receiver $`r`$ and the prefix $`\vec p`$, whose types the rule reads from the
context. The target's selected signature starts with the prefix's types; the
result takes the rest, at any receiver, since invoking it drops the receiver it
is given (`CallCode.bound`, `callsT_bound`):

```math
\frac{\Gamma(f)=F\quad\Gamma(r)=R\quad\Gamma(\vec p)=\vec P\quad
      \forall i.\ (R,\vec P\,\vec D_i,B_i,\epsilon_i)\in\mathrm{callSigs}_G(F)}
     {\Gamma\vdash_G\mathsf{bound}(f,r,\vec p):\textstyle\bigwedge_i (Q_i;\vec D_i\to B_i)\,[\epsilon_i\!\downarrow_{|\vec p|}]}
```

The bound function meets each of the selected signatures, one or more, and
keeps each one's effect. A promise about
the $`p`$-th parameter (`guards p`, `asserts p`) survives only where
$`p\ge|\vec p|`$, and is then about parameter $`p-|\vec p|`$ (`Effect.keeps`,
`Effect.drop`). A call rule (`app`, `callCallable`, `callRest`,
`callPacked`) applies a signature whose result family is its result type
(`Effect.plain`); a promise signature is consumed by the narrowing after a
call ([user-defined guards](SOURCE-CONTRACTS.md#user-defined-guards)).

A method member is host-relative: its contract holds when it is invoked on
the object it is read from ([Source model](SOURCE-MODEL.md#method-members-are-host-relative)).
A member bound to its host (`bindMember`) is read from the object in slot $`i`$
and bound to that same object in one term, so the member is read before any
actual runs, as JavaScript reads it, and the bound function meets the member's
signatures at any receiver, and every signature one of them covers: each
claimed parameter within the member's, for a variadic signature of as many
fixed parameters the claimed rest within the member's too, and the member's
result within the claimed one, by checked subtyping proofs the certificate
carries (`CoveredCallUsing`, `CallProofsUsing`, `CoveredRestUsing`, `RestProofsUsing`).
The host's type is within each type the member's host must meet, a `this`
parameter's ($`m.\mathsf{this}`$), by checked proofs the certificate carries
too. A claim may so name another label for the same type, as a producer's own row
for a declared `[number, number]`, or for a declared rest
`EagerCollection<K, V>[]` at its instance, which the declaration's literal
head applied to the instance's arguments names too. With
$`\mathrm{member}_G(O,k)=m`$ the method of key $`k`$ in $`O`$'s one object
clause (`memberOf`):

```math
\frac{\Gamma(i)=O\quad\mathrm{member}_G(O,k)=m
      \quad\forall(Q,\vec D,B)\in L.\;\exists(\vec C,B')\in m.\mathsf{calls}.\;
        G\vdash\vec D\le\vec C\land G\vdash B'\le B
      \quad\forall(Q,\vec D,P,B)\in S.\;\exists(\vec C,P',B')\in m.\mathsf{rests}.\;
        G\vdash\vec D\le\vec C\land G\vdash P\le P'\land G\vdash B'\le B
      \quad\forall T\in m.\mathsf{this}.\;G\vdash O\le T}
     {\Gamma\vdash_G\mathsf{let}\ f=i.k\ \mathsf{in}\ \mathsf{bound}(f,i,[]):\mathsf{arrs}(L;S)}
```

Both $`\vec D`$ and $`\vec C`$ are the fixed parameters, of equal length, and the
effects are covered as for a call. The rest premise is an inclusion of
argument lists: a checked proof relates the argument-list component of the
two types' meanings as it relates their values (`argsAcceptedUsing`), and a
variadic signature admits every list a narrower one does (`ArgsRest_mono`).

A generic method's member states its signatures as schemes, quantified
signatures the member bound to its host meets
([records](POSITIVE-TYPES.md#records)). The same term, bound to its host, is
then one of those schemes (`bindScheme`), and a call names its instance below
it ([`compareInstArrsState`](POSITIVE-TYPES.md#instances-of-a-scheme-row)):

```math
\frac{\Gamma(i)=O\quad\mathrm{member}_G(O,k)=m\quad [j]\in m.\mathsf{schemes}}
     {\Gamma\vdash_G\mathsf{let}\ f=i.k\ \mathsf{in}\ \mathsf{bound}(f,i,[]):[j]}\ \textsf{bind-scheme}
```

The certificate is `bindMember` with no proofs, at a type of no clauses, the
scheme row. A scheme's own receivers are the forwarding function's, which
ignores them, so a member's scheme admits every receiver; an instance may
state a narrower one, the call's object (`instSig`).

The member read from $`v=\rho(i)`$ meets $`m`$'s signatures with receiver $`\{v\}`$
where $`v`$ is in each of $`m.\mathsf{this}`$ (`memberOf_at`,
`MethodMembers.onHost`), which $`v\in O`$ and the proofs of $`O\le T`$ give. The read finds the key on $`v`$, or, one
step later, on the object $`v`$'s prototype holds (`Step.readProto`,
`member_read_safe`), as the member's meaning says. The bound descriptor, which has
no fields and allocates nothing, forwards any call to it with receiver $`v`$
(`callsT_bound`, `restsT_bound`). The source form `o.m.bind(o)`, `o` one
immutable name and `m` a method member of its type, is this term: `bind`
of what `o.m` holds to `o` itself, a bound function whatever receiver it is
later called with (`closureExpr`); the iterator protocol reads `next` so.

A variadic target with an element rest (`bindRestE`, `restsT_bound`) gives
its first fixed positions to the prefix and, past them, its element $`E`$; the
result keeps the positions left and the rest $`P`$, which admits the prefix's
values past the fixed positions in front of any list it admits:

```math
\frac{\Gamma(f)=F\quad(R,\vec P,P',B)\in\mathrm{restSigs}_G(F)\quad\mathrm{elem}_G(P')=E
      \quad\Gamma(r)=R\quad\Gamma(\vec p)=\vec P_{<k}\,E^{\,k-|\vec P|}\quad k=|\vec p|}
     {\Gamma\vdash_G\mathsf{bound}(f,r,\vec p):(Q;\vec P_{\ge k},\ldots P'\to B)}
```

Here $`\lambda\vec x.t`$ denotes source function creation, graph code whose
body is $`t`$'s graph (`funGraph`): it allocates an object before any invocation. `let` has its own operational constructor, `letE a b`. It evaluates `a`,
then substitutes the resulting value into `b` in one nonallocating step.
Neither a function value nor a function-type graph label is needed. The
producer and consumer use this constructor directly. [ExecutionModelTests.lean](../lean/Verification/Tests/ExecutionModelTests.lean) shows the machine
taking no step of the body while the initializer is stuck.

A class value is construct-only code: JavaScript gives a function object
`[[Call]]` and `[[Construct]]` separately, and a class has only the second,
an arrow only the first. The calculus records which in the closure's code
(`kind`), a plain call dispatches only call code, and `new f(args)` is its own
term, which evaluates `f`, then the actuals, and runs only construct code, with
`undefined` for the receiver. A construct signature
$`\mathsf{new}(A_1,\ldots,A_n)\Rightarrow^{\varepsilon} B`$ (the `ctors` clause)
is met by a class whose code, for actuals at the parameters, is safe at $`B`$
and whose normal return meets the signature's effect $`\varepsilon`$ from the
heap the construction starts in (`ConstructPromise`), as a call signature's
effect is met ([inferred call effects](SOURCE-MODEL.md#inferred-call-effects-elaboration-and-certification)). As for a
function, a signature may offer more parameters than the constructor binds:
the construct step binds its first $`\mathit{arity}`$ actuals and discards the
rest, so the code is checked at the signature's first $`\mathit{arity}`$
parameters, entered with `undefined` for the receiver. Its code $`\kappa^{\mathsf{new}}`$ is
construct-only graph code, allocated, as a function's is, with its code field
$`\kappa_{\mathsf{code}}`$ and, as a callable object's bag is, with its static
fields $`\overline{k_i{=}e_i}`$, each at its contract $`A_i`$ (the class's bag
$`\varphi=\overline{k_i{:}A_i}`$, empty for a class with none):

```math
\frac{L\equiv_G\mathsf{Ctors}(\ldots,(\vec A,B,\varepsilon),\ldots;\varphi)\quad
      U\equiv_G\mathsf{Undefined}\quad
      \kappa_{\mathsf{code}}\,\vec k\ \text{distinct}\quad
      \forall i.\;\Gamma\vdash_G e_i:A_i\quad
      \vec C\vdash_G\kappa^{\mathsf{new}}:(U;\vec A\to^{\varepsilon} B)\ \text{for each signature}\quad
      \forall j.\;\Gamma\vdash_G x_j:C_j}
     {\Gamma\vdash_G \mathsf{make}(\kappa^{\mathsf{new}}[\vec x],\kappa_{\mathsf{code}}{=}\mathsf{null},\overline{k_i{=}e_i}) : L}
\qquad
\frac{\Gamma\vdash_G f:L\quad L\equiv_G\mathsf{Ctors}(\ldots,(\vec A\,\vec U,B,\varepsilon),\ldots;\varphi)\quad
      \varepsilon\ \text{plain}\quad
      \Gamma\vdash_G a_i:A_i\quad\Gamma\vdash_G\mathsf{undefined}:U_j}
     {\Gamma\vdash_G \mathsf{new}\ f(\vec a):B}
```

A plain effect has no promise, so its result operand is the result's type. A
construction with value operands runs within its selected signature's
footprint $`\varepsilon`$ (`CallEffects.construct_safe`), which is how a body
checked against a bound consumes it, as it consumes a call's
([FOOTPRINTS.md](FOOTPRINTS.md#the-checked-callback-contract)).

A static field is read and written as a callable object's bag field is
(`readCallable`, `writeCallable`, over the clause's bag, `Clause.bag`), a
readonly one read as a view (`readBagView`, `views_at`), and a spread of a
class value copies its own data fields, of which its type states its static
fields (`codeOf`, [allocation from parts](SEMANTICS.md#operational-language)):

```math
\frac{\Gamma\vdash_G a:F\quad F\equiv_G\mathsf{Ctors}(\ldots;\vec\varphi;\psi)\quad(f{:}A)\in\psi}
     {\Gamma\vdash_G a.f:A}\ (\texttt{readBagView})
```

A plain call of a class throws in JavaScript: `tests/node-runs.mts` runs
`invalid-class-as-function` under Node beside the pipeline's refusal of it.
[ExecutionModelTests.lean](../lean/Verification/Tests/ExecutionModelTests.lean) shows the model's `new` running no call-only code, as JavaScript's `new`
of an arrow throws.

These are `ctorGraph` (`ctorsT_of_graph`, `make_fields_rule`) and `construct`. As a call may,
`new` may omit trailing positions $`\vec U`$ whose contracts admit `undefined`:
the construct step binds `undefined` there, so the run entered is the one the
padded list enters (`construction_pad`), and the source term keeps the actuals it writes. A
`new` with explicit type arguments, `new C<T>()`, names the instance of a
generic class it constructs: the producer proposes that instantiation, and it
is checked as an inferred one is ([explicit type arguments](SOURCE-CONTRACTS.md#explicit-type-arguments)). No arrow meets a construct signature and no
class a call signature, so `new` on an arrow and a plain call of a class are
refused, as JavaScript throws. A construct signature is covered by one taking
as many parameters, each at least as wide, with a result at most as wide, that
supplies its effect: `new (params: Specific) => R` is a `new (params: never) => R`.

#### Packed binders

A binder a declaration uses both as a value and as a rest's argument lists
(`class RestRunner<T extends readonly unknown[]> { args: T; callback: (...args: T) => number }`)
is **packed**. Write $`T^{*}`$ for its argument lists. Its domain relates
the two components:

```math
\vec v\in T^{*}\ \text{for the element list}\ \vec v\ \text{of each}\ v\in T
\qquad\qquad
\mathrm{fresh}(\vec v)\in T\ \text{for each}\ \vec v\in T^{*}
```

The first law, **spread**, reads a value of $`T`$ as one of its argument
lists. The second, **collection**, makes the fresh array a call collects from
a list of $`T^{*}`$ a value of $`T`$. A packed binder ranges over the
instances where both hold: array or tuple types with no other members and no
sparse holes, whose values are the arrays of their elements. Every
instantiation checks it, at the call, `new` or type argument naming the
instance (`instancePack`, `packOf`); a tagged array type, whose values carry
a member a fresh array lacks, is refused there
(`invalid-class-rest-binder-instance`). The spread law is part of the
binder's meaning and is proved. The collection law is read by no typing
rule and is not proved: it speaks of lists no program has allocated as an
array, which needs an array-allocation lemma whose statement is open
([refused on principle](SOURCE-FRAGMENT.md#refused-on-principle)).

A packed binder is one parameter row read in both components of its mixed
family $`\eta(T)`$: its argument lists are $`\eta(T)^{\mathsf{args}}`$, and
its values are $`\eta(T)`$'s values that are **packable** by those lists:

```math
⟦T⟧_n(W,v)\iff \eta(T)_n(W,v)\ \land\ \mathrm{Packable}(\eta(T)^{\mathsf{args}})_n(W,v)
```

```math
\mathrm{Packable}(P)_n(W,v)\iff \forall j{+}1\le n,\ U\sqsupseteq W|_{j+1},\ h\models_{j+1}U.\
  v=\mathsf{obj}(\varphi),\ h(\varphi.\mathtt{[]})=\mathsf{arr}(\vec\ell),\
  \mathrm{readElems}_h(\vec\ell)=\vec v,\ \forall i{+}1\le j.\ P_i(U|_i,\vec v)
```

(`Packable`, `selectParameter`). The relation is in the meaning of the row,
so a body checked at every assignment (`Parametricity.accepted_at`) needs no
assumption about the assignment. A body reads a packed binder at its row,
without its declared bound, and a scheme quantifying one has no bound for it:
the bound is checked where an instance is named. A spread of a value of the
binder, or of a meet row of it, into a variadic callee whose rest admits the
binder's lists, after the fixed actuals, passes one of those lists
(`callPacked`, `packed_call_safe`, `packedBy_sound`):

```math
\frac{\Gamma\vdash_G f:F\quad(R_t,\vec A,P,B)\in\mathrm{restSigs}_G(F)\quad t\in P\quad
      \Gamma\vdash_G r:R_t\quad\forall i.\;\Gamma\vdash_G a_i:A_i\quad\Gamma\vdash_G a:A\quad
      \mathrm{PackedBy}_G(A,t)}
     {\Gamma\vdash_G f(\vec a,\ {\ldots}a.\mathtt{[]}):B}\ \textsf{callPacked}
```

**Instantiation.** At an instance, an array or tuple type $`X`$ whose store
meets a tuple contract $`\tau`$ with no sparse holes is packable by
$`\tau`$'s lists: a satisfying heap holds at the store's location a store
meeting $`\tau`$ one level down, whose elements fit $`\tau`$ below that;
this lemma has no Lean proof. So at $`T:=X`$, with
$`T^{*}:=\mathsf{Pack}(\tau)`$, the binder's values are exactly $`X`$'s:

```math
\frac{X=\mathsf{Array}(s)\qquad s=\mathsf{list}(\tau)\qquad \tau.\mathrm{presence}\ne\mathsf{sparse}}
     {\forall v\in X.\ \mathrm{Packable}(\mathrm{Fits}\,\tau)(v)}\ \textsf{InstPack}
```

The lemma reads only the heap the program already holds; it allocates
nothing. A declaration's packed parameter's argument at an application is
its instance's value and lists (`packOf`), and a packed binder's lists are
spelled with its packed name, `T#pack`.

#### Variadic construct signatures

A variadic construct signature $`\mathsf{new}(\vec Q,\ {\ldots}P)\Rightarrow^{\varepsilon} B`$,
its effect $`\varepsilon`$ plain, admits the lists whose first $`|\vec Q|`$ actuals are at $`\vec Q`$ and whose
further ones form a pack of $`P`$ (`CtorRest`, `ctorRestsT`). `new` reads a
spread actual as a call does, its store's elements replacing it once every
earlier actual is a value (`Step.constructSpread`), and the parts past the
fixed actuals fit the rest as a variadic call's do ($`\mathrm{Parts}_G`$
above; `constructRest`, `construct_rest_safe`, `construct_pack_safe`,
`ctor_elim_rest`):

```math
\frac{\Gamma\vdash_G f:L\quad L\equiv_G\mathsf{Ctors}(\ldots;\ldots,(\vec Q,P,B,\varepsilon),\ldots)\quad
      \forall i.\;\Gamma\vdash_G a_i:Q_i\quad\mathrm{Parts}_G(P,\vec p)}
     {\Gamma\vdash_G \mathsf{new}\ f(\vec a,\vec p):B}\ \textsf{constructRest}
```

A class meets one with an element rest $`\mathrm{elem}_G(P)=E`$ when its code
of arity $`k`$ is safe from the row binding the fixed parameters, then each
further position up to $`k`$ at $`E`$ or `undefined`: construction binds the
first $`k`$ actuals, `undefined` where the list is shorter, and discards the
rest (`ctorRestParams`, `ctorRestsT_of_graph`):

```math
\frac{\vec C\vdash_G\kappa^{\mathsf{new}}:\bigl(U;\ \vec Q\,(E\mid\mathsf{undefined})^{k-|\vec Q|}\to^{\varepsilon} B\bigr)}
     {\kappa^{\mathsf{new}}[\vec x]\ \text{meets}\ \mathsf{new}(\vec Q,\ {\ldots}P)\Rightarrow^{\varepsilon} B}
```

This is the variadic premise of `ctorGraph`. A class value whose code binds
a position the rest may leave out at a type without `undefined` is refused
there, though TypeScript accepts it (`invalid-constructor-rest-class`, run
under Node).

An object is a finite map from field names to heap locations, fixed at
allocation. Let $`\varphi`$ range over field maps $`\overline{f{:}A}`$ with distinct
names, and write $`\mathsf{Ref}(\varphi)`$ for the record clause carrying those
invariants. `alloc` allocates one fresh location per named field, and the names
being distinct is what makes the result a map from them. The object's own keys
are exactly those names, so its type may also bound them: each own-key bound
$`b`$ the type states must admit every name
([POSITIVE-TYPES.md](POSITIVE-TYPES.md#records)). An array is allocated this
way, its store and prototype as the two fields, own keys among those two, then
read as an array, owning none of `ArrayProto`'s keys, by subsumption. A record
type is of objects meeting the built-ins'
[array invariant](SEMANTICS.md#the-array-invariant), so an allocation owning
the store key $`\sigma`$ must be a built-in array
($`\mathsf{builtins}\vDash\overline{f{:}A}`$, `allocBuiltins`): its store field at a
store type (every clause a `list`, whose element types contain only JavaScript values,
`storeTy_sound`), its prototype field at the built-in prototype type
$`P_{\mathcal B}`$, which reads no parameter row (`builtinsFree`, so it means the
same at the assignment the invariant reads it at, `builtinsFree_meaning`), and
none of its names a key that prototype provides ($`N_{\mathcal B}`$). An
allocation without $`\sigma`$, or in a graph stating no built-ins, meets it at once:

```math
\frac{\overline{f}\ \text{distinct}\qquad\forall i.\;\Gamma\vdash_G a_i:A_i
      \qquad\forall b\in\beta.\;\forall f\in\overline{f}.\;b\vDash f
      \qquad\mathsf{builtins}\vDash\overline{f{:}A}}
     {\Gamma\vdash_G\{\overline{f=a}\}:\mathsf{Ref}(\overline{f{:}A};\beta)}
```

```math
\mathsf{builtins}\vDash\overline{f{:}A}\iff
\sigma\notin\overline{f}\ \lor\ \bigl(\overline{f}\cap N_{\mathcal B}=\varnothing\land
  (\sigma{:}S)\in\overline{f{:}A}\ \text{with}\ S\ \text{a store type}\land(\mathsf{proto}{:}P_{\mathcal B})\in\overline{f{:}A}\bigr)
```

`read` and `write` name the field they act on and require it of the receiver's
contract. A contract constrains only the fields it names, so a receiver may
carry fields the rule never mentions — width subtyping is this openness, not a
separate rule. A read takes the field from the receiver's **named members**,
the invariant fields $`\varphi`$ and readonly views $`\psi`$ of a clause with one
record operand, a record's or a dictionary's, whose named members hold beside
its index views (`namedMembers`):

```math
\mathsf{named}(\mathsf{Ref}(\varphi;\psi;\ldots))=(\varphi;\psi)
\qquad
\mathsf{named}(\mathsf{Dict}(\varphi;\psi;\overline{D};\ldots))=(\varphi;\psi)
```

```math
\frac{\Gamma\vdash_G a:R\quad R\equiv_G c\quad\mathsf{named}(c)=(\varphi;\psi)\quad(f{:}A)\in\varphi}
     {\Gamma\vdash_G a.f:A}
\qquad
\frac{\Gamma\vdash_G a:R\quad R\equiv_G\mathsf{Ref}(\varphi)
      \quad(f{:}A)\in\varphi\quad\Gamma\vdash_G a':A}
     {\Gamma\vdash_G a.f\leftarrow a':\mathsf{Null}}
```

Both rules read $`\varphi`$ off a single reference clause. Eliminating a
conjunction of record contracts to such a view can be justified by subsumption;
no direct multi-contract program rule is assumed, so a field supplied only by a
second operand of an intersection needs such a view before these rules apply.

An index view over a key class $`\theta`$ constrains every **present** field
under a key of $`\theta`$ at its element contract $`A`$ (every string key, the
canonical numeric ones, or every symbol key: [POSITIVE-TYPES](POSITIVE-TYPES.md#records));
it says nothing of any other. A computed index first evaluates the receiver,
then its key, which `ToPropertyKey` converts: a string is its key, a symbol
its identity, a number the key its `ToString` spells. The key's type is the
key clause of a class $`\theta_k`$ within the index's
($`\mathsf{key}(\mathsf{strings})=\mathsf{String}`$,
$`\mathsf{key}(\mathsf{numeric})=\mathsf{Number}`$,
$`\mathsf{key}(\mathsf{symbols})=\mathsf{Symbol}`$; $`\theta_k\sqsubseteq\theta`$),
so a number reads a number index or a string one. Because that key can be
absent, the proved `indexDict` rule includes `undefined` in the result:

```math
\frac{\Gamma\vdash_G a:R\quad R\equiv_G\mathsf{Dict}(\theta{:}A)\quad
      \Gamma\vdash_G k:K\quad K\equiv_G\mathsf{key}(\theta_k)\quad\theta_k\sqsubseteq\theta\quad
      \theta_k\neq\mathsf{strings}\quad U\equiv_G\mathsf{Undefined}}
     {\Gamma\vdash_G a[k]:A\cup U}
```

A read at a key the object may lack finds, in JavaScript, what the prototype
chain holds under it; an ordinary object's chain ends at `Object.prototype`,
whose members (`objectProtoKeys`) the model's objects do not hold. So no rule
reads such a key as possibly absent: `readOptional` and `readDict` take a key
$`\kappa\notin\mathsf{Inh}`$ (`inheritedKey`), and `indexDict` no key of every
string. A required field or view is the object's own and is read under any
name.

The separate `readDict` rule covers a fixed key $`\kappa`$ with the same result
contract, through an index whose class surely admits it ($`\theta\ni_!\kappa`$,
`IndexKeys.surely`: any string key for $`\mathsf{strings}`$, a key a number
spells for $`\mathsf{numeric}`$, checked by that number, a symbol key for
$`\mathsf{symbols}`$); a symbol key is never read through a string index, nor
`"01"` through a number index. The `readOptional` rule reads an optional
field of a record, writable or readonly, at its type or `undefined`: where the
object has the key, its location's contract is that type, or implies it for a
readonly field (`optT`), and where it does not, the read is `undefined`
(`read_optional_rule`). With $`\mathsf{Ref}(\varphi;\psi;\omega)`$ a record's
invariant fields, readonly views and optional fields $`\kappa{:}^{r}A`$ of mode
$`r`$, and $`\kappa`$ a [property key](POSITIVE-TYPES.md#records):

```math
\frac{\Gamma\vdash_G a:R\quad R\equiv_G c\quad\mathsf{named}(c)=(\varphi;\psi)\quad(\kappa{:}A)\in\psi
      \quad\kappa\neq\mathtt{length}\lor\exists b.\;\mathsf{num}(b)\notin A}
     {\Gamma\vdash_G a.\kappa:A}
\qquad
\frac{\Gamma\vdash_G a:R\quad R\equiv_G\mathsf{Ref}(\varphi;\psi;\omega)\quad(\kappa{:}^{r}A)\in\omega
      \quad\kappa\notin\mathsf{Inh}\quad U\equiv_G\mathsf{Undefined}}
     {\Gamma\vdash_G a.\kappa:A\cup U}
```

```math
\frac{\Gamma\vdash_G a:R\quad R\equiv_G\mathsf{Dict}(\varphi;\psi;\overline{D};\omega)\quad (\theta{:}A)\in\overline{D}
      \quad\theta\ni_!\kappa\quad\kappa\notin\mathsf{Inh}\quad U\equiv_G\mathsf{Undefined}}
     {\Gamma\vdash_G a.\kappa:A\cup U}
```

A view of `length` at a type excluding a number is met at the object's own
location: its array alternative, which needs every number there
([records](POSITIVE-TYPES.md#records)), does not hold, so `readView` reads
that location, the number found
among the first few the type's clauses reject (`numWitness`,
`lengthExcluded`). Any other view of `length` may be an array's, whose
`length` is its store's length, so its read tests the object in slot
$`i`$: an array's store is a list, in every graph (the built-ins' invariant, or
`storeListT` without one), whose length is a number, and any other object's
`length` is at its own location. The term is
$`\mathsf{len}_i=\mathsf{if}\ \mathsf{isArray}(x_i)\ \mathsf{then}\ |x_i.\sigma|\ \mathsf{else}\ x_i.\mathtt{length}`$
(`lengthRead`, `lenView`). A member access, in a body or a closure, and a
pattern's read of `length` are this term wherever the type's `length` is a
view an array may meet (`lengthViewed`):

```math
\frac{\Gamma(i)=R\quad R\equiv_G c\quad\mathsf{named}(c)=(\varphi;\psi)\quad(\mathtt{length}{:}A)\in\psi
      \quad\mathsf{Number}\subseteq A}
     {\Gamma\vdash_G\mathsf{len}_i:A}
```

A key one of the record's own-key bounds $`b`$ does not admit is not the
object's own, so its read continues at the prototype, which the record holds
under the reserved key at $`P`$ (`readProto`). For an array, $`b`$ excludes
`ArrayProto`'s keys, so every prototype member is read this way, whatever
further keys the array owns:

```math
\frac{\Gamma\vdash_G a:R\quad R\equiv_G\mathsf{Ref}(\varphi;\psi;\omega;\beta)\quad b\in\beta\quad b\nvDash\kappa\quad
      (\mathsf{proto}{:}P)\in\varphi\,\psi\quad P\equiv_G\mathsf{Ref}(\varphi';\psi';\ldots)\quad
      (\kappa{:}A)\in\varphi'\,(\psi'\setminus\mathtt{length})}
     {\Gamma\vdash_G a.\kappa:A}
```

The delegation is one step (`Step.readProto`), and the prototype's field or
view is read one level down (`read_proto_rule`).

These are `readView`, `readOptional`, `readProto` and `readDict`; the
dictionary reads apply whatever writable index contracts the clause also
carries. The `read` and `write`
rules above take $`(\kappa{:}A)\in\varphi`$ from the invariant fields alone,
whatever the views and optional fields. A dictionary's named field or view is
read at its own contract by `read` or `readView`, since `dictViewT` sits beside
the named members' `recT` and `viewT` (`namedMembers_sem`); only a key it does
not name is read through the index, with `undefined`. An optional named field
($`\omega`$ above) holds beside the index as a named field does, so a key the
dictionary does not name is still read through the index: `process.env` is a
writable index beside the optional `TZ`. A write to a writable optional
field may add its key: it is a [key-adding write](#key-adding-writes), a copy
of a local's own object, refused on any other; a readonly one grants no write
in any case.

A fresh literal meets a readonly dictionary, or a record whose optional
fields it leaves out, with no rule of its own: `alloc` types it at the record
whose own keys are bounded by exactly its names, and that record is below the
target by coverage through the bound
([`CoversKeys`, `CoversOptional`](POSITIVE-TYPES.md#records)). No other key
exists and the prototype key is not among them, so the object has no
prototype, lacks every key it does not write, and each field's contract need
only be within each index view. The literal may be empty, `{}`, and may write
members the dictionary names:

```math
\frac{\vec k\ \text{distinct}\quad\Gamma\vdash_G e_i:A_i\quad
      G\vdash\mathsf{Ref}(\overline{k_i{:}A_i};\{\vec k\})\le D}
     {\Gamma\vdash_G\{\overline{k_i{:}e_i}\}:D}
```

which is `alloc` followed by subsumption; the producer states the bounded
record as the literal's claim wherever its contract has a readonly index or
an optional field. None of these rules grants a write capability to a
readonly dictionary.

A writable index is never met through an own-key bound (but at a contract no
value meets, where no key can be added): code holding the dictionary may add
a key of its class, which a bound listing keys, or one excluding such a key,
says is absent
([writable string index signatures](SOURCE-MODEL.md#writable-string-index-signatures),
[covering](POSITIVE-TYPES.md#records)). So a literal meant for a writable
dictionary is allocated at the dictionary itself, `allocDict`: its fields are
the clause's named fields, none the prototype key or the store key, each whose key an index's
class may admit ($`\theta\ni_?k`$, `IndexKeys.may`) at exactly that index's
type, and the clause states no own-key bound. It may state optional fields
$`\omega`$ the literal leaves out, each, where a writable index's class may
admit its key, at exactly that index's type or beside an index no value meets
($`\varnothing(V)`$), so a key added there keeps it. The object owns no other
key, so every index, a view or writable, holds of it (`dictCellT_of_recT`),
it lacks every optional field (no prototype), and no bound is claimed that a
key added later would falsify. With $`\overline{D}`$ the index views and
$`\overline{C}`$ the writable indexes:

```math
\frac{\begin{array}{c}
      \vec k\ \text{distinct}\quad\mathsf{proto},\sigma\notin\vec k\quad
      \Gamma\vdash_G e_i:A_i\quad
      \forall i.\;\forall(\theta{:}V)\in\overline{D}\,\overline{C}.\;\theta\ni_?k_i\Rightarrow A_i=V\\
      \forall(\kappa{:}^{r}B)\in\omega.\;\kappa\notin\vec k\land
      \forall(\theta{:}V)\in\overline{C}.\;\theta\ni_?\kappa\Rightarrow B=V\lor\varnothing(V)
      \end{array}}
     {\Gamma\vdash_G\{\overline{k_i{:}e_i}\}:\mathsf{Dict}(\overline{k_i{:}A_i};\overline{D};\overline{C};\omega)}
```

Its evidence is `alloc` at a dictionary type. The producer claims the literal
so wherever its contract has a writable index.

```math
\frac{\Gamma\vdash_G t:A\quad\mathrm{check}(G,A,B,p)=\mathsf{true}}
     {\Gamma\vdash_G t:B}
```

One object can carry both a field map and invocation code; the graph clause
$`\mathsf{Callable}(\varphi;L)`$ combines them. Four rules give it the same four
operations, and they are implemented and proved, not proposed:
`callableGraph` allocates it, typing each field's initializer as `alloc` does
and offering its graph code's signatures as `funGraph` does,

```math
\frac{\vec k\ \text{distinct}\quad\forall i.\;\Gamma\vdash_G e_i:A_i
      \quad\mathrm{Kind}_G(k,L,S)\quad\mathrm{Offers}_G(\kappa,\vec C,L,S)
      \quad\forall j.\;\Gamma\vdash_G x_j:C_j}
     {\Gamma\vdash_G \mathsf{make}(\kappa[\vec x],\overline{k_i{=}e_i}):\mathsf{Callable}(\overline{k_i{:}A_i};L,S)}\ (\texttt{callableGraph})
```

one code-table entry per signature; `callCallable`, `readCallable` and
`writeCallable` then invoke, read and write it under the same premises as
`app`, `read` and `write`. Allocation and invocation remain distinct steps:
creation allocates the object, and its code, checked in the table, is not
run.

The clause `top` is semantic top: every closed calculus value inhabits it.
The clause `source` contains every closed JavaScript primitive and object,
including arrays through their identity. Source `unknown` and `void` denote
`source`, as specified by the [source-value boundary](SOURCE-MODEL.md#source-value-boundary).
`undefined` is a particular value, which a body produces by completing;
there is no void value or tag.

A record clause also carries _views_: fields read through a capability. A
view names a location whose stored contract implies the stated family, so a
read through it, by `readView`, observes that family; nothing permits a write
through it, and the backing invariant, which may be stronger, is never
retyped. An invariant field is below a view of the same name whose contract it
implies, and a view is below a weaker view, so a mutable Boolean cell is
viewed as readonly Boolean without ever acquiring a persistent readonly-`true`
guarantee from its current contents; current-content observations stay
separate and subject to invalidation. `readonly` fields are these views.

An array is an object whose store field holds a _store_: the location of each
element in order, or a hole. Identity, aliasing and mutation are the object's;
the store is a value the object replaces when the array grows. A `list` clause
is one or more tuple contracts on a store: required positions, each a
location under its family; optional positions, a hole or such a location; and a
rest family under which any further location must be, without which there is
none. Presence is a separate three-way contract: dense forbids holes,
readable requires a hole's `undefined` to satisfy its position type, and sparse
constrains only present optional/rest entries. Required positions always exist.
Source `T[]` means readable, uniformly in `T`; see the
[array equations](POSITIVE-TYPES.md#arrays). A spread reads at its element type
from either a dense or readable store. A sparse store additionally needs an
explicit `undefined` alternative (`SpreadsInto`); `listT_spreads` proves all three cases. An index in bounds and an
arbitrary one differ, as do a mutable and a readonly array. A readonly store carries
element read capabilities: each location invariant implies the element type.
Writable stores require equality and are invariant; `setElem` requires a
writable store. The outer store field is also a view for a readonly array. `arrLit` allocates a store under the claimed tuple; `elem` reads a
required position named by a literal index, `elemOpt` an optional or rest
position, adding `undefined`, and `elemAny` any numeric index into a
homogeneous array, adding `undefined` (a native result with a required
position, such as the designed non-empty `split`, `[string, ...string[]]`,
is read by `elem` at index 0: [a non-empty `split`](SOURCE-CONTRACTS.md#native-footprints));
`setElem` writes a named position into
its location, or a fresh one the new store records, keeping the contract for
every alias; `len` reads the length. The source read `a.length` of an
array, in a statement and in a closed expression (an arrow's expression
body, a condition's operands) alike, is the length of its store:

```math
\frac{\Gamma\vdash_G a:A\quad \mathit{store}_G(A)=S\quad
      \Gamma\vdash_G a.\mathtt{[]}:S\quad S\equiv_G\mathsf{list}(\tau)\quad N\equiv_G\mathsf{num}}
     {\Gamma\vdash_G⟦a.\mathit{length}⟧=\mathsf{lenOf}\;(a.\mathtt{[]}):N}\ \textsf{len}
```

A write is typed only at an index no
greater than the required length, so it lands in bounds or appends and never
leaves a hole:

```math
\frac{\Gamma\vdash_G a:L\quad L\equiv_G\mathsf{list}(\tau)\quad
      \Gamma\vdash_G i:\mathsf{numLit}(k)\quad \tau(k)=A\quad
      k\le|\vec R_\tau|\quad \tau\ \text{writable}\quad \Gamma\vdash_G v:A}
     {\Gamma\vdash_G a[i]=v:L}\ \textsf{setElem}
```

Writes at a greater index, or at one no contract names, and reads by a
non-literal index into a tuple, have no rule; a program appends with `push`.
A read `xs[k]` of an array or a tuple at a key TypeScript types as `number`,
no literal, is the host's read of the property the number names, a call of
the intrinsic $`\%\mathsf{ElementAt}\%`$ (`intrinsics.mts`), which the parser
writes where TypeScript's types of the object and the key are these:

```math
\mathit{xs}[k]\;\equiv\;\%\mathsf{ElementAt}\%(\mathit{xs},\ k)
\qquad
\%\mathsf{ElementAt}\%:\forall T.\ (\mathtt{readonly}\ T[\,],\ \mathtt{number})\Rightarrow_{\emptyset} T\mid\mathtt{undefined}
```

The element at an index below the length, an own property at another
numeric key, which `Array<T>`'s `[n: number]: T` says holds a `T`, else
`undefined`: `Array.prototype` and `Object.prototype` own no numeric key
([trust surface](DESIGN.md#trust-surface)). No getter runs, so the read
writes nothing and states heap preservation
([effects](SOURCE-MODEL.md#inferred-call-effects-elaboration-and-certification)). `elemAny` would read the store
alone, which answers `undefined` where the array owns such a key.

#### A literal with spreads

A store literal evaluates its parts left to right, and a spread of a ready
store is replaced by the store's elements once every earlier part is a value,
`undefined` at a hole (`Step.arrSpread`); the store then takes one fresh
location per value (`Step.arrAlloc`). Its length is known only at run time,
so its contract is one element type $`E`$ at every position: each plain part
is in $`E`$, each spread a store whose elements are:

```math
\frac{\forall p\in\vec p.\;\Gamma\vdash_G p:E\ \lor\ (p={\ldots}s\land\Gamma\vdash_G s:S\land\mathrm{Spreads}_G(S,E))
      \qquad L\equiv_G\mathsf{list}([\,],[\,],E)_{\pi,\rho}}
     {\Gamma\vdash_G \mathsf{arrLit}(\vec p):L}\ \textsf{arrParts}
```

$`\pi`$ is any presence mode and $`\rho`$ either readonly flag: every
position holds a location of its own, so the fresh store meets each
(`fresh_store_safe`). No existing location is retyped. The parts run in the
same list context as a call's actuals, which `RestCalls.parts_safe` states
once for both (`store_parts_safe`, `spread_parts_safe`). A source literal
`[a, ...xs, b]` spreads the store of the array object `xs`, `xs.[]`; one whose
spread is followed by an element that runs code copies the spread where it is
written, `[...xs]`, the one-part instance of the rule, so the later element
cannot change what the literal holds. A literal without a spread is `arrLit`.

A string owns its `length` and its code units ([semantics](SEMANTICS.md#operational-language),
"Strings"). `lenStr` reads the length of an operand whose every clause is a
string, and `elemStr` a code unit at any numeric index, a string or, past the
end or at a key that is not an index, `undefined`, whatever the literal:

```math
\frac{\Gamma\vdash_G a:S\quad\mathrm{Answers}_G(S,\mathsf{isStr},\mathsf{true})\quad N\equiv_G\mathsf{num}}
     {\Gamma\vdash_G\mathsf{lenOf}\;a:N}\ \textsf{lenStr}
\qquad
\frac{\Gamma\vdash_G a:S\quad\mathrm{Answers}_G(S,\mathsf{isStr},\mathsf{true})\quad
      \Gamma\vdash_G i:I\quad\mathrm{Answers}_G(I,\mathsf{isNum},\mathsf{true})}
     {\Gamma\vdash_G\mathsf{elemAt}\;a\;i:\mathsf{str}\cup\mathsf{undefined}}\ \textsf{elemStr}
```

Any other member of a primitive is read through its wrapper's prototype. The
source read `x.k`, with `x` saved in a slot, lowers to a test of each
primitive shape its type holds, selecting that shape's read, and the object
read last (`dispatchTerm`):

```math
\mathsf{if}\ \mathsf{isStr}(x)\ \mathsf{then}\ r_{\mathsf{str}}\ \mathsf{else}\
\mathsf{if}\ \mathsf{isNum}(x)\ \mathsf{then}\ r_{\mathsf{num}}\ \mathsf{else}\ \cdots\ \mathsf{readAt}\;k\;x,
\qquad
r_s=\mathsf{readAt}\;k\;(\mathsf{makeAt}\;\mathsf{absent}\;[\mathsf{proto}]\;[P_s])
```

with $`P_s`$ the slot holding the built-in prototype for shape $`s`$, and a
string's `length` read by `lenStr`. Every arm is JavaScript's read for values
of its shape, and a value of a shape no arm names reaches the object read,
where a primitive is stuck: the lowering is faithful for every value,
whatever the claim. It is typed by existing rules only: `unionVar` splits
$`x`$'s labels, `ifTag` selects the arm each label's shape answers, `alloc`
types the wrapper at a record holding `[[proto]]` at the prototype's contract
and owning no other key, and `readProto` reads the member there. A method call
`s.m(a)` reads the member so and invokes it with `s` as its receiver, which
the member's signature names (`this: string`).

An array's `length` is its store's. A read of `length` where
$`x`$'s type $`B`$ holds arrays beside other values branches on
$`\mathsf{isArray}`$, each edge binding $`x`$ refined:

```math
\mathsf{isArray}(x)\ ?\ \mathsf{lenOf}\;(\mathsf{readAt}\;\sigma\;x)\ :\ r(x),
\qquad
x:R\ \text{on the true edge},\quad x:\mathsf{tagSlice}_G(B,\mathsf{isArray},\mathsf{false})\ \text{on the false edge}
```

with $`R`$ the built-in sparse `readonly unknown[]` and $`r`$ the read above at
the false edge's type. The true edge is `arraySlice`'s: an array label and a
record or dictionary owning $`\sigma`$ are built-in arrays
([array invariant](SEMANTICS.md#the-array-invariant)), whose store `len`
reads; on the false edge `tagSlice` drops the array labels. The test reads
no heap, and each arm is JavaScript's read for the values reaching it.

**A member of `null` or `undefined`.** JavaScript's read of a member of
`null` or `undefined`, `x.k`, `x[k]` and a method call's, throws a
`TypeError` before reading anything. Where the operand's type admits `null`
or `undefined` beside other values (`nullishSplit`), the operand, held in a
slot, is tested first (`nullishGuard`):

```math
\mathsf{tagBind}\ \mathsf{isNullish}(x):\quad
\mathsf{true}\mapsto \mathsf{let}\ e=\mathsf{makeAt}\;\mathsf{absent}\;[\,]\;[\,]\ \mathsf{in}\ \mathsf{throw}\;e,
\qquad \mathsf{false}\mapsto \text{the access, } x : \mathsf{tagSlice}_G(B,\mathsf{isNullish},\mathsf{false})
```

with $`e`$ a fresh object owning no key, the error object `binopThrows`
throws for the `TypeError` instance ([throws](SOURCE-MODEL.md#throws)). It is
typed by existing rules only: `tagBind` refines the slot on each edge,
`throw` has every type, and the access reads the non-nullish slice. A run
reaching `null` or `undefined` throws, an outcome the safety statement
admits; a handler binds the thrown value at `unknown`. The guard sits where
JavaScript throws:

- `x.k` and `x[key()]`: after the operand, and the key where there is one;
- `x.m(arg())`: before the member is read, so the actuals are not evaluated;
  a method dispatched on a union of shapes takes only actuals that run no
  code, as before;
- `x[key()] += rhs()`: after the key, where the old value is read, so the
  right side is not evaluated; the write tests the operand again, which then
  never throws, to be typed at the refined operand. A compound assignment to
  an element of an array's store, `e[1] += s`, writes the store as an element
  write does.

An optional chain keeps its own test, `x?.[key()]` skipping the key where
`x` is nullish, and a member of its result, `(x?.a).b`, is an ordinary
access. A primitive other than `null` and `undefined` keeps its wrapper and
prototype arms. A plain write to a member of a nullish operand is refused
(`nullish-member-write-refused`). The producer reads a member at the
operand's other values (`nullish-member-reads`, `nullish-member-order`,
`invalid-nullish-member-reads`; a receiver forged without `undefined` is
refused in `pipeline/test.mts`).

Every binary operator has one rule, `arith`, for arithmetic on numbers and on
bigints, for string concatenation, relational comparison and equality alike ([its
meaning](SEMANTICS.md#operational-language), `binop`). A clause pair
classifies the operation, $`\mathrm{op}(op,c,d)`$ (`opResult`), where
$`\mathsf{N}`$ is `num` or `numLit`, $`\mathsf{Z}`$ is `bigint` or `bigintLit`,
$`\mathsf{S}`$ is `str` or `strLit`, and $`\mathsf{P}`$, the printable clauses
(`printableClause`), is $`\mathsf N\cup\mathsf Z\cup\mathsf S`$ with `bool`,
`boolLit`, `nul` and `undef`: every primitive but a symbol. $`\mathsf{Nc}`$
(`numericClause`), the clauses `ToNumeric` converts without code, is
$`\mathsf N\cup\mathsf Z`$ with `bool`, `boolLit`, `nul` and `undef`. $`\mathsf{Pr}`$
(`primitiveClause`) is $`\mathsf P`$ with `symbol`, $`\mathsf{O}`$
(`objectClause`) the object clauses, `refs`, `dict`, `arrs`, `callable` and
`ctors`, whose members are objects, compared by identity, and $`\mathsf{Nl}`$
(`nullishClause`) is `nul` and `undef`; $`\equiv`$ is strict equality (`===`)
and $`\approx`$ loose equality (`==`):

```math
\mathrm{op}(op,c,d)=\begin{cases}
\mathsf{bool} & op={\equiv},\ c\in\mathsf{Pr}\cup\mathsf O\ \text{or}\ d\in\mathsf{Pr}\cup\mathsf O\\
\mathsf{bool} & op={\approx},\ c,d\in\mathsf{Pr}\ \text{or}\ c\in\mathsf{Nl}\ \text{or}\ d\in\mathsf{Nl}\ \text{or}\ c,d\in\mathsf O\\
\mathsf{bool} & op\ \text{relational},\ c,d\in\mathsf{Nc}\ \text{or}\ c,d\in\mathsf S\\
\mathsf{str} & op={+},\ c\in\mathsf S,\ d\in\mathsf P\ \text{or}\ c\in\mathsf P,\ d\in\mathsf S\\
\mathsf{num} & op\ \text{arithmetic},\ c,d\in\mathsf N\\
\mathsf{bigint} & op\ \text{arithmetic},\ c,d\in\mathsf Z\\
\text{none} & \text{otherwise}
\end{cases}
```

A bigint divisor, of `/` or `%`, that may be zero, or an exponent that may be negative, is
admitted: the operation then throws a `RangeError`, an outcome safety admits
([Source model](SOURCE-MODEL.md#throws)). $`\mathrm{Operands}_G(op,A,B,r)`$
requires both types of clause rows and every clause pair of $`A`$ and $`B`$ to
classify as $`r`$, and the result type must hold every value of the kind
($`\mathrm{covers}`$): the number, bigint or string family exactly, or both
Boolean literals:

One operand also decides an equality alone: $`\mathrm{Decided}_G(op,X)`$
(`EqualityDecided`) holds when $`X`$ is of clause rows each of which, for
$`\equiv`$, is in $`\mathsf{Pr}\cup\mathsf O`$, or, for $`\approx`$, in
$`\mathsf{Nl}`$. Its members compared with any value, a type parameter's
included, in either order, give a Boolean (`decidingClause_sound`). The
premise $`\mathrm{OpTypes}_G(op,A,B,N)`$ (`OperatorTypes`) is either:

```math
\frac{\mathrm{Operands}_G(op,A,B,r)\quad\mathrm{covers}_G(N,r)}
     {\mathrm{OpTypes}_G(op,A,B,N)}
\qquad
\frac{\mathrm{Decided}_G(op,A)\ \text{or}\ \mathrm{Decided}_G(op,B)\quad\mathrm{covers}_G(N,\mathsf{bool})}
     {\mathrm{OpTypes}_G(op,A,B,N)}
```

```math
\frac{\Gamma\vdash_G a:A\quad\Gamma\vdash_G b:B\quad
      \mathrm{OpTypes}_G(op,A,B,N)}
     {\Gamma\vdash_G a\mathbin{op}b:N}\ \textsf{arith}
```

The result is never a singleton, since its value is not typed. `opResult_sound`
proves the classification: on members of the two clauses $`\mathsf{binop}`$
answers, with a value of the kind, or $`\mathsf{binopThrows}`$ holds, and the
term steps to a throw (`arith_throw_safe`). So a number never meets a bigint in
arithmetic (a `TypeError`), a string is relationally compared only with a string and
concatenated only with a primitive whose `ToString` runs no code, a Boolean,
`null` or `undefined` is relationally compared after `ToNumeric`, which runs no
code (`undefined` is NaN, so the comparison is false), and a Boolean or object
operand of arithmetic, an object operand of relational comparison, and an
object or symbol concatenated, which JavaScript would convert through code or
by throwing, have no rule, though TypeScript admits concatenating an object
and comparing objects. An operand whose clauses classify differently, a `string | number`
added to a number, has none either: its result is a string or a number by the
value. The certificate premise
(`ClauseOperatorTypes`) reads $`r`$ off the first clause pair and checks the rest.
Strict equality answers for any pair with a primitive or an object
([its meaning](SEMANTICS.md#operational-language)); the source lowering
refuses two operands that may both be of neither kind (`unknown`, a store).

For loose equality, `opResult` gives `bool` when every operand-clause pair
meets one of three conditions: both are primitive; one is `null` or
`undefined`; or both are object clauses. Mutable and readonly arrays are
object records with required store locations. A union must satisfy the condition for every pair, so
`number[] | null` can compare with `number[] | undefined`, while
`number[] | number` compared with `number` needs an object-conversion rule.
The proof `opResult_sound` establishes that each admitted pair computes a
Boolean without invoking client code. The coercions and numeric corner cases
are specified in [the operational semantics](SEMANTICS.md#operational-language).

A successful coercive comparison establishes no cross-kind type refinement:
`x == n` can hold when `x` is the string `"1"` and `n` is the number `1`.
Literal nullish comparisons retain their nullish branch test; named nullish
operands use the Boolean operator rule. A `typeof` result compared loosely
with a supported string literal uses the same shape test as strict equality:
both operands are strings. Neither operand's inferred type is
trusted without its expression obligation.

The unary numeric operators are derived: the operand's claimed type fixes its
family, all numbers or all bigints, and the operator is the binary one with a
constant right operand of that family, $`-a\equiv a*(-1)`$, $`+a\equiv a*1`$ and
$`\sim a\equiv a\mathbin{\hat{}}(-1)`$, each exact on both families
([semantics](SEMANTICS.md#operational-language)). $`+a`$ on a bigint throws a
`TypeError`, and an operand of both families has no one constant: both are
refused. The constant is its own node, typed by its literal rule; the operand's
obligation establishes the family the lowering read. A compound assignment
`x op= e` and an increment use the same rule at the target contract's type,
an increment adding that family's one; `x += e` concatenates where the
contract or `e` is a string. An increment converts its operand to a number
where `+ 1` would concatenate, so it is this addition only on a target of one
numeric family, and is refused on any other. Inside a closed expression (an
operand of `&&`, `||` or `??`, an arrow's expression body) the target is a
local cell, and the steps are the same: its read at the contract, the right
side, the operation, the write back at the contract, and the old or the new
value.

A logical assignment evaluates its target's parts once and reads the target
at its storage contract $`C`$; the right side runs, and is written back at $`C`$,
only on the arm the operator writes on, and the other arm's value is the one
read. With $`r`$ the target's reference, $`\mathsf{read}(r)`$ its read and
$`\mathsf{write}(r,e)`$ the write of $`e`$'s value, which is the expression's
value there:

```math
\begin{aligned}
r\ \mathtt{??=}\ e&\equiv\mathsf{let}\ v=\mathsf{read}(r)\ \mathsf{in}\ \mathsf{if}\ (v\equiv\mathsf{null}\lor v\equiv\mathsf{undefined})\ \mathsf{then}\ \mathsf{write}(r,e)\ \mathsf{else}\ v\\
r\ \mathtt{||=}\ e&\equiv\mathsf{let}\ v=\mathsf{read}(r)\ \mathsf{in}\ \mathsf{if}\ v\ \mathsf{then}\ v\ \mathsf{else}\ \mathsf{write}(r,e)\\
r\ \mathtt{\&\&=}\ e&\equiv\mathsf{let}\ v=\mathsf{read}(r)\ \mathsf{in}\ \mathsf{if}\ v\ \mathsf{then}\ \mathsf{write}(r,e)\ \mathsf{else}\ v
\end{aligned}
```

so $`e`$ is checked at $`C`$, as any write of $`r`$ is. `||=` and `&&=` are
lowered on a Boolean target only ([model limits](SOURCE-FRAGMENT.md#model-limits)).
The encoding is in [Fragment](FRAGMENT-FORMAT.md#receivers).

A template literal is the concatenation of its parts, in order, starting from
its first string part: `` `h$`{a}m`${b}t` `` is $`(((h+a)+m)+b)+t`$, one `arith`
node per `+`, so a substitution is converted by $`\mathsf{str}`$ exactly where
the template converts it, after the ones before it, and one of an object or a
symbol has no rule. A template without substitutions is its string.

The comma operator $`a,b`$ evaluates $`a`$, discards its value and yields $`b`$'s;
`void e` is $`e,\mathtt{undefined}`$. The lowering binds $`a`$'s value in an
unread slot, and the claim at the comma is proved from $`b`$'s value, as a
cast's is from its operand's: no rule of its own.

A tag test
whose answer the operand's type does not settle is typed by `test` as a Boolean
holding both literals, so `ifBool` can branch on it; a settled answer still
uses `ifTag`.

For branching, $`\mathrm{Answers}_G(A,k,q)`$ checks that every expanded
clause of $`A`$ gives the same known Boolean answer $`q`$ to test $`k`$, and that
$`A`$ is of clause rows, since a parameter row's members could be anything:

```math
\mathrm{Answers}_G(A,k,q)\iff
\forall i\in A.\;\mathsf{plain}_G(i)\ \land\
\forall\gamma\in\mathrm{expand}_G(A).\;\mathrm{tag}(k,\gamma)=q.
```

A shape test's answer on a clause is read off its shape: $`\mathsf{isBigint}`$
and $`\mathsf{isSymbol}`$ answer true exactly on the $`\mathsf{bigint}`$ and
$`\mathsf{symbol}`$ clauses, and $`\mathsf{isFun}`$ answers true on an arrow, a
callable and a construct-signature clause alike, since `typeof` reports a
class as a function. $`\mathsf{truthy}`$ answers false on the $`\mathsf{null}`$
and $`\mathsf{undefined}`$ clauses and true on every object, function, class,
symbol and store clause; on a Boolean, number, string or bigint singleton it
answers the singleton's `ToBoolean`, and on the broad $`\mathsf{bool}`$,
$`\mathsf{num}`$, $`\mathsf{str}`$ and $`\mathsf{bigint}`$ clauses it has no fixed
answer. $`\mathsf{typeofObject}`$, `typeof` answering `"object"`, answers true
on the $`\mathsf{null}`$ clause and on a plain-object clause (a record, a
dictionary, an array) and false on every other clause but $`\mathsf{top}`$: an
arrow, callable or construct-signature clause is a function to `typeof`. The
key test $`\mathsf{hasKey}(\kappa)`$, `in`, answers on a record or dictionary
clause by its keys (`keyAnswer`): true where the clause says its object owns
$`\kappa`$; false where a key bound excludes $`\kappa`$, as a fresh literal's does;
and nothing on an open record, which may own any other key. It has no answer
on the other object clauses (an arrow, a callable, a class value) and answers
false on a primitive one, which owns no key. $`\mathsf{isArray}`$,
`Array.isArray`, is the same answer for the store key $`\sigma`$ on a record or
dictionary clause (`arrayAnswer`), true where the clause says its object owns
$`\sigma`$, as every array type's does, and false on every other clause but
$`\mathsf{top}`$:

```math
\mathrm{keys}(\kappa,\gamma)=
\begin{cases}
\mathsf{true} & \kappa\in\mathrm{present}(\gamma)\\
\mathsf{false} & \kappa\notin\mathrm{present}(\gamma),\ \exists K\in\mathrm{bounds}(\gamma).\ \neg K\ \text{admits}\ \kappa\\
\text{none} & \text{otherwise}
\end{cases}
\qquad
\mathrm{tag}(\mathsf{isArray},\gamma)=
\begin{cases}
\mathrm{keys}(\sigma,\gamma) & \gamma\ \text{a record or dictionary clause}\\
\mathsf{false} & \text{otherwise},\ \gamma\neq\mathsf{top}
\end{cases}
```

```math
\mathrm{tag}(\mathsf{hasKey}(\kappa),\gamma)=
\begin{cases}
\mathrm{keys}(\kappa,\gamma) & \gamma\ \text{a record or dictionary clause}\\
\text{none} & \gamma\ \text{an arrow, callable or construct-signature clause}\\
\mathsf{false} & \text{otherwise},\ \gamma\neq\mathsf{top}
\end{cases}
```

`keyAnswer_sound` gives each answer from the clause's meaning: a present key
is owned (`semWithArgs_owns`), and a bound's excluded key is not
(`ownKeysT_lookup`).

Other shape
tests have an answer determined by the clause's shape; numeric singleton
equality also examines its bits. A broad number clause has no fixed answer
to that equality, so it establishes neither outcome:

```math
\frac{\Gamma(x)=A\quad\mathrm{Answers}_G(A,k,q)
      \quad(q=\mathsf{true}\Rightarrow\Gamma\vdash_G t_1:B)
      \quad(q=\mathsf{false}\Rightarrow\Gamma\vdash_G t_2:B)}
     {\Gamma\vdash_G\mathsf{if}\ k(x)\ \mathsf{then}\ t_1\ \mathsf{else}\ t_2:B}.
```

The shape-test rule checks each overload body under its own argument type. It
handles shape dispatch between overloads.

Ordinary Boolean conditionals use a separate rule. Define
$`\mathrm{Boolean}_G(C)`$ as
$`\mathrm{Answers}_G(C,\mathsf{isBool},\mathsf{true})`$; this accepts Boolean
singleton unions as well as the Boolean clause.

```math
\frac{\Gamma\vdash_G c:C\quad\mathrm{Boolean}_G(C)
      \quad\Gamma\vdash_G t_1:A\quad\Gamma\vdash_G t_2:A}
     {\Gamma\vdash_G\mathsf{if}\ c\ \mathsf{then}\ t_1\ \mathsf{else}\ t_2:A}.
```

A condition with a proved singleton type needs only its reachable arm. For
$`q\in\{\mathsf{true},\mathsf{false}\}`$, write $`B_q`$ for a type represented by
$`\mathsf{boolLit}(q)`$, and let $`t_q`$ select the arm that $`q`$ reaches:

```math
\frac{\Gamma\vdash_G c:B_q\qquad\Gamma\vdash_G t_q:A}
     {\Gamma\vdash_G\mathsf{if}\ c\ \mathsf{then}\ t_1\ \mathsf{else}\ t_2:A}.
```

`ifKnown q` carries two proofs: one for the condition at its singleton type,
and one for the selected arm. This is a typing rule, not constant folding:
the condition still runs, and all of its heap effects precede the arm. The Lean
soundness proof uses evaluation-context composition and consumes the ordinary
conditional step. A checked execution example includes a condition that writes
through a reference and an unreachable stuck arm.

The general Boolean rule requires both branches at the supplied result type
$`A`$. No least-upper-bound is computed. Both use the same context: that rule
does not justify narrowed branch environments. Another rule handles a directly
tested immutable variable. Write $`\Gamma[x:=T]`$ for replacing $`x`$'s type:

```math
\frac{\Gamma(x)=C\quad\mathrm{Boolean}_G(C)
      \quad\Gamma[x:=\mathsf{True}]\vdash_G t_1:A
      \quad\Gamma[x:=\mathsf{False}]\vdash_G t_2:A}
     {\Gamma\vdash_G\mathsf{if}\ x\ \mathsf{then}\ t_1\ \mathsf{else}\ t_2:A}.
```

Here $`\mathsf{True}`$ and $`\mathsf{False}`$ must expand to the corresponding singleton
clauses. `HasTyUsing.ifBoolVar` proves this rule sound: the selected branch's actual
value justifies the changed binding, and all others retain their meanings.
It neither refines mutable heap contents nor supplies general union splitting.
Graph edges use the common [observation-based refinement contract](#refinement-under-an-observed-outcome)
below, currently connected to Boolean dispatch.

### Eliminating a variable's union type

A finite union can be split in one immutable binding. Write $`[a]`$ for
one graph label viewed as a type. Every member must establish the same term and
result; all other bindings retain their original types:

```math
\frac{\Gamma(x)=C\qquad
      \forall a\in C.\;\Gamma[x:=[a]]\vdash_G t:A}
     {\Gamma\vdash_G t:A}.
```

`unionVar i` carries one premise for each label in $`C`$, in list order. The checker
rejects missing alternatives, changed terms/results, and changes to unrelated
bindings. An empty union needs no premises because that input environment has
no inhabitants. Soundness chooses the member containing the actual immutable
value and applies that premise's existing world-indexed soundness theorem.
There is no runtime case split added by this rule and no join computation.

Combined with `ifTag`, this checks a term such as
`if isNull(x) then true else x` under `x : Null | Bool`, at result `Bool`.
Proof search uses the rule for tag tests over explicit unions of labels. It does
not repeatedly split a singleton label whose graph definition itself contains
mixed shapes; that representation needs additional decomposition rules.

A method call on a union receiver whose alternatives read different members
is split on its receiver the same way. With the object $`x`$ and the actuals
$`\vec y`$ already in slots, the source call `x.k(y…)` lowers to one term that
reads the member and invokes it, dispatched as a member read is
(`dispatchCallTerm`, over `dispatchTerm`'s tests):

```math
\mathsf{if}\ \mathsf{isStr}(x)\ \mathsf{then}\ \mathsf{invoke}\;r_{\mathsf{str}}\;x\;\vec y\ \mathsf{else}\ \cdots\
\mathsf{invoke}\;o\;x\;\vec y,
\qquad
o=\begin{cases}
\mathsf{let}\ m=\mathsf{readAt}\;k\;x\ \mathsf{in}\ \mathsf{bound}(m,x) & \text{every object alternative holds $k$ as a member}\\
\mathsf{readAt}\;k\;x & \text{otherwise}
\end{cases}
```

with $`r_s`$ a primitive shape's read through its wrapper. `unionVar` splits
$`x`$, `ifTag` selects the arm, and each arm is an ordinary call (`app`, with
`bindMember` for an object's member): nothing but the existing rules. The
member is read after the actuals, where JavaScript reads it before them; the
lowering is used only where no actual runs code (each a name or a literal),
so no step can tell the orders apart.

### Binding and soundness

[Bindings.lean](../lean/Verification/Semantics/Bindings.lean) defines de Bruijn scope and simultaneous closing substitution, and proves
its application law:

```math
\mathsf{invoke}(\mathsf{obj}(\ell,\mathsf{closure}(1,\mathrm{close}^{2}_{\rho}(b))),r,[a])
\longrightarrow \mathrm{close}_{r::a::\rho}(b).
```

The formal statement is `instantiate_beta`; environment entries must be closed.
This is the invocation step for an already allocated function object;
creation is a separate step. The same substitution law applies to `letE`.
Arrow membership requires an object with closed callable code, so every value in a
positive graph type is both a value and closed (`meaning_value`). Semantic
environments retain these properties when extended, when their world grows,
and when their observation budget decreases.

`HasTyUsing.sound` proves, for every proved image checker:

```math
\Gamma\vdash_G t:A\ \land\ \mathrm{EnvOk}_G(\Gamma,\rho,n,W)\ \land\
\mathrm{WorldAdm}(W)\ \land\ \mathrm{HeapOk}(n,W,h)
\ \Longrightarrow\
\mathrm{Safe}(⟦A⟧_G,n,W,h,\mathrm{close}_{\rho}(t)).
```

Safety is partial
correctness and absence of stuck execution, not termination.

The general evaluation-context lemma `bind` composes computations across heap
changes and future worlds. The typing theorem is an induction on derivations;
none of its constructor rules has a semantic safety premise.

### Integration example

The rules type a program equivalent to:

```text
let r = alloc true;
let f = x => if isNull x then read r else null;
let alias = r;
write alias false;
f(true);
f(null)
```

One closure has both `Null → Bool` and `Bool → Null`. Before the final call,
subsumption widens that overload to `(Null | Bool) → (Null | Bool)` by
splitting the union domain.

### Executable program evidence

[ProgramCertificates.lean](../lean/Verification/Programs/ProgramCertificates.lean) checks finite evidence trees. Each node contains a
sequent (context, term, result type), a rule name, and its premise trees.
Subsumption nodes carry the existing positive subtype certificate. Lambda nodes
must supply precisely one body derivation per overload entry, in order. The two
branch rules supply evidence for the selected branch; the shape-answer check
must justify that selection.

`checkTreeUsing G images` checks every local rule and premise tree, at any
proved image checker. `checkTreeUsing_sound` proves that an accepted tree's
root sequent is derivable, `HasTyUsing G images`, so `HasTyUsing.sound` gives
the safety of its term. Checker recursion follows the finite evidence tree;
there is no user-supplied fuel and no semantic level in the evidence. The
image checker is chosen by Lean code; evidence cannot name one.

The explicit sequents keep this initial in-memory format easy to inspect, at the
cost of repeating terms and contexts. This is not a commitment to a serialized
format. The [in-memory producer](SOURCE-ELABORATION.md#producing-evidence-from-supplied-claims)
uses this interface; a decoder or compact representation can be developed
against it.

## Control flow

A finite graph over those expressions: one term per node, an edge discipline
that transfers bindings, and a certificate that checks every node and edge.

Every checker in this section takes a proved image checker, as `checkTreeUsing`
does: edges (`checkEdgeUsing`, `checkMappedUsing`), branch edges
(`checkObservedUsing`), node steps (`checkStepUsing`), graphs and entries
(`checkGraphUsing`, `checkEntryUsing`), graph-code tables (`checkCodesUsing`)
and acceptance (`CertificateProducer.acceptUsing`), as do the evidence
producers. Coverage and point assertions are semantic, family inclusion
and `EnvOk`, so each soundness theorem, parametricity (`accept_reassign`,
`accepted_at`) included, holds for every proved image checker.

### Supplied point claims and incoming edges

[PointClaims.lean](../lean/Verification/Programs/PointClaims.lean) checks supplied type environments. Write $`\Gamma \preceq_G \Delta`$
when every slot in the target claim $`\Delta`$ has a source slot at the same
position in the incoming environment $`\Gamma`$, with a proved subtype relation:

```math
\Gamma \preceq_G \Delta
\quad\Longleftrightarrow\quad
|\Delta| \leq |\Gamma|
\;\land\;
\forall i < |\Delta|.\; \Gamma_i \leq_G \Delta_i.
```

`checkEdgeUsing` takes one subtype certificate per target slot. Lean proves that
acceptance implies coverage, as family inclusion per slot (`Covers`,
`checkEdge_sound`). Coverage also transfers semantic
environments: any concrete environment meeting $`\Gamma`$ meets $`\Delta`$, with
closed values preserved.

`checkEdgeUsing` is the position-preserving specialization: it can widen types and
forget a suffix. `checkMappedUsing` additionally checks an explicit list of source
indices, with exactly one index and subtype certificate per target slot.
Repeated indices retain aliases, and an interior binding can be dropped.
Every selected source index must exist; no missing binding acquires a type from
the total environment's default value.

For a supplied map $`m`$, the rule and its semantic action are:

```math
\frac{
  |m|=|\Delta|
  \qquad
  \forall i<|\Delta|.\;m_i<|\Gamma|\;\land\;\Gamma_{m_i}\leq_G\Delta_i
}{
  \Gamma\preceq_G^{m}\Delta
}
\qquad
\mathrm{mapEnv}(m,\rho)(i)=\rho(m_i).
```

`checkMapped_sound` proves mapped coverage, and `MappedCovers.env` proves that
this simultaneous selection preserves the target semantic environment in the
same world. It does not copy or change heap contents. The absent map means
identity selection, retaining the earlier edge interface.

These are local obligations on the edges given; they do not establish that
the edges enumerate a graph's actual predecessors. The graph checker below
discharges that enumeration obligation.

### Throwing

`throw a` has every type: it never produces a value, and a throw is an
outcome safety admits ([Source model](SOURCE-MODEL.md#throws)). Its operand is typed at a
type of its own contained in the JavaScript-value universe $`J`$, since it runs first:

```math
\frac{\Gamma\vdash_G a:A\qquad A\subseteq J}{\Gamma\vdash_G\mathsf{throw}\ a:B}\ \textsf{throw}
```

The soundness case composes `a`'s safety with the throw's context rule
(`bind` over `Tm.throw`) and closes with `thrown_safe`: the value `a` produces
is a closed JavaScript value (`SourceValues.sound`, `meaning_value`). Evidence
names the rule `throw` with the operand's derivation; the checker also requires
all its clauses to contain only source values. The producer searches for a
type satisfying that requirement.

### Allocation from parts

[ObjectMerge.lean](../lean/Verification/Programs/ObjectMerge.lean) states and proves what a merge's result holds, clause by clause.

$`\mathsf{merge}_\delta(a,b)`$ allocates the fields $`a`$'s object owns and, over
them, the own enumerable data properties $`b`$ has, less $`\delta`$
([SEMANTICS](SEMANTICS.md#operational-language)). Its type is a record every
pair of the operands' clauses gives ([Source model](SOURCE-MODEL.md#object-literals)):

```math
\frac{\Gamma\vdash_G a:A\quad\Gamma\vdash_G b:B\quad
      \mathrm{MergeOk}_G(\delta,A,B,R)}
     {\Gamma\vdash_G\mathsf{merge}_\delta(a,b):R}\ \textsf{merge}
```

$`\mathrm{MergeOk}_G(\delta,A,B,R)`$ holds where $`A`$ and $`B`$ are of clause
rows and, for each clause $`c_a`$ of $`A`$ and $`c_b`$ of $`B`$, some clause
$`\mathsf{Ref}(\varphi;\omega;\beta)`$ of $`R`$ is given by them
(`ObjectMerge.MergeClause`): $`c_a`$ a record or dictionary, $`c_b`$ one too, a
function clause (a function, or a callable object, whose own enumerable
properties are the fields its bag states and whatever else was assigned to
it, so it states no bound; `codeOf`), a class clause (a class value, whose
own enumerable properties are its static fields, of which its bag states its
own and no bound; `codeOf`), a string clause (a string, whose own
enumerable properties are its code units, strings, under index keys, so it
gives no other key; `Src.str`), or a
clause of values owning no enumerable property (`null`, `undefined`,
Booleans, numbers, bigints, symbols); each field $`(k{:}T)\in\varphi`$ surely
given within $`T`$ by $`c_b`$, or by $`c_a`$ where whatever $`c_b`$ gives under $`k`$ is
within $`T`$; each optional field within its type on both sides, and then $`c_a`$
holding no prototype; each bound of $`\beta`$ admitting every key either side
may give (`FieldsOk`). "Within" is label inclusion, whose meaning is a
union's. The model's copy takes no symbol key, where JavaScript's takes an
own enumerable one, so what $`c_b`$ gives under a symbol key is read as
JavaScript's copy may give it: $`c_b`$ never gives a symbol key unless a bound
of its excludes it, and a bound of $`\beta`$ listing keys admits each symbol key
a bound of $`c_b`$ lists (`Src.never`, `boundOk`). The result's type then holds
of the model's copy and of JavaScript's alike.

The result may instead be a dictionary
$`\mathsf{Dict}(\varphi;\iota;\omega;\beta;\chi)`$, of index views $`\iota`$ and
writable indexes $`\chi`$ beside the same fields, optional fields and bounds
(`DictOk`): each entry $`K{:}V_K`$ of $`\iota\mathbin{+\!\!+}\chi`$ is at its
own type, two whose classes overlap at one type (the string and numeric
classes overlap, the symbol class only itself);
$`c_a`$ holds no prototype ($`\neg\pi`$ among its keys, by a bound or by an index
of its own, which `dictViewT` states); and for each entry $`K{:}V`$,
whatever either side gives under a key $`K`$ admits is within $`V`$:

```math
\mathrm{given}_K(c,V)\iff
  \forall (k{:}T)\in\varphi_c\cup\omega_c.\ K\ \text{may admit}\ k\Rightarrow T\subseteq V
  \ \land\ \big(\exists (K'{:}T')\in\iota_c.\ K\subseteq K'\land T'\subseteq V
  \ \lor\ \exists\,\mathsf{among}\,N\in\beta_c.\ \forall k\in N.\ K\ \text{may admit}\ k\Rightarrow k\in\mathrm{dom}(\varphi_c\cup\omega_c)\big)
```

($`\mathrm{given}_K(c_a,V)`$ is `classWithinA`). For the source it is
`classWithin`, over the keys a copy takes, less $`\delta`$, and also no array
store whose elements a copy would give under index keys: a bound excluding the
store key, or a string index at a type no member of which is a list
(`noStore`, since the store key `[]` is a string), or, for the class of the
canonical numeric keys, an array whose store's elements are within $`V`$
(`classWithinPlain`; `arrayRoute`):

```math
\frac{K=\mathsf{numeric}\qquad \mathcal B\ \text{stated}\qquad (\sigma{:}S)\in\varphi_{c_b}\qquad
      \forall c\in S.\ c=\mathsf{list}\,\tau\ldots\land\ \mathrm{positions}(\tau)\subseteq V}
     {\mathrm{gives}_K(c_b,V)}\ \textsf{array-source}
```

its elements are within $`V`$ (`storeData_typed`), and so are its own fields
at those keys, by the built-ins' invariant's $`\mathsf{numericOwn}`$
([the array invariant](SEMANTICS.md#the-array-invariant), `ObjFacts.numeric`,
`numeric_of_inv`). An element sits one location further than its store, so
the copied values are known one level below the merge's, which the
allocation, a step later, needs (`make_fields_rule_below`). For the symbol class, which
admits no key the model's copy gives, $`c_b`$ says what JavaScript's copy gives
there: a symbol index within $`V`$, or a bound listing its keys, none a
symbol. A string source gives strings under its keys, so for another class
$`V`$ holds every string. A field or optional field of the
result whose key a class may admit is within that entry's $`V`$, and exactly
it where a writable index's class may admit it, whose locations hold exactly
$`V`$; and
each bound of a result with a writable index keeps that index's class
($`b\ \mathsf{keeps}\ K`$, [covering](POSITIVE-TYPES.md#records)): none lists
keys or excludes one the class may admit, which the keys outside code may add
under the index would contradict. The
soundness case evaluates the operands with `bind`, as `arith` does, and
closes with `ObjectMerge.merge_values_safe`, which takes the merge's step,
then the allocation's by `make_fields_rule_below`, giving each location the
contract its result key states, the $`V`$ of an entry whose class admits the
key, or its copied value for a key the result does not state. Evidence names
the rule `merge` with the two operands' derivations; the search types a slot
operand at the slot's type and tries the requested type, then the pool's,
for the result, coercing; extraction proposes the clauses
(`ObjectMerge.mergeResult`: where a side states an index, the dictionary over
the sides' classes, each at the union of the index types and the admitted
fields' types of the classes overlapping it, if the rule admits it, else the
record) and states them as hints. The last merge of an
object literal is at the literal's claim where the rule admits it: each pair
of clauses may give a record of the claim's own, so a field written after a
spread is allocated at the type of the arm each pair gives, as TypeScript
types the literal per arm of the contextual union.

For heap knowledge a merge is an allocation, as a literal is
(`HeapExpressionRules.merge_alloc_sound`): it reads the heap and writes no
old location, so every fact survives, and its fresh object's fields, under
whatever keys, are distinct from every field a record-typed slot names.

### Allocation at a computed key

[ComputedKey.lean](../lean/Verification/Programs/ComputedKey.lean) states and proves what an allocation at a key known
only at run time holds. $`\mathsf{makeKey}(k,a)`$ allocates one object owning
one property at the key $`k`$'s value converts to
([SEMANTICS](SEMANTICS.md#operational-language)). Its type gives, for each
clause of the key's type, the object that clause's keys make
(`keyedClause`):

```math
\frac{\Gamma\vdash_G k:K\quad\Gamma\vdash_G a:A\quad
      \forall c\in\mathrm{expand}_G(K).\ \mathrm{keyed}(c,A)\in\mathrm{expand}_G(R)}
     {\Gamma\vdash_G\mathsf{makeKey}(k,a):R}\ \textsf{makeKey}
```

```math
\mathrm{keyed}(c,A)=\begin{cases}
\mathsf{Ref}(\kappa{:}A;\ \mathsf{among}\,\{\kappa\}) &
  c\in\{\mathsf{strLit}(s),\mathsf{numLit}(x),\mathsf{symbolLit}(i)\},\ \kappa=\mathsf{key}(c)\\
\mathsf{Dict}(\theta{:}A\ \text{writable};\ \mathsf{outside}\,\{\texttt{[]},\mathsf{proto}\}) &
  c\in\{\mathsf{str},\mathsf{num},\mathsf{symbol}\},\ \theta\ \text{its class}
\end{cases}
```

with $`\mathsf{key}(c)`$ the key the singleton converts to and no
$`\mathrm{keyed}(c,A)`$ for any other clause (`KeyedOk`). The soundness case
evaluates the key and the initializer with `bind`, as `merge` does, and closes
with `ComputedKey.keyed_values_safe`: the key's value converts to a key of its
clause's object (`keyed_key`), which is none the model keeps for itself
(`Unreserved`: $`\mathsf{esc}`$ spells none, a
number's `ToString` begins with a digit, a minus sign, `NaN` or `Infinity`,
`numberToString_unreserved`, and a symbol is no string), so the object holds
no prototype and no store, and the allocation's one location is at $`A`$
(`make_fields_rule`). For heap knowledge it is an allocation, as a merge is
(`HeapExpressionRules.makeKey_alloc_sound`).

### Key-adding writes

A source write that adds a key is the copy of the object with the key,
rebound to every local that holds it: the statement $`x.k = e`$ (or $`x[\text{"}k\text{"}] = e`$)
where some plain-object clause of $`x`$'s claimed type states $`k`$ neither as a
field, a view nor a method, nor as a readonly optional field (`mayLack`),
lowers, when $`x`$ holds an object its holders $`H`$ **own** at the
statement (a strong update, sound where no other reference exists:
[Smith, Walker and Morrisett 2000](REFERENCES.md#smith-walker-and-morrisett-2000)), to

```math
x;\ e;\ o\leftarrow\mathsf{makeAt}(\{k\mapsto v\});\ m\leftarrow\mathsf{merge}_{[]}(x,o);\ \overline{y\leftarrow m}^{\,y\in H}
```

with the value of $`e`$ at the claim of the write expression $`W`$, the one-key
object at $`\mathsf{Ref}(k{:}W;\ \mathsf{among}\,\{k\})`$ and the merge at the
record or dictionary `mergeResult` proposes, checked by
[$`\textsf{merge}`$](#allocation-from-parts). A constant holder $`y`$ is
rebound by the last node's slot map, which puts the merge's value in $`y`$'s
slot; a `let` holder held in a cell by a write of its cell, checked against
the cell's storage contract, and one held in a slot of its activation
([slot or cell](SOURCE-ELABORATION.md#mutable-bindings-and-module-constants))
by the same slot map, the merge's value checked against its storage contract.
The value of the assignment is discarded: only a statement
is lowered so. A write $`x[k] = e`$ at a key whose claim is of
strings, numbers or symbols, and no one key the source spells
(`computedKeyClaim`), is the same copy, rebound to every holder alike, with
the allocation at the key's value, $`o\leftarrow\mathsf{makeKey}(k,v)`$, checked by
[$`\textsf{makeKey}`$](#allocation-at-a-computed-key) at the type the
object's writable index states for the key's class where it states one (the
copy then keeps the index, as a literal meant for a dictionary is allocated
at it), else at $`W`$. The copy takes string keys only, so a symbol key is the
other way round, $`m\leftarrow\mathsf{merge}_{[]}(o,x)`$, where every clause of
$`x`$'s claimed type lists its own keys, each a key the copy takes
(`listsCopiedKeys`): the copy of $`x`$ then holds all of it, and the
allocation, which no key of $`x`$'s overwrites, its key. A key of strings and
symbols both is refused. JavaScript's write is `[[Set]]`, which on an
ordinary object a literal made defines the property, as the copy does, but
for `__proto__`, which the built-in `Object.prototype` holds as a setter: where
the object does not own the key, the setter makes an object or `null` value
the prototype and does nothing with another. So a key whose claim may be
`__proto__` (a string, or that singleton) is tested first:

```math
\mathbf{if}\ k\equiv\texttt{"\_\_proto\_\_"}\land\lnot\,\mathsf{hasKey}(\texttt{\_\_proto\_\_})(x)\ \mathbf{then}\ v\ \mathbf{else}\ (o\leftarrow\mathsf{makeKey}(k,v);\ m\leftarrow\mathsf{merge}_{[]}(x,o);\ \overline{y\leftarrow m}^{\,y\in H};\ v)
```

two tag dispatches (`strEq`, `hasKey`) where the value's claim holds no
object nor `null` (`noPrototypeValue`); another value is refused. Ownership
(`growSites`) is syntactic. A binding is a name and the statement declaring
it; the holders of an object are the binding $`x_0`$ that allocated it and
each constant bound to a holder since:

```math
\mathrm{Own}(H,s)\iff
  \begin{cases}
  x_0\in H\ \text{is declared}\ \mathtt{const}\ x_0 = a\ \text{or}\ \mathtt{let}\ x_0 = a,\ \text{not at module level, with}\ a\ \text{a fresh allocation;}\\
  \text{every other}\ y\in H\ \text{is declared}\ \mathtt{const}\ y = z\ \text{with}\ z\in H\ \text{declared before it;}\\
  s\ \text{is at the loop depth of}\ x_0\text{'s declaration, in the same body;}\\
  \text{no statement from}\ x_0\text{'s declaration through}\ s\ \text{lets any}\ y\in H\ \text{escape.}
  \end{cases}
```

A fresh allocation is an object literal, or `new C(…)` with $`C`$ a class the
file declares at its top level (or a constant bound to one): its constructor
reads no `this` and ends in the instance's allocation
([classes](SOURCE-CONTRACTS.md#classes)), which nothing has reached when
`new` returns. A constant bound to a holder is no escape; any other binding of
a holder's name removes that holder, since the parser gives every shadowing
local a name of its own, so two bindings of one name are never both in scope.
The lowering finds each holder in scope by its name and declaring statement;
one out of scope holds nothing code can reach, and the receiver $`x`$ must be
one in scope. An expression lets $`y`$ escape (`escapesExpr`) when $`y`$
occurs in it other than as the receiver of a member read, index read, write,
index write, `in` test, compound or logical assignment: in a call's arguments
or as a method call's receiver, in a binding's or field's value, an
assignment, a result, a spread, a comparison, and anywhere in a closure,
which holds the object. In textual order every path from the allocation to
$`s`$ passes only earlier statements, since $`s`$ is in no loop the
allocation is outside; a module constant is read by the module's functions.
With $`\mathrm{Own}(H,s)`$ no reference but the holders' slots and cells
holds the object, so JavaScript's write in place, which every reference sees,
and the copy, which every holder holds from then on, agree. Any other write
adding a key is refused, located at the write, as is a named write of
`__proto__` (a setter); one through a parameter, at a key the source names or
one known only at run time, is
[refused on principle](SOURCE-FRAGMENT.md#refused-on-principle), since the
caller may hold the object at a type leaving the key absent, or optional at
another type.

`Object.assign(t, s_1, …, s_n)` copies each source onto its target as a
spread copies, one $`\mathsf{merge}_{[]}`$ per source as soon as it is
evaluated, checked by $`\textsf{merge}`$. Its target is a fresh literal, whose
result is the call's value; or, for the statement `Object.assign(x, …);`
whose target $`x`$ is the one holder of an object it owns
($`\mathrm{Own}(\{x\},s)`$, $`x`$ a constant), the local, which holds the
result from then on, as for a key-adding write (a source letting $`x`$ escape defeats
ownership). Any other target is refused: the call's value is the target, one
more reference to it. JavaScript sets each key through the target's `[[Set]]`,
where a spread defines it: the two agree on a fresh plain object, but for
`__proto__`, whose setter replaces the prototype. So each source's claimed
type must give no `__proto__` (`ownsNoProto`: every clause owns no
enumerable property, or a key bound excludes the key); a record type, which
may own any key, is refused. As for a spread, the model's copy takes string
keys only ([Source model](SOURCE-MODEL.md#object-literals)).

### Checked control-flow graphs

[ControlFlow.lean](../lean/Verification/Programs/ControlFlow.lean) adds a finite control-flow graph over the existing expression
language. A program is a finite list of nodes indexed by label; each node is one
[term](SEMANTICS.md#operational-language), one of these six continuations,
and an optional handler (below):

| Continuation            | Action after evaluating the expression                                                                                              |
| ----------------------- | ----------------------------------------------------------------------------------------------------------------------------------- |
| `ret`                   | Return its value as the graph's declared result type.                                                                               |
| `bind` to a target      | Push the value, apply the target slot map, and enter its label.                                                                     |
| `effect`, then a target | Discard the value, apply the target slot map, and enter its label.                                                                  |
| `branch`                | Select a target according to the Boolean value and apply its slot map.                                                              |
| `branchBind`            | Select a target, push the tested Boolean, and apply its slot map with a singleton refinement.                                       |
| `tagBind`               | Test the returned value's shape, select a target, push that value, and apply its slot map with the refinement the answer justifies. |

Conditionals therefore exist at two levels: `if` inside a single node's term, and
these branch continuations between nodes. Source lowering uses the continuations
for statement control flow, in function and closure bodies alike, and the term
form inside direct proofs. It emits every continuation except plain `branch`, which remains
available to graphs written against the protocol directly.

A target contains its label and an optional slot map. These are executable
program data, shared by the machine and checker; evidence cannot supply a
different binding transfer. Numeric targets abbreviate an identity map. A bind
or `branchBind` map indexes the environment **after** pushing the result; effect
and ordinary branch maps index the unchanged incoming environment.

A node's **handler** is a target too: where a throw out of its expression
goes, the thrown value pushed as a `bind` pushes a value. A node without one
lets the throw end the run, in the state $`\mathsf{raised}(v)`$. The machine:

```math
\frac{h,t\ \text{raises}\ v}{h,\ \mathsf{eval}(t,\rho,k,\ell)\to h,\ \mathsf{at}(\ell,\mathsf{push}(v,\rho))}\ (\texttt{handle})
\qquad
\frac{h,t\ \text{raises}\ v}{h,\ \mathsf{eval}(t,\rho,k,\varnothing)\to h,\ \mathsf{raised}(v)}\ (\texttt{raise})
```

Node evidence for a node with a handler supplies the type $`T`$ the thrown value
is bound at and the handler edge's certificate. `checkHandlerUsing` requires $`T`$ to
admit every JavaScript value, with a `source` or `top` clause (`admitsAll`), and the edge to
check against the target's claims under the facts that hold wherever the
expression throws, which are those of the node's entry that do not mention the
heap (`handlerFacts`: immutable values, alias and distinct links, shifted past
the thrown value's slot):

```math
\frac{\{\mathsf{source},\mathsf{top}\}\cap\mathrm{expand}_G(T)\ne\varnothing\quad
      \mathrm{TargetOk}_G(C,\ T{:}\Gamma,\ \ell,\ \mathrm{handlerFacts}(K))}
     {\mathrm{HandlerOk}_G(C,\Gamma,K,\ell)}\ \textsf{handler}
```

where $`\Gamma`$ and $`K`$ are the node's entry claims and facts. The machine
state after a throw is safe by that edge, `admitsAll_sound` giving the thrown
value its type, and `handlerFacts_holds` its facts at any heap.

Node evidence supplies its entry environment, expression type and program
evidence, and exactly the edge certificates required by its continuation. It
also supplies an input fact context and an output fact context. Checked expression
evidence must establish the output from the input; every outgoing edge checks
fact entailment against its destination under the executable slot map. Ordinary
expressions discard cell facts; the [effect rules](#checked-expression-postconditions)
justify stronger postconditions. Fact transfer is checked on both branch edges;
Boolean branch outcomes refine cells only through checked, still-valid read
links. Tag outcomes currently retain facts without adding cell refinements.
`checkGraphUsing` enumerates **every node in the actual program**. It requires one
certificate per node, binds expression evidence to that node's actual code,
checks scope, and obtains successor labels directly from the continuation.
Every target must exist in both the program and the certificate. Both branch
edges are checked even when the condition is a literal, and unreachable nodes
are checked too. Omitting a predecessor list cannot bypass these obligations.

`checkEntryUsing` checks the graph and requires the start claim to equal a separately
supplied input context $`\Gamma_0`$, with an empty input fact context.
`accepted_inputs_safe` proves:

```math
\begin{gathered}
\mathrm{checkEntryUsing}(G,\mathit{images},R,P,C,p,\Gamma_0)=\mathsf{true}
\\
\land\;\mathrm{EnvOk}_G(\Gamma_0,\rho,n,W)
\land\;\mathrm{WorldAdm}(W)
\land\;\mathrm{HeapOk}(n,W,h)
\\
\Longrightarrow\quad
\mathrm{SafeGraph}_P(⟦R⟧_G^{\rho},n,W,h,\mathrm{at}(p,\rho)).
\end{gathered}
```

$`R`$ is the graph's goal: a result type, whose meaning is $`⟦R⟧_G`$, or a
guard's promise about the input in entry slot $`s`$, whose meaning relates the
returned value to $`\rho(s)`$ as the
[promise effects](SEMANTICS.md#effect-qualified-call-contracts) state
(`ControlFlow.GoalHolds`). Under a promise goal, a return checks its answer
and, where that answer is `true` or `undefined`, that a slot still holding the
input has a type within the promise once the returned value's yields refine
it (`checkReturnResult`); the slots holding the input, and the implications a
Boolean slot carries, are node evidence the edges transfer.

[`SafeGraph` and the machine state $`\mathrm{at}(p,\rho)`$](SEMANTICS.md#computations-and-recursive-types)
are the graph-level analogues of `Safe`: the run starts at the entry label with
the input environment, and stays safe through every transition.
The arguments, world, heap and budget are arbitrary subject to these premises.
`accepted_entry_safe` is the underlying theorem for a checked point and its
claimed environment and heap facts, both of which its caller must establish.
The proof inducts on execution budget, so it covers cycles without unrolling
the graph or computing invariants. Expressions use the existing small-step
relation, with `SafePost` carrying checked output facts to the continuation.
Node dispatch and control transfer each consume
one step; a control-flow cycle cannot masquerade as progress at zero cost.
This is a safety and partial-correctness theorem, not a termination guarantee.

The graph layer does not change the type-family or expression semantics. A
closure body is a graph as a function body is, run by its own steps
([graph code](SEMANTICS.md#graph-code)) and typed by `funGraph`. Boolean result refinement is proved as described below. A primitive fragment with parameters
is connected; broader source extraction remains integration work. The next section supplies
an in-memory certificate producer; [REQUEST-PROTOCOL.md](REQUEST-PROTOCOL.md)
describes its serialized consumer boundary. No completeness theorem is
claimed for graph, program or edge evidence.

#### Refinement under an observed outcome

[BranchRefinement.lean](../lean/Verification/Programs/BranchRefinement.lean) uses one contract for Boolean equality and tag observations.
An observation $`o`$
is either equality to a Boolean value or the result of a runtime tag test.
Define the semantic obligation:

```math
A\preceq_o B
\quad\Longleftrightarrow\quad
\forall n,W,v.\;
\bigl(v\in⟦A⟧_{n,W}\land o(v)\bigr)
\Longrightarrow v\in⟦B⟧_{n,W}.
```

This is `ObservedSub`. The destination type $`B`$ is supplied. The contract does
not require computing a canonical intersection, difference, or filtered type.
It is a semantic specification; the executable checker uses sufficient finite
checks, not a semantic oracle. No completeness of these checks is claimed.

`ObservedCovers` checks each destination slot selected by a map $`m`$. For the
tested slot $`i`$, it requires $`\Gamma(i)\preceq_o\Delta(j)`$; other selected slots
require ordinary subtyping, or, for a slot $`k`$ holding an object the tested
value was read from through field $`f`$ (a current read link at the dispatch,
`readFields`, or an optional one, `optionalFields`), subtyping from its field
slice $`F^{f}_{t,q}(\Gamma(k))`$
(`fieldSlice`): the labels of $`\Gamma(k)`$ but those every clause of which is a
record fixing $`f`$, as an invariant field or a readonly view, at a type that
answers the tag $`t`$ with $`\lnot q`$. The common environment theorem is:

```math
\frac{
 \mathrm{EnvOk}_G(\Gamma,\rho,n{+}1,W)
 \quad \mathrm{HeapOk}(n{+}1,W,h)
 \quad o(\rho(i))
 \quad \forall (k,f)\in\mathit{fs}.\ h(\rho(k).f)=\rho(i)
 \quad \mathrm{ObservedCovers}_G(\Gamma,\Delta,i,o,m,\mathit{fs})
}{
 \mathrm{EnvOk}_G(\Delta,\mathrm{mapEnv}(m,\rho),n{+}1,W)
}.
```

The field slice is sound one level up (`fieldSlice_sound`): the field's
location holds the read value, and a heap meeting the world holds at that
location a value of the field's type one level down (`field_value`), whose tag
answer is budget-independent. Through an optional link the slice is sound
too: where the object has the key the link is a read link, and an object
lacking it is of no label the slice drops, every clause of which names the
field as a field or a view, a key the object has (`fieldSlice_absent`). What
it establishes is the object's label,
which its allocation fixes; it is not a claim about what the field holds
later, so writes and calls after the test do not undo it. A discriminated
union is this: `s.kind === "circle"` keeps the arms whose `kind` admits
`"circle"`.

A slot $`k`$ the tested value was read from through a key $`f`$ it may lack (an
optional read link, `optionalFields`) is covered by a promotion instead, where
the observation rules `undefined` out (`excludesUndef`): the read then found
the key, which the object keeps from its allocation on, so its type is its
records with $`f`$ present (`promotes`, below). The environment theorem takes the
optional links' meaning as one more premise, $`\forall(k,f)\in\mathit{os}.\ f\notin\mathrm{keys}\rho(k)\Rightarrow\rho(i)=\mathsf{undefined}`$
(`ObservedCovers.env`).

An observation the tested slot's type rules out (`impossible`: a tag answer
every label of it contradicts, or a Boolean it does not hold) covers any
destination: no environment meets both, so the edge is never taken.
`checkObservedUsing` checks slot existence, map and evidence lengths, and each of
these obligations. `checkObserved_sound` and `ObservedCovers.env` prove the
common path. The observation is established by execution, never accepted as a
producer assertion. Heap contents are not refined.

Four implementations discharge the tested-slot obligation:

- **Boolean equality:** `booleanMember` checks that the supplied destination
  contains the observed Boolean. `subset` is the canonical evidence marker for
  this check, not an ordinary subset derivation. No synthetic singleton label
  is needed.
- **Tag outcome:** `tagSlice` discards a label only if every clause contradicts
  the observation, then checks an ordinary subtype certificate from the remaining
  labels to the supplied destination. Mixed-shape labels are retained intact.
  Filtering is a conservative algorithm, not the definition of `ObservedSub`.
  Alternatively, a passed test naming one primitive family is covered by that
  family's clause, $`F_t`$, in the destination, whatever the tested type, `unknown`
  included (`tagMember`, with the marker `subset`): every value `typeof`
  answers `"string"` for is a string. So is equality with one number other
  than a zero, which holds of that number alone, or with one string:
  $`x\equiv 1`$ with $`x:\mathsf{number}`$ gives $`x:1`$. A passed
  `typeof x === "function"` is covered by the two function clauses without
  signatures together, $`F_{\mathsf{isFun}}`$ = `arrs [] []` and `ctors [] []`, TypeScript's
  `Function`: every value `typeof` calls a function is invocable or a class
  ([`Function`](POSITIVE-TYPES.md#functions-and-classes)). A type parameter's
  value is covered so too: where `typeof x === "number"` holds of `x: T`,
  `x` is a `number`, which is what TypeScript's `T & number` holds, though
  no longer read as a `T`. A more precise algorithm can implement the same
  contract without changing the edge or environment rule.
- **Type parameter's value:** a meet row $`p\sqcap\vec q\sqcap\vec c`$, a
  bounded binder's value ([meet rows](POSITIVE-TYPES.md#parameter-and-scheme-rows)),
  keeps its parts where a test answers, and only its values in a clause the
  test does not contradict. Each such clause is a clause of a destination
  meet row of the same parts or fewer, or the destination's meet rows of
  those parts together hold the family the test names (`familyMember`, as
  above), with the marker `subset` (`meetSlice`, `meetSlice_sound`). So
  `x: T extends number | null` is `T ⊓ number` where `x ?? d` takes `x`, and
  `x: T` is `T ⊓ Function` where `typeof x === "function"` holds: TypeScript's
  `T & {}` and `T & Function`, still read as a `T`. The rule reads no part, so
  it holds at every assignment of the parameters. With $`\mathsf{mt}_B`$ the
  meet rows of $`B`$ whose parts are among $`p,\vec q`$, $`\mathsf{cl}(m)`$ a
  meet row's clauses and $`F_t`$ the family clauses of a test $`t`$:

```math
\frac{\forall c\in\vec c.\;\;\mathsf{tag}(t,c)=\lnot q\ \lor\
         \exists m\in\mathsf{mt}_B.\;c\in\mathsf{cl}(m)\ \lor\
         \bigl(q\land F_t\subseteq\textstyle\bigcup_{m\in\mathsf{mt}_B}\mathsf{cl}(m)\bigr)}
      {p\sqcap\vec q\sqcap\vec c\ \preceq_{t=q}\ B}\ \textsf{tag-meet}
```

  Source lowering gives a test's arms these narrowed meet rows
  (`observedSlice`); the producer claims them where the bound states the
  values (`narrow_rigid`), and keeps `T` where the bound is `unknown`, whose
  values other than null and undefined no clause row states.
- **Array of the built-ins:** a passed `Array.isArray` finds an object owning
  the store key. A member of a record, dictionary or `source` clause meets
  the built-ins' [array invariant](SEMANTICS.md#the-array-invariant), so such a
  member is a member of the built-in `sparse ReadonlyArray<unknown>`: a clause
  row $`L`$ holding the array shape over a store of `unknown`,
  $`P_{\mathcal B}`$ and $`N_{\mathcal B}`$, the built-ins' `unknown` row holding
  `source` only (`builtinArrayLabel`, `exactUnknown`, `builtinArray_of_record`).
  Each label the tag slice keeps is kept in the destination, or is a clause
  row each clause of which answers `false` or is one the invariant applies
  to; and the destination holds $`L`$ (`arraySlice`, `arraySlice_sound`, with
  the marker `subset`). A label with `top`, and a parameter row, is none of
  these: `top` and a type parameter are not narrowed so:

```math
\frac{\forall a\in T_{\mathsf{isArray}}(A).\;a\in B\ \lor\ \forall c\in G(a).\;
         \mathsf{tag}(\mathsf{isArray},c)=\mathsf{false}\lor c\ \text{a record's, a dictionary's or}\ \mathsf{source}
       \qquad L\in B\qquad G(L)=[\mathsf{Ref}(;\sigma{:}S,\mathsf{proto}{:}P_{\mathcal B};\langle\mathsf{outside}\,N_{\mathcal B}\rangle)]}
      {A\preceq_{\mathsf{isArray}=\mathsf{true}}B}\ \textsf{tag-array}
```

  with $`S`$ a readonly store at a type holding `top` or `source`. Each
  operand of `&&` and `||` sees this refinement where an earlier operand's
  `Array.isArray` holds (`arrayRefine`, `tagRefine`).

- **Present key:** a passed `in` test finds its key on the object's chain:
  its own, or, where it lacks it, one a prototype holds (`KeyFound`). An
  object of a record lacking one of its optional keys holds no prototype
  (`optT`), so there the key is its own, and an object's keys are fixed at its
  allocation: each record clause $`c`$ of the tested type holds with its
  optional key $`k`$ taken as present, $`c^{+k}`$ (`promote`: a writable optional
  key becomes an invariant field, a readonly one a view, as `optT` states of a
  present key). An object of a dictionary clause holds no prototype either
  (`dictViewT`), so a key $`k`$ found on it is its own, at a contract implying
  the type $`D`$ of each index $`\theta{:}D`$ whose class surely admits $`k`$:
  $`c^{+k}`$ adds the view $`k{:}D`$ for each (`presentViews`). The destination
  needs a clause asking no more than that, $`d\sqsubseteq c^{+k}`$ (`weaker`:
  both records or both dictionaries, each operand of $`d`$ one of
  $`c^{+k}`$'s; every part of their meaning is a statement about each
  operand) (`promotes_sound`, with the marker `subset`):

```math
\frac{\mathsf{tagHolds}(t,v)=\mathsf{true}\ \Rightarrow\ v\in⟦F_t⟧\quad F_t\subseteq\mathrm{expand}_G(B)}
     {A\preceq_{t=\mathsf{true}}B}\ \textsf{tag-member}
\qquad t\in\{\mathsf{isStr},\mathsf{isNum},\mathsf{isBigint},\mathsf{isSymbol},\mathsf{isUndef},\mathsf{isNul},\mathsf{isBool},\mathsf{numEq}(b)_{b\neq\pm0},\mathsf{strEq}(s),\mathsf{isFun}\}
```

```math
\frac{v\in⟦c⟧\quad k\notin\mathrm{keys}(v)\Rightarrow v\ \text{holds a prototype}}
     {v\in⟦c^{+k}⟧}
\qquad
\frac{G\vdash A\ \text{plain}\quad
      \forall c\in\mathrm{expand}_G(F_{\mathsf{hasKey}(k),\mathsf{true}}(A)).\
      \exists d\in\mathrm{expand}_G(B).\ d\sqsubseteq c^{+k}}
     {A\preceq_{\mathsf{hasKey}(k)=\mathsf{true}}B}\ \textsf{present-key}
```

```math
\mathsf{Dict}(\varphi;\psi;\iota;\omega;\beta;\chi)^{+k}=
  \mathsf{Dict}\bigl(\varphi;\ \psi\cup\{k{:}D\mid(\theta{:}D)\in\iota,\ \theta\ \text{surely admits}\ k\};\ \iota;\ \omega;\ \beta;\ \chi\bigr)
```

For the current primitive profile, null filtering gives:

```math
F_{\mathrm{null},\mathrm{true}}(\mathrm{null}\lor\mathrm{bool})=\mathrm{null},
\qquad
F_{\mathrm{null},\mathrm{false}}(\mathrm{null}\lor\mathrm{bool})=\mathrm{bool}.
```

A regression also proves a semantic refinement of a mixed label that the current
filtering checker cannot establish. This records the precision boundary explicitly.
A Boolean shape test does not establish equality to `true`; these observations
have separate tests to prevent conflation.

A graph point whose entry claims a binding of the empty type is unreachable:
every incoming edge establishes that claim, which no value meets. Proof search
derives any sequent there by `unionVar` on the empty slot, which has no
premise, and a jump whose entry is so claimed completes the function rather
than continuing (the exhaustive `switch` in the
[source statement rules](SOURCE-CONTRACTS.md#statement-forms) falls off no end).

The `branchBind` dispatch uses this common checker and environment
theorem with a Boolean observation of the actual pushed value. Its all-budget
safety proof covers cyclic graphs.
The source compiler maps a tested immutable Boolean variable to that pushed
value and preserves the other slot identities. Negations swap branch polarity.

The `tagBind` continuation tests the actual returned value, pushes that value,
and selects the matching edge. Its schematic rule is:

```math
\frac{\Gamma\vdash_G t:A
\quad\mathrm{ObservedCovers}_G(A::\Gamma,\Delta_y,0,\mathrm{tag}(k,\mathsf{true}),m_y)
\quad\mathrm{ObservedCovers}_G(A::\Gamma,\Delta_n,0,\mathrm{tag}(k,\mathsf{false}),m_n)}
{\mathrm{NodeOk}_G(\Gamma,t,\mathrm{tagBind}(k;y,m_y;n,m_n))}.
```

Both edges are checked. Unlike Boolean dispatch, tag dispatch accepts any typed
value. Safety uses the actual `tagHolds` outcome;
the certificate cannot supply it. `tagBind` shares the observed-edge checker
and environment theorem with `branchBind`.

Source branches and loop heads use null or undefined tag dispatch only for syntactically
identified immutable variables, including repeated negations and either literal
operand order. The original condition runs once and its operand/result claims
remain obligations. A subsequent lookup of that immutable variable supplies the
value for tag dispatch; no source call or property read is repeated. Maps retain
the observed value in the target binding and discard saved condition temporaries.
Closure null guards use existing `unionVar` and `ifTag` evidence instead of a new
rule. The condition is evaluated into an anonymous slot. The immutable tested
slot is split into its primitive labels; each label has a known tag answer and
checks the selected arm. Source arm-entry and expression claims remain separate
obligations in the corresponding filtered contexts. The final ordinary term
certificate checks the complete construction. This supports parameters, captured
immutable values, negations and effects in the selected arm within the existing
closure control-flow slice. It does not retain observations of mutable properties.
The finite-label split is a source-profile strategy, not a new semantic rule for
arbitrary mixed-shape type labels.

[ExecutionModelTests.lean](../lean/Verification/Tests/ExecutionModelTests.lean) shows the model's `in` finding a key on the prototype chain, which an
instance does not own.

#### Statement forms as graphs

The [statement forms](SOURCE-CONTRACTS.md#statement-forms) add no node
kind, continuation or rule; each is a shape of ordinary nodes and edges.

- A loop with an update: the body's end and each `continue` edge go to the
  update's first node, whose edge goes to the head. Every edge into the head is
  checked against its cut as before; the update is checked once, from its own
  statement claim.
- A labeled block: `break ℓ` is an administrative null node whose mapped edge
  goes to the statement after the block labeled $`\ell`$, dropping the slots
  the block introduced, exactly as a loop's `break` goes to its exit. A block
  adds no node of its own.
- `throw e`: `e`'s nodes, then one node `throw x` returning, at the result
  type, which the `throw` rule gives it.
- `try`: every node of the body that may throw (not a slot or a value) names
  the handler's entry as its handler, the thrown value landing in the catch
  binding's slot and the `try`'s scope kept; the handler's nodes name the
  `finally` block's throw-path entry, or the enclosing handler. The `finally`
  block is compiled once per way out ([statement forms](SOURCE-CONTRACTS.md#statement-forms)): after a
  normal completion, before each `return` in the body or handler with the
  value held in a slot of its own, before each `break` or `continue` that
  leaves the `try` (every `finally` the jump passes, innermost first, the
  outermost completing into the jump's target), and after a throw with the thrown value
  held, ending in a node that throws it again. Where neither the body nor the
  handler can complete, the normal way leads to an unreachable node that
  loops on itself and states nothing.
- A closing region (the [iterator protocol](SOURCE-CONTRACTS.md#the-iterator-protocol)'s
  IteratorClose): the body's nodes name, as their handler, the close's entry
  under a handler that drops the close's own throws, followed by a node that
  throws the held value again; the loop's `break` goes to the close's entry
  followed by the loop's exit, and each `return` passes it as a `finally`.
- A declaration hiding an outer binding of its name adds no node: the parser
  has given it a name of its own ([shadowing](SOURCE-ELABORATION.md#derived-source-forms)), so
  the lowering never meets two bindings of one name.

## State

What is known about the heap and the environment as execution proceeds, layered
over both of the above: expression typing decides whether an operation is
admitted, the graph decides where its knowledge travels, and these rules decide
what it establishes.

### Current-content rules (semantic layer)

The finite [type and assertion syntax](POSITIVE-TYPES.md#state-assertion-grammar)
is defined alongside the ordinary type grammar. This section owns its rules.

[HeapObservations.lean](../lean/Verification/Semantics/HeapObservations.lean)
defines `SafePost` and proves its composition rules, and
[HeapFacts.lean](../lean/Verification/Semantics/HeapFacts.lean) interprets the
finite current-content assertions.
[HeapExpressionRules.lean](../lean/Verification/Programs/HeapExpressionRules.lean)
checks finite expression evidence, and `checkStep_sound` proves each accepted
step ([checked expression postconditions](#checked-expression-postconditions)).
These rules are not `HasTyUsing` constructors. The maintained graph checker accepts the checked effect forms;
the source adapter binds supplied observations to checked graph checkpoints.
The producer can also derive facts through supported operations.
The [semantic reference](SEMANTICS.md#current-content-assertions-and-postconditions)
defines $`\mathrm{Obs}`$, $`\mathrm{ObservedRef}`$, and `SafePost`; ordinary immutable-value branch
observations above must not be confused with these mutable-heap assertions.

All rules below assume an admissible world and satisfying initial heap. Write
$`\widehat R(n,W,v)=R(v)`$ for a heap-independent content predicate, and require
$`R(v)`$ to imply that $`v`$ is a value. The observed-read rule is:

```math
\frac{\mathrm{Obs}(h,\ell,R)}
 {\mathrm{SafePost}(\widehat R,Q,n,W,h,\mathsf{read}(\ell))},
\qquad Q(h',v)\equiv h'=h\land h'(\ell)=v.
```

Its result type gives $`R(v)`$, and its postcondition
preserves the entire heap, hence other observations. For a value $`v`$ permitted by
the invariant $`B`$, the write rule is:

```math
\frac{\mathrm{Ref}(B)(n,W,\ell)\quad B(n,W,v)\quad\mathrm{isVal}(v)}
 {\mathrm{SafePost}(\mathsf{Null},Q,n,W,h,\mathsf{write}(\ell,v))},
\qquad Q(h',u)\equiv h'=h[\ell:=v]\land u=\mathsf{null}.
```

The write rule requires `Adm B` and no old-content premise. The written
location then observes the new value (`write_new`); a fact at another
location is preserved only with proved runtime inequality. A write through an
alias has the same effect. Allocation returns an invariant reference and the
exact appended heap, and preserves existing facts (`alloc_frames`).

| Rule             | Premise and consequence                                                                                                                                                          |
| ---------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| test             | A current lookup links the tested value to the cell; a predicate on that value then refines current contents. An old snapshot alone does not suffice.                            |
| `forget`         | Ordinary safety embeds with postcondition `True`, so an ordinary arrow call supplies no retained observation.                                                                    |
| `bind`           | For an evaluation context that lifts steps, its continuation receives the actual resulting heap, value membership and postcondition in the future world at the remaining budget. |
| `consequence`    | Implication weakens the result family and postcondition.                                                                                                                         |
| write then read  | The immediate subsequent read returns the written value; there is no ownership or non-escape premise.                                                                            |

The read, write and test rules at this level and the write-then-read
composition have no Lean proof of their own; `checkStep_sound` proves the
finite steps that use them.

The finite assertion layer represents a fact as a slot $`i`$, a field name and
an $`R`$ from the [primitive predicate grammar](POSITIVE-TYPES.md#state-assertion-grammar).
Write $`v\in R`$ for satisfying one of those predicates and
$`\mathrm{Read}_h(o,f,v)`$ for the [property-read relation](SEMANTICS.md#what-is-asserted-and-what-a-heap-change-can-touch).
A fact observes the read result, including the absent-key result:

```math
\mathrm{Holds}(\Delta,\rho,h)
\equiv \forall(i,f,R)\in\Delta.\;
\exists v.\ \mathrm{Read}_h(\rho(i),f,v)\land v\in R.
```

The observation and read rules are:

```math
\frac{\mathrm{Read}_h(o,f,v)\quad v\in R}
 {\mathrm{ReadFact}_h(o,f,R)}
\qquad
\frac{\mathrm{ReadFact}_h(o,f,R)\quad R\subseteq A}
 {\Gamma;K\vdash o.f:A}.
```

`linkFacts_holds` proves observation transfer through a live read link;
`read_sound` proves the read rule and preservation of the heap.
`observeTyped_holds` also derives a supported predicate from the tested value's
ordinary type restricted by the observed tag. For example, the falsy branch of
an object-or-undefined type supplies the predicate `{undefined}`, and its
truthy branch, whose objects no predicate names, `nonNullish`: a slice whose
every clause answers `isNullish` false (`cell-truthiness-narrowing`). Presence is
separate: a read result excluding `undefined` proves presence for an optional
key. A predicate admitting `undefined` covers both absence and a present value.
Writes require the ordinary lifetime contract; the observation grants no write
permission. Allocation preserves observations. Ordinary calls discard them; a write
preserves another observation only through checked location distinctness.

For a slot map $`m`$, the executable entailment check uses this sufficient rule:

```math
\frac{\forall(i,f,R)\in\Sigma'.\;\exists(j,f,S)\in\Sigma.\ j=m(i)\land S\subseteq R}
 {\mathrm{Holds}(\Sigma,\rho,h)\Longrightarrow
  \mathrm{Holds}(\Sigma',\mathrm{mapEnv}(m,\rho),h)}.
```

`HeapFacts.check_sound` proves it. Repeated slot mappings retain aliases; different
slots do not prove disjoint locations. `shift_holds` transports facts when a bind
pushes a result. The finite `read` rule preserves facts. `write` conservatively
drops all old facts and establishes the written value's predicate. `alloc` preserves shifted
old facts and adds the fresh cell at the result slot. These are semantic rules;
source compilation must still supply and check their graph-level use.

#### Checked expression postconditions

`Knowledge` in [HeapKnowledge.lean](../lean/Verification/Semantics/HeapKnowledge.lean) pairs the cell facts above with immutable slot facts
$`V`$, interpreted as $`\forall(i,R)\in V.\;\rho(i)\in R`$. This distinction is
necessary when the producer claims a wide type for a read: the ordinary type
remains unchanged, while a proved fact about the returned value can justify a
narrower subsequent return contract. Mutation invalidates cell contents and read-to-cell relationships, not
values already read into immutable slots or equalities between copied values.

The [assertion layer](SEMANTICS.md#what-is-asserted-and-what-a-heap-change-can-touch)
splits in two. $`\Pi`$ is a conjunction of **value predicates** $`x\in R`$ and
**equalities** $`x=y`$ between two variables. It mentions
only the environment. $`\Sigma`$ contains property-read predicates and read links,
with the meanings in the [semantic reference](SEMANTICS.md#what-is-asserted-and-what-a-heap-change-can-touch).
These heap assertions are duplicable and carry no ownership.

Every atom names a field: `HeapFacts.Fact` and `HeapLinks.Link` each carry one,
and `HeapExpressionRules` reads it off the term rather than taking it from
evidence, so a certificate cannot assert a fact about a field the program never
touched. The `allocated` rule establishes one primitive-content atom per named
field whose initializer slot has a known supported predicate, and none for a
field whose initializer has none; an ordinary allocation alone makes no such
assertion. The rules below are
written in the one-field spelling, $`x\mapsto R`$, which is the general rule at
whichever field its term names; nothing in them is specific to a field name.

Checking an expression is then a **Hoare typing**: an ordinary typing carrying a
precondition and a postcondition. Write

```math
\Gamma;\Pi;\Sigma\vdash_G r\leftarrow t:A\dashv \Pi';\Sigma'
```

for: with variables typed by $`\Gamma`$, in an environment satisfying $`\Pi`$ and a
heap satisfying $`\Sigma`$, evaluating $`t`$ is safe, its value has type $`A`$, and
binding that value to $`r`$ leaves a state satisfying $`\Pi'`$ and $`\Sigma'`$.

The binder is written $`\leftarrow`$ rather than $`=`$, which is already the equality
assertion these rules produce, and rather than $`:=`$, since nothing is assigned:
$`r`$ is a fresh binding, and it is the graph's `bind` continuation that makes it.
$`r`$ is in scope in the postcondition only, so a premise can never mention it.

$`\Gamma`$ does not appear on the right. It types the variables and is fixed for
the derivation; only $`\Pi`$ and $`\Sigma`$ are transformed. Note that $`\Gamma`$ and $`\Pi`$ both
constrain the environment, in different languages: $`\Gamma`$ gives each variable a
graph type, and $`\Pi`$'s primitive predicates refine that for primitives — `valuesAt`
reads a value fact when there is one and falls back to the variable's type when
there is not. What $`\Pi`$ adds beyond $`\Gamma`$ is equalities _between_ variables,
which a type cannot express.

Every rule binds the value it produces. Write $`r`$ for that binding, so a
postcondition can speak about the result alongside everything already in scope.

Rules below name their bindings, and one paragraph justifies that. Environments
are positional, and the implementation pushes the result at position $`0`$, moving
every existing binding up by one; `HeapKnowledge.shift` performs that
renumbering and `shift_holds` proves it preserves meaning. Naming the bindings is
that theorem applied: the precondition may appear unchanged in a postcondition
because nothing about the old bindings changed except their numbers. A name here
is a display for a position, not syntax — the calculus has no identifiers — and
it carries no source scoping; the adapter's own shadowing rules are
[a separate matter](FRAGMENT-FORMAT.md#source-mode). Positions reappear exactly
where a certificate carries a permutation, in
[binding transfer](#supplied-point-claims-and-incoming-edges) and on the wire.

Two auxiliary forms. $`(\Gamma;\Pi)(x)`$ looks $`x`$ up in both contexts, $`\Pi`$
first: it is the primitive predicate recorded for $`x`$ there, or
failing that the one $`\Gamma(x)`$ denotes when it is a supported primitive
union, or the strongest supported nullish exclusion implied by $`\Gamma(x)`$.
Otherwise the predicate is the exhaustive union of null, undefined and
`nonNullish`. It extends the $`\Gamma(x)`$ of the ordinary rules to the pair, is partial
in the same way, and is a lookup rather than a search — `valuesAt` computes it in
that order and `valuesAt_sound` proves the membership it yields.

$`y\approx_\Pi x`$ says $`\Pi`$ contains the equality $`x=y`$, or $`y`$ is $`x`$ itself. It
is deliberately not written as an entailment, because it is **one step and not
the transitive closure**: with $`x=y`$ and $`y=z`$ in $`\Pi`$, the relation holds of
$`y`$ and not of $`z`$ (`HeapLinks.aliases`). A write therefore propagates to the
directly recorded aliases only. That is sound — `aliases_eq` proves each one
denotes the same value — and incomplete, and the rules below say $`\approx_\Pi`$
rather than $`=`$ so as not to claim otherwise.

#### The reference operations

These four rules are the heart of the state discipline. Each is proved in
`HeapExpressionRules.lean`, and each is the postcondition the checker computes,
not one it assumes.

Each has an ordinary typing above the line and a Hoare typing below it, which is
the layering: $`\Gamma\vdash_G t:A`$ is the
[judgment of the ordinary rules](#judgments-and-constructor-views), `HasTyUsing`, and
it knows nothing about state; the conclusion adds what evaluating $`t`$ does to
$`\Pi`$ and $`\Sigma`$. So an operation is admitted only if it already types, and
these rules say what it then establishes. $`\mathrm{Ref}A`$ and
$`\mathsf{Null}`$ are [constructor views](#judgments-and-constructor-views): a type
whose labels expand to exactly that clause.

Here $`x`$ and $`y`$ range over variables, where the ordinary rules write $`a`$ for an
arbitrary term. A variable is a term, so each premise is an ordinary rule at a
special case and no kind is mismatched. The reason for the restriction is that
$`\Pi`$ and $`\Sigma`$ speak only about variables: $`x=R`$, $`x\mapsto y`$ and
$`z\approx_\Pi x`$ all name one. With an arbitrary operand the expression still
types and the operation still runs, but the postcondition would have nothing to
name, and the rule would degenerate into the catch-all below. Naming the operand
buys precision, not soundness.

$`r`$ is reserved throughout for the result of the operation being typed, and
never names one of its operands.

**Allocation** puts $`x`$'s value in a fresh cell and returns it, so the result is
a reference whose contents are whatever $`x`$ was known to equal. Nothing already
known is disturbed: a cell that did not exist cannot be one an existing atom
names, so all of $`\Sigma`$ survives.

```math
\frac{\Gamma\vdash_G\mathrm{alloc}(x):\mathrm{Ref}A
      \qquad(\Gamma;\Pi)(x)=R}
{\Gamma;\Pi;\Sigma\vdash_G r\leftarrow\mathrm{alloc}(x):\mathrm{Ref}A
  \dashv \Pi\;;\;\Sigma,\;r\mapsto R}
\qquad
\frac{\Gamma\vdash_G\mathrm{alloc}(x):\mathrm{Ref}A
      \qquad(\Gamma;\Pi)(x)\ \text{undefined}\qquad x\in\mathrm{dom}\Gamma}
{\Gamma;\Pi;\Sigma\vdash_G r\leftarrow\mathrm{alloc}(x):\mathrm{Ref}A
  \dashv \Pi\;;\;\Sigma}
```

Either way the fresh cell's field is a location distinct from every contract
field of every record-typed slot (the distinct links of `allocOutput`), whether
or not its contents are known: a cell holding an object keeps what is known of
the others, and a later write to either keeps what is known of the other.

**Reading** has two rules for the same term, and neither subsumes the other.

The first applies whenever the read types and $`x`$'s type is a plain reference. It
claims nothing about the contents; what it records is where the result came from,
$`r`$ now holding what the cell $`x`$ names holds — which is what a later test of $`r`$
needs in order to refine $`x`$ itself.

The second applies when $`\Sigma`$ already holds an atom for $`x`$ and the result type
is primitive. It consumes that atom and returns it as an equality on the result.
It needs no typing derivation: the atom and its premise establish the result type
between them, which is why its first premise is a membership in $`\Sigma`$ rather
than a judgment. Writing $`\mathrm{pred}(A)`$ for the primitive predicates a type
denotes — defined only when $`A`$ is primitive, so the premise also fails for a
reference or an arrow result:

```math
\frac{\Gamma\vdash_G\mathrm{read}(x):A\qquad\Gamma(x)=\mathrm{Ref}B}
{\Gamma;\Pi;\Sigma\vdash_G r\leftarrow\mathrm{read}(x):A
  \dashv \Pi\;;\;\Sigma,\{y\mapsto r\mid y\approx_\Pi x\}}
```

```math
\frac{(x\mapsto R)\in\Sigma\qquad R\subseteq\mathrm{pred}(A)}
{\Gamma;\Pi;\Sigma\vdash_G r\leftarrow\mathrm{read}(x):A
  \dashv \Pi,\;r=R\;;\;
   \Sigma,\{y\mapsto^{?} r\mid y\approx_\Pi x\}}
```

A read of a key some record of $`x`$'s type names only as optional has no
location to link where the object lacks the key; there the read gave
`undefined`, since such an object has no prototype (`optT`). Its link is the
optional one, $`x.f\mapsto^{?}r`$ ([its meaning](SEMANTICS.md#what-is-asserted-and-what-a-heap-change-can-touch)),
written for every record of $`\Gamma(x)`$ naming $`f`$, as a field or an optional
key (`optionalOperand`, `optionalRead_sound`):

```math
\frac{\Gamma\vdash_G\mathrm{read}_f(x):A\qquad
      \forall c\in\mathrm{expand}_G(\Gamma(x)).\ f\in\mathrm{fields}(c)\cup\mathrm{optional}(c)}
{\Gamma;\Pi;\Sigma\vdash_G r\leftarrow\mathrm{read}_f(x):A
  \dashv \Pi\;;\;\Sigma,\{y.f\mapsto^{?} r\mid y\approx_\Pi x\}}
```

Two programs show the difference. In the first,

```ts
const cell: { value: boolean } = { value: false };
cell.value = true;
return cell.value;
```

the allocation leaves $`\Sigma`$ holding $`\mathit{cell}\mapsto\{\mathsf{false}\}`$
and the write replaces it with $`\mathit{cell}\mapsto\{\mathsf{true}\}`$. At the
read that atom is present and the result type is `boolean`, whose constants
include $`\mathsf{true}`$, so the second rule applies and returns
$`r=\mathsf{true}`$ — a fact the wider claimed type does not carry, and enough for
a return contract demanding exactly $`\mathsf{true}`$.

In the second the same read follows a call:

```ts
const done: null = reset(false);
return cell.value;
```

The call empties $`\Sigma`$, so no atom for `cell` remains and only the first rule
applies: the read is well typed and records where its value came from, but
establishes nothing about the contents. Nothing about what `cell` holds is
provable at that point, whatever the claimed type says.

Each covers cases the other does not. Reading a $`\mathrm{Ref}(\mathrm{Ref}B)`$
has no primitive result, so only the first applies; a variable whose type is a
union of references does not meet the first rule's plain-reference premise, so
where an atom exists only the second does. Where both apply the second yields
strictly more, the evidence records which was used, and soundness does not depend
on the choice — only precision does.

**Writing** stores $`y`$'s value in the field $`f`$ of the object $`x`$ names. The
result is `null`. Where $`y`$'s value is a known primitive it establishes the new
contents for $`x`$ and every variable recorded equal to it; it keeps the atoms
about locations a distinct link $`z.g\neq x.f`$ separates from the written one;
it destroys the rest of $`\Sigma`$ — including atoms about cells that may or may
not be this one. Writing a value that is not a known primitive, an object say,
establishes no new contents and keeps the separated atoms all the same:

```math
\frac{\Gamma\vdash_G\mathrm{write}_f(x,y):\mathsf{Null}
      \qquad(\Gamma;\Pi)(y)=R}
{\Gamma;\Pi;\Sigma\vdash_G r\leftarrow\mathrm{write}_f(x,y):\mathsf{Null}
  \dashv \Pi,\;r=\mathsf{null}\;;\;
   \{z.f\mapsto R\mid z\approx_\Pi x\},\;\Sigma_{\neq x.f}}
\qquad
\frac{\Gamma\vdash_G\mathrm{write}_f(x,y):\mathsf{Null}
      \qquad(\Gamma;\Pi)(y)\ \text{undefined}}
{\Gamma;\Pi;\Sigma\vdash_G r\leftarrow\mathrm{write}_f(x,y):\mathsf{Null}
  \dashv \Pi,\;r=\mathsf{null}\;;\;\Sigma_{\neq x.f}}
```

where $`\Sigma_{\neq x.f}=\{z.g\mapsto S\in\Sigma\mid z.g\neq x.f\}`$ (`writeOutput`,
`write_sound`).

**Every other expression**, calls included, empties the heap part and leaves the
equalities untouched:

```math
\frac{\Gamma\vdash_G t:A}
{\Gamma;\Pi;\Sigma\vdash_G r\leftarrow t:A\dashv \Pi\;;\;\emptyset}
```

$`\Pi`$ and $`\Sigma`$ are finite lists of atoms, read as their conjunction and
extended with a comma, exactly as $`\Gamma`$ is. $`\emptyset`$ is the empty heap
part: nothing is known about any cell. $`\Pi`$ carries over verbatim, because no
equality mentions the heap. There is no separating conjunction here — these
facts are duplicable, and carry no ownership or disjointness.

The shape a type theorist will look for is missing on purpose: **there is no
general frame rule.** A write through $`x`$ discards what is known about $`z`$ even
when $`z`$ is a different name, because distinct names need not be distinct
locations — $`\Pi`$ can witness that two names are equal, never that they are
not. So the positive direction is proof-driven and the negative direction is
total but for one timeless fact, the distinct link $`z.g\neq x.f`$: two field
locations that differ whatever they hold (`HeapLinks.distinctFrom`,
`distinct_sound`). Allocation states it: a fresh object's locations differ
from every field each record of a record-typed slot names (`contractFields`).
The lowering restates, at each statement entry, the links between a private
cell the code allocated and the slots whose records' fields it was allocated
after, or that were allocated after it
([Source model](SOURCE-MODEL.md#current-content-assertions)); a cell a
closure captures was allocated before the closure's entry, which states no
fact of that allocation, so its body states none of these links.

The practical shape of the gap is worth stating. Facts about several cells
coexist freely: allocation and reads preserve every one of them, so a program
that allocates three cells knows the contents of all three. A write collapses
that set to the written cell, its aliases and the locations distinct links
separate from it, and a call empties it: a callee may write any location its
operands reach, and nothing states which locations those are. $`\Pi`$ is not subject to this at
all, which is why a value read out of a cell before a callback
remains usable after the callback has overwritten that cell.

Two consequences worth naming. Immutable value facts and slot equalities survive
every operation, because no write or call can falsify $`\rho(i)\in R`$ or
$`\rho(i)=\rho(j)`$ — those are statements about the environment, not the heap.
And a read link is what later lets an observation of the result refine the cell
it came from: that is how a guard on `cell.value` refines `cell` itself, and why
a call, which drops read links, ends such a refinement.

The implementation keeps $`\Pi`$ and $`\Sigma`$ in one `HeapKnowledge.Knowledge`;
write $`K`$ for that pair and $`K(\rho,h)`$ for the conjunction of everything in it.
A successful `checkStepUsing` is a derivation of this judgment, and `checkStep_sound`
is its soundness:

```math
\frac{\mathrm{checkStepUsing}(G,\mathit{images},(\Gamma,t,A),K,e)=\mathrm{some}(K')
\quad\mathrm{EnvOk}_G(\Gamma,\rho,n,W)\quad K(\rho,h)}
{\mathrm{SafePost}(⟦A⟧,
  \lambda(h',v).\,K'(v::\rho,h'),n,W,h,\mathrm{close}_{\rho}(t))}.
```

As above, the initial world must be admissible and the heap must satisfy it.
The checker binds evidence to the requested expression and type and checks scope.
It computes a guaranteed output, not an assumed postcondition:

| Evidence                             | Guaranteed output in the result-pushed frame                                                                                                                                                                                             |
| ------------------------------------ | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Pure value or variable copy          | Preserve facts and links; copies establish slot equality and duplicate existing facts. Literals establish their exact result even when their supplied type is wider. Lambda bodies require ordinary typing, without captured heap facts. |
| Pure test or conditional             | Preserve existing facts and links, shifted past the result slot. Every evaluated subexpression must be syntactically pure (a length `lenOf` of a slot among them: an array's store is read by a field read of its own, then counted); no new result-to-cell link is invented.                                                                       |
| Read (`reading`)                     | Field and element reads over values (`readAt`, `elemAt`, `readTerm`): check ordinary evidence and scope, and preserve every fact and link, shifted past the result slot. A read changes no location, and a heap meeting an admissible world holds values, so a read's result is a value. |
| Ordinary typed read                  | Preserve facts and record read links to the receiver and witnessed aliases, retaining its plain or callable descriptor; through a key a record may lack, optional links. No prior current-content fact is needed. Its result has the supplied type. |
| Observed read                        | Preserve facts and links; record the result's primitive predicate and its current read relationship. That set must fit the requested ordinary result type.                                                                               |
| Sliced read (`slicedRead`)           | A read whose cell fact excludes a nullish tag: ordinary read evidence at the location's contract $`C`$, whose negative slice by that tag is below the requested type by a checked subtype proof. As an ordinary typed read otherwise. |
| Known immutable value                | Check the requested primitive type against a proved slot fact or the slot's ordinary primitive type.                                                                                                                                     |
| Allocation                           | Check ordinary creation evidence and scope for either descriptor, preserve old facts, add the fresh bag's initial contents where a checked value slot's are known, and its fields' distinctness from every record slot's. Closure code is not executed. A merge of two slots is an allocation too: old facts preserved, the fields its result type names distinct. So is an array literal's store of value slots, whose element locations lie past the heap's end: old facts preserved (`store_alloc_sound`). |
| Write                                | Check ordinary write evidence (no old-content premise), discard old cell facts but those a distinct link separates from the written location, record new contents for the receiver and its witnessed aliases where the value is a known primitive, or its supported nullish exclusion, and preserve immutable facts and slot equalities. Read links are discarded. |
| Ordinary expression, including calls | Check ordinary evidence, discard cell facts and read links, preserving immutable facts and slot equalities.                                                                                                                              |

`typedRead_sound`, `slicedRead_sound`, `read_sound`, `reading_sound` (by
`read_frame`), `alloc_sound` (with `merge_alloc_sound` and
`store_alloc_sound`) and `write_sound` prove the read, allocation and write
rules above. The read rule is

```math
\frac{\Gamma\vdash_G t : A\quad \mathsf{reads}(t)}
     {\Gamma;\Pi;\Sigma\vdash_G r\leftarrow t : A\dashv\Pi;\Sigma}\ \textsf{read-frame}
```

where $`\mathsf{reads}(t)`$ holds of a term built from variables and values by
field reads and element reads. The sliced
read is

```math
\frac{\Gamma\vdash_G \mathsf{readAt}\,f\,x : C\quad x.f\mapsto R\in\Sigma\quad
      \forall v\in R.\;\tau(v)=\mathsf{false}\quad T_{\mathsf{false}}^{\tau}(C)\le A}
     {\Gamma;\Pi;\Sigma\vdash_G r\leftarrow \mathsf{readAt}\,f\,x : A\dashv\Pi;\Sigma}\ \textsf{read-sliced}
```

where the supported tags are tests for null, undefined and either nullish value.
The write rule takes no premise about the cell's old contents. These are operation rules within a
local segment: at the next statement entry, only the supplied interface
survives.

The `allocated` and `typedRead` evidence constructors serve both plain and
callable bags. `allocationSlots` selects a `make` whose initializers are
existing value slots; it never treats an effectful initializer as a value.
A typed read (`fieldOperand`) requires that every clause of the receiver's nonempty expansion is a `refs`
or `callable` whose first invariant operand has the field read, at any type,
so the read is of a location of the object whichever arm it has, and its link
names that location.
The same allocation proof frames old facts and records the fresh bag, and the
read proof records links with the object's actual descriptor.
Nested invocation uses the existing closure, let-binding and heap rules, with
no separate reentry mechanism. [ExecutionModelTests.lean](../lean/Verification/Tests/ExecutionModelTests.lean) runs the machine on these calls, for a
plain and a callable bag: a closure writes `true` into a captured bag after a
`false` read was saved, and the saved value stays `false` while a fresh read
gives `true`; an active function's callback mutates its bag and reenters it,
and the outer frame keeps its saved read; an initializer's write and
allocation precede the callable's allocation, and the argument's write
precedes the body's read, a stuck initializer blocking the argument and a
stuck argument the body. Under Node, `invalid-closure-graph-captured-cell`
returns the `null` its closure wrote, where the pipeline refuses its number
claim.

`pureTerm` includes values, variables, tests of pure terms, and conditionals
whose condition and both arms are pure. It excludes calls, reads, writes and
allocation, including function creation. A checked creation effect separately
preserves old facts while allocating the function's bag; the body may have
effects because creation does not run it. A pure step changes no existing
cell; an operator that throws appends its error's identity cell. `pure_step`
and `pure_frame` prove, with $`h\sqsubseteq h'`$ for $`h`$ a prefix of $`h'`$:

```math
\frac{\mathrm{Pure}(t)\quad(h,t)\longrightarrow(h',t')}
 {h\sqsubseteq h'\quad\land\quad\mathrm{Pure}(t')},
\qquad
\frac{\mathrm{Pure}(t)\quad\mathrm{Safe}(A,n,W,h,t)\quad\forall h'\sqsupseteq h.\,\forall v.\,Q(h',v)}
 {\mathrm{SafePost}(A,Q,n,W,h,t)}.
```

This extends the existing pure-effect evidence; it does not add another typing
rule or certificate constructor. It retains heap observations through null
predicates without treating an effectful operand as pure. A negated graph guard
checks its full expression claim separately and swaps the operand's successors;
it does not invent an equality between a Boolean and its negation.

Result predicates follow the [assertion grammar](POSITIVE-TYPES.md#state-assertion-grammar). `HeapKnowledge.check_sound`
justifies transfer along executable slot maps.

The maintained graph checker carries the same postconditions in its state
invariant and checks every incoming edge, including back edges. External entry
requires empty knowledge; effect-only continuations drop result-slot facts.
Source observations use the
same checked graph facts, through the checkpoints below.

Boolean guards use the following rule, proved by `observeBoolean_holds`:

```math
\frac{x\mapsto y\quad y=b}
 {x\mapsto\{b\}},\qquad b\in\{\mathsf{true},\mathsf{false}\}.
```

The points-to atom must hold in the current heap. Note that
$`\mathrm{read}(x)`$ is the language's read expression; the assertion that
used to share its name is now $`x\mapsto y`$. A tag observation does the same with
what it leaves of $`y`$'s predicate (`observeTag_holds`): each atom whose clause
answers the other way is dropped, and a family found equal to one of its
values is that value (`observeAtom`: `number` equal to a number other than a
zero is that number, `string` equal to a string is that string; equal to a
zero it stays `number`, the zeros being two values). An optional read link
gives the fact only where what remains rules `undefined` out, which then says
the key is present (`linkFacts_holds`):

```math
\frac{x.f\mapsto y\quad y=R}{x.f\mapsto R}
\qquad
\frac{x.f\mapsto^{?}y\quad y=R\quad \mathsf{undefined}\notin R}{x.f\mapsto R}
\qquad
\frac{y=\mathsf{number}\quad y\equiv b\quad b\neq\pm0}{y=\{b\}}
\qquad
\frac{y=\mathsf{string}\quad y\equiv s}{y=\{s\}}.
```
[ExecutionModelTests.lean](../lean/Verification/Tests/ExecutionModelTests.lean) compares `numberEqual` with IEEE equality on NaN, infinities and adjacent doubles.
A slot equality $`x=y`$ permits a checked write through either alias to
establish the new contents for both, as the
[write rule](#the-reference-operations) above states; every other cell
observation is discarded. Read links are invalidated by writes and calls, while
slot equalities survive. Together these let source lowering discard a receiver
temporary without losing a write to its original cell.

An allocate-false/write-true/read program verifies with an explicit
current-true claim at the return entry; a broad entry claim naming only the
storage contract is insufficient.

#### Source observation checkpoints

`SourceClaims.Function` retains ordinary types and separately indexed current
predicates. The OCaml producer supplies claims through this interface, keyed
by execution point and, for expressions, source span
([claim identities](SOURCE-CLAIMS.md#execution-graph-supplied-to-the-producer)). **Every source statement entry
is a full local interface**, including entries with no current predicates. The
compiler reconstructs its ordinary context $`\Gamma_l`$ and knowledge
$`K_l=(\Delta_l,\varnothing,\varnothing)`$, where $`\Delta_l`$ contains exactly the
supplied current predicates. No immutable-value facts or alias/read links are
implicitly carried across this boundary. Ordinary reference contracts remain in
$`\Gamma_l`$; the calculus always assumes environment and heap well-formedness.

For certificate input $`K_c`$, source acceptance requires:

```math
K_c=K_l.
```

`SourceExtraction.checkGraphAssertions` checks this equality.
Each incoming edge separately establishes the supplied heap interface (ordinary
context coverage is checked alongside it):

```math
\frac{\mathrm{checkKnowledge}(K_{\mathrm{out}},K_l,m)=\mathsf{true}
\qquad K_{\mathrm{out}}(\rho,h)}{K_l(\mathrm{mapEnv}(m,\rho),h)}.
```

The next statement is checked from $`(\Gamma_l,K_l)`$, independently of any
stronger facts proved by predecessors. Loop heads use the same interface on both
initial and back edges. Empty knowledge means forget all extra facts; an empty
_content predicate_ remains an impossible observation, not an absent one.

**Expression claims are local obligations within a statement, not full-state
interfaces.** Their supplied result type must be justified at the expression;
a supplied current predicate is checked at a no-op result checkpoint, naming
slot zero before projection, unless every contract of the read object already
implies it: then it is the persistent-observation obligation below, which
holds at any point, a closure's entry included, where nothing of the heap is
known. Within the statement, the checked effect rules may
retain its entry assumptions and derive postconditions. Calls and writes forget
facts according to those rules. Administrative copies do not discard facts.
Thus a Boolean read claim is compatible with locally proving a true result from
an explicit entry observation; it does not license recovering an observation
forgotten at an earlier statement boundary.

At an expression checkpoint, required knowledge is checked by entailment,
$`\mathrm{checkKnowledge}(K_c,K_r,\mathrm{id})=\mathsf{true}`$.
`HeapKnowledge.check_sound` proves the implication. The independent source consumer
reconstructs both kinds of boundary and checks them alongside graph acceptance
and supplemental expression proofs; these are not producer-selected policies.

Ordinary compositional expression proofs, including lambda bodies, do not carry
heap contexts. For a point assertion $`\mathrm{ObservedRef}(B,R)`$ there,
the adapter conservatively requires the ordinary sequent:

```math
x:B\ \vdash\ x:R.
```

Here $`x`$ is an arbitrary **stored value**, not the reference. This checks that
the invariant implies the observation uniformly. For a union of cell contracts,
$`B`$ is the union of their invariant contents, so every alternative must imply
the observation. Its proof is a supplemental
`heap-observation` obligation at the source site. It never assumes the heap at
closure creation remains unchanged. Consequently a narrower temporary observation
inside a closure may remain unproved even when it is valid locally; exploiting
such facts requires graph-backed closure bodies. The checkpoint integration does
not claim that extra precision.
