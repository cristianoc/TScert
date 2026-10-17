# Positive types

The types are *positive*: each is a formula over clauses built with union and
intersection only, never negation.

This document specifies the types the verifier uses: how a type graph is
written, what each type means, how conjunctions are normalized, which
subtyping rules hold, and how a subtyping certificate is checked. Lean proves
three things about them:

1. the meet of two clauses means the intersection of their meanings;
2. every subtyping rule is sound;
3. an inclusion the certificate checker accepts holds in the model.

The indexed model that gives the types their meaning is in
[SEMANTICS.md](SEMANTICS.md). How programs are typed with them is in
[PROGRAM-TYPING.md](PROGRAM-TYPING.md). [State assertions](#state-assertion-grammar),
which combine types with facts about the current heap, are a separate layer at
the end.

**Notation.** A meaning is a family $X_n(W,v)$: at level $n$ and world $W$,
value $v$ is a member. A lower level is a weaker observation; "below the
level" means at every $j<n$ ([Appel and McAllester 2001](REFERENCES.md#appel-and-mcallester-2001)). Throughout, $\Delta$ is a finite table of subtype
obligations, and $\Delta(A,B)$ says the pair $(A,B)$ is in it or that every
label of $A$ is a label of $B$: a type is within any type listing its labels,
which needs no row (`Rel`). Each section
ends with a "Lean:" line naming the definitions and theorems behind it.

## Types and clauses

A graph maps **labels** to bodies. A label names a whole type, never part of
one, and every operand inside a body is itself a type. So the syntax has two
levels. A **type** is a finite union of labels:

```math
A ::= \bot\mid i\mid A\lor A.
```

A **clause** constrains one value shape. A body is a positive formula over
clauses, and a **normal body** is a union of clauses:

```math
P ::= \bot\mid c\mid P\lor P\mid P\land P,
\qquad
N ::= \bot\mid c\mid N\lor N.
```

The clauses, with what each denotes:

| Clause | Denotes |
| --- | --- |
| `top` | every closed calculus value, including internal stores |
| `source` | every closed JavaScript primitive or object; excludes internal stores |
| `nul`, `undef` | exactly null; exactly undefined |
| `bool`, `boolLit b` | true or false; exactly $b$ |
| `num`, `numLit x` | any number; exactly the number with bit pattern $x$ |
| `str`, `strLit s` | any string; exactly $s$ |
| `bigint`, `bigintLit i` | any bigint; exactly the bigint $i\in\mathbb Z$ |
| `symbol`, `symbolLit n` | any symbol (an opaque identity); exactly the symbol $\mathsf{sym}(n)$ |
| `refs` | a plain object under record contracts, readonly views, optional fields and methods ([Records](#records)) |
| `dict` | a `refs` object whose present keys of each index's class (every string key, the canonical numeric ones, or every symbol key) also meet readonly and writable index contracts |
| `list` | an array under one or more tuple contracts ([Arrays](#arrays)) |
| `arrs` | a function meeting fixed and variadic call signatures ([Functions and classes](#functions-and-classes)) |
| `callable` | a function that is also an object with record contracts |
| `ctors` | a class meeting construct signatures |
| `pack` | no value: a family of argument lists ([Argument packs](#argument-packs)) |

The **shape** of a clause is the kind of value it admits: null, boolean,
plain object (`refs`, `dict`), function (`arrs`, `callable`), undefined,
number, string, array, bigint, symbol, class or argument list. A value has
exactly one shape; `top` and `source` each admit multiple shapes.

Singletons sit below their primitive: $\mathsf{boolLit}\,b\le\mathsf{bool}$,
$\mathsf{numLit}\,x\le\mathsf{num}$, $\mathsf{strLit}\,s\le\mathsf{str}$,
$\mathsf{bigintLit}\,i\le\mathsf{bigint}$,
$\mathsf{symbolLit}\,n\le\mathsf{symbol}$; two singletons of one primitive
meet only when equal, and a singleton meets its family at itself. A bigint's
identity is its integer, so every spelling of one (`16n`, `0x10n`, `1_6n`)
is one singleton. A symbol singleton's identity $n$ is the one a symbol key
$\mathsf{sym}(n)$ carries: the $n$-th `unique symbol` declaration the
declaration document lists, so the type of `Symbol.iterator` and the key
`[Symbol.iterator]` name one symbol.

```math
⟦\mathsf{symbolLit}\,n⟧_k(W,v)\iff v=\mathsf{sym}(n)
\qquad
\mathsf{symbolLit}\,n\sqcap\mathsf{symbol}=\mathsf{symbolLit}\,n
\qquad
\mathsf{symbolLit}\,m\sqcap\mathsf{symbolLit}\,n=
\begin{cases}\mathsf{symbolLit}\,n & m=n\\ \bot & m\ne n\end{cases}
```

Lean: `meet_sound` (the meets), `Covers.sound` (both subtypings).

Lean: `Clause`, `semWithArgs`, `shape`, `valueShape`
(`Types/PositiveNormalization.lean`).

### Records

A record operand maps **property keys** to types. A key is a string or a
symbol, and the two spaces are disjoint:

```math
\kappa ::= \mathsf{str}(s)\mid\mathsf{sym}(n),\qquad
\varphi ::= \overline{\kappa{:}A}.
```

A `refs` clause
$\mathsf{Ref}(\varphi_0\land\cdots\land\varphi_m;\,\psi;\,\omega;\,\mu;\,\beta)$ carries
invariant operands $\varphi_i$, readonly views $\psi$, optional fields
$\omega$, methods $\mu$ and own-key bounds $\beta$. An optional field
$\kappa{:}^{r}T$ carries a mode $r\in\{\mathsf{w},\mathsf{ro}\}$: writable or
readonly. Write $\ell$ for the object
$\mathsf{obj}(\mathit{flds},\mathsf{absent})$, $c_j\equiv T_j$ for "the
location's contract and $T$ agree below the level", $c_j\subseteq T_j$ for
"the contract implies $T$ below the level", and $c_j\sqsubseteq^{r}T_j$ for
$c_j\equiv T_j$ when $r=\mathsf{w}$ and $c_j\subseteq T_j$ when $r=\mathsf{ro}$
(`SlotContract`, as a tuple position's mode). Then

```math
\begin{aligned}
⟦\mathsf{Ref}(\vec\varphi;\psi;\omega;\mu;\beta)⟧_n(W,v)
&\iff \textstyle\bigwedge_i\mathsf{rec}(\varphi_i)\land
      \mathsf{view}(\psi)\land\mathsf{opt}(\omega)\land\mathsf{meth}(\mu)\land
      \bigwedge_{b\in\beta}\mathsf{own}(b),\\
\mathsf{own}(b)_n(W,v)&\iff v=\ell\land\forall\kappa\in\mathrm{dom}(\mathit{flds}).\;b\vDash\kappa,\\
\mathsf{rec}(\overline{\kappa{:}T})_n(W,v)
&\iff v=\ell\land\forall(\kappa{:}T).\;\exists l,c.\;
      \mathit{flds}(\kappa)=l\land W(l)=c\land c_j\equiv T_j,\\
\mathsf{view}(\overline{\kappa{:}T})_n(W,v)
&\iff\forall(\kappa{:}T).\;\mathsf{view}_1(\kappa{:}T)_n(W,v)\lor
      \kappa=\mathtt{length}\land\mathsf{len}(T)_n(W,v),\\
\mathsf{view}_1(\kappa{:}T)_n(W,v)
&\iff v=\ell\land\exists l,c.\;\mathit{flds}(\kappa)=l\land W(l)=c\land c_j\subseteq T_j,\\
\mathsf{len}(T)_n(W,v)
&\iff v=\ell\land\sigma\in\mathrm{dom}(\mathit{flds})\land
      \forall j<n.\;\forall b.\;\mathsf{num}(b)\in T_j,\\
\mathsf{opt}(\overline{\kappa{:}^{r}T})_n(W,v)
&\iff v=\ell\land\forall(\kappa{:}^{r}T).\;
      (\mathit{flds}(\kappa)=\varnothing\Rightarrow\mathit{flds}(\mathsf{proto})=\varnothing)\\
&\qquad\land\forall l.\;\mathit{flds}(\kappa)=l\Rightarrow\exists c.\;W(l)=c\land c_j\sqsubseteq^{r}T_j.
\end{aligned}
```

- **Invariant fields.** Every operand constrains the **same object**. Operands
  naming one key constrain one location, whose single stored contract agrees
  with each of them. They are not several cells, and they are not replaced by
  one contract at the intersection of their types. A plain reference cell is
  $\mathsf{Ref}\,\{\mathsf{value}{:}A\}$.
- **Views** only read: the location's contract implies the view's type, so a
  view grants no write.
- **`length`.** A view of `length` is also met by an object owning the array
  store key $\sigma$, when every number is of its type: an array's
  `length` is its store's length, which the store keeps, and `push` changes
  it (`arrayLenT`, `viewsT`). Every other view, and every view a rule reads
  as a location (an optional field's slot, a key's field, a merge's source),
  is one of a key other than `length`.
- **Optional fields** constrain a key only where the object has it: a
  writable one as an invariant field does, a readonly one (`readonly k?: T`)
  as a view does, so a readonly optional field is a view that may be absent.
  A read gives $T$ or undefined, so an object lacking an optional key has no
  prototype, whose members the read would otherwise reach. No rule writes one
  in place, since an object's keys are fixed at allocation; a write that may
  add the key copies a local's own object
  ([key-adding writes](PROGRAM-TYPING.md#key-adding-writes)).
- **Methods** are host-relative members: read from the object and invoked on
  it, they behave as typed
  ([SOURCE-MODEL](SOURCE-MODEL.md#method-members-are-host-relative)). A member $m$ has
  fixed signatures $(\vec P\to B)$ and variadic ones $(\vec P,\ldots Q)\to B$,
  none with a receiver, **quantified signatures**: types $S$, a generic
  method's scheme rows, that the member bound to its host meets, and the
  types $m.\mathsf{this}$ its host must meet (a `this` parameter's). With
  $\mathsf{bound}(u,v)$ the forwarding function `.bind` makes of $u$ and $v$,
  which invokes $u$ with $v$ whatever receiver it is given, and
  $\mathsf{on}_v(m)$ the invocable values meeting the member's signatures,
  each with receivers $\{v\}\cap\bigcap_{T\in m.\mathsf{this}}⟦T⟧_n(W)$
  (`hostIn`): $v$ as the one receiver it admits, where $v$ is in each type
  its host must meet, and no receiver otherwise; and bound to $v$ its schemes,

  $`u\in\mathsf{on}_v(m)_n(W)\iff u\in\mathsf{Calls}(m.\mathsf{calls}^{v})\cap \mathsf{Rests}(m.\mathsf{rests}^{v})\land \forall S\in m.\mathsf{schemes}.\;\mathsf{bound}(u,v)\in⟦S⟧_n(W),`$

  and $\mathsf{holds}_k(A)$ the objects holding key $k$ at a location whose
  contract implies $A$ below the level,

  $`\mathsf{holds}_k(A)_n(W,v)\iff\exists l,c.\; v=\ell\land\mathit{flds}(k)=l\land W(l)=c\land \forall j<n,\ U\sqsupseteq W|_j,\ u.\;c_j(U,u)\Rightarrow u\in A_j(U),`$

  a member is where JavaScript's lookup finds its key: on the object, or,
  when the object lacks the key, along its prototype chain, $d$ prototypes
  up (`along`):

  $`\begin{aligned} \mathsf{along}^0_k(A)&=\mathsf{holds}_k(A)\qquad \mathsf{along}^{d+1}_k(A)_n(W,v)\iff v=\ell\land k\notin\mathit{flds}\land \mathsf{holds}_{\mathsf{proto}}(\mathsf{along}^d_k(A))_n(W,v)\\ \mathsf{meth}(\mu)_n(W,v)&\iff\forall m\in\mu.\;\exists d.\; \mathsf{along}^d_{m.\mathsf{key}}(\mathsf{on}_v(m))_n(W,v). \end{aligned}`$

  A prototype's member is invoked on $v$, the object the read began at. A
  quantified signature is host-relative through binding: a scheme meets its
  signatures at every instantiation of its binders, and the bound function
  invokes the member with its host, so a scheme's own receivers say nothing of
  the host and admit every value. The
  implication is claimed only in worlds extending the current one: in an
  unrelated world the object's locations need not hold their contracts, and no
  method reading them could be safe.

- **Own-key bounds** say which keys the object may have. Records are open, so
  only a bound says a key is absent, and so that a read of it continues at
  the prototype. A bound $b$ is $\mathsf{among}\,K$, own keys among $K$, or
  $\mathsf{outside}\,N$, no own key in $N$; it **admits** a key accordingly,
  $\mathsf{among}\,K\vDash\kappa\iff\kappa\in K$ and
  $\mathsf{outside}\,N\vDash\kappa\iff\kappa\notin N$ (`KeyBound.admits`), and
  $\beta$ **excludes** $\kappa$, $\beta\nvDash\kappa$, when some $b\in\beta$
  does not admit it (`Excludes`). A fresh literal's own keys are among its
  fields'. An array owns no key its prototype provides,
  $\mathsf{outside}\,N$ with $N$ `ArrayProto`'s keys plus `constructor`: whatever else it owns,
  a read of one of those continues at the prototype, which it holds as a
  readonly view under the reserved key. An array may own further keys, as
  a library may mark the arrays it manages with a hidden symbol key
  ([SOURCE-MODEL](SOURCE-MODEL.md#arrays)). Keys are fixed at allocation,
  so a bound holds in every world.

A `dict` clause adds readonly **index contracts** $\overline{\theta{:}D}$,
each over a **key class** $\theta$ (`IndexKeys`): every string key
($\mathsf{strings}$, `[k: string]`), the canonical numeric keys
($\mathsf{numeric}$, `[k: number]`), or every symbol key ($\mathsf{symbols}$,
`[k: symbol]`). A canonical numeric key is a string some number's `ToString`
spells, the keys `o[n]` reaches for a number $n$
([SOURCE-MODEL](SOURCE-MODEL.md#index-signatures)):

```math
\mathsf{str}(s)\in\mathsf{strings},\qquad
\mathsf{str}(s)\in\mathsf{numeric}\iff\exists x.\;\mathsf{ToString}(x)=s,\qquad
\mathsf{sym}(i)\in\mathsf{symbols},
```

and nothing else: the string and symbol keys are disjoint. The object has no
prototype, and every present field under a key of $\theta$, named or not, has a
contract implying $D$. The object may lack a key, so an arbitrary indexed read
has type $D\mid\mathsf{undefined}$. It also adds **writable index contracts**
$\overline{\theta{:}C}$, a mutable index signature's: every present field
under a key of $\theta$ has a contract agreeing with $C$, as an invariant
field's does. A writable index is also listed among the readonly ones, which
is what reads use. An index over a union of key types is one per member. With
$\mathit{flds}(\mathsf{proto})=\varnothing$ in both,

```math
\begin{aligned}
\mathsf{dictView}(\theta,D)_n(W,v)&\iff v=\ell\land\forall k,l.\;\mathit{flds}(k)=l\land k\in\theta\Rightarrow
  \exists c.\;W(l)=c\land c_j\subseteq D_j,\\
\mathsf{dictCell}(\theta,C)_n(W,v)&\iff v=\ell\land\forall k,l.\;\mathit{flds}(k)=l\land k\in\theta\Rightarrow
  \exists c.\;W(l)=c\land c_j\equiv C_j.
\end{aligned}
```

A class is **within** another when it is it or is $\mathsf{numeric}$ within
$\mathsf{strings}$ (`IndexKeys.within`): then every key of the one is a key
of the other, and a view or writable contract over the larger class is one
over the smaller (`dictViewT_within`, `dictCellT_within`). Two classes
**overlap** when one is within the other. Deciding a key's class uses two
checked approximations of $\mathsf{numeric}$: a key *surely* in it is spelled
by a number found for it (`numericKey?`), and a key *may* be in it unless no
number spells it (`notNumericKey`, sound by `numberToString_shape`: every
number's spelling is `NaN`, an infinity, or begins with a digit or with `-`
and a digit).

The calculus adds no key to an existing object; a program adds one by
copying its own object ([key-adding writes](PROGRAM-TYPING.md#key-adding-writes)).
That TypeScript lets code holding a mutable dictionary add keys of its class
at $C$ is a trust assumption
([SOURCE-MODEL](SOURCE-MODEL.md#writable-string-index-signatures)); covering keeps
every type the object is met at true of it with such a key: no own-key bound
of a type covering a writable index says a key of its class is absent
($b\ \mathsf{keeps}\ \theta$ below). Index contracts are guarded through the world, so a
recursive graph can contain `JsonObject = { readonly [key: string]: Json | null }`.

Lean: `viewT`, `viewsT`, `arrayLenT`, `lengthKey`, `OptionalField`, `optT`, `SlotContract`, `NumericKey`, `IndexKeys`, `dictViewT`, `dictCellT`, `KeyBound`, `ownKeysT` (`Types/Types.lean`), `methodT`,
`memberT`, `along`, `holdsAt`, `onHost`, `boundTo`, `boundOn` (`Types/MethodMembers.lean`). The operands'
meaning `refsT` and its admissibility and congruence (`adm`, `congr_below`)
are in `Types/ReferenceConjunctions.lean`.

#### The built-in array invariant

A graph with arrays states its **built-ins** $\mathcal B$: the row of `ArrayProto`
($P_{\mathcal B}$), the row of `unknown` ($U_{\mathcal B}$, the nullary
`source` row) and the excluded keys ($N_{\mathcal B}$): `ArrayProto`'s
declared keys plus `constructor` and `then` (`NormalGraph.builtins`, set by
`builtinsOf` where the store has an array type). In such a graph a label's
record, dictionary or `source` clause means its members that are also arrays
of the built-ins where they own the store key $\sigma$
([SEMANTICS](SEMANTICS.md#the-array-invariant)):

```math
⟦c⟧^{\mathrm{row}}_n(W,v)\iff⟦c⟧_{\Xi}{}_n(W,v)\land
\bigl(c\ \text{a record, a dictionary or}\ \mathsf{source}\Rightarrow\mathsf{Arr}_{\mathcal B}{}_n(W,v)\bigr)
```

```math
\mathsf{Arr}_{\mathcal B}{}_n(W,v)\iff\forall\mathit{flds}.\;v=\mathsf{obj}(\mathit{flds},\mathsf{absent})\land\sigma\in\mathrm{dom}(\mathit{flds})\Rightarrow
\mathsf{view}(\sigma{:}\mathsf{Store}(⟦U_{\mathcal B}⟧),\mathsf{proto}{:}⟦P_{\mathcal B}⟧)_n(W,v)\land\mathsf{own}(\mathsf{outside}\,N_{\mathcal B})_n(W,v)
\land\mathsf{numericOwn}_n(W,\mathit{flds})
```

```math
\Xi_n(W,v)\iff v\in J\land\mathsf{Arr}_{\mathcal B}{}_n(W,v)
```

with $`\mathsf{Store}(U)`$ the possibly sparse stores of values of $`U`$
($`\mathsf{list}\langle;;U\rangle`$, readonly), $`\mathsf{numericOwn}`$ an
array's own fields at canonical numeric keys within every family its store's
contract stores ([SEMANTICS](SEMANTICS.md#the-array-invariant)), and $`\Xi`$, the built-ins'
`unknown`, the exception family the clause's function types are read with
(`builtinExc`; [throws](SEMANTICS.md#computations-and-recursive-types)). Only
the world is read, through the contracts of $\sigma$ and $\mathsf{proto}$, so
the invariant is admissible and read below the level (`arrayInvariant_adm`,
`arrayInvariant_congr`, `builtinExc_congr`). $P_{\mathcal B}$ and
$U_{\mathcal B}$ are read at one fixed assignment
(`ParameterInterpretation.builtinsAt`), so a row's meaning stays independent of
the graph's own assignment; `ArrayProto` reads no parameter row, and a rule
relating the invariant to a type checks that (`builtinsFree`), and that
$U_{\mathcal B}$ holds the `source` clause (`unknownTy`) or only it
(`exactUnknown`). Every other clause (`top`, primitives, functions, classes,
stores, packs) asks nothing more, its members being no plain objects but
`top`'s (`semWithArgs_not_plain`), and a graph stating no built-ins asks nothing.
Coverage keeps it (a record is covered by records only;
`source` covers JavaScript values, none `top`, `CoversWith.not_top`,
`builtinInvariant_of_member`), and so do meets (`meetLists_row`), renamings
(`builtinInvariant_map`) and instance images (`clauseImg_row`).

Lean: `ArrayBuiltins`, `builtinStoreT`, `arrayInvariant`, `builtinInvariant`,
`builtinExc`, `rowSem` (`Types/PositiveGraphs.lean`).

### Arrays

An array is a value $\mathsf{arr}(\vec l)$ over a list of element locations.
A `list` clause holds one or more **tuple contracts** $\tau$, each with
required positions $\vec R$, optional positions $\vec O$, an optional rest
$E$, a readonly flag, and a presence mode: **dense**, **readable**, or **sparse**.
Length bounds and required positions are independent of this mode. Each
present element has a location whose fixed contract agrees with its position's
type, or implies it for a readonly view. Every contract constrains the same store.

Writing $A_i$ for the family at position $i$, the additional presence condition is

```math
\begin{aligned}
\mathsf{Presence}_{\rm dense}(\tau,\vec\ell,j)
  &\iff \mathsf{none}\notin\vec\ell,\\
\mathsf{Presence}_{\rm sparse}(\tau,\vec\ell,j)&\iff\top,\\
\mathsf{Presence}_{\rm readable}(\tau,\vec\ell,j)
  &\iff\forall i.\;\vec\ell[i]=\mathsf{none}
       \Rightarrow\forall U\in\mathsf{World}_j.\;A_i(j,U,\mathsf{undefined}).
\end{aligned}
```

Thus the complete store interpretation at observation depth $k$ is

```math
\mathsf{List}_\tau(k,W,\mathsf{arr}(\vec\ell))
\iff \mathsf{Bounds}_\tau(\vec\ell)\land
\mathsf{RequiredPresent}_\tau(\vec\ell)\land
\mathsf{PresentContracts}_\tau(k,W,\vec\ell)\land
\forall j<k.\;\mathsf{Presence}_{\tau.\mathsf{presence}}(\tau,\vec\ell,j).
```

Presence is guarded at the same depth as element contracts, preserving the
contractiveness of recursive types. At depth zero there is no element observation;
physical density follows at every positive depth for a dense contract.

Source `T[]`, `Array<T>` and their readonly forms use **readable**. A hole is
therefore permitted by `unknown[]` or `(number | undefined)[]`, but not by
`number[]`. This definition uses the element family, so it commutes with generic
substitution. It is not a special case for the spelling `unknown`. Tuple source
syntax retains dense presence; its required positions always exist in every mode.
Fresh literals and spread copies can establish physical density. A native such as
unrestricted `map` can promise sparse storage without promising safe reads at its
result element type. Presence remains independent of readonly capability.

Lean: `listT`, `SlotContract` (`Types/Types.lean`).

### Functions and classes

A call signature is $(Q;\vec P)\to B$: a receiver $Q$, parameters $\vec P$ and
result $B$. It describes the calls a caller may write: invoked with a receiver
in $Q$ and actuals in $\vec P$ at every future world and satisfying heap below
the level, the function is safe at $B$. A call may pass fewer actuals when
the missing parameters admit undefined. A signature indifferent to its receiver has receiver `top`. A
variadic signature $(Q;\vec P,\ldots P')\to B$ takes the actuals past $\vec P$
as one [argument pack](#argument-packs) at $P'$.

- `arrs L S` is a function meeting every fixed signature in $L$ and every
  variadic one in $S$. With both lists empty it is any function with closed
  invocation code.
- `callable φ⃗ L S` is additionally a plain object under the invariant record
  operands $\vec\varphi$. It has no views, optional fields or methods.
- `ctors L S φ⃗ ψ` is a class, whose code is construct-only. A construct signature
  $\vec A\Rightarrow^{\varepsilon} B$ says that `new` with actuals in $\vec A$
  steps to a term safe at $B$ one level below, whose normal return meets the
  effect $\varepsilon$ from the heap the construction starts in, as a call
  signature's does; a variadic one takes a pack as its rest.
  Its property bag, its static fields, is under the invariant record operands
  $`\vec\varphi`$, as a callable object's is, and the readonly fields
  $`\psi`$, views; with none it states no field.

```math
⟦\mathsf{Ctors}\,\overline{(\vec A,B,\varepsilon)}⟧_k(W,v)
\iff\mathsf{Constructible}(v)\land\forall(\vec A,B,\varepsilon),\,j<k,\,
   U\sqsupseteq W|_j,\,\mathit{heap}\models_j U,\,\vec a\in\vec A.\;
\exists t.\;\mathsf{new}\,v(\vec a)\to t\land
   t\in\mathsf{Safe}_j(\varepsilon.\mathrm{result}(B,\vec a),\varepsilon.\mathrm{post}(\mathit{heap}))(U,\mathit{heap}),
```

```math
⟦\mathsf{Ctors}\,\overline{(\vec A,B,\varepsilon)}\,\vec\varphi\,\psi⟧_k(W,v)
\iff⟦\mathsf{Ctors}\,\overline{(\vec A,B,\varepsilon)}⟧_k(W,v)\land
   \forall\varphi\in\vec\varphi.\;\mathsf{bag}(\varphi)_k(W,v)\land\mathsf{views}(\psi)_k(W,v),
```

with $`\mathsf{bag}(\varphi)`$ the record $`\varphi`$ of the object's own fields
whatever its code (`bagT`), and $`\mathsf{views}(\psi)`$ its views
(`viewsT`). Two classes' meet is one class meeting both signature lists and
both bags (`meet_ctors`).

No class is callable and no function is constructible, so `ctors` meets
neither `arrs` nor `callable`. With no signature, `ctors [] []` is any class.
TypeScript's `Function` is the union of the two empty forms, a value with
closed invocation code or a class
([library types](SOURCE-CONTRACTS.md#library-types)):

```math
⟦\mathtt{Function}⟧_k(W,v)\iff
\mathsf{Invocable}(v)\lor\mathsf{Constructible}(v).
```

Every function and every class is covered by it, since
[coverage](#function-and-class-coverage) has no target signature to derive.

TypeScript's `object` adds the objects with no invocation code, the record
constraining no key, $\mathsf{Ref}(\varepsilon;\varepsilon;\varepsilon;\varepsilon;\varepsilon)$,
whose meaning is $v=\ell$ for some $\mathit{flds}$ (arrays and instances
included, their store and prototype being own keys it does not constrain);
and `{}` adds every primitive but `null` and `undefined`
([library types](SOURCE-CONTRACTS.md#library-types)):

```math
⟦\mathtt{object}⟧_k(W,v)\iff
\exists\mathit{flds}.\;v=\mathsf{obj}(\mathit{flds},\mathsf{absent})\lor⟦\mathtt{Function}⟧_k(W,v),
\qquad
⟦\{\}⟧=\mathtt{boolean}\cup\mathtt{number}\cup\mathtt{string}\cup\mathtt{bigint}\cup\mathtt{symbol}\cup⟦\mathtt{object}⟧.
```

A record, an array, a function or a class is covered by `object` by the
existing rules: a record by width, an array's `refs` shape by width, a
callable by an empty `arrs`, a class by an empty `ctors`.

Lean: `callsT`, `restsT` (`Semantics/Safety.lean`), `objectsT`, `propsT`
(`Types/CallableConjunctions.lean`), `ctorsT`, `ctorRestsT`, `ConstructsTo`.

### Argument packs

An **argument pack** type states which argument lists a rest parameter
admits. An argument list is not a runtime value: a `pack` clause has no value
members, and its meaning is a family of lists. It holds tuple contracts
$\tau_0,\ldots,\tau_m$ as `list` does, and $\mathsf{pos}_\tau(i)$ is the type
the contract states for index $i$: $R_i$, then $O_{i-|\vec R|}$, then $E$ past
both, if any. A list fits a contract when its length is within the bounds and
each value is, **at the current level**, a member at its position:

```math
\begin{aligned}
⟦\mathsf{Pack}(\tau_0\land\cdots\land\tau_m)⟧^{\mathsf{args}}_k(W,\vec v)
&\iff\textstyle\bigwedge_i\mathsf{fits}(\tau_i)_k(W,\vec v),\\
\mathsf{fits}(\tau)_k(W,\vec v)&\iff|\vec R|\le|\vec v|\ \land\
   (E=\varnothing\Rightarrow|\vec v|\le|\vec R|+|\vec O|)
   \land\ \forall i.\;\mathsf{pos}_\tau(i)=A\Rightarrow v_i\in A_k(W).
\end{aligned}
```

Grouping evaluated arguments is not an execution step, so membership is at the
level of the actuals. The call or constructor whose rest it is supplies the
guard, and allocating the rest array consumes a level. A type's argument lists
are those of its pack clauses, or a pack parameter's assigned list family
([Parameter and scheme rows](#parameter-and-scheme-rows)).

Lean: `clauseArguments`, `Tuple.position`, `ArgumentContracts.Fits`,
`graphArguments`.

## Parameter and scheme rows

A label is one of four kinds of **row**:

- a **clause row** means the union of its clauses;
- a **parameter row** means what the graph's assignment `env` gives it. The
  assignment is a mixed family over values and argument lists; a row's kind
  selects the component: values for a value binder, lists for a pack binder;
- a **scheme row** $(\vec p;\Sigma;\beta;\Sigma_\ldots)_\kappa$ means one function
  meeting its signatures at every reassignment of its binders $\vec p$, which
  are parameter rows, within their bounds $\beta$. Its kind $\kappa$ says
  whether the signatures are call signatures ($\kappa=\mathsf{call}$) or
  construct signatures ($\kappa=\mathsf{new}$, a generic constructor type,
  each signature an arrow's arguments and result), whose members are class
  values;
- a **meet row** $p\sqcap\vec q\sqcap\vec c$ means the values the assignment
  gives the value parameter row $p$, and each of the value parameter rows
  $\vec q$ (none, usually), that are also in the clauses $\vec c$: the
  intersection of a type parameter with ground types, `V & DepSafe`, or with
  other type parameters, `U ⊓ T` for a binder bounded by another,
  `U extends T`, whose clauses are then `T`'s, or every value.
  [Instances](#instances-of-a-scheme-row) give it its meaning at each
  instance, and [SOURCE-CONTRACTS](SOURCE-CONTRACTS.md#binders-met-with-ground-types) says how
  it is lowered. In an equation graph a part $`p`$ or $`q`$ may also be a
  scheme row, whose members the meet's are too
  ([RECURSIVE-EQUATIONS §2.2](RECURSIVE-EQUATIONS.md#22-meaning)).

With $\eta$ an assignment and
$⟦A⟧^\eta=\bigcup_{i\in A}⟦i⟧^\eta$, the
denotation is the guarded fixed point of

```math
⟦i⟧^\eta=
\begin{cases}
\eta(i) & i\ \text{a parameter row},\\[2pt]
\bigl\{\,v\;\bigm|\;\mathsf{Callee}_\kappa(v)\land\forall j\le n.\;\forall\vec X\in\mathcal D_s.\;
  \mathsf{Bounded}_j(\vec X)\Rightarrow
  v\in_j⟦\mathsf{body}_\kappa(\Sigma;\Sigma_\ldots)⟧^{\eta'},\
  \eta'=\eta[\vec p\mapsto\vec X]\,\bigr\}
  & i\ \text{a scheme row},\\[2pt]
\eta(p)\cap\textstyle\bigcap_{q\in\vec q}\eta(q)\cap\bigcup_{c\in\vec c}⟦c⟧^\eta & i\ \text{the meet row}\ p\sqcap\vec q\sqcap\vec c,\\[2pt]
\textstyle\bigcup_{c\in G(i)}⟦c⟧^\eta & i\ \text{a clause row},
\end{cases}
```

where the body is the call clause
$`\mathsf{body}_{\mathsf{call}}(\Sigma;\Sigma_\ldots)=\mathsf{arrs}(\Sigma;\Sigma_\ldots)`$ or the
construct clause
$`\mathsf{body}_{\mathsf{new}}(\Sigma;\Sigma_\ldots)=\mathsf{ctors}(\Sigma;\Sigma_\ldots)`$, each
signature read as its arguments and result (`SchemeRow.body`), read at
$`\eta'`$; $`\mathsf{Callee}_{\mathsf{call}}=\mathsf{Invocable}`$ (call code) and
$`\mathsf{Callee}_{\mathsf{new}}=\mathsf{Constructible}`$ (construct-only code); and $n$ is
the approximation level: $`v\in_j F`$ says $`v`$ is in $`F`$ at level $`j`$, in
the world truncated to $`j`$. $\vec X$ ranges over the assignments
$`\mathcal D_s`$ the graph's substitution domain admits for the scheme
(`SchemeDomain.allowed`): admissible mixed families, one per binder, which
for a resolution-qualified scheme also satisfy its descriptor relations
([implied bounds](SOURCE-CONTRACTS.md#implied-bounds)).
$\mathsf{Bounded}_j(\vec X)$ says each bounded binder's family is below its
bound, in both components, at every level under $j$, the bound read at the
scheme's own $\eta$. Quantifying over every level $`j\le n`$ makes the
meaning closed downward by construction, whatever the domain admits; the
domain need not be closed under restricting an assignment to its bounds. A variadic signature's rest may be a binder: a **pack
parameter**, instantiated at a pack type and bounded by one. A meet row reads
its parameter as a parameter row does and its clauses' operands under their
guards as a clause row does, so it keeps the fixed point contractive; a pack
parameter's value component is empty, so a meet row names a value one. A
scheme part is read by the scheme case at the meet's own level, in place of
$`\eta(p)`$: that is one unfolding, not a recursion, since a part is never a
meet row, and the scheme case reads its own operands under guards
(`partSemWithArgs`, `qLayer_part`).

Reading bounds below the level keeps the fixed point contractive; the
approximations are non-expansive in the assignment (`QInv`), which gives
admissibility. The type meanings are read at the graph's assignment:
$⟦A⟧_G=⟦A⟧^{G.\mathit{env}}$ for values
(`meaning`) and its list component for argument lists (`argMeaning`). No check
reads `env`, so every theorem proved for all graphs holds at every
reassignment; for the whole graph checker this is a theorem,
`Parametricity.accept_reassign`, and a generic body checked with its binders
as parameter rows is safe at every assignment of them
([Reynolds 1983](REFERENCES.md#reynolds-1983))
([CALLABLES](CALLABLES.md#overloads-polymorphism-and-binding)). A member of a scheme row meets each instance's signatures,
and a function meeting them at every instantiation is a member: both unfold
the definition of scheme membership.

Only clause rows have clauses. A type holding a parameter, scheme or meet row
has no expansion, so no rule that reads a clause (`Represents`, `Answers`, the
atoms of heap knowledge) applies to it. A meet row is below its parameter and
below its clauses; a covered pair reads it through its clauses
([covered pairs](#covered-pairs)), and instance tables relate it to other types, at
an instance of which it is a clause row.

Lean: `qDenoteWithArgs G (mixedParameters G)`, `Bounded`, `boundedSem`,
`SchemeDomain`, `instanceTWithArgs`,
`instanceRestsWithArgs`, `NormalGraph.meets`, `NormalGraph.plain_iff`
(`Types/PositiveGraphs.lean`); `mixedValues`, `mixedArgs`, `meaning`,
`argMeaning` (`Types/PositiveRules.lean`).

### Finite presentations of application-indexed graphs

The semantics above does not require finitely many labels. A finite set of
parameterized equations can present an infinite graph: unfolding `Pair<T>`
may refer to `Pair<[T, U]>` without first enumerating every later
application. The representation, its support, congruence and substitution
theorems, the equation instance-image checker and the rules still to be
built are specified in [RECURSIVE-EQUATIONS](RECURSIVE-EQUATIONS.md).

## Conjunction and normalization

Normalization rewrites a body into a normal body. It is disjunctive normal
form: it pushes $\land$ down through $\lor$ until every conjunction joins two
clauses,

```math
\begin{aligned}
\mathrm{nf}(\bot)&=\bot,&\mathrm{nf}(c)&=c,\\
\mathrm{nf}(P\lor Q)&=\mathrm{nf}(P)\lor\mathrm{nf}(Q),\\
\mathrm{nf}(P\land Q)&=\textstyle\bigvee\{\,c\land d\;\mid\;
   c\ \text{a clause of}\ \mathrm{nf}(P),\
   d\ \text{a clause of}\ \mathrm{nf}(Q)\,\}.
\end{aligned}
```

So everything reduces to the conjunction of two clauses:

- `top` is the unit: $\mathsf{top}\land c=c$.
- `source` meets `top` as `source`, a store or pack clause as bottom, and
  every other clause as that clause.
- Clauses of **different shapes** meet as $\bot$: no value has two shapes.
- **Primitives** follow their lattice: $c\land c=c$, a singleton meets its
  primitive as the singleton, and two different singletons meet as $\bot$.
- **Structured clauses of one shape concatenate their operands.** No
  computation is needed, since the result is again a clause:

```math
\begin{aligned}
\mathsf{Ref}(\varphi_0\,\vec\varphi;\psi;\omega;\mu;\beta)\land\mathsf{Ref}(\varphi'_0\,\vec\varphi';\psi';\omega';\mu';\beta')
 &=\mathsf{Ref}((\varphi_0\varphi'_0)\,\vec\varphi\,\vec\varphi';\psi\psi';\omega\omega';\mu\mu';\beta\beta'),\\
\mathsf{arrs}(L;S)\land\mathsf{arrs}(M;T)&=\mathsf{arrs}(LM;ST),\qquad
\mathsf{Ctors}\,L\land\mathsf{Ctors}\,M=\mathsf{Ctors}\,(LM),\\
\mathsf{List}\,\vec\tau\land\mathsf{List}\,\vec\tau'&=\mathsf{List}\,(\vec\tau\,\vec\tau'),\qquad
\mathsf{Pack}\,\vec\tau\land\mathsf{Pack}\,\vec\tau'=\mathsf{Pack}\,(\vec\tau\,\vec\tau').
\end{aligned}
```

  The two first invariant operands are joined into one. A value has one
  own-field map, so one operand naming the fields of two says exactly what
  the two say, $\mathsf{rec}(\varphi\varphi')=\mathsf{rec}\,\varphi\cap
  \mathsf{rec}\,\varphi'$ (`recT_append`, `flatten`); and the read rules find
  a named field in the first operand, so a meet's fields are read as a
  record's (`{ readonly a: boolean } & { readonly b: number }` reads `b`).
  `refs` with `dict` gives a `dict` holding both; two `dict` clauses also
  concatenate their index contracts. `callable` with `callable` concatenates
  record operands and signatures; `callable` with `arrs` adds the signatures
  and keeps the record operands.

Nothing is distributed through an operand or a result. This is structural, not
a choice: an operand is a type, already normal, so there is no formula below
to normalize. That is also why guardedness survives untouched. For example,

```math
\mathsf{Ref}\,A\land(\mathsf{Ref}\,B\lor\mathsf{nul})
\quad\longmapsto\quad\mathsf{Ref}\,A\land\mathsf{Ref}\,B.
```

Incompatible invariant contracts are kept, not replaced by $\bot$.
$\mathsf{Ref}\,\mathsf{nul}\land\mathsf{Ref}\,\mathsf{bool}$ has a member at
level zero, though none above; a nested analogue has a member at level one in
a satisfying cyclic heap. So rewriting such clauses to $\bot$ would be
unsound; these examples have no Lean proof.

A clause whose bounds exclude a key it says the object owns has no member at
any level: the key is at a location of the object, and no key of the object
is excluded. Such a clause is dropped from a meet (`Clause.consistent`,
`semWithArgs_consistent`):

```math
\mathsf{consistent}(\mathsf{Ref}(\vec\varphi;\psi;\omega;\mu;\beta))\iff
\forall\kappa\in\mathrm{dom}(\vec\varphi\,\psi).\;\forall b\in\beta.\;b\vDash\kappa,
\qquad
\mathrm{nf}(P\land Q)=\textstyle\bigvee\{\,e\in c\land d\;\mid\;\mathsf{consistent}(e)\,\},
```

and likewise for `dict`. So an array with an own `map`, `number[] & { map:
number }`, whose bound excludes the key its record operand names, normalizes
to $\bot$; an arm $\bot$ of a union adds nothing to it, and a type lowering
to $\bot$ as a whole is refused rather than verified vacuously; an array with a key no prototype member has, such as
`[number, number] & Managed`, is kept.

Lean: `meet`, `meet_sound`, `Clause.consistent`, `semWithArgs_consistent`,
`meetLists` (`Types/PositiveNormalization.lean`).

### Recursive normalization

A formula graph is normalized label by label, $\mathrm{nf}(G)(i)=\mathrm{nf}(G(i))$.
Labels occur only inside operands, so recursion stays guarded, nothing is
unfolded and no label is allocated. A finite graph stays finite, although DNF
can grow a body exponentially. That the normal form means the formula is
argued from the meet's soundness (`meet_sound`) and has no Lean proof.

The Lean consumer has no normalizer. The
[request grammar](REQUEST-PROTOCOL.md#request-fields) has no conjunction above
the clause level, so every graph reaching the consumer is normal by
construction.

## Subtyping

Subtyping is proved in three layers: **clause coverage** relates one source
clause to one target clause under a table $\Delta$; a **core** judgment checks
a whole table at once, which handles recursion; the **structural** rules add
union inclusion, transitivity and the scheme rules.

### Clause coverage

$\Delta;S\vdash c\sqsubseteq d$ says clause $c$ of source type $S$ is covered
by target clause $d$. Every clause is covered by `top`; every clause except `top` and `list` is
covered by `source` (`sourceClause_sound`). Identical primitives,
and a singleton by its primitive, are covered trivially; different shapes are
never covered. `dict` is covered by `dict`, and by `refs`, forgetting its
index contracts (below); `refs` covers `refs`, and `dict` through an own-key
bound (below). Write
$\Delta^{\pm}(A,B)$ for $\Delta(A,B)\land\Delta(B,A)$.

**Records.** With $\Phi=\varphi_0\cdots\varphi_m$ the source's invariant
operands, each target component is found in the source:

```math
\frac{\begin{array}{c}
\forall j,\,(\kappa{:}B)\in\varphi'_j.\;\exists(\kappa{:}A)\in\Phi.\;\Delta^{\pm}(A,B)\qquad
\forall(\kappa{:}B)\in\psi'.\;\exists(\kappa{:}A)\in\Phi\,\psi.\;\Delta(A,B)\;\lor\;
  \kappa=\mathtt{length}\land(\sigma{:}\_)\in\Phi\,\psi\land\mathbb N\subseteq B\\
\forall(\kappa{:}^{r'}B)\in\omega'.\;\mathsf{opt}_\Delta(\Phi;\psi;\omega;\beta)(\kappa{:}^{r'}B)\qquad
\Delta;S\vdash(\Phi\,\psi;\mu)\sqsubseteq_{\mathsf{meth}}\mu'\qquad
\forall b'\in\beta'.\;\beta\vdash b'
\end{array}}
{\Delta;S\vdash\mathsf{Ref}(\Phi;\psi;\omega;\mu;\beta)\sqsubseteq\mathsf{Ref}(\varphi'_0\cdots\varphi'_k;\psi';\omega';\mu';\beta')}
```

An invariant field needs an equivalent invariant field. A view is met by any
field whose type is within it, and a view of `length` whose type holds every
number by a source naming the array store (`numIn`): its object's `length`
is its store's. An optional field is met by a **slot** of the
source of the same key, an invariant field (mode $\mathsf{w}$), a view (mode
$\mathsf{ro}$) or an optional field (its own mode), whose type is within the
target's; a writable target also needs a writable slot of an equivalent type,
so no location is retyped. Or it is met by own-key bounds excluding both its
key and the prototype key: the object lacks the key and has no prototype, so a
read is `undefined`. With $\mathsf{slots}(\Phi;\psi;\omega)$ the source's
fields at $\mathsf{w}$, views at $\mathsf{ro}$ and optional fields,

```math
\mathsf{opt}_\Delta(\Phi;\psi;\omega;\beta)(\kappa{:}^{r'}B)\iff
\bigl(\exists(\kappa{:}^{r}A)\in\mathsf{slots}(\Phi;\psi;\omega).\;
  (r'=\mathsf{w}\Rightarrow r=\mathsf{w}\land\Delta(B,A))\land\Delta(A,B)\bigr)\lor
\beta\nvDash\kappa\land\beta\nvDash\mathsf{proto}.
```

Where the object lacks the key, only an optional slot or a bound allows it, and
each says the object has no prototype. A required field is never met by a view
or an optional field, since neither says the key is present. Fields the target
does not name are not compared: records are open, so a record that does not
name an optional field's key may hold it at any type and does not cover it.
A bounded target's bounds follow from the source's (`CoversBound`,
`CoversBounds`): every key the source's bounds let the object own, each target
bound admits. An $\mathsf{outside}$ target needs each of its keys excluded; an
$\mathsf{among}$ target needs a source $\mathsf{among}$ bound each of whose
keys the target lists or the source excludes:

```math
\beta\vdash\mathsf{outside}\,N'\iff\forall\kappa\in N'.\;\beta\nvDash\kappa,\qquad
\beta\vdash\mathsf{among}\,K'\iff\exists\,\mathsf{among}\,K\in\beta.\;
  \forall\kappa\in K.\;\kappa\in K'\lor\beta\nvDash\kappa.
```

So a fresh array object, own keys among its store and prototype, is an array,
own keys outside `ArrayProto`'s; and an array type is covered by another with
the same exclusion. A `dict` target also needs each readonly index contract within some source one over as many keys ($\theta'\sqsubseteq\theta$: `IndexKeys.within`), and each writable index contract equivalent to a writable source one over as many keys, so a mutable dictionary is invariant and a readonly one is never mutable. Code holding a writable index may add keys of its class at its contract (the trust boundary, [SOURCE-MODEL](SOURCE-MODEL.md#writable-string-index-signatures)), so a writable target's contract must also be within every source index and optional field over a key of its class ($\theta\between\theta'$: the classes overlap; $\theta'\ni_?\kappa$: the class may admit the key), and every source own-key bound must **keep** its class: say no key of it absent. A bound listing keys keeps none; one excluding keys keeps a class that may admit none of them but the model's own prototype and store keys, which no code adds as a property (`KeyBound.keeps`, `KeepsKeys`). A writable index whose contract no value meets ($\varnothing(C')$: plain rows of no clause, `Uninhabited`) takes no key, so it needs no kept bound:

```math
b\ \mathsf{keeps}\ \theta\iff b=\mathsf{outside}\,N\land
  \forall\kappa\in N.\;\kappa\in\{\mathsf{proto},\mathsf{store}\}\lor\theta\not\ni_?\kappa
```

```math
\frac{\begin{array}{c}
\Delta;S\vdash\mathsf{Ref}(\Phi;\psi;\omega;\mu;\beta)\sqsubseteq\mathsf{Ref}(\varphi';\psi';\omega';\mu';\beta')\qquad
      \forall(\theta'{:}D')\in\overline{D'}.\;\exists(\theta{:}D)\in\overline{D}.\;\theta'\sqsubseteq\theta\land\Delta(D,D')\\
      \forall(\theta'{:}C')\in\overline{C'}.\;\bigl(\exists(\theta{:}C)\in\overline{C}.\;\theta'\sqsubseteq\theta\land\Delta^{\pm}(C,C')\bigr)\land
      \bigl(\forall(\theta{:}D)\in\overline{D}.\;\theta\between\theta'\Rightarrow\Delta(C',D)\bigr)\land
      \bigl(\forall(\kappa{:}^{r}A)\in\omega.\;\theta'\ni_?\kappa\Rightarrow\Delta(C',A)\bigr)\land
      \bigl(\varnothing(C')\lor\forall b\in\beta.\;b\ \mathsf{keeps}\ \theta'\bigr)
\end{array}}
     {\Delta;S\vdash\mathsf{Dict}(\Phi;\psi;\overline{D};\overline{C};\omega;\mu;\beta)\sqsubseteq
      \mathsf{Dict}(\varphi';\psi';\overline{D'};\overline{C'};\omega';\mu';\beta')}
```

With the record rule, which meets a writable index only at an uninhabited
contract, every clause covering a writable index some value meets keeps its
class (`KeepsKeys`), so an object meeting it keeps its bounds when
code holding it at that index adds a key of the class, at a value meeting the
contract; this preservation has no Lean proof. A literal meant for a
writable dictionary is allocated at it, with no bound
([`allocDict`](PROGRAM-TYPING.md#judgments-and-constructor-views)); a merge's dictionary
result states only bounds that keep its writable classes
([`MergeClause`](PROGRAM-TYPING.md#allocation-from-parts)).

So `{ [k: string]: number }` is `{ [k: number]: number }`, mutable as it is,
while a mutable `{ [k: string]: S; [k: number]: N }` is not a mutable
`{ [k: string]: S }` unless $S\subseteq N$.

A dictionary is covered by a record whose members its own cover, as a
record's are; the record states no index, so the dictionary's index contracts
are forgotten. So `Serializable<Todo>`, a `Todo` whose every key holds `Json`,
is a `Todo`:

```math
\frac{\Delta;S\vdash\mathsf{Ref}(\Phi;\psi;\omega;\mu;\beta)\sqsubseteq\mathsf{Ref}(\varphi';\psi';\omega';\mu';\beta')}
     {\Delta;S\vdash\mathsf{Dict}(\Phi;\psi;\overline{D};\overline{C};\omega;\mu;\beta)\sqsubseteq
      \mathsf{Ref}(\varphi';\psi';\omega';\mu';\beta')}
```

A record covers a `dict` through an own-key bound (`CoversKeys`): its own
keys are among some $\mathsf{among}\,K\in\beta$, where $K$ lists no
prototype key, so the object has no prototype; and every key of $K$ that a
target index's class may admit ($\theta'\ni_?\kappa$, `IndexKeys.may`) is a
source field or view within that index view, and an invariant field
equivalent to that writable index. No other key exists, so this is what a
fresh literal, whose own keys are exactly its fields, needs to be a readonly
dictionary; a key no number spells, such as `name`, is not held to a number
index. It covers a writable index only at an uninhabited contract: code
holding one some value meets may add a key the bound says is absent, so a
literal meant for a writable dictionary is allocated at it
([`allocDict`](PROGRAM-TYPING.md#judgments-and-constructor-views)). The named
members are compared as a record's:

```math
\frac{\begin{array}{c}
\Delta;S\vdash\mathsf{Ref}(\Phi;\psi;\omega;\mu;\beta)\sqsubseteq\mathsf{Ref}(\varphi';\psi';\omega';\mu';\beta')\qquad
\mathsf{among}\,K\in\beta\qquad\mathsf{proto}\notin K\\
\forall\kappa\in K.\;\bigl(\forall(\theta'{:}D')\in\overline{D'}.\;\theta'\ni_?\kappa\Rightarrow\exists(\kappa{:}A)\in\Phi\,\psi.\;\Delta(A,D')\bigr)\land
\bigl(\forall(\theta'{:}C')\in\overline{C'}.\;\theta'\ni_?\kappa\Rightarrow\exists(\kappa{:}A)\in\Phi.\;\Delta^{\pm}(A,C')\bigr)\\
\forall(\theta'{:}C')\in\overline{C'}.\;\varnothing(C')
\end{array}}
{\Delta;S\vdash\mathsf{Ref}(\Phi;\psi;\omega;\mu;\beta)\sqsubseteq
      \mathsf{Dict}(\varphi';\psi';\overline{D'};\overline{C'};\omega';\mu';\beta')}
```

A record without such a bound, or whose bound admits a key it does not
name, may hold further keys at any type, and covers no index; so does an
array, whose bound only excludes keys.

**Methods.** A target method $m$ is covered by a source method of the same
key, by a function the source holds under that key whose receiver the source
type $S$ is within, or a type $m$'s host must meet, or, when a key bound of
the source excludes the key, by such a function along its prototype chain.
With $\Delta(S\mid m,Q_0)$ for $\Delta(S,Q_0)\lor\exists T\in m.\mathsf{this}.\;\Delta(T,Q_0)$,
the host, which is in $S$ and in each of $m.\mathsf{this}$, is in $Q_0$. A
quantified signature is covered by one of the source member's, the two
related as types: both are met by the same bound function, so the coverage of
two schemes is subtyping between them (below,
[quantified signatures](#covered-pairs)). Each type the source member's host
must meet is within one the target's must, so a host of the target member is
one of the source's:

```math
\frac{\begin{array}{c}m'\in\mu\quad m'.\mathsf{key}=m.\mathsf{key}\quad
      \forall(\vec Q\to D)\in m.\;\exists(\vec P\to B)\in m'.\;\Delta(\vec Q,\vec P)\land\Delta(B,D)\\
      \forall S'\in m.\mathsf{schemes}.\;\exists S\in m'.\mathsf{schemes}.\;\Delta(S,S')\quad
      \forall T\in m'.\mathsf{this}.\;\exists T'\in m.\mathsf{this}.\;\Delta(T',T)\end{array}}
     {\Delta;S\vdash(\Phi\,\psi;\mu)\sqsubseteq_{\mathsf{meth}}m}
```

```math
\frac{(m.\mathsf{key}{:}F)\in\Phi\,\psi\quad F\equiv\mathsf{arrs}(L;\ldots)\quad
      \forall(\vec Q\to D)\in m.\;\exists(Q_0;\vec P)\to B\in L.\;
      \Delta(S\mid m,Q_0)\land\Delta(\vec Q,\vec P)\land\Delta(B,D)}
     {\Delta;S\vdash(\Phi\,\psi;\mu)\sqsubseteq_{\mathsf{meth}}m}
```

```math
\frac{\beta\nvDash m.\mathsf{key}\quad(\mathsf{proto}{:}P)\in\Phi\,\psi\quad
      \Delta;\kappa;S\vdash P\ni^{d}_{\mathsf{proto}}m\quad d\le 16}
     {\Delta;\kappa;S\vdash(\Phi\,\psi;\mu;\beta)\sqsubseteq_{\mathsf{meth}}m}
```

The third reads the member through the prototype chain, as the meaning does
(`CoversByProto`, `ProtoHolds`). The function covers a member stating no
quantified signature as an arrow type (below), and one stating only
quantified signatures as a **scheme received by the host**
(`CoversByScheme`): a scheme row $F=(\vec p;\Sigma;\beta;\Sigma_\ldots)$, a
class's generic method its prototype holds, whose receivers the source type
$S$ is within and read none of its binders ($\vec p\cap\mathit{fv}(Q_0)=\varnothing$, a checked free map), and
whose signatures cover, receivers aside, each of the target's schemes read at
$F$'s binders ($\mathsf{Binds}$, `SchemeBinds`):

```math
\frac{\begin{array}{c}F=(\vec p;\Sigma;\beta;\Sigma_\ldots)\quad
      \forall(Q_0;\vec P)\to B\in\Sigma\,\Sigma_\ldots.\;\Delta(S,Q_0)\land\vec p\cap\mathit{fv}(Q_0)=\varnothing\\
      \forall[j]\in m.\mathsf{schemes}.\;j=(\vec q;\Sigma';\beta';\Sigma'_\ldots)\land\mathsf{Binds}_\rho(F,j)\land
      \forall(\_;\vec Q)\to D\in\Sigma'\rho.\;\exists(\_;\vec P)\to B\in\Sigma.\;\Delta(\vec Q,\vec P)\land\Delta(B,D)\end{array}}
     {\Delta;\kappa;S\vdash F\ni_{\mathsf{fn}}m}
```

$\mathsf{Binds}_\rho(F,j)$ holds in two ways. The target binds the same rows,
$\vec q=\vec p$, with $\beta\subseteq\beta'$ and $\rho$ the identity. Or, up
to renaming ([RECURSIVE-EQUATIONS §4.1](RECURSIVE-EQUATIONS.md#41-quantified-signatures)),
$\rho=[\vec p/\vec q]$ is the checker's own substitution, $\vec p$ and
$\vec q$ are distinct rows, as many, of pairwise equal kinds, each bound
$(p_i,B)\in\beta$ has a bound $(q_i,B')\in\beta'$ with $\Delta(B',B)$, and
no $p_i$ is free in $\Sigma'\,\Sigma'_\ldots$ but as a $q_k$. A class's
generic method is the second case: its closure's scheme and the instance
type's member bind rows of their own.

At an instance $\vec X$ the host is in each receiver at the instance's
assignment, which it reads as the table's, so `.bind`'s forwarding function,
invoked with any receiver, meets the source signature, and the target's by
the premises read at the instance (`bound_sigs_sound`). Renamed, the target's
signatures under $\rho$ mean at the instance of $\vec p$ what the target's
mean at the same instance of $\vec q$ (`renamed_meaning`), and the target's
bounds at that instance give the source's, through $\Delta(B',B)$
(`covers_by_scheme_sound`). A prototype type $P$ holds $m$ where its
one record clause has $m$'s key at a function type covering it, or, where
that clause's key bound $\beta_P$ excludes the key, its own prototype field
does, one prototype further up (`lacksKey`):

```math
\frac{(m.\mathsf{key}{:}F)\ \text{a field or view of}\ P\quad \Delta;\kappa;S\vdash F\ni_{\mathsf{fn}}m}
     {\Delta;\kappa;S\vdash P\ni^{d}_{\mathsf{proto}}m}
\qquad
\frac{P\equiv\mathsf{Ref}(\Phi_P;\psi_P;\omega_P;\mu_P;\beta_P)\quad\beta_P\nvDash m.\mathsf{key}\quad
      (\mathsf{proto}{:}P')\ \text{a field or view of}\ P\quad \Delta;\kappa;S\vdash P'\ni^{d}_{\mathsf{proto}}m}
     {\Delta;\kappa;S\vdash P\ni^{d+1}_{\mathsf{proto}}m}
```

The function type $F$ covers $m$ in two ways (`FoundOn`). It is a **known
row** $(F,L,M)$ of $\kappa$: a row $F$ whose values meet the arrows $L$, $M$,
proved outside the table. For an array, $F$ is a generic member of
`ArrayProto` and $L$ its instance at the array's element type, with the array
as receiver: `Array.prototype[Symbol.iterator]` at `number` covers
`Iterable<number>`'s member. Or it is an arrow type, as for the second rule:
a class instance's methods are its prototype chain's closures, whose
receiver is the class's instance type, or the type a `this` parameter states,
which the instance type's member states its host must meet
([classes](SOURCE-CONTRACTS.md#classes)). Each premise that names $\kappa$ passes it on unchanged:

```math
\frac{(F,L,M)\in\kappa\quad
      \forall(\vec Q\to D)\in m.\;\exists(Q_0;\vec P)\to B\in L.\;
      \Delta(S\mid m,Q_0)\land\Delta(\vec Q,\vec P)\land\Delta(B,D)}
     {\Delta;\kappa;S\vdash F\ni_{\mathsf{fn}}m}
\qquad
\frac{F\equiv\mathsf{arrs}(L;\ldots)\quad
      \forall(\vec Q\to D)\in m.\;\exists(Q_0;\vec P)\to B\in L.\;
      \Delta(S\mid m,Q_0)\land\Delta(\vec Q,\vec P)\land\Delta(B,D)}
     {\Delta;\kappa;S\vdash F\ni_{\mathsf{fn}}m}
```

The depth bound only limits completeness: a method more than 16 prototypes
up is not found, never wrongly admitted. The rule is sound because the
meaning's $\mathsf{along}^{d+1}$ is what the premises state of every member
of the source, one prototype location at a time (`protoHolds_sound`).

Here $\Delta(\vec Q,\vec P)$ pairs the lists position by position and needs
equal lengths (`Domains`). Receivers of two members are not compared: both
are the host; the types their hosts must meet are contravariant, as above.
Variadic member signatures are covered likewise, the target's extra fixed
parameters taken into the source's rest.

**Arrays and packs.** A writable `list` target contract is covered by a
writable source contract with as many required and optional positions, each
position equivalent to the target's (`CoversShape`): no location is retyped,
so mutable arrays are invariant. A readonly target only reads each element
present at its position's type, so it is covered as a pack is, below
(`CoversTuple`): an element's location has the contract of its source
position, which reads within the target position's type, and the list's
length lies within the target's bounds. Both store rules additionally require
$\mathsf{PresenceCovers}(\Delta,\tau,\tau')$ (`CoversPresence`): dense covers
all modes; every mode covers sparse; readable covers readable by the element
coverage; sparse covers readable when each target position admits `undefined`;
readable covers dense when every source position excludes `undefined`.
The last two are checked conservatively from actual clause rows. A rigid
parameter is never mistaken for an empty type. Argument packs hold values
and have no holes, so presence has no effect on their interpretation:

```math
\frac{\mathsf{PresenceCovers}(\Delta,\tau,\tau')\quad\tau'\ \text{writable}\quad\tau\ \text{writable}\quad|\vec R|=|\vec R'|\quad|\vec O|=|\vec O'|\quad
      \forall i.\;\Delta^{\pm}(\mathsf{pos}_\tau(i),\mathsf{pos}_{\tau'}(i))}
     {\Delta\vdash\tau\sqsubseteq_{\mathsf{list}}\tau'}
\qquad
\frac{\mathsf{PresenceCovers}(\Delta,\tau,\tau')\quad\tau'\ \text{readonly}\quad\Delta\vdash\tau\sqsubseteq_{\mathsf{pack}}\tau'}
     {\Delta\vdash\tau\sqsubseteq_{\mathsf{list}}\tau'}
```

So `[number, number]` is a `readonly (Json | null)[]`, and meets `Json`
(`collections-tuple-value.ts`, `tuple-readonly-array.ts`), while it is not a
`number[]`, which TypeScript accepts though a write through it could append
past the tuple (`invalid-tuple-array.ts`).

A pack contract $\tau$ is covered by $\tau'$ when $\tau'$ admits every list
$\tau$ admits: the target requires no more positions; a target without a rest bounds the source's length;
and each source position's type is within the target's, covariantly, since a
pack holds values, not locations. Past both contracts' fixed positions every
index reads the rests, so the positions up to
$N=\max(|\vec R|+|\vec O|,\,|\vec R'|+|\vec O'|)$ decide all:

```math
\frac{\begin{array}{c}
|\vec R'|\le|\vec R|\qquad
E'=\varnothing\Rightarrow E=\varnothing\land|\vec R|+|\vec O|\le|\vec R'|+|\vec O'|\\
\forall i\le N.\;\mathsf{pos}_\tau(i)=A\Rightarrow\exists B.\;\mathsf{pos}_{\tau'}(i)=B\land\Delta(A,B)
\end{array}}
{\Delta\vdash\tau\sqsubseteq_{\mathsf{pack}}\tau'}
\qquad
\frac{\forall\tau'\in\vec\tau'.\;\exists\tau\in\vec\tau.\;\Delta\vdash\tau\sqsubseteq_{\mathsf{pack}}\tau'}
     {\Delta\vdash\mathsf{Pack}\,\vec\tau\sqsubseteq\mathsf{Pack}\,\vec\tau'}
```

So `[number, string]` is within `(number | string)[]` and `[number]` within
`[number, string?]`, while `number[]` is within no bounded tuple.

Lean: `CoversFields`, `CoversViews`, `numIn`, `covers_views_sound`, `optionalSources`, `Excludes`, `CoversOptional`, `CoversKeys`, `covers_keys_sound`, `KeyBound.keeps`, `KeepsKeys`, `Uninhabited`, `CoversMethods`, `CoversBound`, `CoversBounds`,
`CoversSig`, `CoversByFunction`, `CoversShape`, `CoversTuple`, `CoversPack`,
`covers_readonly_sound`, `covers_tuple_sound`.

### Function and class coverage

`arrs` is covered by `arrs`, and `callable` by `arrs` (forgetting its record
operands) or by `callable` (covering the operands as invariant fields). The
reverse, from `arrs` to `callable`, needs evidence of the record operands and
has no rule.

Each target fixed signature $(Q;\vec C)\to D$ must be **derived** from the
source's signatures $L$ and variadic signatures $S$ by the judgment
$\Delta;L,S\vdash(Q;\vec C)\Rightarrow D$:

```math
\frac{(Q_0;\vec A)\to B\in L\quad\Delta(Q,Q_0)\quad\Delta(\vec C,\vec A)\quad
      (B=\bot\lor\Delta(B,D))}
     {\Delta;L,S\vdash(Q;\vec C)\Rightarrow D}\ \textsf{source}
\qquad
\frac{s\in S\ \text{takes}\ (Q;\vec C)\ \text{into its rest, result within}\ D}
     {\Delta;L,S\vdash(Q;\vec C)\Rightarrow D}\ \textsf{rest}
```

```math
\frac{}{\Delta;L,S\vdash(\bot;\vec C)\Rightarrow D}\ \textsf{emptyRecv}
\qquad
\frac{\bot\in\vec C}{\Delta;L,S\vdash(Q;\vec C)\Rightarrow D}\ \textsf{empty}
```

```math
\frac{\Delta;L,S\vdash(Q;\vec C\,A\,\vec C')\Rightarrow D\quad
      \Delta;L,S\vdash(Q;\vec C\,A'\,\vec C')\Rightarrow D}
     {\Delta;L,S\vdash(Q;\vec C\,(A\lor A')\,\vec C')\Rightarrow D}\ \textsf{union}
\qquad
\frac{\Delta;L,S\vdash(Q;\vec C)\Rightarrow D\quad\Delta;L,S\vdash(Q';\vec C)\Rightarrow D}
     {\Delta;L,S\vdash(Q\lor Q';\vec C)\Rightarrow D}\ \textsf{recvUnion}
```

```math
\frac{\Delta;L,S\vdash(Q;\vec C)\Rightarrow B\quad\Delta;L,S\vdash(Q;\vec C)\Rightarrow B'\quad
      \forall i\in B,k\in B'.\;\mathsf{compatible}_G(i,k)\Rightarrow\Delta(\{i\},D)}
     {\Delta;L,S\vdash(Q;\vec C)\Rightarrow D}\ \textsf{combine}
```

`union` splits one parameter's union, `recvUnion` the receiver's. `combine`
uses two source signatures at once: the call's result meets both results, so
it is in some label $i$ of $B$ and some label $k$ of $B'$ that can share a
value. $\mathsf{compatible}_G(i,k)$ holds when some clause of $i$ and some
clause of $k$ have the same shape, or either has `top` or is not a clause
row. It is sufficient, not an exact test of joint inhabitation, and repeated
combination can use any number of source signatures.

Each target variadic signature is covered by a source variadic signature with
a receiver at least as wide, fixed parameters at least as wide (the target's
extra ones taken into the source's rest), a rest at least as wide and a result
at most as wide; or by a fixed source signature when the target's rest is one
**exact tuple** $\mathsf{Pack}(\vec E)$, with no optional position and no
rest. An exact tuple holds its actuals at their positions at the current
level, so they are at the fixed signature's parameters whatever the
positions' types:

```math
\frac{Q'=\mathsf{Pack}(\vec E)\ \text{exact}\quad\Delta(Q,Q_0)\quad
      \Delta(\vec C\vec E,\vec A)\quad\Delta(B,D)}
     {\Delta\vdash(Q_0;\vec A)\to B\ \sqsubseteq\ (Q;\vec C,\ldots Q')\to D}
```

**Classes.** A construct signature $\vec C\Rightarrow^{\varepsilon'} D$ is
covered by a source one $\vec A\Rightarrow^{\varepsilon} B$ with
$\Delta(\vec C,\vec A)$, $\Delta(B,D)$ and $\varepsilon\succeq\varepsilon'$,
the source effect guaranteeing the target's (`Effect.covers`). One with a
`never` parameter admits no actual list, so its promise is vacuous and any
class meets it; the results and effects are still compared, the results as
TypeScript compares them. This is how `ResourceClass<C, never>` holds a class
whatever its constructor takes (`ArgsT_mem`):

```math
\frac{(\vec A\Rightarrow^{\varepsilon} B)\in L\quad\Delta(\vec C,\vec A)\ \lor\ \bot\in\vec C\quad\Delta(B,D)\quad
      \varepsilon\succeq\varepsilon'}
     {\Delta\vdash\mathsf{Ctors}(L)\sqsubseteq(\vec C\Rightarrow^{\varepsilon'} D)}
```

A target's static field is a source field of the same name, covered both
ways, as a callable object's bag field is (`covers_bags_sound`):

```math
\frac{\forall(f{:}D)\in\vec\varphi'.\;\exists(f{:}A)\in\vec\varphi.\;\Delta(A,D)\land\Delta(D,A)
      \qquad\forall(f{:}D)\in\psi'.\;\exists(f{:}A)\in\vec\varphi\,\psi.\;\Delta(A,D)}
     {\Delta\vdash\mathsf{bag}(\vec\varphi;\psi)\sqsubseteq\mathsf{bag}(\vec\varphi';\psi')}
```

A target's readonly static field is a source field or view within it
(`covers_bag_views_sound`).
A variadic one is covered by a variadic source one with as many fixed
parameters, each at least as wide, a rest at least as wide, a result at most as
wide and an effect guaranteeing its own, or, when its rest is an exact tuple, by
a fixed one as above. So a class
taking a number meets `new (...params: [number]) => M`.

Lean: `CallArrow`, `CallArrow.sound`, `Domains`, `RestFixed`, `RestCovers`,
`FixedCallsPack`, `FixedCoversPack`, `mixed_pack_exact`, `fits_exact`,
`compatible`.

### Covered pairs

Subtyping is decided by the algorithm of
[RECURSIVE-EQUATIONS §4](RECURSIVE-EQUATIONS.md#4-subtyping): the premise
judgment on the pair, and otherwise the pairs reachable from it, each
covered with premises read in their table. A pair $(A,B)$ of a table $\Delta$
is **covered** when it satisfies three conditions:

1. **Same kind.** $A$ and $B$ are both value types or both argument-list
   types. A pack clause has argument kind, every other clause and every scheme
   has value kind, a parameter keeps its declared kind, and the empty type has
   either. So value `top` cannot discharge a pack edge, even though a pack's
   value meaning is empty.
2. **Opaque rows.** Every parameter or scheme row of $A$ appears in $B$, or
   $B$ holds `top`; a meet row of $A$ may instead be below a row of $B$ by its
   parameters, or be covered through its clauses, and one with a scheme part
   may be read through any one part; any of these rows may be below a meet
   row of $B$ read part by part; a scheme row of $A$ may instead have its
   quantified signatures covered by a scheme row of $B$.
3. **Coverage.** Every split part of every clause of $A$ is covered by some
   clause of $B$, with $A$ as the source type; so is every split part of the
   clauses of each meet row of $A$ without a scheme part that $B$ does not
   name.

```math
\frac{\mathsf{SameKind}(A,B)\qquad\mathsf{Opaque}(A,B)\qquad
      \forall a\in\mathsf{split}(\mathsf{cl}_G(A)\mathbin{+\!\!+}\mathsf{mcl}_G(A,B)).\;\exists b\in\mathsf{cl}_G(B).\;
      \Delta;\kappa;A\vdash a\sqsubseteq b}
     {\Delta;\kappa\vdash(A,B)\ \mathsf{covered}}
```

Here $\mathsf{cl}_G(A)$ lists the clauses of $A$'s clause rows, and
$\mathsf{mcl}_G(A,B)$ the clauses $\vec c$ of each meet row $p\sqcap\vec c$ of
$A$ not in $B$, with no scheme part and below no row of $B$ by its parameters
(`meetSources`). A
member of $p\sqcap\vec c$ is in one of $\vec c$, so covering them puts it in
$B$: a meet row is below its clauses (`meet_clause_of`). A meet row is below a
row **by its parameters** (`meetBelow`, sound by `meetBelow_sound`) when the
row is one of its value parameters, or a meet row of some of them within
clauses including its own, so `T ⊓ number` is below `T ⊓ (number | null)`:

```math
\frac{j\in\{p\}\cup\vec q}{p\sqcap\vec q\sqcap\vec c\ \sqsubseteq_{\mathsf{par}}\ j}
\qquad
\frac{\{p'\}\cup\vec q'\subseteq\{p\}\cup\vec q\qquad\vec c\subseteq\vec c'}
     {p\sqcap\vec q\sqcap\vec c\ \sqsubseteq_{\mathsf{par}}\ p'\sqcap\vec q'\sqcap\vec c'}
```

A meet row $`i`$ with a scheme part, the case equation graphs add
([RECURSIVE-EQUATIONS §2.2](RECURSIVE-EQUATIONS.md#22-meaning)), is read
through any one part: its parameters as above, a scheme part $`s`$ covered by
a scheme row $`j`$ of $`B`$ ($`s\sqsubseteq_\forall j`$, below), or its clauses
each covered. A row $`i`$ is below a meet row $`j`$ of $`B`$ **part by part**
when each part of $`j`$ is $`i`$, a part of the meet $`i`$, or a scheme that
$`i`$ or one of its scheme parts covers, and $`j`$'s clauses are $`\top`$ or
$`i`$'s own (`MeetOpaque`, sound by `meet_part_value` and
`meet_target_value`):

```math
\frac{\forall q\in\mathsf{parts}(j).\;
      q=i\ \lor\ q\in\mathsf{parts}(i)\ \lor\ i\sqsubseteq_\forall q\ \lor\
      \exists s\in\mathsf{parts}(i).\ s\sqsubseteq_\forall q
      \qquad \vec c_j=\top\ \lor\ \vec c_j=\vec c_i}
     {i\ \sqsubseteq_{\mathsf{meet}}\ j}
```

This is how a binder bounded by another is below it: `U extends T` is
$p_U\sqcap p_T\sqcap\top$, below $p_T$, and with `T extends B` it is
$p_U\sqcap p_T\sqcap B$, below $T$'s $p_T\sqcap B$. This is how a bounded binder, read as the meet of its
parameter row and its bound, is below the bound: `T extends { length: number }`
is $p_T\sqcap\{\mathit{length}:\mathsf{number}\}$, and
$p_T\sqcap\{\mathit{length}:\mathsf{number}\}\le\{\mathit{length}:\mathsf{number}\}$.
**Splitting** replaces a `bool` clause by `boolLit true` and `boolLit false`
and leaves every other clause alone. It preserves meaning, so it adds no power
beyond the model; it lets one source clause be discharged by several target
clauses while coverage stays clause to clause. So
$\mathsf{bool}\le\mathsf{true}\lor\mathsf{false}$ and
$\mathsf{bool}\le\mathsf{bool}$ are derivable, and
$\mathsf{bool}\le\mathsf{true}$ is not.

**Quantified signatures.** A scheme row $i=(\vec p;\Sigma;\beta;\Sigma_\ldots)_\kappa$ of
$A$ is covered by a scheme row $j=(\vec p;\Sigma';\beta';\Sigma'_\ldots)_\kappa$ of $B$
of the same kind (`sameShape`), binding the same parameter rows, each source
bound among the target's, whose body, the binders opaque, the source's covers
as a call or construct clause's (`SchemeCoversWith`):

```math
\frac{i=(\vec p;\Sigma;\beta;\Sigma_\ldots)_\kappa\quad j=(\vec p;\Sigma';\beta';\Sigma'_\ldots)_\kappa\quad
      \beta\subseteq\beta'\quad
      \Delta\vdash\mathsf{body}_\kappa(\Sigma;\Sigma_\ldots)\sqsubseteq\mathsf{body}_\kappa(\Sigma';\Sigma'_\ldots)}
     {\Delta\vdash i\sqsubseteq_{\forall}j}\ \textsf{quantified}
```

It is the subtyping rule for quantified signatures under the restriction of
F<:'s kernel rule ([Pierce 1994](REFERENCES.md#pierce-1994)): the target's
binders are taken rigidly and the source's instantiated at them, which the
same rows make the identity, and no bound is compared but by inclusion of the
lists, so the check stays decidable. A member of $i$ meets, at every instance
$\vec X$ within $\beta'$, which is within $\beta$, $\Sigma$ read at
$\eta[\vec p\mapsto\vec X]$; the body's coverage, call or construct, whose
premises are table entries, gives $\Sigma'$ there (`covers_body_sound`, from
`covers_arrs_sound` and `covers_ctors_sound`; `scheme_covers_sound`). The
same holds up to renaming the binders (`renames_sound`). The premises are read
at the instance's assignment, not the table's own, so the table's induction
is over every assignment at once (`family_sound`): every derivation holds
at every assignment, since none reads it. So `Promise<number>` is below
`Promise<number | string>`: their `then` members bind the same rows, and the
target's callback, which takes `number | string`, is one the source's may be
given. The reverse fails at that callback's parameter, and a method whose
parameter is the declaration's argument, `send<U>(value: T, tag: U)`, makes
the declaration invariant there: TypeScript's method bivariance is refused.

Every cyclic premise occurs under an operand, so the table is sound by
induction on the level; the induction also supplies the source-type premise a
method covered by a function needs.

A premise $\Delta(A,B)$ also holds, with no entry, when every label of $A$ is
one of $B$'s: the meaning of a label list is the union of its labels', so the
induction needs no step for it (`mixed_subset`). A record below an interface
then needs no row relating each of its fields' contracts to itself, and no row
for everything those contracts reach.

The table holds wherever the known rows do: each $(F,L,M)\in\kappa$
with $F$'s values within $\mathsf{arrs}(L;M)$ at every level
(`family_sound`).

Lean: `PairOk`, `FamilyValid`, `Known`, `SameKind`, `SchemeCoversWith`,
`scheme_covers_sound`, `covers_arrs_sound`, `meetSources`, `meet_clause_of`, `MeetOpaque`,
`MeetSource`, `MeetTarget`, `meet_row_iff`, `meet_part_value`, `meet_target_value`, `splitClause`,
`CoversByProto`, `ProtoHolds`, `FoundOn`, `lacksKey`, `viewOf`,
`covers_arrows_sound`, `protoHolds_sound`, `CoversByScheme`, `SchemeBinds`, `bound_sigs_sound`, `bindersFree`,
`covers_by_scheme_sound`, `family_sound`.

### Instances and free rows

The known rows of a table are instances of scheme rows, each checked as
`inst` checks one (below, $\le_{\mathsf{inst}}$), against its arrows given
inline rather than as a type of the graph: an array's instance of a prototype
member has no row of its own.

Instances turn on which **parameter rows a row
depends on**. A free-variable certificate $V$ on a domain $D$ assigns each
$i\in D$ a set $V(i)$ of parameter rows, with $D$ closed under what its rows
read (a clause row its operands, a scheme row its signature types, a meet row
its clauses' operands), such that

```math
i\ \text{a parameter row}\Rightarrow i\in V(i),\qquad
i=p\sqcap\vec c\Rightarrow p\in V(i),\qquad
l\in\mathsf{reads}_G(i)\Rightarrow V(l)\subseteq V(i)\cup\mathsf{binders}(i),
```

where $\mathsf{binders}(i)$ is empty unless $i$ is a scheme row, so a scheme's
own binders are not free in it. A row means the same at two assignments that
agree on $V(i)$.

Lean: `FreeOk`, `freeOk_meet`, `meetClauses`, `agree_freeWith`, `mixed_respectsFree`.

#### Instances of a scheme row

An instance is checked by a finite **instance table** of entries
$(i,\kappa,T)$: under the context $\kappa$, row $i$ means type $T$. A context
maps the binders in scope to what they stand for: an instance type, or, under
a scheme mapped to another, that scheme's binder. Binder rows are shared
between scopes (a generic method of a generic type reuses a few binder rows so
that the graph stays finite), and the context tells the scopes apart. Writing
$\kappa(A)$ for the image of a type, each entry is one of:

- $i$ a parameter row and $T=\kappa(i)$, or $T=\{i\}$ when $\kappa$ does not
  name $i$, with $T$ of $i$'s declared kind;
- **fixed**: $T=\{i\}$ and $\kappa$ fixes $i$: it names no row of $V(i)$
  but parameter rows it maps to themselves, $\kappa(p)\in\{\bot,\{p\}\}$ for
  $p\in V(i)$, with $\kappa(p)=\{p\}$ only for a parameter row $p$ (inside a
  scheme matched against itself its binders stand for themselves; `fixedBy`);
- $i$ a clause row, $T=\{j\}$, $j$ a clause row, and $G(j)\doteq G(i)[\kappa]$:
  the same clauses, each operand with the same members as its image;
- $i$ the meet row $p_1\sqcap\cdots\sqcap p_k\sqcap\vec c$ of value
  parameter rows $\vec p$ (its parameter and `meetParams`), every operand of
  $\vec c$ with an image, and $T=\{j\}$ with either $j$ the meet row
  $q_1\sqcap\cdots\sqcap q_l\sqcap\vec d$ of value parameter rows whose set is
  that of the $\vec p$'s images, each $\kappa(p_i)=\{q\}$ (or $p_i$ itself
  when $\kappa$ does not name it), and $\vec d\doteq\vec c[\kappa]$; or $j$ a
  clause row of value kind, each $\kappa(p_i)=U_i$ a type of clause rows, and
  $G(j)\doteq\mathsf{meetLists}(G(U_1),\ldots,G(U_k),\vec c[\kappa])$, the
  meet folded left to right or in the reverse order (`meetOk`, `meetMany`):
  the meet of the parameters' images with the clauses' images, which is what
  lowering `T & DepSafe` at `T := U`, or `U extends T` at both, gives;
- $i$ the scheme row $(\vec q;\Sigma';\beta';\Sigma'_\ldots)$, $T=\{j\}$, $j$
  the scheme row $(\vec r;\Sigma'[\kappa'];\beta'[\kappa];\Sigma'_\ldots[\kappa'])$
  with $|\vec r|=|\vec q|$, $\vec r$ distinct parameter rows of matching kinds
  and $\kappa'=(\vec q\mapsto\vec r)\cdot\kappa|_{V(i)\setminus\vec q}$, the
  binders then $\kappa$ on $i$'s free rows only, in $V(i)$'s order
  (`enter`), provided no free row of $i$ outside $\kappa$'s domain, and no
  row free in an image $\kappa(p)$ for $p\in V(i)$, is in $\vec r$ (no
  capture).

A meet row's entry is sound because at assignments related by $\kappa$ its
parameter's values are $\kappa(p)$'s, its clauses mean their images', and the
meet of two clause lists means the intersection of their meanings
(`meetLists_row`), in either order:

```math
\frac{\eta_L(p)=⟦U⟧^{\eta_R}\qquad
      ⟦\vec c⟧^{\eta_L}=⟦\vec c[\kappa]⟧^{\eta_R}\qquad
      G(j)\doteq\mathsf{meetLists}(G(U),\vec c[\kappa])}
     {⟦p\sqcap\vec c⟧^{\eta_L}
      =⟦U⟧^{\eta_R}\cap⟦\vec c[\kappa]⟧^{\eta_R}
      =⟦j⟧^{\eta_R}}\ \textsf{meet-image}
```

Neither a meet row nor its image has argument lists (its image is of value
kind). So `V & DepSafe` at `V := [number, number]` is the tuple's meet with
each of DepSafe's alternatives: the primitives meet no array, and `Managed`,
a record, meets the array shape as one object holding its key too. That
object is inhabited: an array owns no key its prototype provides, and may own
`Managed`'s symbol key, which is none of them
([Conjunction and normalization](#conjunction-and-normalization)). The meet
row's rule does not depend on the array bound.

Entering a scheme keeps only what its free rows read, and nothing inside it
reads more (a signature's free rows are $i$'s or its binders), so the entry's
meaning is the same as under all of $\kappa$. Keeping less is what makes a
table for recursive types finite: relating `EagerCollection<K2ᵃ, V2ᵃ>` to
`EagerCollection<K2ᵇ, V2ᵇ>` enters `map`, then `reduce`, then `map` again,
without end, and a context carrying every scheme entered would never recur,
while one restricted to free rows alternates between two.

The table is checked when its rows lie in a domain with a free-variable
certificate and every entry is one of these. The producer (`matchRow`, not
trusted) builds a scheme entry's table by matching the bounds $\beta'$ under
$\kappa$, where they are read, and the signatures under $\kappa'$, so a generic
method whose result is its own interface at a bounded binder, such as
`map<V2, P extends readonly number[]>(m: new (...p: P) => Mapper<V, V2>, ...p: P): Box<V2>`,
has one (`class-value-generic-method`). Then, for every entry and every
pair of assignments related by its context on its row's free rows, the row on
the left means $T$ on the right, in both components. With
$\kappa_0=\vec p\mapsto\vec\theta$ for a scheme's binders and instance types,
the instance assignment and the graph's are related by $\kappa_0$ by
construction:

```math
\frac{\begin{array}{c}
i\ \text{a scheme row}\ (\vec p;\Sigma;\beta;\Sigma_\ldots)\quad
|\vec\theta|=|\vec p|\quad
\forall p.\;\theta_p:\mathsf{kind}(p)\quad
\forall(p,B)\in\beta.\;G\vdash\theta_p\le B\\
\text{a checked table}\quad
T\equiv_G\mathsf{arrs}(L;M)\quad
\forall\tau\in L.\;\exists\sigma\in\Sigma.\;\tau\doteq\sigma[\kappa_0]\land\varepsilon_\sigma\succeq\varepsilon_\tau\quad
\forall\tau\in M.\;\exists\sigma\in\Sigma_\ldots.\;\tau\doteq\sigma[\kappa_0]\land\varepsilon_\sigma\succeq\varepsilon_\tau
\end{array}}
     {G\vdash\{i\}\le T}\ \textsf{inst}
```

Here $\tau\doteq\sigma'$ when the two have the same arity and each type of
$\tau$ has the same members as the corresponding type of $\sigma'$: a type
means the union of its labels, so their order does not matter
(`sameLabels`, `sigMatch`, `restMatch`, and for clauses `sameClauses`). Where
the scheme signature's receiver admits every value (`top`), as a quantified
member's does, the instance's receiver is not compared: a callable safe at
every receiver is safe at a narrower one, every receiver being a closed value
(`instSig`, `instRest`, `top_row_mixed`). So a method call's instance states
its object as the receiver. The finite-table specialization of the premises other than
$`T\equiv_G\mathsf{arrs}(L;M)`$ is
$`G\vdash\{i\}\le_{\mathsf{inst}}\mathsf{arrs}(L;M)`$, checked by `compareInstArrsState`.

The order $`\varepsilon_\sigma\succeq\varepsilon_\tau`$ means that the
source effect guarantees the target effect. Signature images retain their
effects. Instance elimination composes image equality with arrow subsumption: the source effect must cover the target
effect. A preserving signature therefore supplies an unrestricted instance;
an unrestricted signature cannot supply a preserving instance. The argument,
receiver and result images keep their equality obligations. The proof
`inst_images_sound` applies `PromiseWith.weaken` after substitution.

The semantic proof of `inst` separates **image correctness** from universal
elimination. Let $\eta_\theta$ assign each scheme binder the mixed meaning
(value and argument-list components) of its instance type. The image
obligation is

```math
\mathsf{image}(A)=B
\quad\Longrightarrow\quad
⟦A⟧^{\eta_\theta}_{\mathrm{mixed}}
=⟦B⟧^\eta_{\mathrm{mixed}}.
```

`InstanceImages` states this obligation for the images named by a witness.
`table_instanceImages` proves it using the checked finite table, including its
closure, free-variable and kind checks. `inst_images_sound` then proves
elimination from those equalities and the existing bound/signature premises;
fixed and rest arguments, effects and receiver weakening use this one proof.
`compareInstArrsState_sound_at` composes the two. The default checker discharges the obligation with
the finite-table checks; the equation checker discharges it by structural
substitution ([RECURSIVE-EQUATIONS](RECURSIVE-EQUATIONS.md#3-metatheory)).

The checker establishes the bound judgment $`\theta_p \le B`$ through the
common comparison operation, including quantified instantiation, validated
variance and binder renaming. A bound query repeated on an unfinished instance
requires a guarded structural derivation. Prototype-member instances are
validated before structural coverage uses them. The state and its checked
results are described in [RECURSIVE-EQUATIONS §4.4](RECURSIVE-EQUATIONS.md#44-instantiation).

Lean: `entryOk`, `meetOk`, `TableOk`, `instKinds`, `substitutionKind`, `compareInstArrsState`,
`mixed_assignment_substitution`, `InstanceImages`, `table_instanceImages`,
`inst_images_sound`, `meet_row_value`, `meet_noArguments`,
`meetOk_noArguments`, `table_row_mixed`, `checkStructural_sound`,
`compareInstArrsState_sound_at`, `compareInstArrsState_sound`.

## Certificates

Subtype evidence carries optional root instantiation choices and a list of
prototype-member instantiation choices. Each choice includes its substitution
images, type arguments, domain and free-variable information. The checker
validates an instance before using it.

The producer infers prototype-member instances with either the source or
target host as receiver. It also infers from arguments and results alone,
then substitutes the resulting arguments into the complete signature; this
supplies an inherited method's base receiver. A binder occurring through a
meet can take the entire matched meet as its candidate argument. Each path
proposes an instance to the same image and bound checks; method coverage
checks the actual host against the instantiated receiver. Dependency discovery
includes the receiver, argument and result premises of those checked instances
before pruning its candidate relation.

The common operation selects among the rules of
[RECURSIVE-EQUATIONS §4](RECURSIVE-EQUATIONS.md#4-subtyping): identity,
validated variance, quantified instantiation and guarded structural coverage.
It validates the resulting family justification. Evidence production supplies candidate instances
to that operation; evidence checking supplies the recorded choices.

A checked certificate is a semantic inclusion:

```math
\mathrm{checkUsing}(G,I,S,T,p)=\mathsf{true}
\Longrightarrow
\forall\eta,n,W,x.\;
⟦S⟧^\eta_G(n,W,x)\Rightarrow
⟦T⟧^\eta_G(n,W,x),
```

for both components. The typing theorem that uses it is in
[PROGRAM-TYPING.md](PROGRAM-TYPING.md).

The structural engine discovers dependencies (`growTable`), removes unsupported
alternatives (`gfp`), and validates the resulting justification (`checkStructural`).
Its soundness is proved by `compareStructural_sound`.

Lean: `checkClauseWith`, `checkStructural`, `checkEntries`, `compareUsing`,
`compareUsing_sound`, `checkUsing`, `checkUsing_sound`, `acceptedUsing`
(`Types/PositiveCertificates.lean`).

## State-assertion grammar

Point claims can combine ordinary types with facts about the current execution
state. The following notation describes the finite assertion layer; it does
not add constructors to the type grammar. Let $x$ and $y$ name environment
slots, $A$ be a type, and $R$ a finite disjunction of primitive predicates:

```math
\begin{aligned}
a &::= \mathsf{null}\mid\mathsf{undefined}\mid\mathsf{true}\mid\mathsf{false}\mid\mathsf{Number}\mid\mathsf{numLit}(b)\mid\mathsf{String}\mid\mathsf{strLit}(s)\mid\mathsf{defined}\mid\mathsf{nonNull}\mid\mathsf{nonNullish},\\
R &::= \{a_1,\ldots,a_k\}\quad(k\geq 0),\\
J &::= \top\mid x:A\mid x=R\mid x=y\mid x.f\mapsto R\mid x.f\mapsto y\mid x.f\mapsto^{?}y\mid J\land J.
\end{aligned}
```

| Assertion | What it states |
| --- | --- |
| $x:A$ | The value of $x$ belongs to $A$ at the current world and level. |
| $x=R$ | $x$ satisfies one of the predicates in $R$. A statement about the environment, so no heap change can falsify it. |
| $x=y$ | $x$ and $y$ hold the same value, the same location when they hold references. Again untouched by heap changes. |
| $`x.f\mapsto R`$ | Reading field $`f`$ of $`x`$ currently yields a value satisfying $`R`$, including `undefined` for an absent optional key. The one-field spelling omits $`f`$. |
| $`x.f\mapsto y`$ | The present field $`f`$ of $`x`$ holds the value of $`y`$. |
| $`x.f\mapsto^{?}y`$ | Reading $`f`$ of $`x`$ gives $`y`$, including an absent-key result. |
| $\top$, $J_1\land J_2$ | No requirement, or both. Conjunction asserts no ownership or disjointness. |

$=$ speaks only about the environment, $\mapsto$ about the heap as well; that
division decides which facts survive a step, and
[Program typing](PROGRAM-TYPING.md#the-reference-operations) states the rules
over it. Despite the notation there is no separating conjunction and no
ownership: the facts are duplicable, and $\mapsto$ does not claim the cell is
unaliased.

An empty predicate list is an impossible predicate, not an absent assertion.
There is no assertion disjunction, negation or quantifier: the union within
$R$ gives alternatives for one value, not correlated alternatives between
slots. `Number` means any number and `numLit(b)` exactly that bit pattern;
singletons imply `Number`, not conversely. `defined` excludes `undefined`,
`nonNull` excludes `null`, and `nonNullish` excludes both, for values of any
shape. `nonNullish` implies each individual exclusion. These predicates
support a read at the storage contract with the excluded alternatives removed;
[the sliced-read rule](PROGRAM-TYPING.md) checks it.
Predicates on nested references are outside this vocabulary.

The notation used in source claims is an abbreviation:

```math
x:\{\mathsf{value}:B=R\}
\quad\equiv\quad
x:\mathsf{ref}(B)\ \land\ x\mapsto R,
```

where $\mathsf{ref}(B)$ is the plain cell $\mathsf{Ref}\,\{\mathsf{value}{:}B\}$.
On the right of `=`, `true` denotes $\{\mathsf{true}\}$ and `boolean` denotes
$\{\mathsf{true},\mathsf{false}\}$. So `{ value: boolean = true }` combines
`ref(boolean)` with a current-cell fact. It is neither `ref(true)` nor a type
that can appear inside operands; forgetting the cell fact leaves
`ref(boolean)`.

The implementation stores these conjunctions as a context $\Gamma$ plus
`HeapKnowledge.Knowledge`: cell facts (`HeapFacts.Holds`), immutable-value
facts (`HeapKnowledge.ValueHolds`) and read/equality links (`HeapLinks.Holds`,
whose `alias` flag distinguishes timeless slot equality from a current read).
A source expression assertion uses its evaluated result in place of $x$.
[Semantics](SEMANTICS.md#current-content-assertions-and-postconditions)
defines heap observations,
[Program typing](PROGRAM-TYPING.md#checked-expression-postconditions) the
checked rules and fact transfer, and
[Source claims](SOURCE-CLAIMS.md#current-content-assertions) the wire
encoding.

## Related layers

### Quantified scheme layer

A quantified callable is a scheme row
([Parameter and scheme rows](#parameter-and-scheme-rows)): its binders are
parameter rows, and a member meets its signatures at every instantiation of
them within their bounds (`schemeSemWithArgs`). For a scheme $S$ at the outer
assignment $\eta_0$, an instance is a reassignment $\eta$ of its binders
alone:

```math
\begin{aligned}
\mathsf{Instance}_{G}(\eta_0,S,\eta)
\;\overset{\mathrm{def}}{\Longleftrightarrow}\;&
\eta=\eta_0[S.\mathsf{binders}:=\vec A]
\land\mathsf{Bounded}_n(\eta_0,S,\vec A),\\
⟦S⟧^{\mathsf{scheme}}_{G,\eta_0}(n,W,v)
\;\overset{\mathrm{def}}{\Longleftrightarrow}\;&
\mathsf{Callee}_{S.\kappa}(v)\land\forall\eta.\;
\mathsf{Instance}_{G}(\eta_0,S,\eta)
\Rightarrow
v\in⟦\mathsf{body}_{S.\kappa}(\mathsf{Sig}_\eta(S);\mathsf{RestSig}_\eta(S))⟧,
\end{aligned}
```

a bound read at $\eta_0$, outside the binders; the body is the instance's
call clause, $`\mathsf{Calls}\cap\mathsf{Rests}`$, or for a construct scheme its
construct clause (`instanceTWithArgs`, `sigsT`). The quantifier is inside
membership of one $v$ at one $n,W$, so it cannot be witnessed by a different
closure per call, and every row outside the binders, those the captures' types
use included, means the same at every instance. A
generic closure is graph code at a scheme row (`funScheme`): its code is
checked once at the row's signatures, over the binders' parameter rows, and a
code table entry holds at every assignment of them (`CodesSound`), so at every
instance; it is a call scheme, as instance elimination's (`inst`, `compareInstArrsState`)
and a method's received scheme (`CoversByScheme`) are. A generic class's
value is read at a construct scheme ([generic function and constructor
types](SOURCE-CONTRACTS.md#generic-function-and-constructor-types)). A bound naming another binder, `U extends T`, is no scheme bound,
since it reads a binder: the binder is read as the meet of the two parameter
rows (`dependentMeet`), which an instance maps to the meet of their type
arguments (`meetOk`).

Lean: `Types/PositiveGraphs.lean` (`schemeSemWithArgs`).

## Limits

- The clause language has no negation or difference, and no surface `extends`
  language.
- Subtyping is sound; the rules are not complete for the model. For example, incompatible invariant contracts are
  never recognized as empty.
- `compatible` is a shape test, not a test of joint inhabitation.
- Normalization has no growth control and no Lean implementation, and no
  verified compiler from textual type syntax to graphs exists.
- Generic methods are still receiver-quantified signatures, not host-relative
  scheme members.

## Lean files and validation

- [Types/ReferenceConjunctions.lean](../lean/Verification/Types/ReferenceConjunctions.lean): the meaning of a conjunction of record contracts (`refsT`), its admissibility and congruence
- [Types/MethodMembers.lean](../lean/Verification/Types/MethodMembers.lean): host-relative method members
- [Types/CallableConjunctions.lean](../lean/Verification/Types/CallableConjunctions.lean): proves that bag conjunctions and overloads on one callable value merge into one contract (`merge`, `calls_merge`)
- [Types/PositiveNormalization.lean](../lean/Verification/Types/PositiveNormalization.lean): the clause language and the clause meet
- [Types/PositiveGraphs.lean](../lean/Verification/Types/PositiveGraphs.lean): normal graphs and the rows' denotation
- [Types/PositiveRules.lean](../lean/Verification/Types/PositiveRules.lean): the declarative subtyping rules and their soundness
- [Types/SchemeInstances.lean](../lean/Verification/Types/SchemeInstances.lean): instances of a scheme row, their tables and the compiled table check
- [Types/PairFamilies.lean](../lean/Verification/Types/PairFamilies.lean): families of pairs, their entries and soundness (`pairs_sound`, `family_sound`)
- [Types/PositiveCertificates.lean](../lean/Verification/Types/PositiveCertificates.lean): the certificate checker and its soundness
- [Types/GraphRows.lean](../lean/Verification/Types/GraphRows.lean): the label-independent row representation
- `Types/EquationGraphs.lean`, `Types/EquationSupport.lean`, `Types/EquationCongruence.lean`

All under `lean/Verification/`. `lake -d lean build`
checks the whole library; it contains no `sorry` or custom axioms. Semantic
soundness uses `propext`, `Quot.sound` and `Classical.choice`.
