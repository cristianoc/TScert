# Semantics

The stateful development in [lean/Verification](../lean/Verification)
provides the semantic foundation for the positive-type rules specified in
[POSITIVE-TYPES.md](POSITIVE-TYPES.md). This is the semantics used by the current verifier. [PROGRAM-TYPING.md](PROGRAM-TYPING.md) specifies the proved program
typing system and checked control-flow graphs. The
[fragment boundary](SOURCE-FRAGMENT.md#fragment-boundary)
distinguishes the supported source fragment from model-only features.

## Operational language

[Calculus.lean](../lean/Verification/Semantics/Calculus.lean) defines an untyped call-by-value language with a mutable heap.
The following is the original one-field kernel notation, not an exhaustive
constructor inventory (see `Tm` in `Calculus.lean` for the maintained syntax):

```math
t ::= x_i\mid t\,t\mid\mathsf{null}\mid\mathsf{undefined}\mid\mathsf{true}\mid\mathsf{false}
\mid\mathsf{obj}(\ell,c)\mid\mathsf{make}(c,t)\mid\mathsf{let}(t,t)
\mid\mathsf{read}(t)\mid\mathsf{write}(t,t)
\mid\mathsf{test}_k(t)\mid\mathsf{if}\;t\;t\;t.
```

Here $x_i$ is a variable, given as a de Bruijn position, $\ell$ a heap location,
and $k$ a shape test
drawn from $\{\mathsf{isNul},\mathsf{isUndef},\mathsf{isNullish},\mathsf{isBool},\mathsf{isRef},\mathsf{isFun}\}$.
The nullish test accepts null or undefined; the others recognize individual value shapes. Values are
the subset

```math
v ::= \mathsf{null}\mid\mathsf{undefined}\mid\mathsf{true}\mid\mathsf{false}\mid\mathsf{obj}(\ell,c),
```

where $c ::= \mathsf{absent}\mid\mathsf{bound}(f,r,\vec p)\mid\mathsf{graph}(m,E,K,s,\vec c,\kappa,\varrho)$ is a separate invocation
descriptor, the call code. `bound` is the forwarding descriptor `.bind`
creates: the target, the receiver and the argument prefix it saved, values
that no field holds and no write can reach. $\mathsf{graph}$ is code whose
body is a control-flow graph, as a program's is: a declared parameter count
$m$, node expressions $E$, each node's continuation and handler $K$, an entry
label $s$ and the captured values $\vec c$, invoked by a call or,
construct-only, by `new` ($\kappa$), collecting a rest or not ($\varrho$)
([graph code](#graph-code)). Every closure the source creates, a class and a
callable object included, is graph code; there is no other code. An argument list is not a value: which lists a rest
parameter's type admits is a separate contract on lists of values
([argument packs](POSITIVE-TYPES.md#argument-packs)).
`make c a` evaluates its initializer `a`, then appends that value and one
identity cell holding $\mathsf{null}$ to the heap and returns `obj h.length c`,
where `h.length` is the length before appending. Every allocation ends with
its identity cell: an object value $\mathsf{objAt}(\mathit{fs},c,i)$ carries the
locations $\mathit{fs}$ of its fields, its call code $c$ and the location $i$
of that cell, its identity, which no field names and no write reaches.
`alloc a` abbreviates `make absent a`; creating code is `make (graph …) a`.
Both use the same constructor and the same allocation step, `Step.makeV`.
The code is not run during creation. There is no bare lambda value.

Since that kernel, the values also include numbers (the bit pattern of the
double), strings, bigints $\mathsf{bigint}(i)$ with $i\in\mathbb Z$ (a bigint is
its integer, as a number is its double) and symbols $\mathsf{sym}(i)$ (a symbol
is its identity: distinct declarations are distinct symbols); an object's fields are keyed by property
keys $\kappa::=\mathsf{str}(s)\mid\mathsf{sym}(i)$; and the tests include
$\mathsf{isNum}$, $\mathsf{isStr}$, $\mathsf{isBigint}$, $\mathsf{isSymbol}$,
$\mathsf{isArray}$, $\mathsf{typeofObject}$, $\mathsf{hasKey}(\kappa)$, the singleton equalities of every primitive kind that carries a value
($\mathsf{numEq}(b)$ by `Number::equal`, $\mathsf{strEq}(s)$, $\mathsf{boolEq}(q)$,
$\mathsf{bigintEq}(i)$, each false on every other kind) and $\mathsf{truthy}$, JavaScript's `ToBoolean`:

```math
\mathsf{truthy}(v)=\mathsf{false}\iff v\in\{\mathsf{null},\mathsf{undefined},\mathsf{false},
\mathsf{num}(\pm0),\mathsf{num}(\mathrm{NaN}),\mathsf{str}(\texttt{""}),\mathsf{bigint}(0)\}
```

(`numberTruthy`: a number is falsy where it equals zero or is not equal to
itself); every object, function, class, symbol and store is truthy. $\mathsf{isArray}$ holds of a
plain object owning the array store key $\sigma$, which no source property
names, so it holds of exactly the arrays, as `Array.isArray` does of
JavaScript's Array exotic objects:
$\mathsf{isArray}(\mathsf{obj}(\mathit{fs},\mathsf{absent}))\iff\sigma\in\mathrm{dom}\mathit{fs}$,
and false of every other value. $\mathsf{typeofObject}$ holds of
$\mathsf{null}$ and of an object without call code, which is where `typeof`
answers `"object"`: $\mathsf{typeofObject}(v)\iff v=\mathsf{null}\lor v=\mathsf{obj}(\mathit{fs},\mathsf{absent})$.
$\mathsf{hasKey}(\kappa)$ is `in`: it holds of an object owning the key
$\kappa$, whatever its code, or lacking it and holding under the prototype key
$\pi$ an object of which it holds, as far as the heap reaches, and of no other
value. It is the one test that reads the heap (`tagHoldsIn`, `keyInChain`):

```math
\mathsf{hasKey}_h(\kappa)(\mathsf{obj}(\mathit{fs},c))\iff\kappa\in\mathrm{dom}\mathit{fs}\ \lor\
  (\mathit{fs}(\pi)=\ell\land\mathsf{hasKey}_h(\kappa)(h(\ell)))
```

bounded by the heap's length, so a chain the heap makes cyclic, which no
JavaScript object has, answers false. Keys are fixed at allocation and no
source writes a prototype, so its answer never changes. It is `in` for the
keys the lowering admits ([SOURCE-MODEL](SOURCE-MODEL.md#guards)); JavaScript's `in`
throws on a primitive. For $\kappa_C$, the key only class `C`'s prototype
object owns, it is `instanceof C`: an object along whose chain that
prototype is, and `false` of a primitive, as JavaScript's `instanceof`
answers. Where the object owns the key or holds no prototype
(`protoFree`) the answer is the heap-free $\kappa\in\mathrm{dom}\mathit{fs}$
(`tagHoldsIn_of_protoFree`), which is what a type's answer states. Graph code
records which invocation it admits, $\kappa\in\{\mathsf{call},\mathsf{construct}\}$:
JavaScript gives a function object `[[Call]]` and `[[Construct]]` separately,
an arrow has only the first and a class only the second. A plain call
dispatches only call code (`CallCode.callable` is false of construct code), and
$\mathsf{new}\,f(\vec a)$ is its own term, which evaluates the callee, then
the actuals left to right, and runs only construct code, with `undefined` for
the receiver:

```math
\frac{h,f\to h',f'}{h,\mathsf{new}\,f(\vec a)\to h',\mathsf{new}\,f'(\vec a)}
\qquad
\frac{f\ \text{a value}\quad a_1,\ldots,a_{i-1}\ \text{values}\quad h,a_i\to h',a_i'}
     {h,\mathsf{new}\,f(\vec a)\to h',\mathsf{new}\,f(\vec a[i:=a_i'])}
```

(`constructL`, `constructArg`), then enters the code as a call does
([`constructGraph`](#graph-code)), missing actuals `undefined`. The step
relation stays deterministic (`Step_det`). What a construct signature promises
is in [the clause's meaning](POSITIVE-TYPES.md#functions-and-classes):
the construct step's result is safe at the signature's result, one level below
the budget, and its normal return meets the signature's effect, as a call's
body does.

**Allocation from parts.** $\mathsf{merge}_\delta(a,b)$ (`Tm.merge`)
evaluates $a$, then $b$ (`mergeC1`, `mergeC2`), then reads, in the heap as it
is, the fields $a$'s object owns but the array store $\sigma$, and the own
enumerable data properties $b$ has, less the keys in $\delta$, and steps to
the allocation of both, $b$'s over $a$'s:

```math
\frac{\mathsf{own}_h(v_a)=P\quad\mathsf{data}_h(v_b)=Q}
     {h,\ \mathsf{merge}_\delta(v_a,v_b)\to h,\ \mathsf{makeAt}(\mathsf{absent},\ P\lhd(Q\setminus\delta))}\ (\texttt{mergeV})
```

where $\mathsf{own}_h(\mathsf{obj}(\mathit{fs},\mathsf{absent}))$, of an
object whose $\mathit{fs}$ lacks the host key $\kappa_{\mathsf{host}}$, is each key of
$\mathit{fs}$ but $\sigma$ at its value (the first entry of a key, as a read
finds it); $\mathsf{data}_h(\mathsf{obj}(\mathit{fs},c))$, of an object with
any call code $c$ but a host object, is each string key of $\mathit{fs}$ but $\sigma$, $\pi$,
the code field $\kappa_{\mathsf{code}}$ and $\kappa_{\mathsf{host}}$ at its value, then, for an array, each
element under its index's decimal spelling; $\mathsf{data}_h$ of a string is
each code unit, a one-unit string as `elemAt` reads it, under its index's
decimal spelling, as JavaScript's string wrapper owns them enumerable
(`stringData`); $\mathsf{data}_h$ of
$\mathsf{null}$, $\mathsf{undefined}$, a Boolean, a number, a bigint or a symbol
is empty; and $P\lhd Q$ keeps $P$'s entries whose key $Q$ lacks, then $Q$'s
(`mergeParts`, `ownAll`, `ownData`, `mergeData`). A function the program
creates holds one field, under $\kappa_{\mathsf{code}}$ (`codeField`, spelled
`[[code]]`, which no source key spells), which gives it a location; a copy
takes none of it, as JavaScript's function owns no enumerable property. A
class value the program creates holds that field and its static fields, which
a copy takes, as JavaScript's class owns each static field as an enumerable
data property. A host object (`hostKey`, spelled `[[host]]`, owned by the
package's instances and node lists, [restricted values](COMPILER-API.md#restricted-values))
has neither, so a merge of one is stuck. A
value the heap lacks, or a term that is not a value there, reads as
`undefined`, so the step never depends on one (`heapVal`). It allocates
nothing itself; the `makeAt` it steps to does, as a literal's. Symbol-keyed
fields are not read ([SOURCE-MODEL](SOURCE-MODEL.md#object-literals)).

**Binary operators.** $a\mathbin{op}b$ (`Tm.arith`) evaluates $a$, then $b$
(`arithC1`, `arithC2`), then takes one step where the operator answers for the
two values, or throws where JavaScript throws, and is stuck otherwise:

```math
\frac{\mathsf{binop}(op,v_1,v_2)=v}{h,\ v_1\mathbin{op}v_2\to h,\ v}\ (\texttt{arithV})
\qquad
\frac{\mathsf{binopThrows}(op,v_1,v_2)}{h,\ v_1\mathbin{op}v_2\to h\mathbin{+\!\!+}[\mathsf{null}],\ \mathsf{throw}\ \mathit{err}_{|h|}}\ (\texttt{arithThrow})
\qquad op\in\{+,-,*,/,\%,{*}{*},\mathbin{\hat{}},\mathbin{\&},\mathbin{|},\ll,\gg,\ggg,<,\le,>,\ge,\equiv\}.
```

$\mathsf{binop}$ is JavaScript's operation on the operand kinds it models;
$\mathsf{binopThrows}$ is where JavaScript throws with no code of the
program's run first, and $\mathit{err}_i$ the error object (`thrownError`, an
object without fields whose identity cell the step appends at $i$, standing
for the `TypeError` or `RangeError` instance). Neither answers where JavaScript converts through code or
coercions the calculus does not have:

| Operands | Arithmetic ($+,-,*,/,\%,{*}{*},\hat{},\&,\vert,\ll,\gg,\ggg$) | Relational ($<,\le,>,\ge$) |
| --- | --- | --- |
| two numbers | the IEEE-754 double operation; ${*}{*}$ is `Number::exponentiate` (C's `pow`, but NaN for a NaN exponent and for a base of magnitude 1 to an infinite power); $\hat{}$, $\&$ and $\vert$ are exclusive or, and and or after `ToInt32` on both; $\ll$ and $\gg$ shift the left operand's `ToInt32` left (modulo $2^{32}$, read as signed) or right (sign-propagating) by the right operand's `ToUint32` modulo 32, and $\ggg$ shifts its `ToUint32` right by that count, zero-filling; $\%$ is `Number::remainder`, exact: $n-d\cdot q$ for $q$ the quotient truncated toward zero, with $n$'s sign (so `-4 % 2` is $-0$), NaN for a NaN or infinite $n$ or a NaN or zero $d$, and $n$ itself for an infinite $d$ or a zero $n$ | the IEEE order: false when either is NaN, the two zeros equal |
| two bigints | the integer operation; $/$ truncates toward zero and $\%$ is the remainder it leaves, with the dividend's sign; throws for $/$ or $\%$ by $0$ and ${*}{*}$ by a negative exponent (a `RangeError`); none for $\&,\vert,\ll,\gg,\ggg$ (`numberOnly`) | the integer order |
| a number and a bigint | throws (a `TypeError`) | the exact order of the double's rational value and the integer; false when the number is NaN, an infinity beyond every integer |
| two strings | $+$ concatenates; others none | lexicographic over UTF-16 code units, a proper prefix less |
| a string and a number, bigint, Boolean, `null` or `undefined`, either order | $+$ concatenates the string with $\mathsf{str}$ of the other, in operand order; others none | none |
| a Boolean, `null` or `undefined` and a number, bigint, Boolean, `null` or `undefined`, either order | none | the order of the two after `ToNumeric` (`relNumeric`): `undefined` is NaN, `null` and `false` are $+0$, `true` is $1$; so false where `undefined` is an operand |
| a symbol and a primitive, either order | throws (a `TypeError`: `ToString` or `ToNumeric` of a symbol) | throws |
| anything else | none | none |

Strict equality $\equiv$ (`===`, `Arith.eq`; `strictEquals`) answers a Boolean
except on two stores:

```math
v_1\equiv v_2=\begin{cases}
\mathsf{sameValue}(v_1,v_2) & v_1\ \text{or}\ v_2\ \text{a primitive}\\
i_1=i_2 & v_k=\mathsf{objAt}(\mathit{fs}_k,c_k,i_k)\\
\mathsf{false} & \text{an object and a store}\\
\text{none} & \text{two stores}
\end{cases}
```

$\mathsf{sameValue}$ is false across kinds, `Number::equal` on two numbers
(NaN equals nothing, the zeros each other), and equality of the string, the
bigint, the Boolean or the symbol, `null` and `undefined` each only to itself.
An object's identity is the location of its identity cell, which only its
allocation creates, fresh (`makeFields`): two objects are one object exactly
when their identities are, with or without fields. Strict equality converts
nothing, so it never throws ($\mathsf{binopThrows}$ is false for $\equiv$).

Loose equality (`==`, `Arith.looseEq`; `looseEquals`) follows
[ECMA-262's `IsLooselyEqual`](REFERENCES.md#ecma-262) on these operand pairs;
`!=` negates its Boolean result. Both operands execute once, left to right,
before comparison.

| Operands, in either order | Meaning |
| --- | --- |
| Two primitives of the same kind | Strict equality, including symbol identity, NaN unequal to itself and the two zeros equal |
| `null` and `undefined` | Equal |
| A nullish value and anything else | Unequal; no conversion hook runs |
| A Boolean and a non-nullish primitive | Convert the Boolean to 0 or 1, then compare |
| A string and a number | Convert the string by `ToNumber`, then compare numbers |
| A string and a bigint | Parse by `StringToBigInt`; invalid integer text compares unequal |
| A number and a bigint | Compare the double's exact mathematical value with the integer; NaN and infinities compare unequal |
| A symbol and a different primitive kind | Unequal |
| Two objects | Compare their identities, as strict equality does |

Numeric strings admit ECMAScript whitespace, empty text, decimal fractions and
exponents, unsigned binary/octal/hexadecimal prefixes and signed `Infinity`.
Separators and trailing text are invalid. Bigint strings admit signed decimal
integers and unsigned radix prefixes, without fractional or exponent syntax.
`stringNumber` uses the same IEEE conversion as runtime literals;
`doubleIntOrder` compares mixed numeric kinds without rounding the bigint.
The execution-model controls check conversion answers independently of typing:
a Boolean result alone cannot establish the correct truth value.

Object-to-primitive conversion has no operator rule. It may call
`Symbol.toPrimitive`, `valueOf` or `toString`, mutate aliases or throw.
Arrays need that audit too: default-hint conversion tries `valueOf` before
standard string conversion. The host boundary excludes `document.all` and
its browser-only `[[IsHTMLDDA]]` behavior.

$\mathsf{str}(v)$ (`primString`) is JavaScript's `ToString` of a primitive
other than a symbol, which runs no code: a string is itself, `true`, `false`,
`null` and `undefined` their names, a bigint its decimal integer with a leading
`-` when negative, and a number `Number::toString` in radix 10
(`numberToString`): `NaN`, `Infinity` with its sign, `0` for both zeros, and
otherwise the fewest decimal digits $s$ whose value $s\cdot10^{d}$ rounds to
the double, the one closest to it where several have that length (the even one
on a tie, as the specification's note recommends and engines do), written
plainly up to 21 integer digits, as `0.` and up to six zeros below one, else
in exponent form `d.ddde±x`. A symbol converts by throwing a `TypeError`,
which $+$ with it does (`binopThrows`), and an object through its own
`toString`/`valueOf`, which is code: $+$ with one is stuck.

So the operation never computes on a value it would convert through code or a
coercion it does not define: a string compared with a number, a Boolean in
arithmetic and an object (whose `valueOf` is code) all leave the term stuck,
which the typing rule rules out. The unary operators are this one with a
constant right operand of the operand's family ([source
forms](PROGRAM-TYPING.md#judgments-and-constructor-views)): $-x=x*(-1)$, $+x=x*1$
and $\sim x=x\mathbin{\hat{}}(-1)$, exact on doubles (a sign flip, the identity,
`ToInt32` complemented) and on integers alike. Lean: `binop`, `arithBits`, `remBits`, `intAnd`, `intOr`, `toUint32`,
`bigintArith`, `doubleIntOrder`, `utf16Units`, `primString`, `numberToString`
(`Semantics/Calculus.lean`); their agreement with node's values rests on
review.

**Strings.** A string owns its `length` and its index properties, and
`lenOf` and `elemAt` read them as they read a store's:

```math
\frac{}{h,\ \mathsf{lenOf}\;\mathsf{str}(s)\ \to\ h,\ \mathsf{num}(|\mathit{units}(s)|)}\ (\texttt{lenStr})
\qquad
\frac{}{h,\ \mathsf{elemAt}\;\mathsf{str}(s)\;\mathsf{num}(b)\ \to\ h,\ \mathit{codeUnitAt}(s,b)}\ (\texttt{elemStr})
```

where $\mathit{units}(s)$ is $s$'s UTF-16 code units (`utf16Units`) and
$\mathit{codeUnitAt}(s,b)$ is the one-unit string at the array index $b$
denotes (`indexOfBits`, so `-0` is index 0) below the length, and
`undefined` at any other number: past the end, negative, fractional, NaN or
infinite, JavaScript finds no own property and the built-in `String.prototype`
and `Object.prototype` own no numeric key. A model string is a sequence of
Unicode scalar values, as Lean's `String` is, so half of a surrogate pair has
no string of its own: it reads as U+FFFD (`unitString`), where JavaScript
yields the lone half. This is the one place the model's strings differ from
JavaScript's; the fragment computes on a string only by equality, order,
length and these reads, and both are strings of one code unit.

Every other member of a primitive is its wrapper prototype's: JavaScript's
`ToObject` makes a wrapper whose `[[Prototype]]` is the built-ins'
`String.prototype` (`Number.prototype`, `BigInt.prototype`,
`Boolean.prototype`), and the read continues there. The calculus writes that
wrapper as it is: a fresh object owning only `[[proto]]`,
$\mathsf{makeAt}\;\mathsf{absent}\;[\mathsf{proto}]\;[P]$ with $P$ the built-ins'
prototype, from which `readProto` reads the member. No step is added.

`make_fields_rule` proves heap and world extension once, with a result
obligation for the fresh object's descriptor. `makeFn_rule` is its one-field
case, creating a function object; creating code uses it with the code's
contracts (`HasTyUsing.sound`).

The graph consumer checks
[`sourceTerm`](../lean/Verification/Semantics/ObjectCoherence.lean) on every
node, so program syntax embeds no already allocated identity, even inside
unselected branches and empty-overload bodies.

`Val` abbreviates `Tm`, so worlds, heaps and the step relation all speak
about the same objects. `letE a b` is an explicit binding: it evaluates `a`,
then substitutes the resulting value into `b` in one step without changing the
heap. Only `b` is under the new binder. `HasTyUsing.letE`, source lowering, and the
certificate producer and consumer all use that constructor. `Step_det` proves
that a term and heap have at most one successor.

A read of a named property on an object with no such own field continues at
the object's prototype, when it has one: the reserved key `protoField` holds
it, no source name spells it, and one step turns the read into the same read
of the prototype (`Step.readProto`, `Step.indexProto` for a computed key).
Without a prototype the read steps to `undefined` (`Step.readMissing`,
`Step.indexMissing`); a present field still reads its heap location. A computed
key is converted by `ToPropertyKey` first, where it runs no code: a string is
its own key, as the model spells it, a symbol its identity, and a number the
key its `ToString` spells, so `o[1]` reads `o["1"]` (`propertyKey`); `indexAt`
on any other key is stuck:

```math
\mathsf{key}(\mathsf{str}\,s)=\mathsf{str}(\mathsf{esc}(s))\qquad
\mathsf{key}(\mathsf{sym}\,i)=\mathsf{sym}(i)\qquad
\mathsf{key}(\mathsf{num}\,x)=\mathsf{str}(\mathsf{ToString}(x))
\qquad
\frac{\mathsf{key}(v)=k\quad\mathit{fs}(k)=l\quad h(l)=u}
     {h,\ \mathsf{indexAt}\;(\mathsf{obj}(\mathit{fs},c))\;v\ \to\ h,\ u}
```

The model keeps keys for itself: the array store's `[]`, and names in double
brackets, the prototype's `[[proto]]`, a function's `[[code]]`, a host
object's `[[host]]` and a class's
prototype object's own key. JavaScript's string key $`s`$ is represented
under $`\mathsf{esc}(s)`$ (`escapeKey`), which prefixes `[!` to a reserved
spelling and to one beginning `[!`, and is $`s`$ otherwise:

```math
\mathsf{esc}(s)=\begin{cases}
\texttt{[!}\,s & s\in R\ \lor\ s\ \text{begins with}\ \texttt{[!}\\
s & \text{otherwise}
\end{cases}
\qquad R=\{\texttt{[]}\}\cup\{\texttt{[[}\,t\,\texttt{]]}\}
```

$`\mathsf{esc}`$ is injective (an image begins with `[!` exactly when it
adds the prefix) and its image misses
$`R`$ (`reservedSpelling_escapeKey`), so every string key JavaScript has is
represented apart from the model's own keys by construction. A key the
source spells is one $`\mathsf{esc}`$ leaves as it is
(`Fragment.reservedSourceKey`), so a key written in the source and the same
key computed at run time are one.

**Allocation at a computed key.** $`\mathsf{makeKey}(k,a)`$ (`Tm.makeKey`)
evaluates $`k`$, then $`a`$ (`makeKeyC1`, `makeKeyC2`), and steps to the
allocation of one fresh plain object owning one property, at the key
$`k`$'s value converts to, holding $`a`$'s value; it is JavaScript's
`{ [k]: a }`:

```math
\frac{\mathsf{key}(v_k)=\kappa\quad v_a\ \text{a value}}
     {h,\ \mathsf{makeKey}(v_k,v_a)\to h,\ \mathsf{makeAt}(\mathsf{absent},[\kappa],[v_a])}\ (\texttt{makeKeyV})
```

It is stuck on a key of no other kind; the key's conversion runs no code.

and `indexProto`, `indexMissing` as `readProto`, `readMissing` at
$\mathsf{key}(v)$:

```math
\frac{\mathit{fs}(k)=\varnothing\quad\mathit{fs}(\mathsf{proto})=l\quad h(l)=p}
     {h,\ \mathsf{readAt}\;k\;(\mathsf{obj}(\mathit{fs},c))\ \to\ h,\ \mathsf{readAt}\;k\;p}
\qquad
\frac{\mathit{fs}(k)=\varnothing\quad\mathit{fs}(\mathsf{proto})=\varnothing}
     {h,\ \mathsf{readAt}\;k\;(\mathsf{obj}(\mathit{fs},c))\ \to\ h,\ \mathsf{undefined}}
```

The semantic index view `dictViewT K A` requires the object to have no
prototype and every *present* field under a key the class `K` admits (every
string key, the canonical numeric ones, or every symbol key: `IndexKeys`,
[POSITIVE-TYPES](POSITIVE-TYPES.md#records)) to have a stored contract implying
`A` at lower budgets. This is guarded
and admissible even when `A` is recursive, and it grants no write permission.
An empty object satisfies
the Boolean dictionary view, while a read of any key yields `undefined`, which
is not Boolean. An arbitrary indexed read therefore needs a result including
`undefined`. The positive graph has a `dict` clause whose operands are guarded
recursive labels, and the checked covering rule can compare dictionary views.
The source parser and OCaml producer lower inline index annotations into that
clause. A key the clause names as a field or view is read at that member's
contract by `read` or `readView`, whose premise `namedMembers` accepts a
dictionary's named members as a record's. Any other named key read uses the
proved `readDict` rule, through an index whose class surely admits the key; a
computed key uses `indexAt`, which evaluates the receiver before the key and
then reads the selected field (or `undefined` if it is absent). The proved
`indexDict` rule checks the key at the key clause of a class within the
index's (`string`, `number` or `symbol`; a number's key is canonical numeric,
`numeric_admits_number`). Both reads carry `undefined` in their result. This path reaches the same certified
source acceptance theorem as other expressions. A fresh literal is a
readonly dictionary through its exact own keys: `alloc` bounds them among the
literal's names (`ownKeysT_slots`), and a record so bounded, with no prototype
key among them, meets an index view whose contract every field's is within
(`covers_keys_sound`); an existing open record, which may hold further keys,
meets none. A writable index some value meets is never met through an
own-key bound, since code holding it may add a key the bound says is absent
(`KeepsKeys`): a literal meant for one is allocated at the
dictionary, each field an index may admit at that index's type
(`HasTyUsing.allocDict`, `dictCellT_of_recT`). A mutable index
signature lowers to a writable index contract `dictCellT K A`, whose present
fields under keys of `K` have contracts agreeing with `A` rather than implying
it, and covering keeps it invariant. Imported recursive declarations remain outside the source fragment.

Term and descriptor equality use explicit structural comparisons, each returning
a kernel-checked `Decidable` result and recurring only on strict subterms. This
keeps certificate equality executable for list-valued
applications: Lean's `DecidableEq` deriving handler does not support nested
mutually recursive types. The comparisons inspect every constructor field,
including descriptor arity.

Two different things are named here, and both run through the whole development.
A **binding** lives in the environment $\rho$; a **location** $\ell$ is an address
in the heap $h$. This is the usual store/heap pair of an ML-style operational
semantics. A binding may *hold* an object: $\rho(x)=\mathsf{obj}(\ell,c)$. Below,
$\ell$ abbreviates the plain-object value $\mathsf{obj}(\ell,\mathsf{absent})$.
A function object carries graph code at the same kind of heap identity;
[callable contracts](CALLABLES.md#callables) additionally constrain that code.

Because the calculus is nameless, a binding is really a de Bruijn position, and
the implementation calls it a **slot**: environments are lists, and pushing a
value renumbers everything already there. Rules in these documents write names
for bindings anyway, which reads better and matches the source they describe.
The two views agree, and `shift_holds` is the theorem that says so: renumbering
on a push preserves every fact. Positions surface again only where something
genuinely carries them — a certificate's binding transfer, and the wire format.

Assertions are attached to bindings, because bindings are what a checker can
name; locations arise only during execution and never appear in a program. So
$x\mapsto R$ is not a claim about $x$'s value but about the
location that value *is*: there exist $\ell$ and $v$ with $\rho(x)=\ell$,
$h(\ell)=v$ and $v\in R$. That one indirection is where aliasing enters, and it
is why the checked rules have
[no frame rule](PROGRAM-TYPING.md#the-reference-operations): two names can hold
the same location, and no assertion can say they do not.

Two of these forms are deliberately outside the typing judgment. A location
arises only at run time and takes its contract from the world, never from a
typing rule. A shape test is typed only in the guard of a conditional, by
`ifTag`; it has no standalone rule. The source fragment uses a singleton test
for a strict comparison with a singleton operand, the nullish test for `??` and
for `== null`, and strict equality $\equiv$ for any other strict comparison. Every test is total on values.

Substitution operates on closed substituted values. `Bindings.lean` supplies
scope and simultaneous closing substitution, which entering a node of graph
code instantiates in its run's environment. The program
typing theorem uses semantic environments of closed values.

### Graph code

A run of graph code is a term of its own: $\mathsf{goto}(E,K,l,\rho)$, about to
enter node $l$ in the environment $\rho$, and
$\mathsf{frame}(E,K,t,\rho,k,x)$, evaluating node expression $t$, then
continuing by $k$, a throw out of $t$ going to the handler $x$. Neither is
source syntax (`sourceTerm` refuses both). An environment is a list of slots
and the value every slot past it holds (`envOf`). Invocation enters the code
with the receiver, the parameters padded as a closure's are, then the
captures, then the invoked object itself, the code's self entry (a recursive
closure's read of itself, [recursive constants](SOURCE-MODEL.md#recursive-constants));
entering a node instantiates its expression in the environment; the
node's value then leaves the run or moves along an edge, whose slot map
$\mu$ acts on the pushed environment as a program's does:

```math
\frac{r,\vec a\ \text{values}\quad\mathrm{binds}(\kappa,r)}{h,\mathsf{invoke}(\mathsf{obj}(\mathit{fs},\mathsf{graph}(m,E,K,s,\vec c,\kappa,\varrho)),r,\vec a)\to h,\mathrm{entry}^{o}_\varrho(r,\vec a)}\ (\texttt{callGraph})
```

where the code's kind $`\kappa`$ binds the receiver (`Invoke.binds`):

```math
\mathrm{binds}(\mathsf{call},r)\qquad
\mathrm{binds}(\mathsf{sloppy},r)\iff r=\mathsf{obj}(\ldots)
```

`call` code is strict code's, or code that reads no `this`; `sloppy` code is
sloppy code that reads `this`, whose call binds `this` by
OrdinaryCallBindThis ([ECMA-262](REFERENCES.md#ecma-262)) with
`[[ThisMode]]` global: an object unchanged, `undefined` or `null` replaced by
the global object and a primitive by a wrapper object. The model has the
first case, the receiver bound unchanged, and no step for the others, so a
safe run calls sloppy code with objects only.

```math
\frac{\vec a\ \text{values}}{h,\mathsf{construct}(\mathsf{obj}(\mathit{fs},\mathsf{graph}(m,E,K,s,\vec c,\mathsf{construct},\varrho)),\vec a)\to h,\mathrm{entry}^{o}_\varrho(\mathsf{undefined},\vec a)}\ (\texttt{constructGraph})
```

where $o$ is the invoked object, and code without a rest enters at once,
$\mathrm{entry}^o_{\mathsf{false}}(r,\vec a)=\mathsf{goto}(E,K,s,[r,\mathrm{pad}_m(\vec a),\vec c,o])$,
and code with one first allocates the actuals past its $m$ parameters as a
fresh store, found in slot 0, below the receiver,
$\mathrm{entry}^o_{\mathsf{true}}(r,\vec a)=\mathsf{let}\ x=[\vec a_{\ge m}]\ \mathsf{in}\ \mathsf{goto}(E,K,s,[x,r,\mathrm{pad}_m(\vec a),\vec c,o])$
(`CallArguments.graphEntry`). Padding never enters the store. Code with
$\kappa=\mathsf{construct}$ has no call step: a plain call of a class value
throws. `new` on code with a rest is not yet a construction
(`CallArguments.construction`): padding omitted actuals would change its
store.

```math
\frac{E_l=e\quad K_l=(k,x)}{h,\mathsf{goto}(E,K,l,\rho)\to h,\mathsf{frame}(E,K,e[\rho],\rho,k,x)}\ (\texttt{gotoEnter})
\qquad
\frac{h,t\to h',t'}{h,\mathsf{frame}(E,K,t,\rho,k,x)\to h',\mathsf{frame}(E,K,t',\rho,k,x)}\ (\texttt{frameC})
```

```math
\frac{v\ \text{a value}}{h,\mathsf{frame}(E,K,v,\rho,\mathsf{ret},x)\to h,v}\ (\texttt{frameRet})
\qquad
\frac{v\ \text{a value}}{h,\mathsf{frame}(E,K,v,\rho,\mathsf{bind}(l,\mu),x)\to h,\mathsf{goto}(E,K,l,\mu(v::\rho))}\ (\texttt{frameBind})
```

```math
\frac{t\ \text{raises}\ v}{h,\mathsf{frame}(E,K,t,\rho,k,(l,\mu))\to h,\mathsf{goto}(E,K,l,\mu(v::\rho))}\ (\texttt{frameHandle})
\qquad
\frac{t\ \text{raises}\ v}{h,\mathsf{frame}(E,K,t,\rho,k,\mathsf{none})\to h,\mathsf{throw}\ v}\ (\texttt{frameRaise})
```

and `effect`, `branch`, `branchBind` and `tagBind` move as their program
continuations do (`frameEffect`, `frameYes`, `frameNo`, `frameYesBind`,
`frameNoBind`, `frameTag`). A throw leaving the run is a throw of the call
term, which the caller's context carries on. The steps stay deterministic
(`Step_det`).

A run steps as the code's program graph does from the same label and
environment: `GraphCode.Sim` relates the two, and `GraphCode.safe_of_sim`
carries the graph's safety to the run, so a checked graph code is safe at its
signature (`GraphCode.goto_safe`).

## One meaning for callable contracts

The core equation is a behavioral promise, shared by fixed signatures, rest
signatures, overloads and callable objects. Let $R_c$ be the receiver family,
$\mathcal A$ describe the admitted lists of actual values and $R$ the result
family. Then

```math
f\in\mathcal F(R_c,\mathcal A,R)(n,W)\iff
\mathrm{Invocable}(f)\ \land\
\forall j<n,\ U\succeq W{\downarrow}j,\ h,r,\vec v.\;
\begin{aligned}
&\mathrm{WorldAdm}(U)\land\mathrm{HeapOk}(j,U,h)
 \land r\in R_c(j,U)\land\mathrm{Values}(\vec v)\land\mathcal A(j,U,\vec v)\\
&\quad\Longrightarrow\exists t.\;
 \mathrm{Invoke}(f,r,\vec v,t)\land\mathrm{Safe}(R,j,U,h,t).
\end{aligned}
```

This is `Invocable` together with `Safety.Promise`. The receiver is not an
actual: it changes no arity, optional position or rest, and $\mathcal A$
never sees it. A plain call passes `undefined`; a method call, the object the
method was read from; `.call`, its first argument. A signature indifferent to
its receiver states top. Weakening is contravariant in $R_c$ as in each
domain: a function that ignores its receiver meets any receiver requirement,
and one that reads its receiver cannot be widened to accept arbitrary ones. `Invoke` dispatches the
saved code and yields a term; `Safe` describes its execution, including any
allocation, mutation or further call. The call spends a step before using
this lower-budget guarantee. Safety permits nontermination. Neither the
contract nor the equation requires a particular parameter-binding descriptor.

An imported interface method `m(P): R` is lowered to a writable `m` field
whose function contract is $\mathcal F(I,P,R)$, where $I$ is the containing
interface's recursive graph node. Thus a call through `value.m` passes the
required $I$ receiver; copying the function and calling it plainly passes
`undefined` and cannot use that promise. This uses the same field and call
rules as an explicitly function-valued property. It is a client contract
relative to the imported declaration, not a proof of the method's implementation.
It is stronger than TypeScript's structural method declaration: a method body
may depend on implementation-private state and fail when called with another
structurally matching receiver. A checked implementation or an explicit external
assumption must establish this promise before any imported runtime value is
claimed to inhabit the interface.

This supplies the call component of the existing
[callable-object equation](CALLABLES.md#types-describe-behaviour-not-internal-storage):

```math
\mathsf{Callable}(L;P)=\mathsf{Fun}\cap\mathsf{Props}(P)
  \cap\bigcap_{\sigma\in L}\mathsf{CallSpec}(\sigma).
```

Here `Invocable` supplies function shape, `propsT` supplies the field
requirements, and `Promise` supplies each call specification. The same value
must satisfy every conjunct; neither overloads nor generic instantiation
allocate a replacement function or choose a new storage contract.

All the callable uses build on this equation:

- A fixed signature uses `ArgsShort`: written actuals meet their corresponding
  domains, and each omitted trailing domain admits `undefined`. A rest
  signature uses `ArgsRest`: its fixed domains admit the first actuals as a
  fixed signature's do, and the actuals past them, as one argument list, are
  at its rest contract, a predicate on lists (`ArgFam`); an element rest
  admits any number at its element. `callsT` and `restsT` conjoin `Promise` over
  their respective signature lists.
- Overloads conjoin promises on **one value**. The `arrs L S` clause combines
  fixed and variadic promises; either list may be empty. Thus compatible
  fixed and variadic contracts overlap. Their syntax does not divide runtime
  functions into disjoint type shapes.
- A callable object's field contract is intersected with these same promises:
  `callable P Ps L S` means `propsT P Ps ∩ callsT L ∩ restsT S`.
  Reads and writes use the fixed world contracts of the fields; invocation
  uses the call promises on that same object. Returning, passing or capturing
  a callback simply uses this family as a result, domain or environment type.
- Quantification requires the same value, in the same world, to satisfy the
  promises at every admissible binder assignment. A scheme row
  (`schemeSemWithArgs`) universally quantifies the conjunction of instantiated
  `callsT` and `restsT`; its shape condition is `Invocable`, even when no
  assignment satisfies the bounds. `T[]` denotes invariant array storage under
  the same assignment, and each invocation allocates its rest store with that
  contract.
- Contract weakening follows `PromiseWith.weaken`: admit fewer argument lists
  and weaken the result. Fixed-to-variadic coverage is not generally valid
  from a fixed contract alone, since it promises nothing about longer lists.
  Concrete code of fixed arity can nevertheless have stronger behavior
  (`restsT_of_graph`).

The [typing rules](PROGRAM-TYPING.md#expressions) build creation and
application rules on this meaning. What code promises is proved where it is
created, from its graph's check at each signature (`GraphCodeSpec`):
`callsT_of_graph`, `restsT_of_graph`, `restsT_of_graphRest` and
`ctorsT_of_graph` turn a checked code into the behavioral contracts above.

### Effect-qualified call contracts

[CallEffects.lean](../lean/Verification/Semantics/CallEffects.lean) extends exactly the callable equation above;
graph code, expression effects and equation lowering read its contracts.
For a signature effect $\epsilon$, replace
its conclusion `Safe` with

```math
\exists t.\;\mathrm{Invoke}(f,r,\vec v,t)\land
\mathrm{SafePost}(R,Q_\epsilon(h),j,U,h,t).
```

All quantifiers and premises are unchanged: the guarantee holds at every future
world and compatible entry heap, for every receiver and actual list admitted
by that signature. Write the resulting family
$\mathcal F_\epsilon(R_c,\mathcal A,R)$. An effect $`\epsilon = (\Phi, \pi, \varphi, \sigma)`$ is
a [closed footprint](FOOTPRINTS.md#changes-and-footprints) $`\Phi`$, an
optional promise $`\pi`$, and two Booleans: $`\varphi`$, a fresh result, and
$`\sigma`$, the receiver's store excepted. Its postcondition, for a call
with receiver $`r`$, is the footprint's, on every old location but $`r`$'s
array store where $`\sigma`$, and the result's store allocated by the call
where $`\varphi`$ (`Effect.post`):

```math
Q_{\epsilon}(r,h)(h',v)=\mathsf{Post}_\Phi^{\,\neg\sigma\lor l\ne\mathsf{store}(r)}(h,h')\land
(\varphi\Rightarrow \exists s.\ \mathsf{store}(v)=s\land |h|\le s),
```

where $`\mathsf{Post}_\Phi^{P}`$ is the footprint's postcondition on the old
locations $`l`$ satisfying $`P`$ (`Closed.HoldsOn`) and $`\mathsf{store}(v)`$
the location of $`v`$'s array store (`storeOf`).

Two footprints are its extremes: the empty one, $`Q_{(\emptyset,\pi)}(h)(h',v)=(h\preceq h')`$,
where $h\preceq h'$ means that $h'$ extends the heap list $h$ without changing
any existing entry (`Closed.holds_empty`), and the one letting every location
change, $`Q_{(\top,\pi)}(h)(h',v)=(|h|\le|h'|)`$, which every run meets
(`Closed.holds_top`, `Closed.top_safe`).

A promise is about one actual, the $`p`$-th, written $`v_p`$ (`undefined`
where the call passes fewer). It replaces the result family $`R`$ by one
relating the result to $`v_p`$, with $`R`$ the promise's type:

```math
R^{\mathsf{guards}\,p}(v) = (v=\mathsf{true}\land v_p\in R)\lor v=\mathsf{false},\qquad
R^{\mathsf{asserts}\,p}(v) = (v=\mathsf{undefined}\land v_p\in R).
```

Membership of $`v_p`$ is taken at the world and heap of the return. One
signature covers another when its footprint is within the other's, their
promises are the same, it states a fresh result where the other does, and it
excepts the receiver's store only where the other does or lets everything
change (`Effect.covers`); a conjunction of signatures with the same promise
and exception meets their footprints (`Effect.meet`). A bound function
forwards to its target with a saved receiver: its signature keeps the fresh
result and lets everything change where the target's excepts the receiver's
store (`Effect.drop`). The promises state a type
guard's and an assertion function's promise
([user-defined guards](SOURCE-CONTRACTS.md#user-defined-guards)). Fresh allocation is allowed. This is a guarantee at normal
return, not a ban on intermediate writes, a termination claim, or preservation
on an exceptional exit. A caller catching an exception cannot recover entry
heap facts from this effect. A callback that temporarily mutates and restores
state must still satisfy ordinary safety for all intermediate execution.

`PromiseWith` formalizes this equation; `PromiseWith.erase` forgets the
postcondition. `callsT_adm` proves admissibility for a conjunction of qualified
fixed signatures; `restsT_adm` does the same for argument-pack rests.
`PromiseWith.weaken` and the fixed/rest congruence and conjunction lemmas
justify effect-aware contract operations. `call_safe` proves application from
the qualified promise without access to the body.
[GraphCode.lean](../lean/Verification/Programs/GraphCode.lean) checks ordinary
graph evidence and the effect together in `codeCheckedUsing`; `codeChecked_sound`
establishes the semantic contract used by fixed and variadic closure introduction.
The positive type graph carries the effect on every signature. Source export
and inference still need integration.

This remains a value type, despite mentioning heaps: membership quantifies over
**all** eligible entry heaps. It does not store an observation about the current
contents of one captured cell. A closure must meet the effect whenever it is
called under the signature's contract, not just in the state where it was
created. The effect concerns typed invocations only; it promises nothing for
arguments outside the signature, such as an object passed to a numeric callback
whose arithmetic would then invoke JavaScript conversion hooks.

A native method may use such a callback contract as a premise of its own
specification. The built-ins use ordinary array construction: arrays own
no `constructor`, and the host preserves the standard constructor/species
behavior, including across external calls. Under that premise, `map` on a dense
array can use callback heap preservation to retain source presence throughout
traversal and hence result density. An unrestricted callback justifies only a
sparse result. The host premise is explicit in the
[boundary](SOURCE-MODEL.md#exact-contracts-and-native-effects); custom species are
outside this semantics. Native compliance remains a separate review obligation,
not a consequence of `PromiseWith`'s Lean proofs. The [planned typing rules](SOURCE-ELABORATION.md#certifying-inferred-call-effects)
state where the callback guarantee is established and consumed.

## Argument-list preparation

Applications use `invoke f r args`: the callee, the receiver, the ordered
actuals. `call f args` abbreviates `invoke f undefined args`, and `app f a` the
singleton call; neither is a second form of call. Substitution, scope checking,
capture instantiation and object-name traversal visit the receiver, the entire
list and every code descriptor, including a `bound` descriptor's saved values.
[CallArguments.lean](../lean/Verification/Semantics/CallArguments.lean) defines call preparation: its `Frame` keeps the callee, the receiver and
ordered arguments separate from invocation.

`Prepare` evaluates the callee, then the receiver, then processes arguments from
left to right.
`Step.callArg` requires earlier arguments to be values. A `spread` is not a
value: `Step.callSpread` consumes its ready store before any later argument
can step, replacing holes with `undefined`; `new` reads one alike
(`Step.constructSpread`), and a store literal (`Step.arrSpread`). Splicing can change list length.
`call_step_iff` proves every call step to be preparation or dispatch, and
`invoke_deterministic` that dispatch of a frame yields one term. A frame
whose operands are values dispatches to the invocation code its callee holds
(`Invoke`); dispatch does not establish typing.

Code uses `parameters n args` to pad missing positions with `undefined` and
discard extra positions after their effects have occurred; entering graph
code places the receiver in slot 0 and these values after it, without
allocating (`graphEntry`). Code collecting a rest pads its fixed positions in
the same way, while `args.drop n` becomes a fresh rest store in slot 0, below
the receiver. Padding never enters the rest store. Dispatch itself leaves the
heap unchanged; the yielded term allocates the store with the ordinary store
step, and the code wraps it into an array with the prototype it captured, as
an array literal is allocated. These operational distinctions are independent
of the contracts callers use.

A `bound` descriptor dispatches without binding anything: `Step.callBound`
turns `invoke (bound f r₀ p⃗) r a⃗` into `invoke f r₀ (p⃗ ++ a⃗)`, dropping the
receiver `r` it was given, so binding a bound function forwards to it, which
forwards with the first saved receiver.
`CallEffects.callsT_bound` proves the residual contract: a target meeting
$(R_t, \vec P \mathbin{+\!\!+} \vec D, R)$ with a saved receiver in $R_t$ and a
saved prefix in $\vec P$ gives an object meeting $(R_c, \vec D, R)$ for any
$R_c$, and `CallEffects.restsT_bound` the same for a variadic target, whose residual keeps
its rest, when the rest admits the prefix's values past the fixed positions in
front of any pack it admits, as an element rest does. There is no forwarding wrapper closure: construction and
`new.target` are not modelled, and a bound function has no own fields.

`.apply` is a source lowering onto these steps, not a new preparation: it saves
the target, the receiver and the list, then reads the list's length and each
index in order with the ordinary store operations, then invokes the target with
those elements. It never iterates the list, so it shares the prepared actual
list with ordinary calls but not the spread's operation.

[ArgumentContracts.lean](../lean/Verification/Semantics/ArgumentContracts.lean) states same-level contracts on argument lists and proves dispatch under them safe;
its `call_safe` obtains safe dispatch from a behavioral promise.
`ProgramTyping.call_safe_short` first evaluates the callee and composes effectful
arguments using `bind_list` and `FutureSafe`. `ArgsT_transfer` preserves saved
value types as the budget decreases and the world extends. Variadic calls
add `RestCalls.spread_parts_safe` and `call_elim_rest`; source lowering copies
a spread's elements at its evaluation point when later operands run code.
The copy preserves element values, including object references, rather than
merely saving the source array's identity.

`callsT_adm`, `restsT_adm` and the corresponding congruence lemmas establish
world monotonicity and guardedness of both domains and results. The
source/calculus correspondence remains the documented trusted-adapter
boundary; these theorems establish safety of the extracted program.

Worlds have different types at different budgets. Consequently, “the type is
just the intersection of its approximations” is not a complete standalone
account of membership. The proved subtype soundness theorem quantifies over
every budget, matching world, and value; no quotient of worlds or all-budget
observational equivalence is assumed.

## Computations and recursive types

`Safe A 0 W h e` imposes no obligation. At a positive budget, either `e` is a
value belonging to `A`, or it throws a closed JavaScript value, or it can step with one
budget spent, preserving heap satisfaction in an admissible extension of the
truncated world. This is partial correctness/safety, not termination, and a
throw is an outcome, as a value is: a type says what a value is, never that
none is thrown ([SOURCE-MODEL](SOURCE-MODEL.md#throws)). The model is step-indexed
([Appel and McAllester 2001](REFERENCES.md#appel-and-mcallester-2001)) with worlds for mutable state ([Ahmed 2004](REFERENCES.md#ahmed-2004)); the
safety shape is that of [Wright and Felleisen 1994](REFERENCES.md#wright-and-felleisen-1994).

[Worlds.lean](../lean/Verification/Semantics/Worlds.lean) defines stratified worlds, the contract each location is for, and proves world extension a preorder preserved by truncation (`WExt_trans`, `WExt_trunc`). A world is admissible (`WorldAdm`) when each contract survives the world growing and admits only values, so a heap meeting an admissible world above level zero holds values at every location (`heap_values`).
[Heaps.lean](../lean/Verification/Semantics/Heaps.lean) defines the heap invariant `HeapOk`, every location holding a value meeting its contract, and proves reads, writes and allocation sound for it (`read_sound`, `write_sound`, `heap_alloc`).
[Types.lean](../lean/Verification/Types/Types.lean) defines semantic types: budget-indexed families judged against a world.
[Safety.lean](../lean/Verification/Semantics/Safety.lean) defines the safety predicate `Safe` and function types, and proves `Safe` monotone in its result type (`Safe_mono`) and the function types admissible (`callsT_adm`, `restsT_adm`).

**Throws.** `throw a` (`Tm.throw`) evaluates `a` (`throwC`), then throws its
value. A term *throws* $`v`$ (`Raises t v`) when `throw v`, $`v`$ a JavaScript value, is in
evaluation position: under exactly the contexts the step relation evaluates
in, one constructor per congruence rule of `Step`:

```math
\frac{v\in J}{\mathsf{throw}\ v\ \text{raises}\ v}
\qquad
\frac{t\ \text{raises}\ v}{E[t]\ \text{raises}\ v}
\qquad
E ::= [\,]\ a\mid f\,[\,]\mid\mathsf{let}([\,],b)\mid\mathsf{read}([\,])\mid v\mathbin{op}[\,]\mid\cdots
```

Here $`J`$ is the [source-value universe](SOURCE-MODEL.md#source-value-boundary).
`raises_sourceVal` proves that every exception belongs to it. Throwing an
internal store is stuck; a safe external callable therefore cannot expose a
store as an exception.

A throwing term is not a value, does not step, and throws one value
(`raises_not_val`, `raises_no_step`, `Raises_det`), so evaluation stays
deterministic. No step propagates a throw: the context closure is the
predicate, and a handler, where there is one, catches it
([graphs](PROGRAM-TYPING.md#checked-control-flow-graphs)). The safety
predicate is relative to an **exception family** $`\Xi`$, the values a throw
carries:

```math
\mathit{Safe}_{\Xi}(A)(n{+}1,W,h,t)\iff
\bigl(t\in A(n{+}1,W)\ \lor\ \exists v\ \text{closed}.\ t\ \text{raises}\ v\land v\in\Xi(n{+}1,W)\bigr)\ \lor\
\exists W',h',t'.\ h,t\to h',t'\land\ldots\land\mathit{Safe}_{\Xi}(A)(n,W',h',t')
```

A graph's exception family is the built-ins' `unknown`,
$`\Xi_G=\mathsf{builtinExc}_G`$ ([the array invariant](#the-array-invariant)),
and every function type of the graph is read with it (`callsT`, `restsT`,
`ctorsT`, `PromiseWith`, `methodT`, through `semWithArgs`): a function a type
promises throws only values of `unknown`. An operator that throws
(`binopThrows`) throws a fresh object owning no key, which every graph's
exception family holds (`ErrorsIn`, `builtinExc_errors`).

Every composition lemma takes, beside its context's step rule, the context's
throw rule (`bind`, `bind_list` with `ArgRaises`, `ctx_bind`,
`HeapObservations.bind`); `thrown_safe` makes a term throwing a value of
$`\Xi`$ safe at every type. `SafePost` is the same with no postcondition on a throw: the facts it
states describe the heap a value is produced in.

`SafeGraph` is the same predicate one level up, for the machine that runs a
control-flow graph rather than a single term. Its states are

```math
s ::= \mathsf{at}(p,\rho)\mid\mathsf{eval}(t,\rho,k,x)\mid\mathsf{done}(v)\mid\mathsf{raised}(v),
```

where $p$ is a program point (a node label, not a location), $\rho$ an
environment of closed values, $k$ a
[continuation](PROGRAM-TYPING.md#checked-control-flow-graphs) and $x$ the
node's handler, if it has one. Entering a node
instantiates its term against $\rho$; the term then steps as usual; a value meets
the node's continuation, which either finishes the run or moves to the next label
with a transformed environment; a throw goes to the handler, the thrown value
bound, or without one ends the run in $\mathsf{raised}(v)$. `SafeGraph Ξ P T n W h s`
says that at a positive budget the state is $\mathsf{done}(v)$ with $v\in T$,
or $\mathsf{raised}(v)$ with $v$ closed and in $`\Xi`$, or it can take one
graph transition, spending a budget and preserving heap satisfaction in an
admissible future, and remain safe there. `Safe` is the special case with no
graph. Starting a graph means starting at $\mathsf{at}(p,\rho)$ for the entry
point and the input environment.

`CallableConjunctions.objectsT` combines invariant field requirements and
fixed call promises on one value. `PositiveNormalization.sem` intersects it
with `restsT` for the graph's `callable first rest arrows variadic` clause.
The plain `arrs arrows variadic` clause carries the same call promises without
field requirements. Normalization concatenates both kinds of signature and
retains invariant field operands. Checked creation establishes field storage
and code obligations separately; calls, reads and writes use the corresponding
part of the same object's contract. The common function equation above governs
all these call obligations.

A guarded operator consults recursive operands only below the current budget.
Its approximation tower stabilizes at every finite observation level, and the
diagonal is a fixed point. [Tower.lean](../lean/Verification/Semantics/Tower.lean) supplies that construction for graph
interpretations. It does not require monotonicity of the recursive operand, so
negative occurrences in function domains are permitted when guarded. This is
not a greatest-fixed-point construction on unindexed sets of values; it is
guarded recursion ([Nakano 2000](REFERENCES.md#nakano-2000); [Birkedal et al. 2012](REFERENCES.md#birkedal-et-al-2012))
with [Banach's](REFERENCES.md#banach-1922) fixed point.

The type graph is a finite system of guarded positive formulas in normal form;
no cycle is unfolded during normalization. See the grammar and equations
in [POSITIVE-TYPES.md](POSITIVE-TYPES.md).

## The array invariant

`Array.isArray` holds of an object owning the store key $\sigma$
([operational language](#operational-language)); what makes such an object an
array of `Array.prototype` is an **invariant** of every object the program
receives or allocates: it holds a possibly sparse store and the built-in prototype, and
owns no key that prototype provides. The model states it in the meaning of
types, not in the heap premise: the tested value is in a slot, not in the heap,
and it came from an input, a read, a call's result or an allocation, each of
which a type describes. With $\mathcal B$ the graph's built-ins (`ArrayBuiltins`: the
row of `ArrayProto`, $P_{\mathcal B}$; the row of `unknown`, $U_{\mathcal B}$;
and $N_{\mathcal B}$, `ArrayProto`'s declared keys plus `constructor` and
`then`):

```math
\mathsf{Arr}_{\mathcal B}{}_n(W,v)\iff\forall\mathit{flds}.\;
v=\mathsf{obj}(\mathit{flds},\mathsf{absent})\land\sigma\in\mathrm{dom}(\mathit{flds})\Rightarrow
\mathsf{view}(\sigma{:}\mathsf{Store}(⟦U_{\mathcal B}⟧),\mathsf{proto}{:}⟦P_{\mathcal B}⟧)_n(W,v)
\land\mathsf{own}(\mathsf{outside}\,N_{\mathcal B})_n(W,v)
\land\mathsf{numericOwn}_n(W,\mathit{flds})
```

with $`\mathsf{Store}(U)`$ the possibly sparse stores of values of $`U`$
(`builtinStoreT`; `PositiveGraphs.arrayInvariant`), and
$`\mathsf{numericOwn}`$ stating `Array<T>`'s declared `[n: number]: T` of
every array type at once, with $`c_\sigma`$ the contract of the store's
location and $`c_l`$ that of an own field's:

```math
\mathsf{numericOwn}_n(W,\mathit{flds})\iff
\forall\kappa\in\mathsf{numeric}.\;\mathit{flds}(\kappa)=l\Rightarrow
\forall j{+}1<n.\;\forall A.\;
c_{\sigma,j+1}\subseteq\mathsf{Store}(A)_{j+1}\Rightarrow c_{l,j}\subseteq A_j .
```

A store's contract at level $`j+1`$ states its elements' contracts at $`j`$,
so the field holds at $`j`$ what an element does: an array of a type whose
store holds $`T`$ holds $`T`$ under its own canonical numeric keys too, below
the world's level (`numericOwn`, `numeric_of_inv`). An array whose store's
contract admits every store of `T[]` and whose numeric fields hold $`T`$
meets it, by the definition above, so an input with `a[-1] = 1` at
`number[]` is one. An allocation owning the store key
owns no field at such a key (`allocBuiltins`). Every record, dictionary
and `source` clause of a row means its members meeting it; in a graph
stating no built-ins, its members owning $`\sigma`$ hold a list there
(`storeListT`, an array's store being one whatever the built-ins)
(`Clause.carriesInvariant`, `builtinInvariant`, `rowSem`;
[POSITIVE-TYPES](POSITIVE-TYPES.md#the-built-in-array-invariant)), so the
built-ins' `unknown` is

```math
\Xi_{\mathcal B}{}_n(W,v)\iff v\in J\land\mathsf{Arr}_{\mathcal B}{}_n(W,v)
```

(`builtinExc`), the graph's exception family ([throws](#computations-and-recursive-types)).
The invariant reads the world only: the contract of $\sigma$'s location
implies a store of values of `unknown` in every world and heap to come, and
the contract of $\mathsf{proto}$'s implies `ArrayProto`; $`U_{\mathcal B}`$
and $`P_{\mathcal B}`$ are read below the level, through those contracts, so
the recursion through `unknown`'s own meaning is guarded. A world grows only
by appending contracts and never replaces one, so the invariant is admissible
(`arrayInvariant_adm`), and nothing a step does to the heap can falsify it.

**Every step keeps it.** A value's keys and their locations are its identity,
fixed at its allocation, so only allocation creates a value the invariant is
about:

- an allocation from named fields (`HasTyUsing.alloc`) owning $\sigma$ is typed only
  as a built-in array: its store field at a store type whose positions
  are of JavaScript values, each of which is a value of `unknown`
  (`sourceTy_exc`, `unknownTy_sound`), its prototype field at
  $P_{\mathcal B}$, no name among $N_{\mathcal B}$ (`allocBuiltins`,
  `allocBuiltins_sound`); every other allocation owns no $\sigma$
  (`builtinInvariant_of_lookup`);
- a literal allocated at a dictionary names neither $\sigma$ nor the prototype
  key (`HasTyUsing.allocDict`);
- a merge, the copy a spread or a key-adding write is, allocates the
  accumulator's fields but its store and the source's copied keys and index
  keys, never $\sigma$ (`ObjectMerge.mergeParts_store`);
- closures, bound functions and class values carry code, and `isArray` is false
  of them;
- a write stores a value at an existing location and adds no key; the heap is
  not read by the invariant, and a location's contract is fixed.

A read, a call's result, a caught value and a value passed on are values of
types, which already state what they state. A value of a type of JavaScript
values is one of `unknown` (`sourceTy_exc`): a clause the invariant does not
apply to, top aside, has no plain object among its members
(`semWithArgs_not_plain`). So a `throw` throws a value of `unknown`
(`SourceValues.exc`), and a handler binding its exception at `unknown`
binds a value of it (`admitsAll_sound`).

**The premise.** The safety theorem (`checkJson_safe`) quantifies over
environments meeting the unit's inputs at their types (`EnvOk`), so a value
the unit receives at a record, a dictionary or `unknown` meets the invariant:
an object owning an array's store is a possibly sparse array of `unknown`
values holding `Array.prototype` (meeting `ArrayProto`) and owning none of
its keys; and a function the unit receives throws only such values. That is
an assumption about the host and the unit's callers, stated in the
[trust surface](DESIGN.md#trust-surface). The heap premise `HeapOk` is
unchanged.

**Type parameters and classes.** A type parameter's row asks what its
assignment gives: an assignment within a bound of `unknown`, a record or a
dictionary meets the invariant through the bound's meaning, and a qualified
binder's descriptor families are within the built-ins' `unknown`
(`ResolutionDescriptors.Capabilities`). No invariant ties an object whose
prototype chain holds a class's prototype to the class's fields: JavaScript
gives any object any prototype (`Object.create`, `Object.setPrototypeOf`,
`Reflect.construct` with another new target; [ECMA-262](REFERENCES.md#ecma-262)),
so `x instanceof C` does not narrow `unknown`.

## Current-content assertions and postconditions

The [assertion grammar](POSITIVE-TYPES.md#state-assertion-grammar) defines the
notation and its separation from ordinary types. This section gives its meaning.

A world records a location's persistent storage contract, while a heap records
its current contents. Both a true heap and a false heap can satisfy the same
Boolean world. A point claim `{ value: B = R }` combines the invariant reference
with a current-content predicate:

```math
\mathrm{Obs}(h,\ell,R)
\equiv \exists v.\ h(\ell)=v \land R(v),
\qquad
\mathrm{ObservedRef}(B,R,n,W,h,\ell)
\equiv \mathrm{Ref}(B)(n,W,\ell)\land\mathrm{Obs}(h,\ell,R).
```

$`\mathrm{ObservedRef}`$ is read with `HeapOk(n,W,h)`. For primitive predicates this requires the contents
to satisfy both the storage invariant and the observation. Consequently
`{ value: true = false }` is inconsistent in a satisfying heap at every positive
budget. The raw predicate without `HeapOk` does not enforce that connection;
the invariant check is vacuous at budget zero. Giving the conjunction meaning
does not require a syntactic subtype relation between `R` and `B`.

The right side of `=` is a predicate, not an initializer or a future-read promise.
Null/undefined/Boolean, numeric and string predicates are supported,
including the whole number family and exact numeric singletons, and
the nullish exclusions in the [assertion grammar](POSITIVE-TYPES.md#state-assertion-grammar),
which apply to values of any shape. These assertions are duplicable facts, not exclusive write
permissions. This is a chosen plain-cell interpretation, not a theorem equating
a producer's internal types with heap assertions.

### What is asserted, and what a heap change can touch

The property-read relation is defined for an object $`o`$ with own-field map
$`F_o`$. It covers a present location and an absent key with no prototype:

```math
\mathrm{Read}_h(o,f,v)\equiv
(\exists\ell.\ F_o(f)=\ell\land h(\ell)=v)\lor
(f\notin\mathrm{dom}(F_o)\land\mathsf{proto}\notin\mathrm{dom}(F_o)
 \land v=\mathsf{undefined}).
```

`HeapFacts.ReadGave` defines this relation. `ReadGave.step` proves its
correspondence with a single heap-preserving calculus read step.
The finite assertions distinguish environment facts from heap observations:

```math
\begin{aligned}
x=R&\equiv\rho(x)\in R,\\
x=y&\equiv\rho(x)=\rho(y),\\
x.f\mapsto R&\equiv\exists v.\ \mathrm{Read}_h(\rho(x),f,v)\land v\in R,\\
x.f\mapsto y&\equiv
  \exists\ell.\ F_{\rho(x)}(f)=\ell\land h(\ell)=\rho(y),\\
x.f\mapsto^{?}y&\equiv\mathrm{Read}_h(\rho(x),f,\rho(y)).
\end{aligned}
```

The predicate fact covers either presence or absence. A required read link
also establishes presence; an optional read link states only the read result.
The one-field notation omits $`f`$ for the private cell field.
An observation of the result excluding `undefined` proves presence for an
optional key. An observation admitting it retains both possibilities.
The [predicate vocabulary](POSITIVE-TYPES.md#state-assertion-grammar) includes
numeric singletons and the whole number family.
The $=$ atoms mention only $\rho$; the $\mapsto$ atoms mention $h$ as well, and
that is the only difference that matters. $x=R$ abbreviates membership in the
disjunction of predicates in $R$. For constant predicates this is a disjunction
of equalities; the numeric-family predicate also admits any numeric value.
Write $\Pi$ for a list of them. The remaining forms mention $h$ as
well. Write $\Sigma$ for a list of those. Both are read as the conjunction of
their atoms and extended with a comma, exactly as $\Gamma$ is; neither carries
ownership or disjointness, and the atoms are duplicable, so there is no
separating conjunction to write.

That division is the whole state discipline. No write and no call can disturb
$\Pi$, because nothing in $\Pi$ speaks about the heap: two copied references remain
the same location after any write, and a constant a variable is equal to does not
change when a cell does. Everything in $\Sigma$ is a claim about the heap as it is
now, so a write to an unknown location or a call to an unknown function can
falsify any of it. Allocation is the exception that proves it: a fresh cell
cannot be one an existing fact names, so allocation preserves both. The
checked `allocated` rule applies to both plain and callable objects through
`make`, with a known initializer slot. Typed reads also use one proof for both
kinds of bag and retain their actual descriptor in the read links. Closure
bodies may mutate when called; allocating their code does not execute them.

`ValueHolds` and the alias branch of the links in [HeapLinks.lean](../lean/Verification/Semantics/HeapLinks.lean) interpret $\Pi$;
`HeapFacts.Holds` and the read branch interpret $\Sigma$. The implementation stores
them as three lists — cell facts, value facts, and links carrying an `alias`
flag — so the links list straddles the division: the flag is what says which side
a link is on. [Program typing](PROGRAM-TYPING.md#the-reference-operations) states
the rules over $\Pi$ and $\Sigma$; the
[assertion grammar](POSITIVE-TYPES.md#state-assertion-grammar) owns the notation
for what a source claim may say.

`SafePost T Q n W h e` strengthens `Safe T n W h e`: at a positive-budget final
value it additionally requires `Q h e`; its step case uses exactly the same
operational step, truncated-world extension, admissibility and heap satisfaction.
At budget zero it is true. Divergence is permitted.
[HeapObservations.lean](../lean/Verification/Semantics/HeapObservations.lean)
defines it: `erase` yields ordinary safety, and `forget` embeds ordinary
safety with `Q = True`.

Current contents depend on the heap, so they are not a value type, and an
observation does not narrow a cell's invariant: a Boolean cell currently
`true` is a `Ref boolean`. An ordinarily typed captured writer may overwrite
such a cell, so an ordinary arrow promises no preservation of captured
current contents.

[Program typing](PROGRAM-TYPING.md#current-content-rules-semantic-layer) specifies
the operation and composition rules using this predicate;
[SOURCE-MODEL](SOURCE-MODEL.md#current-content-assertions) owns the graph-integration plan.

## What the checked development establishes

- [Rules.lean](../lean/Verification/Semantics/Rules.lean) proves the semantic typing rules for calls, heap operations, shape
  testing and branching.
- `ProgramTyping.lean` proves safety by induction on syntactic typing
  derivations (`HasTyUsing.sound`).
- `ProgramCertificates.lean` checks finite program evidence and proves an
  accepted tree a derivation (`checkTreeUsing_sound`).
- `PointClaims.lean` checks supplied environment claims against individual
  incoming edges and proves environment transfer (`checkEdge_sound`,
  `checkMapped_sound`).
- `ControlFlow.lean` enumerates every actual node and outgoing edge, handler
  edges included, then proves that every run from an accepted entry is safe:
  it returns at the result type, ends in a throw of the exception family, or
  takes a transition (`accepted_inputs_safe`), including cyclic graphs. It
  reuses expression steps and adds explicit dispatch, transfer and handler
  steps.
- `PositiveNormalization.lean` proves the clause meet sound (`meet_sound`).
- `PositiveRules.lean` defines declarative subtype rules and proves their
  semantic soundness; `SchemeInstances.lean` adds instances of a scheme row and
  `PairFamilies.lean` families of pairs.
- `PositiveCertificates.lean` proves checker soundness for those rules
  (`checkUsing_sound`) and transports accepted subtyping to value
  subsumption (`acceptedUsing`).

## A design constraint

Unrestricted arrow-result distribution fails:

```text
((x: A) => B) & ((x: A) => C) ≤ (x: A) => B & C
```

An allocating function can satisfy the two signatures using different
invariant choices for a new cell; requiring a single result-world
interpretation is stronger. This counterexample is argued here and has no
Lean proof. The maintained combination rule uses a conservative shape
condition instead. The law holds in set-theoretic semantic subtyping
([Frisch, Castagna and Benzaken 2008](REFERENCES.md#frisch-castagna-and-benzaken-2008)), which has no state.

## Remaining scope

The source adapter and graph consumer are connected; their guarantees are in
[Program typing](PROGRAM-TYPING.md) and the
[request protocol](REQUEST-PROTOCOL.md). Source-to-graph correspondence is
not proved: the lowering is a trusted step
([trust surface](DESIGN.md#trust-surface)). Generic bodies are graph requests
over parameter rows, certified at every assignment of those rows
([generic bodies](DESIGN.md#generic-bodies)); general difference and negation
types are not in the calculus. A receiver is bound unchanged: sloppy
code's global-object substitution and primitive boxing have no step
([graph code](#graph-code)); `new.target` and a bound function's reflective
properties (`name`, `length`) are not modelled, and the source forms that
would need them are refused. What the source
fragment admits is summarised in the
[README](../README.md#status); what it refuses, on principle or
as a model limit, is the [fragment boundary](SOURCE-FRAGMENT.md#fragment-boundary),
and the open work is
[next steps](../WORK.md#next-steps).
