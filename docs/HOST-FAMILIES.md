# Host families

Libraries hand programs objects of a **tagged family**: one field, the
**tag**, whose value determines the object's shape. Examples are the
TypeScript compiler API's nodes (`kind`), ESTree and Babel nodes (`type`) and
DOM nodes (`nodeType`). The library also exports **guard functions** whose
code is a test of the tag (`ts.isIdentifier`, `t.isIdentifier`).
TScert already narrows program-declared discriminated unions by a literal
field ([union shapes](UNION-SHAPES.md), R3). A host family is the external
case: the declared type of a family member (`Node`, `Expression`) does not
spell the union of its shapes, and the guards are library code.

This document specifies one mechanism for every such family, parameterized
by a reviewed **family description**. Each part has one implementation,
which reads the description; no part names a family. The
[compiler API](COMPILER-API.md) is the first instance. This document is a
design: the pipeline implements no part of it, and its Lean obligations are
unproved.

## The parts

### Tag sets

A tag's values are numbers or strings. A union of two or more tag values is
one clause of the type language, a **tag set**: for a finite set $`S`$ of
number bit patterns, or of strings, with $`|S|\ge 2`$, the clause
$`\mathsf{numIn}(S)`$ means exactly the numbers whose bit pattern is in
$`S`$, and $`\mathsf{strIn}(S)`$ exactly the strings in $`S`$. Tag sets are
general clauses: a program's union of literals uses them as a family's tag
does. Every union of two or more literals of one primitive normalizes to
one, a set of one element is its literal, and two sets of one primitive in
a union are their union:

```math
\mathsf{numLit}(b_1)\cup\cdots\cup\mathsf{numLit}(b_n)=\mathsf{numIn}(\{b_1,\ldots,b_n\})\quad(n\ge 2),
\qquad
\mathsf{numIn}(S)\cup\mathsf{numIn}(T)=\mathsf{numIn}(S\cup T)
```

and likewise for strings. Subtyping is inclusion of sets, and every tag set
is within its primitive:

```math
\frac{S\subseteq T}{\mathsf{numIn}(S)\le\mathsf{numIn}(T)}
\qquad
\frac{b\in S}{\mathsf{numLit}(b)\le\mathsf{numIn}(S)}
\qquad
\frac{}{\mathsf{numIn}(S)\le\mathsf{Number}}
```

A test answers on a tag set element by element, and its slices are sets
again (a set of one element is its literal, an empty one no clause):

```math
T_{\mathsf{numEq}(b)}(\mathsf{numIn}(S))=\{s\in S\mid\mathrm{numberEqual}(s,b)\},\qquad
T_{\lnot\mathsf{numEq}(b)}(\mathsf{numIn}(S))=\{s\in S\mid\lnot\mathrm{numberEqual}(s,b)\},\qquad
T_{\mathsf{truthy}}(\mathsf{numIn}(S))=S\setminus Z,\qquad
T_{\lnot\mathsf{truthy}}(\mathsf{numIn}(S))=S\cap Z
```

with $`\mathrm{numberEqual}`$ the step's equality of numbers
(`Calculus.numberEqual`, ECMAScript's `Number::equal`): $`+0`$ and $`-0`$
are equal and a NaN equals nothing, so for $`S=\{-0,1\}`$ a test against
$`+0`$ keeps $`-0`$ on its true edge, and a NaN in $`S`$ is on every false
edge. $`Z`$ is the bit patterns of $`0`$, $`-0`$ and the NaNs. String sets
slice by `strEq`, and their falsy part is `""` if $`S`$ holds it. A test of
a slot at a tag set is one node of evidence whatever $`|S|`$ is, and a field
test reaches the record arms through the field slice unchanged.

On the wire a tag set is `{"numIn": {"bits": [b, …]}}` or
`{"strIn": {"values": [s, …]}}`, sorted and distinct, at least two; a
decoder refuses any other list. A type's labels that are rows of single
literals of one primitive are one row of a tag set wherever a type is built:
the producer's claims, a source annotation's lowering and a declaration's
equation.

The demonstrated cost is a residual arm's tag ([residuals](#residuals)): 20
record arms beside one arm whose tag was a union of 330 literals took 9.2 s
through `verify-source.mts` (cbe2893, 2026-10-16). A tag set makes such a
union one clause. The cost that remains is the record arms' own, which
grows with their number (100 record arms exceeded the 30 s limit, same
measurement); it is measured as units grow.

Lean: the clauses `numIn` and `strIn` of `PositiveNormalization.Clause`, their
meaning, meets, coverings and slices, and the normalization's soundness.

### The family contract

A family description $`F`$ gives a **shape table**: for each tag value
$`t\in\mathcal T_F`$, the record type $`S_t`$, with the family's
**marker**, a required readonly view of the model's reserved key `[[host]]`
at the string literal $`m_F`$, the tag at the literal $`t`$, and the members
of the declaration $`I_t`$ the description's table rule selects, with the
description's audited corrections applied. The model's host objects own
`[[host]]`, and no allocation of the program does
([host classification](COMPILER-API.md#the-host-classification)), so no
program object meets the marker.

A family type $`A`$, a declared type of the family whose tag is no set of
literals (an abstract base, the root, an alias of one), is the union of the
shapes of its **members**:

```math
\frac{A\ \text{a family type of}\ F,\quad \text{the tag of}\ A\ \text{not a set of literals}}
     {⟦A⟧=\textstyle\bigcup\{\,S_t \mid t\in\mathrm{members}_F(A)\,\}}\ \textsf{family-union}
```

$`t\in\mathrm{members}_F(A)`$ when $`I_t`$ reaches $`A`$ through `extends`
clauses, or $`A`$ is an alias whose union reaches $`I_t`$. Membership is
computed on the declaration graph before any correction. A concrete union
(`Identifier | PrivateIdentifier`) is read as declared.

#### Residuals

A unit's family union keeps the shapes of the tag values $`K_u`$ its tests
and types name, and one residual arm for the rest, the join of the shapes it
replaces:

```math
⟦A⟧_u=\textstyle\bigcup\{\,S_t\mid t\in K_u\cap\mathrm{members}_F(A)\,\}\ \cup\ R_u,
\qquad
R_u=\textstyle\bigsqcup\{\,S_t\mid t\in\mathrm{members}_F(A)\setminus K_u\,\}
```

The join of records keeps the fields every operand has, each at the union of
its operands' types and optional where any operand has it optional, the tag
at the tag set of the literals, and the marker. Each replaced shape is below
$`R_u`$: every member of $`R_u`$ is a member of $`S_t`$, a readonly view
whose type contains $`S_t`$'s, which covariance admits, the tag included;
an optional member of $`R_u`$ admits a required one; a member the join
drops is forgotten, which record subtyping allows for every field mode. So
$`⟦A⟧\subseteq⟦A⟧_u`$, with no invariant field widened. The client never
produces $`R_u`$. Shapes with the same members and different tag values are
one arm whose tag is their tag set. $`K_u`$ is the tag values the unit's
tests name (comparisons with the tag's constants, `case` labels, and the tag
sets of the guards it calls) and those of the family types it names whose
tag is a set of literals.

#### Agreement across units

Two units read one family type with different arms, whose record meanings
differ: $`R_u`$ admits objects with the marker and only the common members.
They agree on the values that occur: a value with the marker and the tag
$`t`$ meets $`S_t`$ (trust F1′ below), so there $`⟦R_u⟧`$ is the union of the
replaced shapes' meanings and $`⟦A⟧_u=⟦A⟧_v`$. This is an external-model
obligation, stated per family in its trust rows; it is no conjunct of
`WorldAdm`, which states contract admissibility and is the premise
`checkJson_safe` keeps. The import rule's assumption that a separately
verified function meets its importer's reading rests on it.

### Guard recognition

A guard of $`F`$ is an export of the family's package whose whole function,
parameter initialization included, the **guard check** reads with the front
end's parser from the module the package's `exports` map resolves, and
accepts in this syntax:

```math
\begin{aligned}
b &::= \mathtt{return}\ c \mid \mathtt{const}\ y\ \mathtt{=}\ x.\tau\mathtt{;\ return}\ c \mid \mathtt{switch\ (}x.\tau\mathtt{)\ \{\ \overline{\mathtt{case}\ \kappa:}\ \mathtt{return\ true;\ default: return\ false;}\ \}}\\
c &::= e\ \mathtt{===}\ \kappa \mid e\ \mathtt{>=}\ \kappa \mid e\ \mathtt{<=}\ \kappa \mid c\ \mathtt{||}\ c \mid c\ \mathtt{\&\&}\ c \mid h(e)\\
e &::= x.\tau \mid y \mid x
\end{aligned}
```

with $`\tau`$ the family's tag field, $`x`$ the guard's one parameter and
$`\kappa`$ a tag constant: a literal, or a member of the tag enum the
description names, read through the module's import binding of it. The side
conditions, each checked on the resolved files: the enum binding and every
helper $`h`$ are the module's own bindings, never reassigned; a helper is a
function declaration whose body is again in this syntax; the helper graph
is acyclic; the body declares nothing but $`y`$, assigns nothing, and reads
only its parameter's tag, or the parameter itself for a guard taking a tag
value. Any other effect is outside the syntax. The result is a function of
the tag: the check computes $`K_g\subseteq\mathcal T_F`$ by evaluating $`c`$
over $`\mathcal T_F`$, and a guard taking a tag value must be built from
equalities alone. The description lists the guards outside the syntax, with
their texts; such a guard is read at its declared signature.

A call is recognized by **resolution**, never by name: its callee resolves
through the unit's import binding to the checked export of the identified
package. A same-named local function, a re-bound name, or any other callee
is an ordinary call. Where the argument's claimed type is a family type, so
that its marker is stated, the parser writes the call as one evaluation of
the argument followed by the test of its tag:

```math
\frac{g\ \text{a checked guard of}\ F,\quad K_g=\{t_1,\ldots,t_n\},\quad e\ \text{at a family type of}\ F}
     {g(e)\ \leadsto\ \mathsf{let}\ y=e\ \mathsf{in}\ y.\tau\equiv t_1\lor\cdots\lor y.\tau\equiv t_n}\ \textsf{host-guard}
```

with $`y`$ fresh, or $`y`$ the binding itself where $`e`$ is an immutable
name. A call with a spread or with an argument past the guard's parameter is
refused. Reading $`\tau`$ again gives the same value (F2), runs no code and
throws nothing (F4), so the chain has the call's result, effects and
exceptions. The fragment gains no form: Lean sees reads and tests, and
narrows both edges by `if-field` through the family union, since the test is
the guard's body. A guard of another argument type keeps its declared
signature ([user-defined guards](SOURCE-CONTRACTS.md#user-defined-guards)).

### Stable members

The description's **stable-member rule** names the members of each shape
whose read gives the same value every time (F2). The trusted front end, and
nothing else, marks them **stable views** in the shapes it emits.

A **stable contract** is one fixed value: a location contract $`c`$ is
stable when
$`\exists v_0.\ \forall j, U, u.\ c_j(U,u)\Rightarrow u=v_0`$, the same
$`v_0`$ at every level and world. A stable view of $`f`$ at $`B`$ holds of an
object whose field $`f`$ is a location with a stable contract implying
$`B`$. Truncation and world extension keep it. A stable view is below the
plain view of the same type; no rule makes a stable view of a plain one, of
an invariant field or of an optional one; mappings and subtyping keep the
flag. Decoders accept the flag only in the rows of the declaration document
the front end emits for an active family, so a claim stating a stable view
the declarations do not give is refused.

**Read equality.** A test refines a value, and the narrowing rules
([guards](SOURCE-CONTRACTS.md#guards)) refine every slot known to hold it. A
path $`p = x.f_1\cdots f_n`$, $`n\ge 0`$, is a root binding $`x`$ and member
reads; a variable is the path of length zero. Where a read link
$`x.f\mapsto y`$ holds, every arm of $`x`$'s claim states $`f`$ as a stable
view and $`y`$ is claimed at $`B`$, $`x`$ is claimed at those arms with
$`f`$'s view at $`B`$:

```math
\frac{x.f\mapsto y\quad \Gamma\vdash x : \textstyle\bigcup_i \mathsf{Ref}(\ldots;\,f{:}^{\mathsf{st}}A_i;\ldots)\quad \Gamma\vdash y : B}
     {\Gamma\vdash x : \textstyle\bigcup_i \mathsf{Ref}(\ldots;\,f{:}^{\mathsf{st}}B;\ldots)}\ \textsf{read-eq}
```

Sound because the location's stable contract makes it hold $`\rho(y)`$ in
every later world, and a type's meaning is preserved by world extension and
lower levels. The refined claim is a type in $`\Gamma`$, so a call or a
write of another location leaves it; a write of $`x`$'s slot, also through
a captured binding, replaces it. Paths compose: the rule applied at each
segment transports a test of $`x.f.g`$ to $`x`$. A branch over a test of a
path is derived notation:

```math
\frac{\Gamma\vdash p : A\quad \Gamma,\ p \mapsto T_c(A)\vdash_R S_1\quad \Gamma,\ p \mapsto T_{\lnot c}(A)\vdash_R S_2}
     {\Gamma\vdash_R\ \mathsf{if}\ (c(p))\ S_1\ \mathsf{else}\ S_2}\ \textsf{if-path}
```

where $`p\mapsto B`$ means the claim `read-eq` gives each later read of $`p`$.
Tests, their slices and their Boolean combinations are the existing rules'.
Lean checks the segment's stable flag, the read link (the same root and
member), the branch the claim is on, the root's preservation and the slice;
the family's trust supplies only that the location behind a stable member
has a stable contract (F1′, F2). A path's fact ends where its root's slot is
written; it is no
[current-content assertion](SOURCE-MODEL.md#current-content-assertions),
whose facts a call ends.

## The family description

A family description is data in the trusted host contracts
(`tools/host-families.mts`, each instance contributed by the contract file of
its package), typed by one declared type, and reviewed as those contracts
are: every entry carries the declaration text it was reviewed against, and a
check compares each with the installed declaration. It states:

- **package:** the host package's identity, its name, version and the
  digest of its audited installation (the binding check C0 of the
  [compiler API](COMPILER-API.md#binding-the-contract-to-the-implementation)
  generalized: the SHA-256 of every module in the static closure of the
  admitted entry points);
- **root:** the declaration whose extensions are the family's types;
- **tag:** the tag field $`\tau`$, its primitive, and the declaration of its
  constants (an enum the binding check compares with its runtime object, or
  string literals);
- **table rule:** how $`I_t`$ is selected for each tag value, as a fixed rule
  over the declaration graph (the declaration whose tag is the literal $`t`$
  and which extends no other such; then any fallbacks the description lists,
  each with its text);
- **corrections:** the audited members the declarations state required and
  the runtime leaves absent, each read as optional;
- **marker:** the value $`m_F`$ of `[[host]]`;
- **stable-member rule:** which members are stable (for instance every
  property member but the listed allocating ones), with the regression check
  that reads each twice on a corpus;
- **guards:** the modules holding guard bodies, as the `exports` map
  resolves them, and the guards outside the syntax, with their texts.

## Activation

The mechanism is explicit, and nothing activates it by spelling:

- **The family:** a reviewed description in the trusted contracts turns a
  family on, for the package its identity names. Without one, the package's
  declarations are read by the ordinary rules.
- **Membership:** a value is a family member only through the marker. The
  host supplies it: a value at the family's declared types from the
  identified package is assumed to carry it (F1), and no allocation of the
  program owns `[[host]]`.
- **Guards:** a call is a guard call only when its callee resolves to a
  checked export binding of the identified package.

So:

- A **look-alike** a program declares (`interface Node { kind: number }`, an
  object literal with a `kind`) has no marker. Its types are ordinary
  records, narrowed by the ordinary rules; a test of its `kind` drops the arms
  of a union the program wrote, as R3 does.
- A **forged claim** stating a program value at a family shape has no
  derivation, since the marker view admits no program object; a forged
  stable view is refused by the decoder; a forged guard call is an ordinary
  call, since recognition is by resolution.
- An **unidentified package version**, whose installation's digest differs
  from the description's, has no active family: its types are read as
  declared, and its guards at their declared signatures. The binding check
  fails the suite for the installation the front end itself uses, and the
  description is reviewed again.

## Trust rows

Each family adds these assumptions, instantiated with its description.
None is proved; the description's checks bind them to the reviewed files.

- **F1 (member to marker).** Every runtime member of $`F`$, an object the
  package creates as one, corresponds to a model value holding $`m_F`$ under
  `[[host]]`, with its tag in $`\mathcal T_F`$ and the members $`S_t`$ states
  for its tag $`t`$, each holding a value of the member's type.
- **F1′ (marker to shape).** Every model value of an admitted external value
  holding $`m_F`$ under `[[host]]` meets $`S_t`$ for its tag $`t`$ at every
  later step, and the locations of its stable members have stable contracts.
  With F1 the marker and the shape table correspond in both directions,
  which the agreement of two units' residuals needs.
- **F2 (stability).** Each stable member returns the same value on every
  read, and nothing the package does after creation changes it.
- **F3 (guard identity).** The guard bodies the guard check reads are the
  functions Node runs for the package's exports, under the bindings the
  check resolved.
- **F4 (transparent tag reads).** A read of the tag runs no code and throws
  nothing.

## Instances

### The compiler API

The description of `typescript` 7.0.2's syntax trees
([the node invariant](COMPILER-API.md#the-node-invariant)):

- package: `typescript` 7.0.2, its audited installation and closure digest
  (C0); entry point `typescript/unstable/ast`;
- root: `Node`;
- tag: `kind`, a number, its constants the enum `SyntaxKind` of
  `#enums/syntaxKind`, which C1 compares with the runtime object;
  $`\mathcal T_F`$ is its 352 values;
- table rule: the non-generic interface whose `kind` is the literal $`k`$
  and which extends no other such; otherwise the meet of the generic families
  whose kind parameter's bound admits $`k`$, at $`k`$; otherwise `NodeBase`;
- corrections: the [corrections](COMPILER-API.md#corrections) table;
- marker: `"RemoteNode"`;
- stable members: every property member of a shape but `jsDoc`, which
  allocates (reading rule 1), checked by C4;
- guards: `dist/ast/is.generated.js` and `dist/ast/is.js`; outside the
  syntax, `isLeftHandSideExpression` and `isUnaryExpression`.

Its trust rows are T1 (F1 and F2), T1′ (F1′), T2 (F3) and T4, which includes
F4, in [the compiler API's trust](COMPILER-API.md#trust).

### A second instance: Babel's AST

A sketch, not implemented. `@babel/types` describes the trees
`@babel/parser` returns:

- package: `@babel/types` and `@babel/parser` at a reviewed version, with
  the digest of their closures;
- root: `Node`, a union alias of every node interface;
- tag: `type`, a string; its constants are the string literals of the
  interfaces; tag sets are $`\mathsf{strIn}`$;
- table rule: the interface whose `type` is the literal $`t`$;
- marker: a value of `[[host]]` for parser-created nodes, `"BabelNode"`,
  which F1 states of every object the parser returns as a node;
- stable members: none. Babel nodes are plain objects that transforms
  write, so their members are invariant fields, and narrowing by `type`
  follows the existing rule that an object's arm is fixed where it is
  allocated;
- guards: `lib/validators/generated/index.js`, whose bodies are
  `if (!node) return false; if (node.type !== "Identifier") return false;
  return opts == null || shallowEqual(node, opts);`. The guard syntax would
  gain the null test and the `opts` parameter, the latter refused at a call
  passing it: an extension of the one syntax, which every family then reads.

## Implementation plan

The parts land in this order, each a commit of its own with its controls,
the compiler API the first instance throughout.

1. **Tag sets** in Lean's type language, the producer and the wire, with
   the normalization of literal unions at every place a type is built.
2. **The family contract**: the description type, the compiler API's
   description, the shape table, residuals and the marker in the
   declaration graph; the trust rows F1 and F1′. Controls: the residual
   (`parent` of a source file), separate units, the JavaScript typedef, a
   look-alike interface, and a forged claim stating a node at an arm its
   kind excludes.
3. **Guard recognition**: the guard check C2 over the description's modules,
   recognition by resolution, the `host-guard` writing. Controls: one
   evaluation of the argument (`invalid-compiler-api-guard-argument`, under
   Node), a guard outside the syntax, a local function named as a guard, a
   spread argument, `compiler-api-guard-false-branch` from gap to positive,
   and forged claims. Measured: a long guard chain (`isExpression`, 46 kinds).
4. **Stable members**: the stable flag, its decoder restriction, `read-eq`.
   Controls: a readonly program-object path, mutation through an alias and
   by a call, a root written directly and from a closure, a mixed path, a
   segment off a `Type`, and forged claims before the test and after the
   root's write.

Out of order: guards before the family contract read `ts.isIdentifier(n) &&
n.text` with `n: Node` as a test of `kind` on `Node`'s declared record and
lose the narrowing the promise gives today (`compiler-api-kind-narrowing`);
the family contract before tag sets gives residual tags of hundreds of
literals; stable members before guards meet the guard's call, of an
unchecked effect, between the read and its test.
