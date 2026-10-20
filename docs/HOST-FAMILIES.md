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
[compiler API](COMPILER-API.md) is the first instance. The pipeline
implements [tag sets](#tag-sets), with their Lean proofs, and
[the family contract](#the-family-contract) in the front end, whose readings
the checker reads by its ordinary rules; [guard recognition](#guard-recognition)
and [stable members](#stable-members) are a design, which the pipeline does
not implement, and their Lean obligations are unproved.

## The parts

### Tag sets

A tag's values are numbers or strings. A union of two or more literals of
one primitive is one clause of the type language, a **tag set**: for a
finite set $`S`$ of number bit patterns, or of strings, with $`|S|\ge 2`$,
the clause $`\mathsf{numIn}(S)`$ means exactly the numbers whose bit pattern
is in $`S`$, and $`\mathsf{strIn}(S)`$ exactly the strings in $`S`$. Tag sets
are general clauses: a program's union of literals is one as a family's tag
is.

**Normalization.** The literals and tag sets of one primitive in a union are
merged into one set, a set of one element being its literal:

```math
\mathsf{numLit}(b_1)\cup\cdots\cup\mathsf{numLit}(b_n)\cup\mathsf{numIn}(T_1)\cup\cdots\cup\mathsf{numIn}(T_m)
=\mathsf{numIn}(\{b_1,\ldots,b_n\}\cup T_1\cup\cdots\cup T_m)
```

and likewise for strings. Every other clause, and every label of a parameter
or scheme row, is left as it is, so a binder's identity survives. The merge
applies where a union is formed:

- the producer's claims: a type's labels that are literals of one primitive
  are one set row;
- a source annotation's lowering (`SourceTypes.numberLabels`) and a
  declaration's equation (`mergeLiterals`, at a union's arms and at the
  literal `0`, whose two zeros are one set);
- a meet row's clauses (`mergeSets`).

Lean's instantiation of an equation at its arguments forms no label, so a
union a substitution forms (`A | 3` at `A = 1 | 2`) stays a union of
labels; the producer merges the unions it states, and the element rule
below covers the rest. Wherever a set label is formed, each element's own
label is formed beside it. The meaning is unchanged (proved:
`setSem_mergeSets`); the checker's acceptance is not implied by the meaning,
which is why coverage, elimination, slicing and key enumeration below each
read sets directly.

**Elements.** A graph states, for a literal, a label whose row is that
literal, where it has one (`NormalGraph.literal`); a reader checks the
label's row before reading it so (`elementLabel`). A set label all of whose
elements have labels has those labels as its **members**.

**Subtyping.** Inclusion of sets, and every tag set is within its
primitive:

```math
\frac{S\subseteq T}{\mathsf{numIn}(S)\le\mathsf{numIn}(T)}
\qquad
\frac{b\in S}{\mathsf{numLit}(b)\le\mathsf{numIn}(S)}
\qquad
\frac{}{\mathsf{numIn}(S)\le\mathsf{Number}}
```

A source set is also covered by a target union whose clauses cover its
elements between them, each element by one:

```math
\frac{\forall b\in S.\ \exists i.\ \mathsf{numLit}(b)\le d_i}
     {\mathsf{numIn}(S)\le d_1\cup\cdots\cup d_m}
```

tried only where no one target clause covers the set.

**Elimination.** A union of labels in one immutable slot is eliminated
member by member (`unionVar`): a set label by its elements' labels. So a
dispatch over a set's elements (a computed key, an equality of two operands
of several singletons) reads each element as a label of its own.

**Tests.** A test answers on a tag set where all its elements answer the
same way, and otherwise element by element:

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
slice by `strEq`, and their falsy part is `""` if $`S`$ holds it. A slice
splits a set label into the labels of the elements it keeps, where the
graph has them (`tagSlice`); where it does not, the set label is kept, and a
claim of the elements the test leaves is checked element by element
(`setSlice`). A passed equality with a singleton the target's set holds
leaves the operand in the target (`familyMember`). A field test reaches the
record arms through the field slice, a set-valued field answering as its
elements do. A field's current contents at a set are its elements' atoms
(`HeapKnowledge.primitive`). Clause selection
([union shapes](UNION-SHAPES.md), R2 and R3) reads a set as the literals it
admits. A computed key at a tag set enumerates its elements, as a key at a
union of literals does, in a read and in a key-adding allocation
(`splitSets`, `KeyedOk`).

**Wire.** A tag set is `{"numIn": {"bits": [b, …]}}` or
`{"strIn": {"values": [s, …]}}`, sorted and distinct, at least two; a
decoder refuses any other list (`RequestJson`, `type-graph.mts`). Its strings
are well-formed Unicode, as every wire string is
([wire text](REQUEST-PROTOCOL.md#wire-text)). Numbers
are ordered by their bit patterns as unsigned integers, strings
lexicographically by Unicode code point: Lean's `String` order, OCaml's byte
order of UTF-8 and `codePointLess` in TypeScript, whose own `<` compares UTF-16
code units and would order U+10000 below U+E000.

**Cost.** The demonstrated cost is a residual arm's tag
([residuals](#residuals)): 20 record arms beside one arm whose tag was a
union of 330 literals took 9.2 s through `verify-source.mts` (cbe2893,
2026-10-16). A tag set makes such a union one clause and one evidence node.
Sorting, inclusion and slicing still take time proportional to the sets'
sizes, a split into members as many labels as elements, and the record
arms' own cost grows with their number (100 record arms exceeded the 30 s
limit, same measurement).

Lean: the clauses `numIn` and `strIn` of `PositiveNormalization.Clause` with
their meaning, meets (`meet_sound`), coverings (`Covers.sound`,
`ClauseCovered.sound`), normalization (`setSem_mergeSets`,
`setSem_mergeSets_row`), elements (`Clause.elements`, `rowSem_elements`,
`elementLabel_sound`, `members_sound`), tests (`tagClause_sound`,
`tagSlice_sound`, `setSlice_sound`, `familyMember_sound`) and keys
(`keyed_values_safe`).

### The family contract

A family description $`F`$ ([below](#the-family-description)) gives a
**shape table**: for each tag value $`t\in\mathcal T_F`$, the record type
$`S_t`$, with the family's **marker**, a required readonly view of the
model's reserved key `[[host]]` at the string literal $`m_F`$, the tag at
the literal $`t`$, and the members of the declaration $`I_t`$ the
description's table selects, with the description's corrections applied.
The model's host objects own `[[host]]`, and no allocation of the program
does ([host classification](COMPILER-API.md#the-host-classification)), so no
program object meets the marker.

A family type $`A`$, a declared type of the family whose tag is no set of
literals (an abstract base, the root, an alias of one), is the union of the
shapes of its **members**:

```math
\frac{A\ \text{a family type of}\ F,\quad \text{the tag of}\ A\ \text{not a set of literals}}
     {⟦A⟧=\textstyle\bigcup\{\,S_t \mid t\in\mathrm{members}_F(A)\,\}}\ \textsf{family-union}
```

$`\mathrm{members}_F(A)`$ is computed on the declaration graph before any
correction or flattening, by the root's form: for an **inheritance root**, the $`t`$ whose
$`I_t`$ reaches $`A`$ through `extends` clauses; for a **union root**, an
alias of a union of declarations, the $`t`$ whose $`I_t`$ the union of $`A`$
reaches through aliases. An alias of a family type is that type. A concrete
union (`Identifier | PrivateIdentifier`) is read as declared.

The members of a shape are read only as readonly views and optional readonly
members, never as invariant fields: an invariant field's record admits no
host value (`ReferenceConjunctions.refsT` requires `NoHost` of every record
with an invariant operand), so a marked shape with one would be uninhabited.
A family whose clients write its objects is outside this mechanism.

$`\mathrm{members}_F`$ and the table are computed on the declarations as
declared; a shape then **flattens** $`I_t`$: its own members and, for each
other name, the declaration of it nearest $`I_t`$ along `extends`. A name two
bases state through declarations neither of which extends the other is
refused, since its contract would be their meet. A declaration whose tag is
a literal the table selects another declaration for (a **refinement**,
`PropertyAccessEntityNameExpression`) is read as its own flattened members
with the marker, so its narrower members are kept; a test of the tag gives
the selected shape, never a refinement sharing its tag. A family type keeps
its declaration's identity, its equation the union; the identity alone
relates nothing.

A generic shape source is read as its application at the tag, its one type
parameter; a generic declaration with another parameter is refused. The arms of
one generic declaration at several selected tags are one application at
their tag set where the declaration's other members do not mention its tag
parameter, so that the application at the set is the union of the
applications at each tag; otherwise each tag is its own arm.

In the declaration graph (`tools/host-families.mts` interprets the
description, `tools/declaration-graph.mts` writes the readings) the marker is
the optional `host` field of an object type term, which only a family's
reading writes and which Lean lowers to the required readonly view of
`hostKey` at the marker's string (`objectClause`); a declared member's key is
never a reserved key. A shape is a definition whose bases are one per
method it states required, a definition of that method alone, so that every
shape stating a generic method shares its one method head whatever other
methods it overrides; a member a reading states optional, by its
declaration or by a correction at any tag the reading covers (a literal
declaration's tags, a generic declaration's every application, so every
generic arm), is that reading's own optional member. A residual forgets a method some
replaced shape states optional, so it relates both to the shapes stating it
required, through the shared definition, and to those stating it optional;
an optional property it holds optional. The base shapes, the residuals and the method definitions are
definitions of the module `tscert/family/<marker>`, named by what they read:
the declaration and method, or the declaration, the number of tags and a
digest of the tag set.

#### Residuals

A unit's family union keeps the shapes of the tag values $`K_u`$ its tests
and types name, and one residual arm for the rest, the join of the shapes it
replaces:

```math
⟦A⟧_u=\textstyle\bigcup\{\,S_t\mid t\in K_u\cap\mathrm{members}_F(A)\,\}\ \cup\ R_u,
\qquad
R_u=\textstyle\bigsqcup\{\,S_t\mid t\in\mathrm{members}_F(A)\setminus K_u\,\}
```

The join of records keeps the members every operand has, each at the union
of its operands' types and optional where any operand has it optional, the
tag at the tag set of the literals, and the marker. The join over-approximates
the union it replaces: it forgets the correlation between a member and the
tag, and the members some shapes lack (of shapes `{kind: 1, x: number}` and
`{kind: 2, y: string}` it requires neither `x` nor `y`), so two selections
give a family type different meanings. Each replaced shape is
below $`R_u`$: every member of $`R_u`$ is a member of $`S_t`$, a readonly
view whose type contains $`S_t`$'s, which covariance admits, the tag
included; an optional member of $`R_u`$ admits a required one; a member the
join drops is forgotten, which record subtyping allows. So
$`⟦A⟧\subseteq⟦A⟧_u`$. The client never produces $`R_u`$. Shapes with the
same members and different tag values are one arm whose tag is their tag
set.

#### The run's selection

A verification run has one selection $`K`$ for each family, computed in the
front end before any module is lowered, and every module the run lowers
reads the family with it. $`K`$ is the tag values the run's
**candidate modules** name: the checked module and, transitively, each
program module it imports a function from by a value import, the modules
the run may lower; a candidate the run leaves unlowered, or a qualified
read that falls back to its ordinary signature, keeps $`K`$. A module names
the tag constants it compares by equality and its `case` labels, the tag
sets of the guards it calls, and the tags of the family types it names whose
tag is a set of literals, through the package's aliases. Its arms are in
tag order, each at the least tag it holds, the residual last. A family type
named only through a program alias of another module, outside the
candidates, and a program alias written as a generic shape's tag argument,
name no tag: those tags stay in the residual, a loss of precision only, since
the residual admits every shape it replaces.

One selection per run makes two modules' readings of a family declaration
the same definitions, which the structural comparison of a
[qualified import](SOURCE-MODEL.md#certified-imports) requires; with
different selections their residuals would differ in meaning, not only in
form. A run's own selection is a fact of the front end, so no producer
proposal and no checker premise states it.

#### Agreement across runs

Two runs read one family type with different arms, whose record meanings
differ: $`R_u`$ admits objects with the marker and only the common members.
A value a unit of one run passes a unit verified in another at a family
type is read by both through their own arms. That the two readings agree on the values that occur is a
correspondence between the units' sources and the host's objects (F1′): a
marked value with the tag $`t`$ meets $`S_t`$. It is an external obligation
of the import rule's assumption that a separately verified function meets
its importer's reading. It is no premise of any checker proof, no conjunct of
`WorldAdm`, and no subtyping between the units' residuals; `checkJson_safe`
keeps its statement.

### Guard recognition

A guard of a family is read from an audited table of what its code does,
never from its name or its declared predicate. A declaration such as
`isTypeAliasDeclaration(node: Node): node is TypeAliasDeclaration` is the
package author's statement, and it is false: the function also accepts
`JSTypeAliasDeclaration`, a JSDoc `@typedef`, whose kind is 345 where
`TypeAliasDeclaration`'s is 266. Read at that predicate, as an imported
guard's declared type is
([user-defined guards](SOURCE-CONTRACTS.md#user-defined-guards)), the program
`isTypeAliasDeclaration(n) ? n.kind : undefined` typed
`SyntaxKind.TypeAliasDeclaration | undefined` verifies and returns 345 under
Node. No guard of a family is read at its declared predicate: a guard the
table lists narrows by its entry, and every other is read at its declared
parameters and result without predicate, narrowing nothing. So is every
other function of the host package declaring a predicate, the sync API's
`isUnionType(type: Type)` among them (`invalid-compiler-api-sync-guard`):
a predicate of the package narrows only by an audited entry.

It is an instance of the [effects vision](#stable-members): an operation
proved stable for a structure makes the effect-free rule sound for code
using only it. A listed guard, called on an established member of the
family, reads one member of its argument, the tag, which is stable (F2) and
whose read runs no code (F4); the call has no other effect, so code calling
only listed guards and reading stable members, a callback among it, is
checked by the rules for code without calls.

#### The guard table

The trusted boundary is a **guard table** in the family description, pinned
to the digest of the audited closure (C0). Each entry records:

- the guard's **export identity** and its **resolution**: the package entry
  point and export name; the resolution conditions, those Node enables
  (`node`, `import`, `module-sync`, `node-addons`, with `default`); the
  module the entry point resolves to; the module declaring the function, by
  its path in the package; and the dependency edges, each helper and enum
  binding the function reads, by its importing module, local name, the
  module it resolves to and the name that module exports; with the reviewed
  text of the function and of each helper;
- its **kind**: a *node guard*, whose one parameter is a member of the
  family, or a *tag guard*, whose one parameter is a tag value;
- its **domain**: for a node guard the family type its parameter is
  declared at, for a tag guard the tag's primitive;
- its exact tag set $`K_g\subseteq\mathcal T_F`$: the tags for which the
  guard returns `true`, for every member of the domain.

The entry states that, for every argument in its domain, the guard
returns `true` exactly when the argument's tag (a tag guard: the argument)
is in $`K_g`$, reads nothing of its argument but the tag, runs no other
code, throws nothing, and returns the same answer whatever it receives
beyond its one parameter (further arguments, a receiver).

Before the table is activated, the front end checks each entry against
the package as Node loads it, once per process, reading the package's
modules with a compiler of its own. The table's conditions must be the ones
Node enables in the running process, read through a resolve hook, and no
flag may preserve symlinks. The entry point, by the package's name,
resolves through Node's own resolver to the recorded module. Before loading
it, the front end reads and parses its complete executable closure from disk.
Every static import and export-from, including its attributes, resolves from
its importing module through Node's resolver; errors, queries and fragments
refuse the table. The module set, SHA-256 file digests and binding edges
(importing module, local name, target module, exported name, attributes and
import/export form) equal the table's reviewed closure. Dynamic imports,
require/createRequire, import.meta, await and eval/Function capabilities are
outside the recorded loading forms and refused. The file digests bind other
indirect execution to the reviewed code. A closure mismatch leaves every
module unevaluated by activation. Over the unchanged installation, Node then
loads the entry in the front end's own process: each entry's export is a
function whose text is the entry's, the very function the recorded module
exports, which declares it with that text and assigns it nowhere. The
function's dependency closure, each free name a function of its module or
a named import without attributes that Node resolves from the importing
module to a module of the package and that the loaded module exports, has
exactly the entry's helpers and binding edges, each helper of exactly its
reviewed text, as loaded where it is exported. A mismatch, or a load Node
refuses, like a digest
mismatch, leaves the family without guards, each read without predicate. File digests alone do not pin
resolution, since a manifest or a re-export can select other code among
files already hashed.

The table is **generated and reviewed**, not computed by the front end at
run time. A generator reads each export's function with the front end's
parser and accepts it only in this syntax, whose recognition contract is
complete and fails closed:

```math
\begin{aligned}
b &::= \mathtt{return}\ c \mid \mathtt{const}\ y\ \mathtt{=}\ x.\tau\mathtt{;\ return}\ c \mid \mathtt{switch\ (}x.\tau\mathtt{)\ \{\ \overline{\mathtt{case}\ \kappa:}\ \mathtt{return\ true;\ default: return\ false;}\ \}}\\
c &::= e\ \mathtt{===}\ \kappa \mid e\ \mathtt{>=}\ \kappa \mid e\ \mathtt{<=}\ \kappa \mid c\ \mathtt{||}\ c \mid c\ \mathtt{\&\&}\ c \mid h(e)\\
e &::= x.\tau \mid y \mid x
\end{aligned}
```

with $`\tau`$ the tag field, $`x`$ the one parameter and $`\kappa`$ a tag
constant. The contract, every condition checked on the resolved files:

- a plain function declaration with one plain parameter: no rest
  parameter, no initializer, no optional second parameter, not `async`,
  not a generator; its body reads neither `this` nor `arguments`;
- a node guard reads only $`x.\tau`$; a tag guard reads only $`x`$;
- a **public tag guard**, an export whose parameter is a tag value a
  program may pass any number of its primitive, is built from equalities
  alone, transitively through its helpers, so its answer is `true` exactly
  on the literals of $`K_g`$ for every value of the primitive;
- a **family helper**, a tag-taking function called only by guards of the
  table on $`x.\tau`$ of a family member, may also test ranges ($`e\
  \mathtt{>=}\ \kappa`$, $`e\ \mathtt{<=}\ \kappa`$) over the tag's
  numeric order (`isTypeNodeKind`), since its domain is the finite
  $`\mathcal T_F`$ (T1) and the table records the exact set the range
  selects there; called with any other argument it is a public tag guard,
  and the contract above applies;
- every helper $`h`$ is a function declaration, of the module or imported
  from a module of the package through a binding the entry's dependency
  edges record, itself under this contract, called with an argument of its
  own domain: a node guard's helper on $`x.\tau`$ is a family helper or a
  tag guard, on $`x`$ a node guard; the helper graph is acyclic; a helper's
  binding is stable: a function declaration no statement of its module
  assigns, or an import binding whose exporting binding is stable under F5;
- every constant $`\kappa`$ is a literal or a member of the tag enum read
  through an import binding the entry's edges record, resolving to the
  enum's audited runtime object, each member of which C1 checks is an own
  data property holding a primitive;
- the body declares nothing but $`y`$ and assigns nothing.

The generator computes $`K_g`$ by evaluating $`c`$ over $`\mathcal T_F`$.
A function outside the contract, or one whose bindings do not resolve, gets
no entry: it loses its predicate and any preservation effect. The
generator's output is compared with the reviewed table in a fast check,
and a Node run of every entry on an object of each tag compares its answers
with $`K_g`$; both are regression evidence for the review, not proofs of
the entry's statement.

#### Calls

A call is recognized by **the loaded binding**: Node's own resolver
resolves the unit's import from the unit's module, loading nothing, to a
URL; where that URL, with no query or fragment, is one of the modules
activation loaded and checked, the export there must be the very function
activation checked. Where Node resolves a module of the program, that
module's `export { g } from "…"` is resolved the same way, from that
module. Any other file of the installation is refused unloaded, so its code
never runs in the front end. An import or a re-export with attributes, a
resolution Node refuses, a module Node resolves that the program does not
hold, and any other binding are no guard: a declaration TypeScript
reaches through another subpath (`invalid-compiler-api-guard-subpath`),
through a re-export whose file Node does not load
(`invalid-compiler-api-guard-reexport-mismatch`), or through another copy
of the package in a nested `node_modules` (`pipeline/test.mts`). The
fixture projects resolve the package as Node does, through installation
links (`pipeline/fixture-links.mts`), with no `paths` for it. A
same-named local function, a re-bound name, or a function wrapping a guard
is an ordinary call, the wrapper an ordinary verified function. A call with
a spread or more than one argument is refused.

**A call on an immutable name** $`x`$, a binding the existing
classification calls immutable (a `const`, or a parameter no statement
assigns), is written as the Fragment's membership test, `tagMember`, of
$`x`$, or of its tag field, against the entry's exact tag set, after the
obligation that $`x`$ is within the guard's declared parameter type $`P`$:

```math
\frac{g\ \text{a node guard of}\ F,\quad K_g=\{t_1,\ldots,t_n\},\quad x\ \text{an immutable name}}
     {g(x)\ \leadsto\ x : P\ \text{checked};\ \ \mathsf{member}(K_g,\ x.\tau)}\ \textsf{host-guard}
```

with $`\mathsf{member}`$ the calculus's tests of each tag in turn,
`true` where one holds
([a membership test](PROGRAM-TYPING.md#a-membership-test)). Lean lowers it
to a read of $`x.\tau`$ into a slot of its own, then the test of that
slot, at the `member-yield` rule: where the test answers `true`, $`x`$'s
object is at the arms of its type whose tag meets $`K_g`$; where `false`,
at those every tag of $`K_g`$ leaves, one after another. The derivation is
one node per tag, whatever the number of arms. Reading a name has no effect
and throws nothing, so the call's single evaluation of its argument is
kept, and the tag is read once, as the guard reads it.

**The domain obligation.** Lean emits a `guard-domain` obligation for each
`tagMember`, checking $`x`$'s claim at $`P`$, the family type with its
marker, whatever the producer claims; a value the checker cannot type there
(an `unknown`, `null`, an arbitrary object) refuses the call, located at the
call. The Fragment decoder refuses a `tagMember` without its domain, an
empty $`K_g`$ included.

**A call on any other argument** (a call's result, a member path) is an
ordinary call of the guard at the signature its entry gives
(`guard-value`, below): the call evaluates the argument once and
propagates its exception, Lean's call rule checks the argument at the
domain, and the promise narrows no binding, since no name holds the
argument. A member path narrows with [stable members](#stable-members).

On the guard's admitted domain the test is exactly the guard: `true` on an
argument whose tag is in $`K_g`$, `false` otherwise, by the entry. The
`false` edge subtracts $`K_g`$ from what $`x`$ already holds: an arm of
the object whose tag is one of the set's tags is dropped, and one whose tag
is a set of several values stays (a `Token` arm of its tag set, under
`isToken`'s `false`), since each tag is decided alone
(`compiler-api-guard-false-branch`, `compiler-api-guards`).

A tag guard's call on an immutable name $`x`$ is the membership test of
$`x`$ itself, $`\mathsf{member}(K_g, x)`$, with $`P`$ the tag's primitive,
and refines $`x`$ on both edges (`isModifierKind(kind)`); a broad number
stays a number on the `false` edge. On any other argument it is an ordinary
call at `tag-guard-value`.

#### Guards as values

A listed guard **used as a value** (`statements.filter(ts.isImportDeclaration)`,
a guard passed to a function) is read at the signature its entry gives, in
place of its declared type. A node guard:

```math
\frac{g\ \text{a node guard of}\ F,\quad K_g,\quad A\ \text{the reading of its domain}}
     {g : (A)\to\mathtt{boolean}\ \{\mathsf{keep},\mathsf{keep}\}\ \land\ (A)\to\textstyle\bigcup_{t\in K_g} S_t\,[\mathsf{guards}\ 0]\ \land\ (A,\ \ldots\mathtt{unknown}[])\to\mathtt{boolean}\ \{\mathsf{keep},\mathsf{keep}\}}\ \textsf{guard-value}
```

A tag guard promises a union of literals, its domain the tag's primitive
$`P`$:

```math
\frac{g\ \text{a tag guard of}\ F,\quad K_g}
     {g : (P)\to\mathtt{boolean}\ \{\mathsf{keep},\mathsf{keep}\}\ \land\ (P)\to\textstyle\bigcup_{t\in K_g}\{t\}\,[\mathsf{guards}\ 0]\ \land\ (P,\ \ldots\mathtt{unknown}[])\to\mathtt{boolean}\ \{\mathsf{keep},\mathsf{keep}\}}\ \textsf{tag-guard-value}
```

with $`\{\mathsf{keep},\mathsf{keep}\}`$ the footprint that changes no value
and no store, $`\bigcup_{t\in K_g} S_t`$ the union of the root's arms under
the run's selection whose tags meet $`K_g`$ (the family's definition
`guard.g`, of one arm per tag of $`K_g`$ where the selection gives each its
own, an arm covering several tags otherwise), and the promise signature of
[user-defined guards](SOURCE-CONTRACTS.md#user-defined-guards), which
narrows the `true` edge. The parameter is the domain: a callback receives
the guard only where its argument type is within $`A`$ (or $`P`$), so its
marker is established at every call; the entry states that further
arguments (an index, the array) and a receiver change no answer, which the
third signature states, so the guard meets a callback of more parameters
(`nodes.filter(ts.isIdentifier)`, `compiler-api-guard-values`). The
declaration document states this signature for the guard's import, so Lean
reads it as any import's declared type; what it rests on is the table.

The run's [selection](#the-runs-selection) includes $`K_g`$ for every
listed node guard its candidate modules call or use as a value, so the
shapes a guard tests are arms of the union it narrows.

#### Trust

The table keeps, for each entry, the statement above (exact $`K_g`$, the
tag the only member read, no other effect, independence of further
arguments and of the receiver), under F2 and F4 of the family, F3 of the
binding, and F5: the enum objects and the module bindings in the table's
recorded dependency closure are never written, by the program or by
external code
(the package builds its enums as ordinary mutable objects and freezes
nothing). A source write to them is refused by the existing rules: a write
through a record or dictionary view of an enum object, `Object.assign` onto
it, and a write of a namespace member or an import binding, each pinned by
a control. It removes the import assumption of every family guard's
declared predicate. The front end's generator and analysis are no part of
the trusted base; the table and its review are.

### Stable members

The description's **stable-member rule** names the members of each shape
whose read gives the same value every time; the tag is always one. The
trusted front end, and nothing else, marks them **stable views** in the
shapes it emits.

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
member), the branch the claim is on, the root's preservation and the slice.
What it assumes is that the location behind a stable member has a stable
contract (F1′'s modeled realization of F2). A path's fact ends where its
root's slot is written; it is no
[current-content assertion](SOURCE-MODEL.md#current-content-assertions),
whose facts a call ends.

## Identity through program code

Family identity and marker requirements follow values and declarations
through the program's own code by the ordinary rules, never by a program's
naming of a package type:

- **Markers** are unique among active descriptions: each $`m_F`$ is owned by
  one description, tied to the resolved identity of its package and root
  declaration.
- **Types:** a program alias of a family type, or a re-export of one, is the
  family type, resolved to the package's declaration. Generic substitution
  keeps a marker requirement: a `T` instantiated at a family type is the
  family type, its marker required wherever `T` is.
- **Values:** F1 holds of the objects the package supplies as family members,
  the results and callback arguments its audited entry-point contracts give
  at family types. A program annotation naming a package type grants no
  provenance: a program value claimed there must be derived, and none is,
  since no program allocation owns `[[host]]`.
- **Wrappers:** a verified function returning a family value it received
  returns it with its marker, the same object. A new object holding it
  (`{ node }`) is an ordinary object whose field holds the host value. A
  spread of it (`{ ...node }`) is refused by the host-operation boundary
  ([operations](COMPILER-API.md#operations-and-their-obligations)), which
  admits no copy of a host object's own keys.
- **Callbacks:** a callback's argument has a marker only where the audited
  contract of the function passing it states a family type; a callback's
  result at a family type must be derived, as any result.
- **Guards:** a re-export of a guard resolves to the checked binding; a
  program function calling a guard is an ordinary verified function, whose
  own promise, if it states one, is proved at its body.

Controls, each with a forged-evidence counterpart refused in search and in
checking: a program alias and a re-export of `Node` read as the family type;
a generic identity function returning a node at `T`; a verified wrapper
returning its node argument; `{ node }` passed where a node is expected
(refused) and its field read as a node (verified); `{ ...node }` (refused at
the spread); a program literal annotated as a node (refused); a callback of
`forEachChild` reading its node argument's members, and one whose result is
claimed at a node type it did not receive (refused); a re-exported guard
narrowing; a wrapper of a guard, read at its own signature.

## The family description

A family description is data in the trusted host contracts
(`tools/host-families.mts`, each instance contributed by the contract file of
its package), of one declared type that one interpreter reads, and reviewed
as those contracts are: every entry carries the declaration text it was
reviewed against, and a check compares each with the installed declaration.
It states:

- **package:** the host package's identity, its name, version and the
  digest of its audited installation (the binding check C0 of the
  [compiler API](COMPILER-API.md#binding-the-contract-to-the-implementation)
  generalized: the SHA-256 of every module in the static closure of the
  admitted entry points);
- **root:** the root declaration and its form, `inheritance` or `union`;
- **tag:** the tag field $`\tau`$, its primitive, and the source of its
  constants: an enum declaration, which the binding check compares with its
  runtime object, or the string literals the shapes state;
- **table:** an ordered list of selection rules the interpreter applies to
  each tag value, the first that selects a declaration giving $`I_t`$:
  - `literal`: the declaration whose tag is the literal $`t`$, excluding
    declarations that extend another candidate with the same tag;
  - `generic`: the meet of the named generic declarations whose tag
    parameter's bound admits $`t`$, instantiated at $`t`$;
  - `base`: a named declaration;
- **corrections:** the audited members the declarations state required and
  the runtime leaves absent, each read as optional, with its text;
- **marker:** the value $`m_F`$ of `[[host]]`;
- **stable members:** every property member of a shape, the tag included, but
  the listed exclusions, with the regression check that reads each twice on
  a corpus;
- **guards:** the [guard table](#the-guard-table), each entry an export's
  identity and reviewed text, its kind, domain and exact tag set.

## Activation

The mechanism is explicit, and nothing activates it by spelling:

- **The family:** a reviewed description in the trusted contracts turns a
  family on, for the package its identity names. Without one, the package's
  declarations are read by the ordinary rules.
- **Membership:** a value is a family member only through the marker, which
  the host supplies for the objects its entry points give as family members
  (F1); no allocation of the program owns `[[host]]`.
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

Each family adds these obligations to the host model it is part of. They
are not a host model by themselves: the compiler instance relies as well on
T4's correspondence between runtime objects, their reads and the modeled
operations, and on the audited contracts of its entry points
([trust](COMPILER-API.md#trust)). None is proved; the description's checks
bind them to the reviewed files.

- **F1 (supplied members).** Every object the package supplies as a family
  member corresponds to a model value holding $`m_F`$ under `[[host]]`, with
  its tag in $`\mathcal T_F`$ and the members $`S_t`$ states for its tag
  $`t`$, each holding a value of the member's type.
- **F1′ (modeled realization).** Every model value of an admitted external
  value holding $`m_F`$ under `[[host]]` meets $`S_t`$ for its tag $`t`$ at
  every later step, and the locations of its stable members have stable
  contracts. This is the model's side: what F2 says of the runtime, F1′ says
  of the world the run is checked in, and with F1 it makes the marker and the
  shape table correspond in both directions, which the agreement of two
  units' residuals needs.
- **F2 (runtime stability).** Each stable member, the tag among them,
  returns the same value on every read, and nothing the package or its
  clients do after creation changes it.
- **F3 (guard identity).** Each guard table entry's statement holds of the
  function Node runs for its export identity, resolved as the entry
  records, under the audited digest. Activation reads that resolution from
  the verifying process's Node; F3 assumes the program runs under the same
  Node configuration (its conditions), through ES module resolution, over
  the unchanged installation, with no hook or loader altering resolution.
  The installation is trusted code: the front end executes it to parse the
  program before activation runs. Activation establishes that the reviewed
  table describes that installation as Node loads it, a consistency check
  under these assumptions; it is no defence against an installation
  modified before the front end starts, or a process whose loaded modules
  differ from their files.
- **F5 (unwritten constants).** The enum objects and the module bindings in
  the guard table's recorded dependency closure are never written after the
  package loads, by the program or by external code.
- **F4 (transparent tag reads).** A read of the tag runs no code and throws
  nothing.

## Instances

### The compiler API

The description of `typescript` 7.0.2's syntax trees
([the node invariant](COMPILER-API.md#the-node-invariant)):

- package: `typescript` 7.0.2, its audited installation and closure digest
  (C0); entry point `typescript/unstable/ast`;
- root: `Node`, an inheritance root;
- tag: `kind`, a number, its constants the enum `SyntaxKind` of
  `#enums/syntaxKind`, which C1 compares with the runtime object;
  $`\mathcal T_F`$ is its 352 values;
- table: `literal`, excluding interfaces that extend another candidate with
  the same tag (so `PropertyAccessExpression` is selected, not its two
  refinements);
  `generic` over `Token<k>`, `KeywordTypeNode<k>` and `KeywordExpression<k>`,
  every generic node declaration (the last gives `null`, `true`, `false`,
  `this`, `super` and `import`, which the declarations make expressions);
  `base` `NodeBase` (`JSTypeAliasDeclaration`, `JSImportDeclaration`);
- corrections: the [corrections](COMPILER-API.md#corrections) table;
- marker: `"RemoteNode"`;
- stable members: every property member of a shape but `jsDoc`, which
  allocates (reading rule 1), checked by C4;
- guards: the table of the exports of `typescript/unstable/ast` whose
  functions, in `dist/ast/is.generated.js` and `dist/ast/is.js`, meet the
  recognition contract; `isLeftHandSideExpression` and `isUnaryExpression`,
  which read `expression`, get no entry.

Its rows are T1 (F1 and F2), T1′ (F1′), T2 (F3) and T4, which includes F4
([the compiler API's trust](COMPILER-API.md#trust)).

### A string-tagged stand-in

A test-only stand-in package (`pipeline/string-family-fixture/`), which
`pipeline/test.mts` installs as the host with a description of its own,
shows the mechanism general over the tag's primitive: its units are tagged
by `type`, a string, whose constants are a string enum; its guard table
lists `isName`, an equality, and `isExpression`, through a helper of its
tag, each activated over the stand-in's own modules; `isNameLoosely`, whose
answer depends on an option argument, takes two parameters and has no
entry. Each listed guard's call is the membership test of the family's
string constants and narrows both edges; the unlisted one narrows nothing
(`pipeline/string-family-fixture-project/`, whose `node_modules/typescript`
links the stand-in, so that Node and TypeScript resolve its specifier
alike).

### A second instance: a readonly Babel interface

A sketch, not implemented. Babel's nodes are plain objects that transforms
write; a family's shapes admit readonly members alone, so mutable Babel code
needs a separate model design. What the mechanism covers is code that only
reads trees `@babel/parser` returns, a linter's for instance, under a
restricted client interface:

- package: `@babel/types` and `@babel/parser` at a reviewed version, with
  the digest of their closures;
- root: `Node`, a union root, the alias of a union of the node interfaces;
- tag: `type`, a string; its constants are the string literals of the
  interfaces; tag sets are $`\mathsf{strIn}`$;
- table: `literal`;
- marker: `"BabelNode"`, which F1 states of every object the parser returns
  as a node;
- stable members: every property member. F2 then needs a lifetime shape
  preservation assumption the interface makes true: the client reaches nodes
  only through the parser's result and the readonly shapes, which grant no
  write, and the parser writes no node after it returns;
- guards: `lib/validators/generated/index.js`, whose bodies are
  `if (!node) return false; if (node.type !== "Identifier") return false;
  return opts == null || shallowEqual(node, opts);`. The guard syntax would
  gain the null test and the `opts` parameter, a call passing it refused: an
  extension of the one syntax, which every family then reads.

## Implementation plan

The parts land in this order, each a commit of its own with its controls,
the compiler API the first instance throughout.

1. **Tag sets** in Lean's type language, the producer and the wire, with
   normalization at every place a union is formed, the set coverage rule,
   selection, slicing and computed keys. Controls and acceptance:
   - positive: mixed unions of literals, sets and other clauses; a program
     alias of a literal union; a computed key at a set; a meet of two sets
     and of a set with its primitive; both edges of an equality and of a
     truthiness test; slices to one element and to none; signed zero
     (`0 | -0` against `0`) and a NaN in a set; a source set covered by
     several target clauses;
   - negative: a slice read at an element it excludes; a set covered by a
     target missing one element; malformed encodings (unsorted, duplicated,
     fewer than two elements), refused by the decoder;
   - every existing case keeps its outcome, each change inspected and
     accounted for in the record; literal-heavy cases measured before and
     after; `checkJson_safe`'s statement and `WorldAdm` unchanged.
2. **The family contract**: the description type and its interpreter, the
   compiler API's description, the shape table, residuals and the marker in
   the declaration graph; the trust rows F1 and F1′. Controls: the residual
   (`parent` of a source file), separate units, the JavaScript typedef, a
   look-alike interface, a forged claim stating a node at an arm its kind
   excludes, and the controls of [identity](#identity-through-program-code).
3. **Guard recognition**: the guard table in the family description (each
   entry its export identity and reviewed text, node or tag guard, domain
   and exact $`K_g`$, pinned to the audited digest); its generator under
   the recognition contract and the fast check comparing its output with
   the table; recognition by resolution; `host-guard` and the tag guard's
   writing with the domain obligation; `guard-value` and `tag-guard-value`;
   every unlisted guard of the family without predicate; $`K_g`$ in the
   run's selection; a second instance (below). Controls, each pipeline
   negative run under Node; a forged control rejects a false entailment,
   not an over-approximation, and bypasses the producer in search and in
   checking, at the forged claim:
   - `invalid-compiler-api-js-alias`: `isTypeAliasDeclaration(n) ? n.kind :
     undefined` at `SyntaxKind.TypeAliasDeclaration | undefined`, verified at
     the declared predicate, refused; under Node, on a `@typedef`, 345;
   - the argument evaluated once, through the pipeline: `isIdentifier(next())`
     with `next` counting its calls, the count after the guard asserted 1,
     verified and run under Node, so a parser duplicating the argument
     fails the case;
   - the domain: a guard called on an `unknown`, on `null` claimed through
     a union, and on a program object, each refused at the argument; forged
     claims weakening the obligation (the cast's operand claimed at the
     family type where its derivation gives `unknown`, the cast's claim
     restated without the marker), refused in search and in checking;
   - F5's boundary: a write to `ts.SyntaxKind` through a
     `Record<string, unknown>` view and through `{ Identifier: number }`,
     `Object.assign(ts.SyntaxKind, …)`, and a reassignment of
     `ts.isIdentifier` through the namespace and of an imported
     `isIdentifier`, each refused at the write;
   - the comma in a test position: `(x satisfies T, x.kind === 1) ? x.a : …`
     verified, and its left operand's effects kept (a counter run under
     Node);
   - resolution: an entry whose recorded module or mapping differs from the
     installation's (a stand-in manifest) leaves the guards without
     predicate;
   - `compiler-api-guard-false-branch` from gap to positive; a tag guard on
     both edges (`isAssignmentOperator(op)`);
   - guards as values: `filter(ts.isImportDeclaration)` and `some(n =>
     ts.isIdentifier(n))` within a callback's effect-free footprint
     (positive); a guard value receiving an index, the array and another
     receiver through `filter` and `call`, its answer unchanged (positive,
     run under Node); a tag guard value at a union of literals;
   - recognition by resolution: a re-exported guard narrows; a local
     function named `isIdentifier`, a guard re-bound to a `let`, and a
     wrapper of a guard are ordinary calls, the wrapper read at its own
     signature; a spread argument and an extra argument, refused;
   - an unlisted guard: `isUnaryExpression(n) && n.operand`, refused (no
     predicate);
   - forged claims of false entailments: on a guard's `false` edge the
     argument claimed at one kind that an input reaching that edge
     contradicts (refused); a guard value's promise claimed at shapes that
     exclude an actual `true` answer (refused);
   - the table: the generator's output equals the reviewed table; the
     functions outside the contract are exactly the unlisted exports;
     every entry run under Node on an object of each tag answers
     exactly $`K_g`$ (regression evidence).

   The census record lists the exports the generator leaves out and why
   (range tests outside a family helper, reads beyond the tag), next to the
   expected movements. A second family shows the mechanism general: a stand-in package of
   string-tagged nodes (`type: "A" | "B" | …`), one guard through a checked
   helper, and one guard outside the contract whose answer depends on an
   option argument, which gets no entry and narrows nothing. Guards outside
   the contract stay explicit coverage gaps.

   Measured: a long guard chain (`isExpression`, 46 kinds) through
   `verify-source.mts`, and the `tools/` census before and after. Expected
   in the census, to be recorded in WORK.md as it turns out, with the
   motivating fixtures and their next blockers: the 21 slices of
   `fragment-statements.mts` refused with "missing field elements" read a
   `BindingName` after `if (ts.isIdentifier(node)) return …`, a guard's
   `false` edge on a binding, and are expected past that refusal. The
   "missing field text" (18) and "missing field name" (6) groups read a
   member path after a guard of it (`ts.isIdentifier(m.name) &&
   m.name.text`), and are expected to wait on
   [stable members](#stable-members). `interfacesOf`, a guard closure
   passed to `filter`, is expected to stay refused, for `filter<S>`'s
   overload, which no review states. The uses of `isTypeAliasDeclaration`
   and `isImportDeclaration` that read `name` or `moduleSpecifier` after
   the guard are expected to be refused, since `JSTypeAliasDeclaration` and
   `JSImportDeclaration` hold neither; each is a coverage loss its source
   repairs with a test of the kind.
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
