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
implements [tag sets](#tag-sets), with their Lean proofs; the other parts are
a design, which the pipeline does not implement, and their Lean obligations
are unproved.

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
correction, by the root's form: for an **inheritance root**, the $`t`$ whose
$`I_t`$ reaches $`A`$ through `extends` clauses; for a **union root**, an
alias of a union of declarations, the $`t`$ whose $`I_t`$ the union of $`A`$
reaches through aliases. An alias of a family type is that type. A concrete
union (`Identifier | PrivateIdentifier`) is read as declared.

The members of a shape are read only as readonly views and optional readonly
members, never as invariant fields: an invariant field's record admits no
host value (`ReferenceConjunctions.refsT` requires `NoHost` of every record
with an invariant operand), so a marked shape with one would be uninhabited.
A family whose clients write its objects is outside this mechanism.

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
tag at the tag set of the literals, and the marker. Each replaced shape is
below $`R_u`$: every member of $`R_u`$ is a member of $`S_t`$, a readonly
view whose type contains $`S_t`$'s, which covariance admits, the tag
included; an optional member of $`R_u`$ admits a required one; a member the
join drops is forgotten, which record subtyping allows. So
$`⟦A⟧\subseteq⟦A⟧_u`$. The client never produces $`R_u`$. Shapes with the
same members and different tag values are one arm whose tag is their tag
set. $`K_u`$ is the tag values the unit's tests name (comparisons with the
tag's constants, `case` labels, and the tag sets of the guards it calls)
and those of the family types it names whose tag is a set of literals.

#### Agreement across units

Two units read one family type with different arms, whose record meanings
differ: $`R_u`$ admits objects with the marker and only the common members.
A value one unit passes another at a family type is read by both through
their own arms. That the two readings agree on the values that occur is a
correspondence between the units' sources and the host's objects (F1′): a
marked value with the tag $`t`$ meets $`S_t`$. It is an external obligation
of the import rule's assumption that a separately verified function meets
its importer's reading. It is no premise of any checker proof, no conjunct of
`WorldAdm`, and no subtyping between the units' residuals; `checkJson_safe`
keeps its statement.

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

A call is recognized by **resolution**: its callee resolves, through the
unit's import binding and any re-exports, to the checked export of the
identified package. A same-named local function, a re-bound name, or a
function wrapping a guard is an ordinary call, the wrapper an ordinary
verified function. Where the argument's claimed type is a family type, so
that its marker is stated, the parser writes the call as one evaluation of
the argument followed by the test of its tag:

```math
\frac{g\ \text{a checked guard of}\ F,\quad K_g=\{t_1,\ldots,t_n\},\quad e\ \text{at a family type of}\ F}
     {g(e)\ \leadsto\ \mathsf{let}\ y=e\ \mathsf{in}\ y.\tau\equiv t_1\lor\cdots\lor y.\tau\equiv t_n}\ \textsf{host-guard}
```

with $`y`$ fresh, or $`y`$ the binding itself where $`e`$ is an immutable
name. A call with a spread or with an argument past the guard's parameter is
refused. The guard reads $`\tau`$ once; the chain reads it $`n`$ times. They
agree because the tag is a stable member of every family (F2 holds of
$`\tau`$ in every description; a family whose tag may change has no guard
recognition) and a read of it runs no code and throws nothing (F4), so the
chain has the call's result, effects and exceptions. The fragment gains no
form: Lean sees reads and tests, and narrows both edges by `if-field`
through the family union, since the test is the guard's body. A guard of
another argument type keeps its declared signature
([user-defined guards](SOURCE-CONTRACTS.md#user-defined-guards)).

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
- **guards:** the modules holding guard bodies, as the `exports` map
  resolves them, and the guards outside the syntax, with their texts.

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
- root: `Node`, an inheritance root;
- tag: `kind`, a number, its constants the enum `SyntaxKind` of
  `#enums/syntaxKind`, which C1 compares with the runtime object;
  $`\mathcal T_F`$ is its 352 values;
- table: `literal`, excluding interfaces that extend another candidate with
  the same tag (so `PropertyAccessExpression` is selected, not its two
  refinements);
  `generic` over `Token<k>` and `KeywordTypeNode<k>`; `base` `NodeBase`
  (`JSTypeAliasDeclaration`, `JSImportDeclaration`);
- corrections: the [corrections](COMPILER-API.md#corrections) table;
- marker: `"RemoteNode"`;
- stable members: every property member of a shape but `jsDoc`, which
  allocates (reading rule 1), checked by C4;
- guards: `dist/ast/is.generated.js` and `dist/ast/is.js`; outside the
  syntax, `isLeftHandSideExpression` and `isUnaryExpression`.

Its rows are T1 (F1 and F2), T1′ (F1′), T2 (F3) and T4, which includes F4
([the compiler API's trust](COMPILER-API.md#trust)).

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
